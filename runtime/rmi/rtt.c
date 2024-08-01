/*
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <buffer.h>
#include <errno.h>
#include <granule.h>
#include <measurement.h>
#include <planes.h>
#include <realm.h>
#include <ripas.h>
#include <s2tt.h>
#include <smc-handler.h>
#include <smc-rmi.h>
#include <smc.h>
#include <status.h>
#include <stddef.h>
#include <string.h>
#include <xlat_defs.h>

/*
 * Validate the map_addr value passed to RMI_RTT_* and RMI_DATA_* commands.
 */
static bool validate_map_addr(unsigned long map_addr,
			      long level,
			      struct rd *rd)
{
	return ((map_addr < realm_ipa_size(rd)) &&
		s2tte_is_addr_lvl_aligned(primary_s2_context(rd), map_addr, level));
}

/*
 * Structure commands can operate on all RTTs except for the root RTT so
 * the minimal valid level is the stage 2 starting level + 1.
 */
static bool validate_rtt_structure_cmds(unsigned long map_addr,
					long level,
					struct rd *rd)
{
	int min_level = realm_rtt_starting_level(rd) + 1;

	if ((level < min_level) || (level > S2TT_PAGE_LEVEL)) {
		return false;
	}
	return validate_map_addr(map_addr, level - 1L, rd);
}

/*
 * Map/Unmap commands can operate up to a level 2 block entry so min_level is
 * the smallest block size.
 */
static bool validate_rtt_map_cmds(unsigned long map_addr,
				  long level,
				  struct rd *rd)
{
	if ((level < S2TT_MIN_BLOCK_LEVEL) || (level > S2TT_PAGE_LEVEL)) {
		return false;
	}
	return validate_map_addr(map_addr, level, rd);
}

/*
 * Entry commands can operate on any entry so the minimal valid level is the
 * stage 2 starting level.
 */
static bool validate_rtt_entry_cmds(unsigned long map_addr,
				    long level,
				    struct rd *rd)
{
	if ((level < realm_rtt_starting_level(rd)) ||
	    (level > S2TT_PAGE_LEVEL)) {
		return false;
	}
	return validate_map_addr(map_addr, level, rd);
}

/*
 * On a change of RIPAS from any other value to RAM, the AP of the target
 * protected IPA must be set to DEFAULT_PROTECTED_OVERLAY_INDEX.
 */
static unsigned long default_protected_ap(const struct s2tt_context *s2_ctx)
{
	return s2tte_update_ap_from_index(s2_ctx, 0UL,
					  DEFAULT_PROTECTED_OVERLAY_INDEX);
}

static unsigned long rtt_create(unsigned long rd_addr,
				unsigned long rtt_addr,
				unsigned long map_addr,
				unsigned long ulevel,
				unsigned long index,
				bool aux)
{
	struct granule *g_rd;
	struct granule *g_tbl;
	struct rd *rd;
	struct s2tt_walk wi;
	unsigned long *s2tt, *parent_s2tt, parent_s2tte;
	long level = (long)ulevel;
	unsigned long ret;
	struct s2tt_context s2_ctx;

	if (!find_lock_two_granules(rtt_addr,
				    GRANULE_STATE_DELEGATED,
				    &g_tbl,
				    rd_addr,
				    GRANULE_STATE_RD,
				    &g_rd)) {
		return RMI_ERROR_INPUT;
	}

	rd = buffer_granule_map(g_rd, SLOT_RD);
	assert(rd != NULL);

	if (!validate_rtt_structure_cmds(map_addr, level, rd)) {
		buffer_unmap(rd);
		granule_unlock(g_rd);
		granule_unlock(g_tbl);
		return RMI_ERROR_INPUT;
	}

	if (aux) {
		if ((!rd->rtt_tree_pp) ||
		    (index == (unsigned long)PRIMARY_S2_CTX_ID) ||
		    (index >= (unsigned long)realm_num_s2_contexts(rd))) {
			buffer_unmap(rd);
			granule_unlock(g_rd);
			granule_unlock(g_tbl);
			return RMI_ERROR_INPUT;
		}
		s2_ctx = *index_to_s2_context(rd, (unsigned int)index);
	} else {
		s2_ctx = *primary_s2_context(rd);
	}

	if ((s2_ctx.enable_lpa2 == false) &&
			(rtt_addr >= (1UL << LM1_XLAT_ADDRESS_SHIFT))) {
		buffer_unmap(rd);
		granule_unlock(g_rd);
		granule_unlock(g_tbl);
		return RMI_ERROR_INPUT;
	}

	/*
	 * Lock the RTT root. Enforcing locking order RD->RTT is enough to
	 * ensure deadlock free locking guarantee.
	 */
	granule_lock(s2_ctx.g_rtt, GRANULE_STATE_RTT);

	/* Unlock RD after locking RTT Root */
	granule_unlock(g_rd);

	s2tt_walk_lock_unlock(&s2_ctx, map_addr, level - 1L, &wi);
	if (wi.last_level != (level - 1L)) {
		ret = pack_return_code(RMI_ERROR_RTT,
					(unsigned char)wi.last_level);
		goto out_unlock_llt;
	}

	parent_s2tt = buffer_granule_map(wi.g_llt, SLOT_RTT);
	assert(parent_s2tt != NULL);

	parent_s2tte = s2tte_read(&parent_s2tt[wi.index]);
	s2tt = buffer_granule_map(g_tbl, SLOT_DELEGATED);
	assert(s2tt != NULL);

	if (s2tte_is_unassigned_empty(&s2_ctx, parent_s2tte)) {
		s2tt_init_unassigned_empty(&s2_ctx, s2tt, parent_s2tte);

		/*
		 * Increase the refcount of the parent, the granule was
		 * locked while table walking and hand-over-hand locking.
		 * Atomicity and acquire/release semantics not required because
		 * the table is accessed always locked.
		 */
		__granule_get(wi.g_llt);

	} else if (s2tte_is_unassigned_ram(&s2_ctx, parent_s2tte)) {
		/*
		 * @TODO: Double check that the AP in this case are correct, as
		 * the spec states that on a change of RIPAS from any other value
		 * to RAM the AP should be equivalent to the overlay index
		 * DEFAULT_PROTECTED_OVERLAY_INDEX but here we are creating
		 * a new table.
		 */
		s2tt_init_unassigned_ram(&s2_ctx, s2tt, default_protected_ap(&s2_ctx));
		__granule_get(wi.g_llt);

	} else if (s2tte_is_unassigned_ns(&s2_ctx, parent_s2tte)) {
		s2tt_init_unassigned_ns(&s2_ctx, s2tt);
		__granule_get(wi.g_llt);

	} else if (s2tte_is_unassigned_destroyed(&s2_ctx, parent_s2tte)) {
		s2tt_init_unassigned_destroyed(&s2_ctx, s2tt, parent_s2tte);
		__granule_get(wi.g_llt);

	} else if (s2tte_is_assigned_destroyed(&s2_ctx, parent_s2tte,
					       level - 1L)) {
		unsigned long block_pa;

		/*
		 * We should observe parent assigned s2tte only when
		 * we create tables above this level.
		 */
		assert(level > S2TT_MIN_BLOCK_LEVEL);

		block_pa = s2tte_pa(&s2_ctx, parent_s2tte, level - 1L);

		s2tt_init_assigned_destroyed(&s2_ctx, s2tt, block_pa, level,
					     parent_s2tte);

		/*
		 * Increase the refcount to mark the granule as in-use. refcount
		 * is incremented by S2TTES_PER_S2TT (ref RTT unfolding).
		 */
		__granule_refcount_inc(g_tbl, (unsigned short)S2TTES_PER_S2TT);

	} else if (s2tte_is_assigned_empty(&s2_ctx, parent_s2tte, level - 1L)) {
		unsigned long block_pa;

		/*
		 * We should observe parent assigned s2tte only when
		 * we create tables above this level.
		 */
		assert(level > S2TT_MIN_BLOCK_LEVEL);

		block_pa = s2tte_pa(&s2_ctx, parent_s2tte, level - 1L);

		s2tt_init_assigned_empty(&s2_ctx, s2tt, block_pa, level,
					 parent_s2tte);

		/*
		 * Increase the refcount to mark the granule as in-use. refcount
		 * is incremented by S2TTES_PER_S2TT (ref RTT unfolding).
		 */
		__granule_refcount_inc(g_tbl, (unsigned short)S2TTES_PER_S2TT);

	} else if (s2tte_is_assigned_ram(&s2_ctx, parent_s2tte, level - 1L)) {
		unsigned long block_pa;

		/*
		 * We should observe parent valid s2tte only when
		 * we create tables above this level.
		 */
		assert(level > S2TT_MIN_BLOCK_LEVEL);

		/*
		 * Break before make. This may cause spurious S2 aborts.
		 */
		s2tte_write(&parent_s2tt[wi.index], 0UL);
		s2tt_invalidate_block(&s2_ctx, map_addr);

		block_pa = s2tte_pa(&s2_ctx, parent_s2tte, level - 1L);

		/*
		 * @TODO: Double check that the AP in this case are correct, as
		 * the spec states that on a change of RIPAS from any other value
		 * to RAM the AP should be equivalent to the overlay index
		 * DEFAULT_PROTECTED_OVERLAY_INDEX but here we are creating
		 * a new table.
		 */
		s2tt_init_assigned_ram(&s2_ctx, s2tt, block_pa, level,
					default_protected_ap(&s2_ctx));
		/*
		 * Increase the refcount to mark the granule as in-use. refcount
		 * is incremented by S2TTES_PER_S2TT (ref RTT unfolding).
		 */
		__granule_refcount_inc(g_tbl, (unsigned short)S2TTES_PER_S2TT);

	} else if (s2tte_is_assigned_ns(&s2_ctx, parent_s2tte, level - 1L)) {
		unsigned long block_pa;

		/*
		 * We should observe parent assigned_ns s2tte only when
		 * we create tables above this level.
		 */
		assert(level > S2TT_MIN_BLOCK_LEVEL);

		/*
		 * Break before make. This may cause spurious S2 aborts.
		 */
		s2tte_write(&parent_s2tt[wi.index], 0UL);
		s2tt_invalidate_block(&s2_ctx, map_addr);

		block_pa = s2tte_pa(&s2_ctx, parent_s2tte, level - 1L);

		s2tt_init_assigned_ns(&s2_ctx, s2tt, parent_s2tte,
				      block_pa, level, parent_s2tte);

		/*
		 * Increment the refcount on the parent for the new RTT we are
		 * about to add. The NS block entry doesn't have a refcount
		 * on the parent RTT.
		 */
		__granule_get(wi.g_llt);

	} else if (s2tte_is_table(&s2_ctx, parent_s2tte, level - 1L)) {
		ret = pack_return_code(RMI_ERROR_RTT,
					(unsigned char)(level - 1L));
		goto out_unmap_table;

	} else {
		assert(false);
	}

	ret = RMI_SUCCESS;

	granule_set_state(g_tbl, GRANULE_STATE_RTT);

	parent_s2tte = s2tte_create_table(&s2_ctx, rtt_addr, level - 1L);
	s2tte_write(&parent_s2tt[wi.index], parent_s2tte);

out_unmap_table:
	buffer_unmap(s2tt);
	buffer_unmap(parent_s2tt);
out_unlock_llt:
	granule_unlock(wi.g_llt);
	granule_unlock(g_tbl);
	buffer_unmap(rd);
	return ret;
}

unsigned long smc_rtt_create(unsigned long rd_addr,
			     unsigned long rtt_addr,
			     unsigned long map_addr,
			     unsigned long ulevel)
{
	return rtt_create(rd_addr, rtt_addr, map_addr, ulevel, 0UL, false);
}

unsigned long smc_rtt_aux_create(unsigned long rd_addr,
				 unsigned long rtt_addr,
				 unsigned long map_addr,
				 unsigned long ulevel,
				 unsigned long index)
{
	return rtt_create(rd_addr, rtt_addr, map_addr, ulevel, index, true);
}

static void rtt_fold(unsigned long rd_addr,
		     unsigned long map_addr,
		     unsigned long ulevel,
		     unsigned long index,
		     bool aux,
		     struct smc_result *res)
{
	struct granule *g_rd;
	struct granule *g_tbl;
	struct rd *rd;
	struct s2tt_walk wi;
	unsigned long *table, *parent_s2tt, parent_s2tte;
	long level = (long)ulevel;
	unsigned long rtt_addr;
	unsigned long ret;
	unsigned long s2tte_ap;
	struct s2tt_context s2_ctx;

	g_rd = find_lock_granule(rd_addr, GRANULE_STATE_RD);
	if (g_rd == NULL) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	rd = buffer_granule_map(g_rd, SLOT_RD);
	assert(rd != NULL);

	if (!validate_rtt_structure_cmds(map_addr, level, rd)) {
		buffer_unmap(rd);
		granule_unlock(g_rd);
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	if (aux) {
		if ((!rd->rtt_tree_pp) ||
		    (index == (unsigned long)PRIMARY_S2_CTX_ID) ||
		    (index >= (unsigned long)realm_num_s2_contexts(rd))) {
			buffer_unmap(rd);
			granule_unlock(g_rd);
			res->x[0] = RMI_ERROR_INPUT;
			res->x[2] = 0UL;
			return;
		}
		s2_ctx = *index_to_s2_context(rd, (unsigned int)index);
	} else {
		s2_ctx = *primary_s2_context(rd);
	}

	buffer_unmap(rd);
	granule_lock(s2_ctx.g_rtt, GRANULE_STATE_RTT);
	granule_unlock(g_rd);

	s2tt_walk_lock_unlock(&s2_ctx, map_addr, level - 1L, &wi);
	if (wi.last_level != (level - 1L)) {
		ret = pack_return_code(RMI_ERROR_RTT,
					(unsigned char)wi.last_level);
		goto out_unlock_parent_table;
	}

	parent_s2tt = buffer_granule_map(wi.g_llt, SLOT_RTT);
	assert(parent_s2tt != NULL);

	parent_s2tte = s2tte_read(&parent_s2tt[wi.index]);
	if (!s2tte_is_table(&s2_ctx, parent_s2tte, level - 1L)) {
		ret = pack_return_code(RMI_ERROR_RTT,
					(unsigned char)(level - 1L));
		goto out_unmap_parent_table;
	}

	rtt_addr = s2tte_pa(&s2_ctx, parent_s2tte, level - 1L);
	g_tbl = find_lock_granule(rtt_addr, GRANULE_STATE_RTT);

	/*
	 * A table descriptor S2TTE always points to a TABLE granule.
	 */
	assert(g_tbl != NULL);

	table = buffer_granule_map(g_tbl, SLOT_RTT2);
	assert(table != NULL);

	/*
	 * The command can succeed only if all 512 S2TTEs are of the same type.
	 * We first check the table's ref. counter to speed up the case when
	 * the host makes a guess whether a memory region can be folded.
	 */
	if (g_tbl->refcount == 0UL) {
		s2tte_ap = table[0U];
		if (s2tt_is_unassigned_destroyed_block(&s2_ctx, table, &s2tte_ap)) {
			parent_s2tte = s2tte_create_unassigned_destroyed(&s2_ctx, s2tte_ap);
		} else if (s2tt_is_unassigned_empty_block(&s2_ctx, table, &s2tte_ap)) {
			parent_s2tte = s2tte_create_unassigned_empty(&s2_ctx, s2tte_ap);
		} else if (s2tt_is_unassigned_ram_block(&s2_ctx, table, &s2tte_ap)) {
			parent_s2tte = s2tte_create_unassigned_ram(&s2_ctx, s2tte_ap);
		} else if (s2tt_is_unassigned_ns_block(&s2_ctx, table)) {
			parent_s2tte = s2tte_create_unassigned_ns(&s2_ctx);
		} else if (s2tt_maps_assigned_ns_block(&s2_ctx, table, level, &s2tte_ap)) {

			/*
			 * The RMM specification does not allow creating block entries less than
			 * S2TT_MIN_BLOCK_LEVEL for ASSIGNED_NS state.
			 */
			if (level <= S2TT_MIN_BLOCK_LEVEL) {
				ret = pack_return_code(RMI_ERROR_RTT,
						(unsigned char)wi.last_level);
				goto out_unmap_table;
			}
			unsigned long s2tte = s2tte_read(&table[0]);

			/*
			 * Since s2tt_maps_assigned_ns_block() has succedded,
			 * the PA in first entry of the table is aligned at
			 * parent level. Use the TTE from the first entry
			 * directly as it also has the NS attributes to be used
			 * for the parent block entry.
			 */
			parent_s2tte = s2tte_create_assigned_ns(&s2_ctx, s2tte,
								level - 1L, s2tte_ap);
		} else {
			/*
			 * The table holds a mixture of destroyed and
			 * unassigned entries.
			 */
			ret = pack_return_code(RMI_ERROR_RTT,
						(unsigned char)level);
			goto out_unmap_table;
		}
		__granule_put(wi.g_llt);
	} else if (g_tbl->refcount == (unsigned short)S2TTES_PER_S2TT) {

		unsigned long s2tte, block_pa;

		/* The RMM specification does not allow creating block
		 * entries less than S2TT_MIN_BLOCK_LEVEL even though
		 * permitted by the Arm Architecture.
		 * Hence ensure that the table being folded is at a level
		 * higher than the S2TT_MIN_BLOCK_LEVEL.
		 *
		 * A fully populated table cannot be destroyed if that
		 * would create a block mapping below S2TT_MIN_BLOCK_LEVEL.
		 */
		if (level <= S2TT_MIN_BLOCK_LEVEL) {
			ret = pack_return_code(RMI_ERROR_RTT,
						(unsigned char)wi.last_level);
			goto out_unmap_table;
		}

		s2tte = s2tte_read(&table[0]);
		block_pa = s2tte_pa(&s2_ctx, s2tte, level);

		/*
		 * The table must also refer to a contiguous block through the
		 * same type of s2tte, either Assigned or Valid.
		 */
		s2tte_ap = table[0U];
		if (s2tt_maps_assigned_empty_block(&s2_ctx, table, level, &s2tte_ap)) {
			parent_s2tte = s2tte_create_assigned_empty(&s2_ctx,
					block_pa, level - 1L, s2tte_ap);
		} else if (s2tt_maps_assigned_ram_block(&s2_ctx,
							table, level,
							&s2tte_ap)) {
			parent_s2tte = s2tte_create_assigned_ram(&s2_ctx,
								 block_pa,
								 level - 1L,
								 s2tte_ap);
		} else if (s2tt_maps_assigned_destroyed_block(&s2_ctx,
							      table, level, &s2tte_ap)) {
			parent_s2tte = s2tte_create_assigned_destroyed(&s2_ctx,
						block_pa, level - 1L, s2tte_ap);
		/* The table contains mixed entries that cannot be folded */
		} else {
			ret = pack_return_code(RMI_ERROR_RTT,
						(unsigned char)level);
			goto out_unmap_table;
		}

		__granule_refcount_dec(g_tbl, (unsigned short)S2TTES_PER_S2TT);
	} else {
		/*
		 * The table holds a mixture of different types of s2ttes.
		 */
		ret = pack_return_code(RMI_ERROR_RTT,
					(unsigned char)level);
		goto out_unmap_table;
	}

	ret = RMI_SUCCESS;
	res->x[1] = rtt_addr;

	/*
	 * Break before make.
	 */
	s2tte_write(&parent_s2tt[wi.index], 0UL);

	if (s2tte_is_assigned_ram(&s2_ctx, parent_s2tte, level - 1L) ||
	    s2tte_is_assigned_ns(&s2_ctx, parent_s2tte, level - 1L)) {
		s2tt_invalidate_pages_in_block(&s2_ctx, map_addr);
	} else {
		s2tt_invalidate_block(&s2_ctx, map_addr);
	}

	s2tte_write(&parent_s2tt[wi.index], parent_s2tte);

	granule_memzero_mapped(table);
	granule_set_state(g_tbl, GRANULE_STATE_DELEGATED);

out_unmap_table:
	buffer_unmap(table);
	granule_unlock(g_tbl);
out_unmap_parent_table:
	buffer_unmap(parent_s2tt);
out_unlock_parent_table:
	granule_unlock(wi.g_llt);
	res->x[0] = ret;
}

void smc_rtt_fold(unsigned long rd_addr,
		  unsigned long map_addr,
		  unsigned long ulevel,
		  struct smc_result *res)
{
	rtt_fold(rd_addr, map_addr, ulevel, 0UL, false, res);
}

void smc_rtt_aux_fold(unsigned long rd_addr,
		      unsigned long map_addr,
		      unsigned long ulevel,
		      unsigned long index,
		      struct smc_result *res)
{
	rtt_fold(rd_addr, map_addr, ulevel, index, true, res);
}

static void rtt_destroy(unsigned long rd_addr,
			unsigned long map_addr,
			unsigned long ulevel,
			unsigned long index,
			bool aux,
			struct smc_result *res)
{
	struct granule *g_rd;
	struct granule *g_tbl;
	struct rd *rd;
	struct s2tt_walk wi;
	unsigned long *table, *parent_s2tt, parent_s2tte;
	long level = (long)ulevel;
	unsigned long  rtt_addr;
	unsigned long ret;
	struct s2tt_context s2_ctx;
	bool in_par, skip_non_live = false;

	g_rd = find_lock_granule(rd_addr, GRANULE_STATE_RD);
	if (g_rd == NULL) {
		res->x[0] = RMI_ERROR_INPUT;
		res->x[2] = 0UL;
		return;
	}

	rd = buffer_granule_map(g_rd, SLOT_RD);
	assert(rd != NULL);

	if (!validate_rtt_structure_cmds(map_addr, level, rd)) {
		buffer_unmap(rd);
		granule_unlock(g_rd);
		res->x[0] = RMI_ERROR_INPUT;
		res->x[2] = 0UL;
		return;
	}

	if (aux) {
		if ((!rd->rtt_tree_pp) ||
		    (index == (unsigned long)PRIMARY_S2_CTX_ID) ||
		    (index >= (unsigned long)realm_num_s2_contexts(rd))) {
			buffer_unmap(rd);
			granule_unlock(g_rd);
			res->x[0] = RMI_ERROR_INPUT;
			res->x[2] = 0UL;
			return;
		}
		s2_ctx = *index_to_s2_context(rd, (unsigned int)index);
	} else {
		s2_ctx = *primary_s2_context(rd);
	}

	in_par = addr_in_par(rd, map_addr);
	granule_lock(s2_ctx.g_rtt, GRANULE_STATE_RTT);

	s2tt_walk_lock_unlock(&s2_ctx, map_addr, level - 1L, &wi);

	parent_s2tt = buffer_granule_map(wi.g_llt, SLOT_RTT);
	assert(parent_s2tt != NULL);

	parent_s2tte = s2tte_read(&parent_s2tt[wi.index]);

	if ((wi.last_level != (level - 1L)) ||
	    !s2tte_is_table(&s2_ctx, parent_s2tte, level - 1L)) {
		ret = pack_return_code(RMI_ERROR_RTT,
					(unsigned char)wi.last_level);
		skip_non_live = true;
		goto out_unmap_parent_table;
	}

	rtt_addr = s2tte_pa(&s2_ctx, parent_s2tte, level - 1L);

	/*
	 * Lock the RTT granule. The 'rtt_addr' is verified, thus can be treated
	 * as an internal granule.
	 */
	g_tbl = find_lock_granule(rtt_addr, GRANULE_STATE_RTT);

	/*
	 * A table descriptor S2TTE always points to a TABLE granule.
	 */
	assert(g_tbl != NULL);

	/*
	 * Read the refcount value. RTT granule is always accessed locked, thus
	 * the refcount can be accessed without atomic operations.
	 */
	if (g_tbl->refcount != 0UL) {
		ret = pack_return_code(RMI_ERROR_RTT, (unsigned char)level);
		goto out_unlock_table;
	}

	ret = RMI_SUCCESS;
	res->x[1] = rtt_addr;
	skip_non_live = true;

	table = buffer_granule_map(g_tbl, SLOT_RTT2);
	assert(table != NULL);

	if (in_par) {
		/*
		 * @TODO: Though it is a valid implementation if here we reset
		 * the S2APs to default value, we may prefer to preserve the
		 * S2APs if they are identical across entire RTT that has been
		 * deleted.
		 */
		parent_s2tte = s2tte_create_unassigned_destroyed(&s2_ctx,
				s2tte_update_ap_from_index(&s2_ctx, 0UL,
					DEFAULT_PROTECTED_OVERLAY_INDEX));
	} else {
		parent_s2tte = s2tte_create_unassigned_ns(&s2_ctx);
	}

	__granule_put(wi.g_llt);

	/*
	 * Break before make. Note that this may cause spurious S2 aborts.
	 */
	s2tte_write(&parent_s2tt[wi.index], 0UL);

	if (in_par) {
		/* For protected IPA, all S2TTEs in the RTT will be invalid */
		s2tt_invalidate_block(&s2_ctx, map_addr);
	} else {
		/*
		 * For unprotected IPA, invalidate the TLB for the entire range
		 * mapped by the RTT as it may have valid NS mappings.
		 */
		s2tt_invalidate_pages_in_block(&s2_ctx, map_addr);
	}

	s2tte_write(&parent_s2tt[wi.index], parent_s2tte);

	granule_memzero_mapped(table);
	granule_set_state(g_tbl, GRANULE_STATE_DELEGATED);

	buffer_unmap(table);
out_unlock_table:
	granule_unlock(g_tbl);
out_unmap_parent_table:
	if (skip_non_live) {
		res->x[2] = s2tt_skip_non_live_entries(&s2_ctx, map_addr,
						       parent_s2tt, &wi);
	} else {
		res->x[2] = map_addr;
	}
	buffer_unmap(parent_s2tt);
	granule_unlock(wi.g_llt);
	buffer_unmap(rd);
	granule_unlock(g_rd);
	res->x[0] = ret;
}

void smc_rtt_destroy(unsigned long rd_addr,
		     unsigned long map_addr,
		     unsigned long ulevel,
		     struct smc_result *res)
{
	rtt_destroy(rd_addr, map_addr, ulevel, 0UL, false, res);
}

void smc_rtt_aux_destroy(unsigned long rd_addr,
			 unsigned long map_addr,
			 unsigned long ulevel,
			 unsigned long index,
			 struct smc_result *res)
{
	rtt_destroy(rd_addr, map_addr, ulevel, index, true, res);
}

enum map_unmap_ns_op {
	MAP_NS,
	UNMAP_NS
};

/*
 * We don't hold a reference on the NS granule when it is
 * mapped into a realm. Instead we rely on the guarantees
 * provided by the architecture to ensure that a NS access
 * to a protected granule is prohibited even within the realm.
 */
static void map_unmap_ns(unsigned long rd_addr,
			  unsigned long map_addr,
			  long level,
			  unsigned long host_s2tte,
			  enum map_unmap_ns_op op,
			  struct smc_result *res)
{
	struct granule *g_rd;
	struct rd *rd;
	unsigned long *s2tt, s2tte;
	struct s2tt_walk wi;
	struct s2tt_context s2_ctx;

	g_rd = find_lock_granule(rd_addr, GRANULE_STATE_RD);
	if (g_rd == NULL) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	rd = buffer_granule_map(g_rd, SLOT_RD);
	assert(rd != NULL);

	s2_ctx = *primary_s2_context(rd);

	if ((op == MAP_NS) &&
	    (!host_ns_s2tte_is_valid(&s2_ctx, host_s2tte, level))) {
		buffer_unmap(rd);
		granule_unlock(g_rd);
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	if (!validate_rtt_map_cmds(map_addr, level, rd)) {
		buffer_unmap(rd);
		granule_unlock(g_rd);
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	/* Check if map_addr is outside PAR */
	if (addr_in_par(rd, map_addr)) {
		buffer_unmap(rd);
		granule_unlock(g_rd);
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	buffer_unmap(rd);
	granule_lock(s2_ctx.g_rtt, GRANULE_STATE_RTT);
	granule_unlock(g_rd);

	s2tt_walk_lock_unlock(&s2_ctx, map_addr, level, &wi);

	/*
	 * For UNMAP_NS, we need to map the table and look
	 * for the end of the non-live region.
	 */
	if ((op == MAP_NS) && (wi.last_level != level)) {
		res->x[0] = pack_return_code(RMI_ERROR_RTT,
						(unsigned char)wi.last_level);
		goto out_unlock_llt;
	}

	s2tt = buffer_granule_map(wi.g_llt, SLOT_RTT);
	assert(s2tt != NULL);

	s2tte = s2tte_read(&s2tt[wi.index]);

	if (op == MAP_NS) {
		unsigned long s2tte_ap;

		if (!s2tte_is_unassigned_ns(&s2_ctx, s2tte)) {
			res->x[0] = pack_return_code(RMI_ERROR_RTT,
						(unsigned char)level);
			goto out_unmap_table;
		}

		s2tte_ap = host_s2tte;

		/*
		 * Set the access permissions that are not
		 * controlled by the host.
		 */
		s2tte_ap &= ~MASK(S2TTE_PERM_XN);
		s2tte_ap |= S2TTE_PERM_XU_XNP;

		s2tte = s2tte_create_assigned_ns(&s2_ctx, host_s2tte,
						 level, s2tte_ap);
		s2tte_write(&s2tt[wi.index], s2tte);

	} else if (op == UNMAP_NS) {
		/*
		 * The following check also verifies that map_addr is outside
		 * PAR, as valid_NS s2tte may only cover outside PAR IPA range.
		 */
		bool assigned_ns = s2tte_is_assigned_ns(&s2_ctx, s2tte,
							wi.last_level);

		if ((wi.last_level != level) || !assigned_ns) {
			res->x[0] = pack_return_code(RMI_ERROR_RTT,
						(unsigned char)wi.last_level);
			goto out_unmap_table;
		}

		s2tte = s2tte_create_unassigned_ns(&s2_ctx);
		s2tte_write(&s2tt[wi.index], s2tte);
		if (level == S2TT_PAGE_LEVEL) {
			s2tt_invalidate_page(&s2_ctx, map_addr);
		} else {
			s2tt_invalidate_block(&s2_ctx, map_addr);
		}
	}

	res->x[0] = RMI_SUCCESS;

out_unmap_table:
	if (op == UNMAP_NS) {
		res->x[1] = s2tt_skip_non_live_entries(&s2_ctx, map_addr,
						       s2tt, &wi);
	}
	buffer_unmap(s2tt);
out_unlock_llt:
	granule_unlock(wi.g_llt);
}

unsigned long smc_rtt_map_unprotected(unsigned long rd_addr,
				      unsigned long map_addr,
				      unsigned long ulevel,
				      unsigned long s2tte)
{
	long level = (long)ulevel;
	struct smc_result res;

	(void)memset(&res, 0, sizeof(struct smc_result));
	if ((level < S2TT_MIN_BLOCK_LEVEL) || (level > S2TT_PAGE_LEVEL)) {
		return RMI_ERROR_INPUT;
	}

	map_unmap_ns(rd_addr, map_addr, level, s2tte, MAP_NS, &res);

	return res.x[0];
}

void smc_rtt_unmap_unprotected(unsigned long rd_addr,
				unsigned long map_addr,
				unsigned long ulevel,
				struct smc_result *res)
{
	long level = (long)ulevel;

	if ((level < S2TT_MIN_BLOCK_LEVEL) || (level > S2TT_PAGE_LEVEL)) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	map_unmap_ns(rd_addr, map_addr, level, 0UL, UNMAP_NS, res);
}

static void rtt_read_entry(unsigned long rd_addr,
			   unsigned long map_addr,
			   unsigned long ulevel,
			   unsigned long index,
			   bool aux,
			   struct smc_result *res)
{
	struct granule *g_rd;
	struct rd *rd;
	struct s2tt_walk wi;
	unsigned long *s2tt, s2tte;
	long level = (long)ulevel;
	struct s2tt_context s2_ctx;

	g_rd = find_lock_granule(rd_addr, GRANULE_STATE_RD);
	if (g_rd == NULL) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	rd = buffer_granule_map(g_rd, SLOT_RD);
	assert(rd != NULL);

	if (!validate_rtt_entry_cmds(map_addr, level, rd)) {
		buffer_unmap(rd);
		granule_unlock(g_rd);
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	if (aux) {
		if ((!rd->rtt_tree_pp) ||
		    (index == (unsigned long)PRIMARY_S2_CTX_ID) ||
		    (index >= (unsigned long)realm_num_s2_contexts(rd))) {
			buffer_unmap(rd);
			granule_unlock(g_rd);
			res->x[0] = RMI_ERROR_INPUT;
			return;
		}
		s2_ctx = *index_to_s2_context(rd, (unsigned int)index);
	} else {
		s2_ctx = *primary_s2_context(rd);
	}

	buffer_unmap(rd);

	granule_lock(s2_ctx.g_rtt, GRANULE_STATE_RTT);
	granule_unlock(g_rd);

	s2tt_walk_lock_unlock(&s2_ctx, map_addr, level, &wi);
	s2tt = buffer_granule_map(wi.g_llt, SLOT_RTT);
	assert(s2tt != NULL);

	s2tte = s2tte_read(&s2tt[wi.index]);
	res->x[1] = (unsigned long)wi.last_level;

	if (s2tte_is_unassigned_empty(&s2_ctx, s2tte)) {
		res->x[2] = RMI_UNASSIGNED;
		res->x[3] = 0UL;
		res->x[4] = (unsigned long)RIPAS_EMPTY;
	} else if (s2tte_is_unassigned_ram(&s2_ctx, s2tte)) {
		res->x[2] = RMI_UNASSIGNED;
		res->x[3] = 0UL;
		res->x[4] = (unsigned long)RIPAS_RAM;
	} else if (s2tte_is_unassigned_destroyed(&s2_ctx, s2tte)) {
		res->x[2] = RMI_UNASSIGNED;
		res->x[3] = 0UL;
		res->x[4] = (unsigned long)RIPAS_DESTROYED;
	} else if (s2tte_is_assigned_empty(&s2_ctx, s2tte, wi.last_level)) {
		res->x[2] = RMI_ASSIGNED;
		res->x[3] = s2tte_pa(&s2_ctx, s2tte, wi.last_level);
		res->x[4] = (unsigned long)RIPAS_EMPTY;
	} else if (s2tte_is_assigned_ram(&s2_ctx, s2tte, wi.last_level)) {
		res->x[2] = RMI_ASSIGNED;
		res->x[3] = s2tte_pa(&s2_ctx, s2tte, wi.last_level);
		res->x[4] = (unsigned long)RIPAS_RAM;
	} else if (s2tte_is_assigned_destroyed(&s2_ctx, s2tte, wi.last_level)) {
		res->x[2] = RMI_ASSIGNED;
		res->x[3] = 0UL;
		res->x[4] = (unsigned long)RIPAS_DESTROYED;
	} else if (s2tte_is_unassigned_ns(&s2_ctx, s2tte)) {
		res->x[2] = RMI_UNASSIGNED;
		res->x[3] = 0UL;
		res->x[4] = (unsigned long)RIPAS_EMPTY;
	} else if (s2tte_is_assigned_ns(&s2_ctx, s2tte, wi.last_level)) {
		res->x[2] = RMI_ASSIGNED;
		res->x[3] = host_ns_s2tte(&s2_ctx, s2tte, wi.last_level);
		res->x[4] = (unsigned long)RIPAS_EMPTY;
	} else if (s2tte_is_table(&s2_ctx, s2tte, wi.last_level)) {
		res->x[2] = RMI_TABLE;
		res->x[3] = s2tte_pa(&s2_ctx, s2tte, wi.last_level);
		res->x[4] = (unsigned long)RIPAS_EMPTY;
	} else {
		assert(false);
	}

	buffer_unmap(s2tt);
	granule_unlock(wi.g_llt);

	res->x[0] = RMI_SUCCESS;
}

void smc_rtt_read_entry(unsigned long rd_addr,
			unsigned long map_addr,
			unsigned long ulevel,
			struct smc_result *res)
{
	rtt_read_entry(rd_addr, map_addr, ulevel, 0UL, false, res);
}

void smc_rtt_aux_read_entry(unsigned long rd_addr,
			    unsigned long map_addr,
			    unsigned long ulevel,
			    unsigned long index,
			    struct smc_result *res)
{
	rtt_read_entry(rd_addr, map_addr, ulevel, index, true, res);
}

static unsigned long validate_data_create_unknown(unsigned long map_addr,
						  struct rd *rd)
{
	if (!addr_in_par(rd, map_addr)) {
		return RMI_ERROR_INPUT;
	}

	if (!validate_map_addr(map_addr, S2TT_PAGE_LEVEL, rd)) {
		return RMI_ERROR_INPUT;
	}

	return RMI_SUCCESS;
}

static unsigned long validate_data_create(unsigned long map_addr,
					  struct rd *rd)
{
	if (get_rd_state_locked(rd) != REALM_NEW) {
		return RMI_ERROR_REALM;
	}

	return validate_data_create_unknown(map_addr, rd);
}

/*
 * Implements both RMI_DATA_CREATE and RMI_DATA_CREATE_UNKNOWN
 *
 * if @g_src == NULL, implements RMI_DATA_CREATE_UNKNOWN
 * and RMI_DATA_CREATE otherwise.
 */
static unsigned long data_create(unsigned long rd_addr,
				 unsigned long data_addr,
				 unsigned long map_addr,
				 struct granule *g_src,
				 unsigned long flags)
{
	struct granule *g_data;
	struct granule *g_rd;
	struct rd *rd;
	struct s2tt_walk wi;
	struct s2tt_context *s2_ctx;
	unsigned long s2tte, *s2tt;
	unsigned char new_data_state = GRANULE_STATE_DELEGATED;
	unsigned long ret;

	if (!find_lock_two_granules(data_addr,
				    GRANULE_STATE_DELEGATED,
				    &g_data,
				    rd_addr,
				    GRANULE_STATE_RD,
				    &g_rd)) {
		return RMI_ERROR_INPUT;
	}

	rd = buffer_granule_map(g_rd, SLOT_RD);
	assert(rd != NULL);

	ret = (g_src != NULL) ?
		validate_data_create(map_addr, rd) :
		validate_data_create_unknown(map_addr, rd);

	if (ret != RMI_SUCCESS) {
		goto out_unmap_rd;
	}

	s2_ctx = primary_s2_context(rd);
	granule_lock(s2_ctx->g_rtt, GRANULE_STATE_RTT);

	s2tt_walk_lock_unlock(s2_ctx, map_addr, S2TT_PAGE_LEVEL, &wi);
	if (wi.last_level != S2TT_PAGE_LEVEL) {
		ret = pack_return_code(RMI_ERROR_RTT,
					(unsigned char)wi.last_level);
		goto out_unlock_ll_table;
	}

	s2tt = buffer_granule_map(wi.g_llt, SLOT_RTT);
	assert(s2tt != NULL);

	s2tte = s2tte_read(&s2tt[wi.index]);
	if (!s2tte_is_unassigned(s2_ctx, s2tte)) {
		ret = pack_return_code(RMI_ERROR_RTT,
					(unsigned char)S2TT_PAGE_LEVEL);
		goto out_unmap_ll_table;
	}

	if (g_src != NULL) {
		bool ns_access_ok;
		unsigned long ap;
		void *data = buffer_granule_map(g_data, SLOT_DELEGATED);

		assert(data != NULL);

		ns_access_ok = ns_buffer_read(SLOT_NS, g_src, 0U,
					      GRANULE_SIZE, data);
		if (!ns_access_ok) {
			/*
			 * Some data may be copied before the failure. Zero
			 * g_data granule as it will remain in delegated state.
			 */
			granule_memzero_mapped(data);
			buffer_unmap(data);
			ret = RMI_ERROR_INPUT;
			goto out_unmap_ll_table;
		}

		measurement_data_granule_measure(
			rd->measurement[RIM_MEASUREMENT_SLOT],
			rd->algorithm,
			data,
			map_addr,
			flags);
		buffer_unmap(data);

		if (s2tte_is_assigned_ram(s2_ctx, s2tte, S2TT_PAGE_LEVEL)) {
			/* Maintain same access permissions */
			ap = s2tte;
		} else {
			/*
			 * If changing the RIPAS to RAM, set the default
			 * access permissions.
			 */
			ap = default_protected_ap(s2_ctx);
		}

		s2tte = s2tte_create_assigned_ram(s2_ctx, data_addr,
						  S2TT_PAGE_LEVEL, ap);
	} else {

		s2tte = s2tte_create_assigned_unchanged(s2_ctx, s2tte,
							data_addr,
							S2TT_PAGE_LEVEL);
	}

	new_data_state = GRANULE_STATE_DATA;

	s2tte_write(&s2tt[wi.index], s2tte);
	__granule_get(wi.g_llt);

	ret = RMI_SUCCESS;

out_unmap_ll_table:
	buffer_unmap(s2tt);
out_unlock_ll_table:
	granule_unlock(wi.g_llt);
out_unmap_rd:
	buffer_unmap(rd);
	granule_unlock(g_rd);
	granule_unlock_transition(g_data, new_data_state);
	return ret;
}

unsigned long smc_data_create(unsigned long rd_addr,
			      unsigned long data_addr,
			      unsigned long map_addr,
			      unsigned long src_addr,
			      unsigned long flags)
{
	struct granule *g_src;

	if ((flags != RMI_NO_MEASURE_CONTENT) &&
	    (flags != RMI_MEASURE_CONTENT)) {
		return RMI_ERROR_INPUT;
	}

	g_src = find_granule(src_addr);
	if ((g_src == NULL) || (g_src->state != GRANULE_STATE_NS)) {
		return RMI_ERROR_INPUT;
	}

	return data_create(rd_addr, data_addr, map_addr, g_src, flags);
}

unsigned long smc_data_create_unknown(unsigned long rd_addr,
				      unsigned long data_addr,
				      unsigned long map_addr)
{
	return data_create(rd_addr, data_addr, map_addr, NULL, 0);
}

void smc_data_destroy(unsigned long rd_addr,
		      unsigned long map_addr,
		      struct smc_result *res)
{
	struct granule *g_data;
	struct granule *g_rd;
	struct s2tt_walk wi;
	unsigned long data_addr, s2tte, *s2tt;
	struct rd *rd;
	struct s2tt_context s2_ctx;

	g_rd = find_lock_granule(rd_addr, GRANULE_STATE_RD);
	if (g_rd == NULL) {
		res->x[0] = RMI_ERROR_INPUT;
		res->x[2] = 0UL;
		return;
	}

	rd = buffer_granule_map(g_rd, SLOT_RD);
	assert(rd != NULL);

	if (!addr_in_par(rd, map_addr) ||
	    !validate_map_addr(map_addr, S2TT_PAGE_LEVEL, rd)) {
		buffer_unmap(rd);
		granule_unlock(g_rd);
		res->x[0] = RMI_ERROR_INPUT;
		res->x[2] = 0UL;
		return;
	}

	s2_ctx = *primary_s2_context(rd);
	buffer_unmap(rd);

	granule_lock(s2_ctx.g_rtt, GRANULE_STATE_RTT);
	granule_unlock(g_rd);

	s2tt_walk_lock_unlock(&s2_ctx, map_addr, S2TT_PAGE_LEVEL, &wi);
	s2tt = buffer_granule_map(wi.g_llt, SLOT_RTT);
	assert(s2tt != NULL);

	if (wi.last_level != S2TT_PAGE_LEVEL) {
		res->x[0] = pack_return_code(RMI_ERROR_RTT,
						(unsigned char)wi.last_level);
		goto out_unmap_ll_table;
	}

	s2tte = s2tte_read(&s2tt[wi.index]);

	if (s2tte_is_assigned_ram(&s2_ctx, s2tte, S2TT_PAGE_LEVEL)) {
		data_addr = s2tte_pa(&s2_ctx, s2tte, S2TT_PAGE_LEVEL);
		s2tte = s2tte_create_unassigned_destroyed(&s2_ctx, s2tte);
		s2tte_write(&s2tt[wi.index], s2tte);
		s2tt_invalidate_page(&s2_ctx, map_addr);
	} else if (s2tte_is_assigned_empty(&s2_ctx, s2tte, S2TT_PAGE_LEVEL)) {
		data_addr = s2tte_pa(&s2_ctx, s2tte, S2TT_PAGE_LEVEL);
		s2tte = s2tte_create_unassigned_empty(&s2_ctx, s2tte);
		s2tte_write(&s2tt[wi.index], s2tte);
	} else if (s2tte_is_assigned_destroyed(&s2_ctx, s2tte,
					       S2TT_PAGE_LEVEL)) {
		data_addr = s2tte_pa(&s2_ctx, s2tte, S2TT_PAGE_LEVEL);
		s2tte = s2tte_create_unassigned_destroyed(&s2_ctx, s2tte);
		s2tte_write(&s2tt[wi.index], s2tte);
	} else {
		res->x[0] = pack_return_code(RMI_ERROR_RTT,
						(unsigned char)S2TT_PAGE_LEVEL);
		goto out_unmap_ll_table;
	}

	__granule_put(wi.g_llt);

	/*
	 * Lock the data granule and check expected state. Correct locking order
	 * is guaranteed because granule address is obtained from a locked
	 * granule by table walk. This lock needs to be acquired before a state
	 * transition to or from GRANULE_STATE_DATA for granule address can happen.
	 */
	g_data = find_lock_granule(data_addr, GRANULE_STATE_DATA);
	assert(g_data != NULL);
	buffer_granule_memzero(g_data, SLOT_DELEGATED);
	granule_unlock_transition(g_data, GRANULE_STATE_DELEGATED);

	res->x[0] = RMI_SUCCESS;
	res->x[1] = data_addr;
out_unmap_ll_table:
	res->x[2] = s2tt_skip_non_live_entries(&s2_ctx, map_addr, s2tt, &wi);
	buffer_unmap(s2tt);
	granule_unlock(wi.g_llt);
}

/*
 * Update the ripas value for the entry pointed by @s2ttep.
 *
 * Returns:
 *  < 0  - On error and the operation was aborted,
 *	   e.g., entry cannot have a ripas.
 *    0  - Operation was success and no TLBI is required.
 *  > 0  - Operation was success and TLBI is required.
 * Sets:
 * @(*do_tlbi) to 'true' if the TLBs have to be invalidated.
 */
static int update_ripas(const struct s2tt_context *s2_ctx,
			unsigned long *s2ttep, long level,
			enum ripas ripas_val,
			enum ripas_change_destroyed change_destroyed)
{
	unsigned long pa, s2tte = s2tte_read(s2ttep);
	int ret = 0;

	assert(s2_ctx != NULL);

	if (!s2tte_has_ripas(s2_ctx, s2tte, level)) {
		return -EPERM;
	}

	if (ripas_val == RIPAS_RAM) {
		if (s2tte_is_unassigned_empty(s2_ctx, s2tte)) {
			s2tte = s2tte_create_unassigned_ram(s2_ctx,
						default_protected_ap(s2_ctx));
		} else if (s2tte_is_unassigned_destroyed(s2_ctx, s2tte)) {
			if (change_destroyed == CHANGE_DESTROYED) {
				s2tte = s2tte_create_unassigned_ram(s2_ctx,
						default_protected_ap(s2_ctx));
			} else {
				return -EINVAL;
			}
		} else if (s2tte_is_assigned_empty(s2_ctx, s2tte, level)) {
			pa = s2tte_pa(s2_ctx, s2tte, level);
			s2tte = s2tte_create_assigned_ram(s2_ctx, pa, level,
						default_protected_ap(s2_ctx));
		} else if (s2tte_is_assigned_destroyed(s2_ctx, s2tte, level)) {
			if (change_destroyed == CHANGE_DESTROYED) {
				pa = s2tte_pa(s2_ctx, s2tte, level);
				s2tte = s2tte_create_assigned_ram(s2_ctx, pa,
					level, default_protected_ap(s2_ctx));
			} else {
				return -EINVAL;
			}
		} else {
			/* No action is required */
			return 0;
		}
	} else if (ripas_val == RIPAS_EMPTY) {
		if (s2tte_is_unassigned_ram(s2_ctx, s2tte)) {
			s2tte = s2tte_create_unassigned_empty(s2_ctx, s2tte);
		} else if (s2tte_is_unassigned_destroyed(s2_ctx, s2tte)) {
			if (change_destroyed == CHANGE_DESTROYED) {
				s2tte = s2tte_create_unassigned_empty(s2_ctx,
								      s2tte);
			} else {
				return -EINVAL;
			}
		} else if (s2tte_is_assigned_ram(s2_ctx, s2tte, level)) {
			pa = s2tte_pa(s2_ctx, s2tte, level);
			s2tte = s2tte_create_assigned_empty(s2_ctx, pa, level,
							    s2tte);
			/* TLBI is required */
			ret = 1;
		} else if (s2tte_is_assigned_destroyed(s2_ctx, s2tte, level)) {
			if (change_destroyed == CHANGE_DESTROYED) {
				pa = s2tte_pa(s2_ctx, s2tte, level);
				s2tte = s2tte_create_assigned_empty(s2_ctx,
								    pa, level,
								    s2tte);
				/* TLBI is required */
				ret = 1;
			} else {
				return -EINVAL;
			}
		} else {
			/* No action is required */
			return 0;
		}
	}
	s2tte_write(s2ttep, s2tte);
	return ret;
}

void smc_rtt_init_ripas(unsigned long rd_addr,
			unsigned long base,
			unsigned long top,
			struct smc_result *res)
{
	struct granule *g_rd;
	struct rd *rd;
	unsigned long addr, map_size;
	struct s2tt_walk wi;
	struct s2tt_context *s2_ctx;
	unsigned long s2tte, *s2tt;
	long level;
	unsigned long index;
	unsigned int s2ttes_per_s2tt;

	if (top <= base) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	g_rd = find_lock_granule(rd_addr, GRANULE_STATE_RD);
	if (g_rd == NULL) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	rd = buffer_granule_map(g_rd, SLOT_RD);
	assert(rd != NULL);

	if (!validate_map_addr(base, S2TT_PAGE_LEVEL, rd) ||
	    !validate_map_addr(top, S2TT_PAGE_LEVEL, rd) ||
	    !addr_in_par(rd, base) || !addr_in_par(rd, top - GRANULE_SIZE)) {
		buffer_unmap(rd);
		granule_unlock(g_rd);
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	if (get_rd_state_locked(rd) != REALM_NEW) {
		buffer_unmap(rd);
		granule_unlock(g_rd);
		res->x[0] = RMI_ERROR_REALM;
		return;
	}

	s2_ctx = primary_s2_context(rd);
	granule_lock(s2_ctx->g_rtt, GRANULE_STATE_RTT);

	s2tt_walk_lock_unlock(s2_ctx, base, S2TT_PAGE_LEVEL, &wi);
	level = wi.last_level;
	s2tt = buffer_granule_map(wi.g_llt, SLOT_RTT);
	assert(s2tt != NULL);

	map_size = s2tte_map_size(level);
	addr = base & ~(map_size - 1UL);

	/*
	 * If the RTTE covers a range below "base", we need to go deeper.
	 */
	if (addr != base) {
		res->x[0] = pack_return_code(RMI_ERROR_RTT,
						(unsigned char)level);
		goto out_unmap_llt;
	}

	s2ttes_per_s2tt =
		(unsigned int)((level == S2TT_MIN_STARTING_LEVEL_LPA2) ?
			S2TTES_PER_S2TT_LM1 : S2TTES_PER_S2TT);
	for (index = wi.index; index < s2ttes_per_s2tt; index++) {
		unsigned long next = addr + map_size;

		/*
		 * Break on "top_align" failure condition,
		 * or if this entry crosses the range.
		 */
		if (next > top) {
			break;
		}

		s2tte = s2tte_read(&s2tt[index]);
		if (s2tte_is_unassigned_empty(s2_ctx, s2tte)) {
			s2tte = s2tte_create_unassigned_ram(s2_ctx,
						default_protected_ap(s2_ctx));
			s2tte_write(&s2tt[index], s2tte);
		} else if (!s2tte_is_unassigned_ram(s2_ctx, s2tte)) {
			break;
		}
		measurement_init_ripas_measure(rd->measurement[RIM_MEASUREMENT_SLOT],
					       rd->algorithm,
					       addr,
					       next);
		addr = next;
	}

	if (addr > base) {
		res->x[0] = RMI_SUCCESS;
		res->x[1] = addr;
	} else {
		res->x[0] = pack_return_code(RMI_ERROR_RTT,
						(unsigned char)level);
	}

out_unmap_llt:
	buffer_unmap(s2tt);
	buffer_unmap(rd);
	granule_unlock(wi.g_llt);
	granule_unlock(g_rd);
}

static void rtt_set_ripas_range(struct s2tt_context *s2_ctx,
				unsigned long *s2tt,
				unsigned long base,
				unsigned long top,
				struct s2tt_walk *wi,
				enum ripas ripas_val,
				enum ripas_change_destroyed change_destroyed,
				struct smc_result *res)
{
	unsigned long index;
	long level = wi->last_level;
	unsigned long map_size = s2tte_map_size((int)level);

	/* Align to the RTT level */
	unsigned long addr = base & ~(map_size - 1UL);

	/* Make sure we don't touch a range below the requested range */
	if (addr != base) {
		res->x[0] = pack_return_code(RMI_ERROR_RTT,
						(unsigned char)level);
		return;
	}

	for (index = wi->index; index < S2TTES_PER_S2TT; index++) {
		int ret;

		/*
		 * Break on "top_align" failure condition,
		 * or if this entry crosses the range.
		 */
		if ((addr + map_size) > top) {
			break;
		}

		ret = update_ripas(s2_ctx, &s2tt[index], level,
					ripas_val, change_destroyed);
		if (ret < 0) {
			break;
		}

		/* Handle TLBI */
		if (ret != 0) {
			if (level == S2TT_PAGE_LEVEL) {
				s2tt_invalidate_page(s2_ctx, addr);
			} else {
				s2tt_invalidate_block(s2_ctx, addr);
			}
		}

		addr += map_size;
	}

	if (addr > base) {
		res->x[0] = RMI_SUCCESS;
		res->x[1] = addr;
	} else {
		res->x[0] = pack_return_code(RMI_ERROR_RTT,
						(unsigned char)level);
	}
}

void smc_rtt_set_ripas(unsigned long rd_addr,
		       unsigned long rec_addr,
		       unsigned long base,
		       unsigned long top,
		       struct smc_result *res)
{
	struct granule *g_rd, *g_rec;
	struct rec *rec;
	struct rd *rd;
	struct s2tt_walk wi;
	unsigned long *s2tt;
	struct s2tt_context *s2_ctx;
	enum ripas ripas_val;
	enum ripas_change_destroyed change_destroyed;

	if (top <= base) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	if (!find_lock_two_granules(rd_addr,
				   GRANULE_STATE_RD,
				   &g_rd,
				   rec_addr,
				   GRANULE_STATE_REC,
				   &g_rec)) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	if (granule_refcount_read_acquire(g_rec) != 0U) {
		res->x[0] = RMI_ERROR_REC;
		goto out_unlock_rec_rd;
	}

	rec = buffer_granule_map(g_rec, SLOT_REC);
	assert(rec != NULL);

	if (g_rd != rec->realm_info.g_rd) {
		res->x[0] = RMI_ERROR_REC;
		goto out_unmap_rec;
	}

	ripas_val = rec->set_ripas.ripas_val;
	change_destroyed = rec->set_ripas.change_destroyed;

	/*
	 * Return error in case of target region:
	 * - is not the next chunk of requested region
	 * - extends beyond the end of requested region
	 */
	if ((base != rec->set_ripas.addr) || (top > rec->set_ripas.top)) {
		res->x[0] = RMI_ERROR_INPUT;
		goto out_unmap_rec;
	}

	rd = buffer_granule_map(g_rd, SLOT_RD);
	assert(rd != NULL);

	/*
	 * At this point, we know base == rec->set_ripas.addr
	 * and thus must be aligned to GRANULE size.
	 */
	assert(validate_map_addr(base, S2TT_PAGE_LEVEL, rd));

	s2_ctx = primary_s2_context(rd);
	granule_lock(s2_ctx->g_rtt, GRANULE_STATE_RTT);

	/* Walk to the deepest level possible */
	s2tt_walk_lock_unlock(s2_ctx, base, S2TT_PAGE_LEVEL, &wi);

	/*
	 * Base has to be aligned to the level at which
	 * it is mapped in RTT.
	 */
	if (!validate_map_addr(base, wi.last_level, rd)) {
		res->x[0] = pack_return_code(RMI_ERROR_RTT,
						(unsigned char)wi.last_level);
		goto out_unlock_llt;
	}

	s2tt = buffer_granule_map(wi.g_llt, SLOT_RTT);
	assert(s2tt != NULL);

	rtt_set_ripas_range(s2_ctx, s2tt, base, top, &wi,
				ripas_val, change_destroyed, res);

	if (res->x[0] == RMI_SUCCESS) {
		rec->set_ripas.addr = res->x[1];
	}

	buffer_unmap(s2tt);
out_unlock_llt:
	granule_unlock(wi.g_llt);
	buffer_unmap(rd);
out_unmap_rec:
	buffer_unmap(rec);
out_unlock_rec_rd:
	granule_unlock(g_rec);
	granule_unlock(g_rd);
}

void smc_rtt_set_s2ap(unsigned long rd_addr, unsigned long rec_addr,
		      unsigned long base, unsigned long top,
		      struct smc_result *res)
{
	struct granule *g_rd, *g_rec;
	struct rec *rec;
	struct rd *rd;
	struct s2tt_walk wi;
	struct s2tt_context *s2_ctx;
	unsigned long *s2tt;
	unsigned long perm_index, map_size, s2tt_idx, next, s2tte;

	if ((top <= base) || !(GRANULE_ALIGNED(top))) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	if (!find_lock_two_granules(rd_addr,
				   GRANULE_STATE_RD,
				   &g_rd,
				   rec_addr,
				   GRANULE_STATE_REC,
				   &g_rec)) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	if (granule_refcount_read_acquire(g_rec) != 0U) {
		res->x[0] = RMI_ERROR_REC;
		goto out_unlock_rec_rd;
	}

	rec = buffer_granule_map(g_rec, SLOT_REC);
	assert(rec != NULL);

	if (g_rd != rec->realm_info.g_rd) {
		res->x[0] = RMI_ERROR_REC;
		goto out_unmap_rec;
	}

	if ((rec->set_s2ap.base != base) || (top > rec->set_s2ap.top)) {
		res->x[0] = RMI_ERROR_INPUT;
		goto out_unmap_rec;
	}

	perm_index = rec->set_s2ap.index;

	/*
	 * Return error in case of target region:
	 * - Is not the next chunk of requested region.
	 * - Extends beyond the end of requested region.
	 */
	if ((base != rec->set_s2ap.base) || (top > rec->set_s2ap.top)) {
		res->x[0] = RMI_ERROR_INPUT;
		goto out_unmap_rec;
	}

	rd = buffer_granule_map(g_rd, SLOT_RD);
	assert(rd != NULL);

	if (rd->rtt_tree_pp) {
		s2tt_idx = (rec->set_s2ap.cookie & ~GRANULE_MASK);
	} else {
		s2tt_idx = PRIMARY_S2_CTX_ID;
	}

	s2_ctx = index_to_s2_context(rd, s2tt_idx);
	granule_lock(s2_ctx->g_rtt, GRANULE_STATE_RTT);

	/* Walk to the deepest level possible */
	s2tt_walk_lock_unlock(s2_ctx, base, S2TT_PAGE_LEVEL, &wi);

	if (base > realm_ipa_size(rd)) {
		res->x[0] = RMI_ERROR_INPUT;
		goto out_unlock_llt;
	}

	if (!s2tte_is_addr_lvl_aligned(s2_ctx, base, wi.last_level)) {
		unsigned int error_id = (s2tt_idx == PRIMARY_PLANE_ID) ?
					 RMI_ERROR_RTT : RMI_ERROR_RTT_AUX;

		res->x[0] = pack_return_code(error_id, (unsigned char)wi.last_level);
		res->x[1] = base;
		res->x[2] = s2tt_idx;
		goto out_unlock_llt;
	}

	map_size = s2tte_map_size(wi.last_level);
	s2tt = buffer_granule_map(wi.g_llt, SLOT_RTT);
	assert(s2tt != NULL);

	/*
	 * Update the entries in the RTT that we have reached by the walk.
	 */
	next = base;
	while ((wi.index < S2TTES_PER_S2TT) && (next < top)) {
		if (next + map_size > top) {
			/*
			 * The RTT entry covers the IPA space that partially
			 * lays beyond 'top'. We need the next level RTT to
			 * continue the operation
			 */
			unsigned int error_id = (s2tt_idx == PRIMARY_S2_CTX_ID) ?
					RMI_ERROR_RTT : RMI_ERROR_RTT_AUX;

			res->x[0] = pack_return_code(error_id,
						(unsigned char)wi.last_level);
			res->x[1] = next;
			res->x[2] = s2tt_idx;
			goto out_unmap_s2tt;
		}

		s2tte = s2tte_read(&s2tt[wi.index]);
		if (s2tte_is_table(s2_ctx, s2tte, wi.last_level)) {
			/*
			 * We need to walk one more level to continue the
			 * operation.
			 */
			break;
		}

		/* Update the S2AP with the new permission */
		s2tte = s2tte_update_ap_from_index(s2_ctx, s2tte, perm_index);
		s2tte_write(&s2tt[wi.index], s2tte);

		/* Only invalidate for valid entries */
		if (s2tte_is_assigned_ram(s2_ctx, s2tte, wi.last_level) ||
		    s2tte_is_table(s2_ctx, s2tte, wi.last_level)) {
			s2tt_invalidate_page(s2_ctx, next);
		}

		wi.index++;
		next += map_size;
	}

	res->x[0] = RMI_SUCCESS;
	res->x[1] = next;

out_unmap_s2tt:
	rec->set_s2ap.base = next;
	buffer_unmap(s2tt);
out_unlock_llt:
	granule_unlock(wi.g_llt);
	buffer_unmap(rd);
out_unmap_rec:
	buffer_unmap(rec);
out_unlock_rec_rd:
	granule_unlock(g_rec);
	granule_unlock(g_rd);
}

/*
 * Calculate the PA mapped @ipa.
 *
 * @ipa is the intermediate physical address mapped @level that
 * may not be aligned @level.
 * @pa_base is the base physical address of that mapping @level.
 */
static unsigned long realign_pa(struct s2tt_context *s2_ctx,
				unsigned long pa_base,
				unsigned long level,
				unsigned long ipa)
{
	unsigned long offset = ipa -
			(ipa & s2tte_lvl_mask(level, s2_ctx->enable_lpa2));

	return pa_base + offset;
}

static void rtt_aux_map(unsigned long rd_addr,
			unsigned long map_addr,
			unsigned long index,
			struct smc_result *res,
			bool protected)
{
	struct granule *g_rd;
	struct rd *rd;
	struct s2tt_walk wi;
	unsigned long *s2tt, primary_s2tte, s2tte;
	struct s2tt_context s2_ctx, aux_s2_ctx;
	unsigned long primary_level, primary_ripas, primary_pa, aux_pa;
	unsigned long map_size;

	g_rd = find_lock_granule(rd_addr, GRANULE_STATE_RD);
	if (g_rd == NULL) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	rd = buffer_granule_map(g_rd, SLOT_RD);
	assert(rd != NULL);

	if (!validate_rtt_entry_cmds(map_addr, S2TT_PAGE_LEVEL, rd)) {
		buffer_unmap(rd);
		granule_unlock(g_rd);
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	if ((!rd->rtt_tree_pp) ||
	    (index == (unsigned long)PRIMARY_S2_CTX_ID) ||
	    (index >= (unsigned long)realm_num_s2_contexts(rd))) {
		buffer_unmap(rd);
		granule_unlock(g_rd);
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	s2_ctx = *primary_s2_context(rd);

	buffer_unmap(rd);

	granule_lock(s2_ctx.g_rtt, GRANULE_STATE_RTT);

	s2tt_walk_lock_unlock(&s2_ctx, map_addr, S2TT_PAGE_LEVEL, &wi);
	s2tt = buffer_granule_map(wi.g_llt, SLOT_RTT);
	assert(s2tt != NULL);

	primary_s2tte = s2tte_read(&s2tt[wi.index]);
	buffer_unmap(s2tt);
	granule_unlock(wi.g_llt);

	primary_level = wi.last_level;
	primary_ripas = (unsigned long)s2tte_get_ripas(&s2_ctx, primary_s2tte);
	primary_pa = s2tte_pa(&s2_ctx, primary_s2tte, primary_level);

	if (protected) {
		/* If the IPA is not assigned on the primary RTT, report and return */
		if (!s2tte_is_assigned_ram(&s2_ctx, primary_s2tte, primary_level)) {
			res->x[0] = pack_return_code(RMI_ERROR_RTT,
						(unsigned char)primary_level);
			res->x[1] = (unsigned long)PRIMARY_S2_CTX_ID;
			res->x[2] = primary_level;
			res->x[3] = s2tte_is_unassigned(&s2_ctx, primary_s2tte) ?
					(unsigned long)RMI_UNASSIGNED :
					(unsigned long)RMI_ASSIGNED;
			res->x[4] = primary_ripas;

			granule_unlock(g_rd);
			return;
		}
	} else {
		/* If the IPA is not assigned_ns on the primary RTT, report and return */
		if (!s2tte_is_assigned_ns(&s2_ctx, primary_s2tte, primary_level)) {
			res->x[0] = pack_return_code(RMI_ERROR_RTT, primary_level);
			res->x[1] = (unsigned long)PRIMARY_S2_CTX_ID;
			res->x[2] = primary_level;
			res->x[3] = s2tte_is_unassigned(&s2_ctx, primary_s2tte) ?
						(unsigned long)RMI_UNASSIGNED :
						(unsigned long)RMI_ASSIGNED;

			granule_unlock(g_rd);
			return;
		}
	}

	/*
	 * We have retrieved all the info we needed from the walk on the
	 * primary table. Prepare a walk on the auxiliary one.
	 */
	aux_s2_ctx = *index_to_s2_context(rd, (unsigned int)index);
	granule_lock(aux_s2_ctx.g_rtt, GRANULE_STATE_RTT);
	granule_unlock(g_rd);
	s2tt_walk_lock_unlock(&aux_s2_ctx, map_addr, S2TT_PAGE_LEVEL, &wi);
	s2tt = buffer_granule_map(wi.g_llt, SLOT_RTT);
	assert(s2tt != NULL);

	s2tte = s2tte_read(&s2tt[wi.index]);

	/*
	 * The address space to map on the auxiliary table cannot be larger
	 * than the one on the primary one.
	 */
	if (wi.last_level < primary_level) {
		res->x[0] = pack_return_code(RMI_ERROR_RTT_AUX,
					     (unsigned char)wi.last_level);
		res->x[1] = (unsigned long)index;
		res->x[2] = primary_level;
		res->x[3] = s2tte_is_unassigned(&aux_s2_ctx, s2tte) ?
				(unsigned long)RMI_UNASSIGNED :
				(unsigned long)RMI_ASSIGNED;
		if (protected) {
			res->x[4] = primary_ripas;
		}

		granule_unlock(wi.g_llt);
		return;
	}

	/*
	 * Realign the PA on the primary S2TTE to the level in the
	 * auxiliary RTT entry.
	 */
	aux_pa = realign_pa(&aux_s2_ctx, primary_pa, wi.last_level, map_addr);

	s2tt = buffer_granule_map(wi.g_llt, SLOT_RTT);
	assert(s2tt != NULL);

	s2tte = s2tte_read(&s2tt[wi.index]);

	if (protected) {
		/* If the entry ripas is destroyed, report it and exit */
		if (s2tte_get_ripas(&aux_s2_ctx, s2tte) == RIPAS_DESTROYED) {
			res->x[0] = pack_return_code(RMI_ERROR_RTT_AUX,
					     (unsigned char)wi.last_level);
			res->x[1] = (unsigned long)wi.index;
			res->x[2] = primary_level;
			res->x[3] = (unsigned long)RMI_AUX_DESTROYED;
			res->x[4] = primary_ripas;

			buffer_unmap(s2tt);
			granule_unlock(wi.g_llt);
			return;
		}

		/* If the entry ripas is RAM, we exit with success condition */
		if (s2tte_is_assigned_ram(&aux_s2_ctx, s2tte, wi.last_level)) {
			res->x[0] = RMI_SUCCESS;

			buffer_unmap(s2tt);
			granule_unlock(wi.g_llt);
			return;
		}

		/*
		 * Increment the refcounter for all the DATA granules that are going
		 * to be mapped.
		 */
		map_size = s2tte_map_size(wi.last_level);
		for (unsigned long offset = 0UL; offset < map_size; offset += GRANULE_SIZE) {
			struct granule *g_data = find_lock_granule(aux_pa + offset,
								   GRANULE_STATE_DATA);

			assert(g_data != NULL);
			__granule_get(g_data);
			granule_unlock(g_data);
		}

		/*
		 * Create the new entry maintaining the access permissions from the
		 * original auxiliary entry.
		 */
		s2tte = s2tte_create_assigned_ram(&aux_s2_ctx, aux_pa,
						  wi.last_level, s2tte);
	} else {
		/* If the entry is already assigned_ns, exit with success condition */
		if (s2tte_is_assigned_ns(&aux_s2_ctx, s2tte, wi.last_level)) {
			res->x[0] = RMI_SUCCESS;

			buffer_unmap(s2tt);
			granule_unlock(wi.g_llt);
			return;
		}

		/*
		 * Create an assigned_ns descriptor, reusing the AP from the
		 * descriptor on the primary tree.
		 */
		s2tte = s2tte_create_assigned_ns(&aux_s2_ctx, s2tte,
						 wi.last_level, primary_s2tte);
	}

	s2tte_write(&s2tt[wi.index], s2tte);

	buffer_unmap(s2tt);
	granule_unlock(wi.g_llt);

	res->x[0] = RMI_SUCCESS;
}

void smc_rtt_aux_map_protected(unsigned long rd_addr,
			       unsigned long map_addr,
			       unsigned long index,
			       struct smc_result *res)
{
	rtt_aux_map(rd_addr, map_addr, index, res, true);
}

void smc_rtt_aux_map_unprotected(unsigned long rd_addr,
				 unsigned long map_addr,
				 unsigned long index,
				 struct smc_result *res)
{
	rtt_aux_map(rd_addr, map_addr, index, res, false);
}

void smc_rtt_aux_unmap_protected(unsigned long rd_addr,
				 unsigned long unmap_addr,
				 unsigned long index,
				 struct smc_result *res)
{
	struct granule *g_rd;
	struct rd *rd;
	struct s2tt_walk wi;
	unsigned long *s2tt, s2tte;
	struct s2tt_context s2_ctx;
	unsigned long pa, map_size;

	g_rd = find_lock_granule(rd_addr, GRANULE_STATE_RD);
	if (g_rd == NULL) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	rd = buffer_granule_map(g_rd, SLOT_RD);
	assert(rd != NULL);

	if (!validate_rtt_entry_cmds(unmap_addr, S2TT_PAGE_LEVEL, rd)) {
		buffer_unmap(rd);
		granule_unlock(g_rd);
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	if ((!rd->rtt_tree_pp) ||
	    (index == (unsigned long)PRIMARY_S2_CTX_ID) ||
	    (index >= (unsigned long)realm_num_s2_contexts(rd))) {
		buffer_unmap(rd);
		granule_unlock(g_rd);
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	s2_ctx = *index_to_s2_context(rd, (unsigned int)index);

	buffer_unmap(rd);

	granule_lock(s2_ctx.g_rtt, GRANULE_STATE_RTT);
	granule_unlock(g_rd);

	s2tt_walk_lock_unlock(&s2_ctx, unmap_addr, S2TT_PAGE_LEVEL, &wi);
	s2tt = buffer_granule_map(wi.g_llt, SLOT_RTT);
	assert(s2tt != NULL);

	s2tte = s2tte_read(&s2tt[wi.index]);

	/* If the IPA is not assigned on the auxiliary RTT, report and return */
	if (!s2tte_is_assigned_ram(&s2_ctx, s2tte, wi.last_level)) {
		res->x[0] = pack_return_code(RMI_ERROR_RTT,
					     (unsigned char)wi.last_level);
		res->x[1] = s2tt_skip_non_live_entries(&s2_ctx, unmap_addr,
							s2tt, &wi);
		buffer_unmap(s2tt);
		granule_unlock(wi.g_llt);
		return;
	}

	/*
	 * Save the PA mapped by the entry, as we will need it later to
	 * decrement the reference count for the associated granules.
	 */
	pa = s2tte_pa(&s2_ctx, s2tte, wi.last_level);

	/*
	 * Create the new S2TTE, reusing the original one so that they
	 * have the same Access Permissions.
	 */
	s2tte = s2tte_create_unassigned_empty(&s2_ctx, s2tte);

	s2tte_write(&s2tt[wi.index], s2tte);

	if (wi.last_level == S2TT_PAGE_LEVEL) {
		s2tt_invalidate_page(&s2_ctx, unmap_addr);
	} else {
		s2tt_invalidate_block(&s2_ctx, unmap_addr);
	}

	/*
	 * Decrement the refcounter for all the DATA granules that are going
	 * to be mapped.
	 */
	map_size = s2tte_map_size(wi.last_level);
	for (unsigned long offset = 0UL; offset < map_size; offset += GRANULE_SIZE) {
		struct granule *g_data = find_lock_granule(pa + offset,
							   GRANULE_STATE_DATA);

		assert(g_data != NULL);
		__granule_put(g_data);
		granule_unlock(g_data);
	}

	res->x[0] = RMI_SUCCESS;
	res->x[1] = s2tt_skip_non_live_entries(&s2_ctx, unmap_addr, s2tt, &wi);
	res->x[2] = wi.last_level;

	buffer_unmap(s2tt);
	granule_unlock(wi.g_llt);
}
