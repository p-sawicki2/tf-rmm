/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch_helpers.h>
#include <bitmap.h>
#include <granule.h>
#include <ripas.h>
#include <s2tt.h>
#include <s2tt_pvt_defs.h>
#include <smc.h>
#include <stddef.h>
#include <string.h>

/* TODO: Fix this when introducing LPA2 support */
COMPILER_ASSERT(S2TT_MIN_STARTING_LEVEL >= 0);

/*
 * Invalidates S2 TLB entries from [ipa, ipa + size] region tagged with `vmid`.
 */
static void stage2_tlbi_ipa(const struct s2tt_context *s2_ctx,
			    unsigned long ipa,
			    unsigned long size)
{
	/*
	 * Notes:
	 *
	 * - This follows the description provided in the Arm ARM on
	 *   "Invalidation of TLB entries from stage 2 translations".
	 *
	 * - @TODO: Provide additional information to this primitive so that
	 *   we can utilize:
	 *   - The TTL level hint, see FEAT_TTL,
	 *   - Final level lookup only invalidation,
	 *   - Address range invalidation.
	 */

	assert(s2_ctx != NULL);

	/*
	 * Save the current content of vttb_el2.
	 */
	unsigned long old_vttbr_el2 = read_vttbr_el2();

	/*
	 * Make 'vmid' the `current vmid`. Note that the tlbi instructions
	 * bellow target the TLB entries that match the `current vmid`.
	 */
	write_vttbr_el2(INPLACE(VTTBR_EL2_VMID, s2_ctx->vmid));
	isb();

	/*
	 * Invalidate entries in S2 TLB caches that
	 * match both `ipa` & the `current vmid`.
	 */
	while (size != 0UL) {
		tlbiipas2e1is(ipa >> 12);
		size -= GRANULE_SIZE;
		ipa += GRANULE_SIZE;
	}
	dsb(ish);

	/*
	 * The architecture does not require TLB invalidation by IPA to affect
	 * combined Stage-1 + Stage-2 TLBs. Therefore we must invalidate all of
	 * Stage-1 (tagged with the `current vmid`) after invalidating Stage-2.
	 */
	tlbivmalle1is();
	dsb(ish);
	isb();

	/*
	 * Restore the old content of vttb_el2.
	 */
	write_vttbr_el2(old_vttbr_el2);
	isb();
}

/*
 * Invalidate S2 TLB entries with "addr" IPA.
 * Call this function after:
 * 1.  A L3 page desc has been removed.
 */
void s2tt_invalidate_page(const struct s2tt_context *s2_ctx, unsigned long addr)
{
	stage2_tlbi_ipa(s2_ctx, addr, GRANULE_SIZE);
}

/*
 * Invalidate S2 TLB entries with "addr" IPA.
 * Call this function after:
 * 1.  A L2 block desc has been removed, or
 * 2a. A L2 table desc has been removed, where
 * 2b. All S2TTEs in L3 table that the L2 table desc was pointed to were invalid.
 */
void s2tt_invalidate_block(const struct s2tt_context *s2_ctx, unsigned long addr)
{
	stage2_tlbi_ipa(s2_ctx, addr, GRANULE_SIZE);
}

/*
 * Invalidate S2 TLB entries with "addr" IPA.
 * Call this function after:
 * 1a. A L2 table desc has been removed, where
 * 1b. Some S2TTEs in the table that the L2 table desc was pointed to were valid.
 */
void s2tt_invalidate_pages_in_block(const struct s2tt_context *s2_ctx,
				    unsigned long addr)
{
	stage2_tlbi_ipa(s2_ctx, addr, BLOCK_L2_SIZE);
}

/*
 * Return the index of the entry describing @addr in the translation table at
 * level @level.  This only works for non-concatenated page tables, so should
 * not be called to get the index for the starting level.
 *
 * See the library pseudocode
 * aarch64/translation/vmsa_addrcalc/AArch64.TTEntryAddress on which this is
 * modeled.
 */
static unsigned long s2_addr_to_idx(unsigned long addr, long level)
{
	unsigned int levels, lsb;

	levels = (unsigned int)(S2TT_PAGE_LEVEL - level);
	lsb = (levels * S2TTE_STRIDE) + GRANULE_SHIFT;

	addr >>= lsb;
	addr &= (1UL << S2TTE_STRIDE) - 1UL;
	return addr;
}

/*
 * Return the index of the entry describing @addr in the translation table
 * starting level.  This may return an index >= S2TTES_PER_S2TT when the
 * combination of @start_level and @ipa_bits implies concatenated
 * stage 2 tables.
 *
 * See the library pseudocode
 * aarch64/translation/vmsa_addrcalc/AArch64.S2SLTTEntryAddress on which
 * this is modeled.
 */
static unsigned long s2_sl_addr_to_idx(unsigned long addr, int start_level,
				       unsigned long ipa_bits)
{
	unsigned int levels, lsb;

	levels = (unsigned int)(S2TT_PAGE_LEVEL - start_level);
	lsb = (levels * S2TTE_STRIDE) + GRANULE_SHIFT;

	addr &= (1UL << ipa_bits) - 1UL;
	addr >>= lsb;
	return addr;
}

static unsigned long addr_level_mask(unsigned long addr, long level)
{
	unsigned int levels, lsb, msb;

	assert(level <= S2TT_PAGE_LEVEL);
	assert(level >= S2TT_MIN_STARTING_LEVEL);

	levels = (unsigned int)(S2TT_PAGE_LEVEL - level);
	lsb = (levels * S2TTE_STRIDE) + GRANULE_SHIFT;
	msb = S2TTE_OA_BITS - 1U;

	return (addr & BIT_MASK_ULL(msb, lsb));
}

static inline bool entry_is_table(unsigned long entry)
{
	return ((entry & S2TT_DESC_TYPE_MASK) == S2TTE_L012_TABLE);
}

static unsigned long table_get_entry(struct granule *g_tbl,
				     unsigned long idx)
{
	unsigned long *table, entry;

	table = granule_map(g_tbl, SLOT_RTT);
	assert(table != NULL);

	entry = s2tte_read(&table[idx]);
	buffer_unmap(table);

	return entry;
}

#define table_entry_to_phys(tte)	addr_level_mask(tte, S2TT_PAGE_LEVEL)

static struct granule *find_next_level_idx(struct granule *g_tbl,
					   unsigned long idx)
{
	const unsigned long entry = table_get_entry(g_tbl, idx);

	if (!entry_is_table(entry)) {
		return NULL;
	}

	return addr_to_granule(table_entry_to_phys(entry));
}

static struct granule *find_lock_next_level(struct granule *g_tbl,
					    unsigned long map_addr,
					    long level)
{
	const unsigned long idx = s2_addr_to_idx(map_addr, level);
	struct granule *g = find_next_level_idx(g_tbl, idx);

	if (g != NULL) {
		granule_lock(g, GRANULE_STATE_RTT);
	}

	return g;
}

/*
 * Walk an RTT until level @level using @map_addr.
 * @g_root is the root (level 0) table and must be locked before the call.
 * @start_level is the initial lookup level used for the stage 2 translation
 * tables which may depend on the configuration of the realm, factoring in the
 * IPA size of the realm and the desired starting level (within the limits
 * defined by the Armv8 VMSA including options for stage 2 table concatenation).
 * The function uses hand-over-hand locking to avoid race conditions and allow
 * concurrent access to RTT tree which is not part of the current walk; when a
 * next level table is reached it is locked before releasing previously locked
 * table.
 * The walk stops when either:
 * - The entry found is a leaf entry (not an RTT Table entry), or
 * - Level @level is reached.
 *
 * On return:
 * - s2tt_walk::last_level is the last level that has been reached by the walk.
 * - s2tt_walk.g_llt points to the TABLE granule at level @s2tt_walk::level.
 *   The granule is locked.
 * - s2tt_walk::index is the entry index at s2tt_walk.g_llt for @map_addr.
 */
void s2tt_walk_lock_unlock(struct granule *g_root,
			  int start_level,
			  unsigned long ipa_bits,
			  unsigned long map_addr,
			  long level,
			  struct s2tt_walk *wi)
{
	struct granule *g_tbls[NR_RTT_LEVELS] = { (struct granule *)NULL };
	unsigned long sl_idx;
	int i, last_level;

	assert(start_level >= S2TT_MIN_STARTING_LEVEL);
	assert(start_level <= S2TT_PAGE_LEVEL);
	assert(level >= start_level);
	assert(level <= S2TT_PAGE_LEVEL);
	assert(map_addr < (1UL << ipa_bits));
	assert(wi != NULL);
	assert(g_root != NULL);
	assert(ipa_bits <= s2tt_max_ipa_size());

	/* Handle concatenated starting level (SL) tables */
	sl_idx = s2_sl_addr_to_idx(map_addr, start_level, ipa_bits);
	if (sl_idx >= S2TTES_PER_S2TT) {
		unsigned int tt_num = (unsigned int)(sl_idx >> S2TTE_STRIDE);
		struct granule *g_concat_root;

		assert(tt_num < S2TTE_MAX_CONCAT_TABLES);

		g_concat_root = (struct granule *)((uintptr_t)g_root +
						(tt_num * sizeof(struct granule)));

		granule_lock(g_concat_root, GRANULE_STATE_RTT);
		granule_unlock(g_root);
		g_root = g_concat_root;
	}

	g_tbls[start_level] = g_root;
	for (i = start_level; i < level; i++) {
		/*
		 * Lock next RTT level. Correct locking order is guaranteed
		 * because reference is obtained from a locked granule
		 * (previous level). Also, hand-over-hand locking/unlocking is
		 * used to avoid race conditions.
		 */
		g_tbls[i + 1] = find_lock_next_level(g_tbls[i], map_addr, i);
		if (g_tbls[i + 1] == NULL) {
			last_level = i;
			goto out;
		}
		granule_unlock(g_tbls[i]);
	}

	last_level = (int)level;
out:
	wi->last_level = last_level;
	wi->g_llt = g_tbls[last_level];
	wi->index = s2_addr_to_idx(map_addr, last_level);
}

/*
 * Creates an unassigned_empty s2tte.
 */
unsigned long s2tte_create_unassigned_empty(void)
{
	return (S2TTE_INVALID_HIPAS_UNASSIGNED | S2TTE_INVALID_RIPAS_EMPTY);
}

/*
 * Creates an unassigned_ram s2tte.
 */
unsigned long s2tte_create_unassigned_ram(void)
{
	return (S2TTE_INVALID_HIPAS_UNASSIGNED | S2TTE_INVALID_RIPAS_RAM);
}

/*
 * Creates an unassigned_destroyed s2tte.
 */
unsigned long s2tte_create_unassigned_destroyed(void)
{
	return (S2TTE_INVALID_HIPAS_UNASSIGNED | S2TTE_INVALID_RIPAS_DESTROYED);
}

/*
 * Creates an unassigned_ns s2tte.
 */
unsigned long s2tte_create_unassigned_ns(void)
{
	return (S2TTE_NS | S2TTE_INVALID_HIPAS_UNASSIGNED |
		S2TTE_INVALID_UNPROTECTED);
}

/*
 * Creates an invalid s2tte with output address @pa, HIPAS=ASSIGNED and
 * RIPAS=@s2tte_ripas, at level @level.
 */
static unsigned long s2tte_create_assigned(unsigned long pa, long level,
					   unsigned long s2tte_ripas)
{
	(void)level;

	assert(level >= S2TT_MIN_BLOCK_LEVEL);
	assert(level <= S2TT_PAGE_LEVEL);
	assert(s2tte_ripas <= S2TTE_INVALID_RIPAS_DESTROYED);
	assert(s2tte_is_addr_lvl_aligned(pa, level));

	if (s2tte_ripas == S2TTE_INVALID_RIPAS_RAM) {
		if (level == S2TT_PAGE_LEVEL) {
			return (pa | S2TTE_PAGE);
		}
		return (pa | S2TTE_BLOCK);
	}

	return (pa | S2TTE_INVALID_HIPAS_ASSIGNED | s2tte_ripas);
}

/*
 * Creates and invalid s2tte with output address @pa, HIPAS=ASSIGNED and
 * RIPAS=DESTROYED at level @level.
 */
unsigned long s2tte_create_assigned_destroyed(unsigned long pa, long level)
{
	return s2tte_create_assigned(pa, level, S2TTE_INVALID_RIPAS_DESTROYED);
}

/*
 * Creates an invalid s2tte with output address @pa, HIPAS=ASSIGNED and
 * RIPAS=EMPTY at level @level.
 */
unsigned long s2tte_create_assigned_empty(unsigned long pa, long level)
{
	return s2tte_create_assigned(pa, level, S2TTE_INVALID_RIPAS_EMPTY);
}

/*
 * Creates an assigned_ram s2tte with output address @pa.
 */
unsigned long s2tte_create_assigned_ram(unsigned long pa, long level)
{
	return s2tte_create_assigned(pa, level, S2TTE_INVALID_RIPAS_RAM);
}

/*
 * Creates an assigned s2tte with output address @pa and the same
 * RIPAS as passed on @s2tte.
 */
unsigned long s2tte_create_assigned_unchanged(unsigned long s2tte,
					      unsigned long pa,
					      long level)
{
	unsigned long current_ripas = s2tte & S2TTE_INVALID_RIPAS_MASK;

	return s2tte_create_assigned(pa, level, current_ripas);
}

/*
 * Creates an assigned_ns s2tte at level @level.
 *
 * The following S2 TTE fields are provided through @s2tte argument:
 * - The physical address
 * - MemAttr
 * - S2AP
 * - Shareability
 */
unsigned long s2tte_create_assigned_ns(unsigned long s2tte, long level)
{
	unsigned long new_s2tte = s2tte & ~S2TT_DESC_TYPE_MASK;

	assert(level >= S2TT_MIN_BLOCK_LEVEL);
	assert(level <= S2TT_PAGE_LEVEL);
	assert((s2tte & S2TTE_NS_ATTR_RMM) == 0UL);

	if (level == S2TT_PAGE_LEVEL) {
		return (new_s2tte | S2TTE_PAGE_NS);
	}
	return (new_s2tte | S2TTE_BLOCK_NS);
}

/*
 * Validate the portion of NS S2TTE that is provided by the host.
 */
bool host_ns_s2tte_is_valid(unsigned long s2tte, long level)
{

	unsigned long mask = addr_level_mask(~0UL, level) |
						S2TTE_NS_ATTR_HOST_MASK;

	assert(level >= S2TT_MIN_BLOCK_LEVEL);

	/*
	 * Test that all fields that are not controlled by the host are zero
	 * and that the output address is correctly aligned. Note that
	 * the host is permitted to map any physical address outside PAR.
	 */
	if ((s2tte & ~mask) != 0UL) {
		return false;
	}

	/*
	 * Only one value masked by S2TTE_MEMATTR_MASK is invalid/reserved.
	 */
	if ((s2tte & S2TTE_MEMATTR_MASK) == S2TTE_MEMATTR_FWB_RESERVED) {
		return false;
	}

	/*
	 * Only one value masked by S2TTE_SH_MASK is invalid/reserved.
	 */
	if ((s2tte & S2TTE_SH_MASK) != S2TTE_SH_IS) {
		return false;
	}

	/*
	 * Note that all the values that are masked by S2TTE_AP_MASK are valid.
	 */
	return true;
}

/*
 * Returns the portion of NS S2TTE that is set by the host.
 */
unsigned long host_ns_s2tte(unsigned long s2tte, long level)
{
	unsigned long mask = addr_level_mask(~0UL, level) |
						S2TTE_NS_ATTR_HOST_MASK;
	assert(level >= S2TT_MIN_BLOCK_LEVEL);

	return (s2tte & mask);
}

/*
 * Creates a table s2tte at level @level with output address @pa.
 */
unsigned long s2tte_create_table(unsigned long pa, long level)
{
	(void)level;

	assert(level < S2TT_PAGE_LEVEL);
	assert(level >= S2TT_MIN_STARTING_LEVEL);
	assert(GRANULE_ALIGNED(pa));

	return (pa | S2TTE_TABLE);
}

/*
 * Returns true if s2tte has defined ripas value, namely if it is one of:
 * - unassigned_empty
 * - unassigned_ram
 * - unassigned_destroyed
 * - assigned_empty
 * - assigned_ram
 * - assigned_destroyed
 */
bool s2tte_has_ripas(unsigned long s2tte, long level)
{
	return (((s2tte & S2TTE_NS) == 0UL) && !s2tte_is_table(s2tte, level));
}

/*
 * Returns true if @s2tte has HIPAS=@hipas.
 */
static inline bool s2tte_has_hipas(unsigned long s2tte, unsigned long hipas)
{
	unsigned long desc_type = s2tte & S2TT_DESC_TYPE_MASK;
	unsigned long invalid_desc_hipas = s2tte & S2TTE_INVALID_HIPAS_MASK;

	return ((desc_type == S2TTE_INVALID) && (invalid_desc_hipas == hipas));
}

/*
 * Returns true if @s2tte has HIPAS=UNASSIGNED and RIPAS=@ripas.
 */
static inline bool s2tte_has_unassigned_ripas(unsigned long s2tte,
					      unsigned long ripas)
{
	return (((s2tte & S2TTE_INVALID_RIPAS_MASK) == ripas) &&
		  s2tte_has_hipas(s2tte, S2TTE_INVALID_HIPAS_UNASSIGNED));
}

/*
 * Returns true if @s2tte has HIPAS=ASSIGNED and RIPAS=@ripas.
 */
static inline bool s2tte_has_assigned_ripas(unsigned long s2tte,
					    unsigned long ripas)
{
	return (((s2tte & S2TTE_INVALID_RIPAS_MASK) == ripas) &&
		  s2tte_has_hipas(s2tte, S2TTE_INVALID_HIPAS_ASSIGNED));
}

/*
 * Returns true if @s2tte has HIPAS=UNASSIGNED.
 */
bool s2tte_is_unassigned(unsigned long s2tte)
{
	return s2tte_has_hipas(s2tte, S2TTE_INVALID_HIPAS_UNASSIGNED);
}

/*
 * Returns true if @s2tte is an unassigned_empty.
 */
bool s2tte_is_unassigned_empty(unsigned long s2tte)
{
	return (((s2tte & S2TTE_NS) == 0UL) &&
		  s2tte_has_unassigned_ripas(s2tte, S2TTE_INVALID_RIPAS_EMPTY));
}

/*
 * Returns true if @s2tte is an unassigned_ram.
 */
bool s2tte_is_unassigned_ram(unsigned long s2tte)
{
	return s2tte_has_unassigned_ripas(s2tte, S2TTE_INVALID_RIPAS_RAM);
}

/*
 * Returns true if @s2tte is unassigned_ns.
 */
bool s2tte_is_unassigned_ns(unsigned long s2tte)
{
	return (((s2tte & S2TTE_NS) != 0UL) &&
		  s2tte_has_hipas(s2tte, S2TTE_INVALID_HIPAS_UNASSIGNED));
}

/*
 * Returns true if @s2tte has RIPAS=DESTROYED.
 */
bool s2tte_is_unassigned_destroyed(unsigned long s2tte)
{
	return s2tte_has_unassigned_ripas(s2tte, S2TTE_INVALID_RIPAS_DESTROYED);
}

/*
 * Returns true if @s2tte is an assigned_destroyed.
 */
bool s2tte_is_assigned_destroyed(unsigned long s2tte, long level)
{
	(void)level;

	return s2tte_has_assigned_ripas(s2tte, S2TTE_INVALID_RIPAS_DESTROYED);
}

/*
 * Returns true if @s2tte is an assigned_empty.
 */
bool s2tte_is_assigned_empty(unsigned long s2tte, long level)
{
	(void)level;

	return s2tte_has_assigned_ripas(s2tte, S2TTE_INVALID_RIPAS_EMPTY);
}

static bool s2tte_check(unsigned long s2tte, long level, unsigned long ns)
{
	unsigned long desc_type;

	if ((s2tte & S2TTE_NS) != ns) {
		return false;
	}

	desc_type = s2tte & S2TT_DESC_TYPE_MASK;

	/* Only pages at L3 and valid blocks at L2 allowed */
	if (((level == S2TT_PAGE_LEVEL) && (desc_type == S2TTE_L3_PAGE)) ||
	    ((level == S2TT_MIN_BLOCK_LEVEL) && (desc_type == S2TTE_L012_BLOCK))) {
		return true;
	}

	return false;
}

/*
 * Returns true if @s2tte is an assigned_ram.
 */
bool s2tte_is_assigned_ram(unsigned long s2tte, long level)
{
	return s2tte_check(s2tte, level, 0UL);
}

/*
 * Returns true if @s2tte is an assigned_ns s2tte.
 */
bool s2tte_is_assigned_ns(unsigned long s2tte, long level)
{
	return s2tte_check(s2tte, level, S2TTE_NS);
}

/*
 * Returns true if @s2tte is a table at level @level.
 */
bool s2tte_is_table(unsigned long s2tte, long level)
{
	return ((level < S2TT_PAGE_LEVEL) &&
		((s2tte & S2TT_DESC_TYPE_MASK) == S2TTE_L012_TABLE));
}

/*
 * Returns RIPAS of @s2tte.
 *
 * Caller should ensure that HIPAS=UNASSIGNED or HIPAS=ASSIGNED.
 * The s2tte, if valid, should correspond to RIPAS_RAM.
 */
enum ripas s2tte_get_ripas(unsigned long s2tte)
{
	unsigned long desc_ripas = s2tte & S2TTE_INVALID_RIPAS_MASK;

	/*
	 * If valid s2tte descriptor is passed, then ensure S2AP[0]
	 * bit is 1 (S2AP is set to RW for lower EL), which corresponds
	 * to RIPAS_RAM (bits[6:5] = b01) on a valid descriptor.
	 */
	assert(((s2tte & S2TT_DESC_TYPE_MASK) == S2TTE_INVALID) ||
	       (desc_ripas == S2TTE_INVALID_RIPAS_RAM));

	assert(EXTRACT(S2TTE_INVALID_HIPAS, s2tte) <=
	       EXTRACT(S2TTE_INVALID_HIPAS, S2TTE_INVALID_HIPAS_ASSIGNED));

	desc_ripas = desc_ripas >> S2TTE_INVALID_RIPAS_SHIFT;

	assert(desc_ripas <= RIPAS_DESTROYED);

	return (enum ripas)desc_ripas;
}

/*
 * Populates @s2tt with unassigned_empty s2ttes.
 *
 * The granule is populated before it is made a table,
 * hence, don't use s2tte_write for access.
 */
void s2tt_init_unassigned_empty(unsigned long *s2tt)
{
	assert(s2tt != NULL);

	unsigned long s2tte =
		s2tte_create_unassigned_empty();

	for (unsigned int i = 0U; i < S2TTES_PER_S2TT; i++) {
		s2tt[i] = s2tte;
	}

	dsb(ish);
}

/*
 * Populates @s2tt with unassigned_ram s2ttes.
 *
 * The granule is populated before it is made a table,
 * hence, don't use s2tte_write for access.
 */
void s2tt_init_unassigned_ram(unsigned long *s2tt)
{
	assert(s2tt != NULL);

	unsigned long s2tte = s2tte_create_unassigned_ram();

	for (unsigned int i = 0U; i < S2TTES_PER_S2TT; i++) {
		s2tt[i] = s2tte;
	}

	dsb(ish);
}

/*
 * Populates @s2tt with unassigned_ns s2ttes.
 *
 * The granule is populated before it is made a table,
 * hence, don't use s2tte_write for access.
 */
void s2tt_init_unassigned_ns(unsigned long *s2tt)
{
	assert(s2tt != NULL);

	unsigned long s2tte = s2tte_create_unassigned_ns();

	for (unsigned int i = 0U; i < S2TTES_PER_S2TT; i++) {
		s2tt[i] = s2tte;
	}

	dsb(ish);
}

/*
 * Populates @s2tt with s2ttes which have HIPAS=DESTROYED.
 *
 * The granule is populated before it is made a table,
 * hence, don't use s2tte_write for access.
 */
void s2tt_init_unassigned_destroyed(unsigned long *s2tt)
{
	assert(s2tt != NULL);

	unsigned long s2tte =
		s2tte_create_unassigned_destroyed();

	for (unsigned int i = 0U; i < S2TTES_PER_S2TT; i++) {
		s2tt[i] = s2tte;
	}
	dsb(ish);
}

/*
 * Populates @s2tt with HIPAS=ASSIGNED, RIPAS=DESTROYED s2ttes that refer to a
 * contiguous memory block starting at @pa, and mapped at level @level.
 *
 * The granule is populated before it is made a table,
 * hence, don't use s2tte_write for access.
 */
void s2tt_init_assigned_destroyed(unsigned long *s2tt, unsigned long pa, long level)
{
	assert(level >= S2TT_MIN_BLOCK_LEVEL);
	assert(level <= S2TT_PAGE_LEVEL);
	assert(s2tt != NULL);
	assert(s2tte_is_addr_lvl_aligned(pa, level));

	const unsigned long map_size = s2tte_map_size(level);

	for (unsigned int i = 0U; i < S2TTES_PER_S2TT; i++) {
		s2tt[i] = s2tte_create_assigned_destroyed(pa, level);
		pa += map_size;
	}
	dsb(ish);
}

/*
 * Populates @s2tt with HIPAS=ASSIGNED, RIPAS=EMPTY s2ttes that refer to a
 * contiguous memory block starting at @pa, and mapped at level @level.
 *
 * The granule is populated before it is made a table,
 * hence, don't use s2tte_write for access.
 */
void s2tt_init_assigned_empty(unsigned long *s2tt, unsigned long pa, long level)
{
	assert(level >= S2TT_MIN_BLOCK_LEVEL);
	assert(level <= S2TT_PAGE_LEVEL);
	assert(s2tt != NULL);
	assert(s2tte_is_addr_lvl_aligned(pa, level));

	const unsigned long map_size = s2tte_map_size(level);

	for (unsigned int i = 0U; i < S2TTES_PER_S2TT; i++) {
		s2tt[i] = s2tte_create_assigned_empty(pa, level);
		pa += map_size;
	}
	dsb(ish);
}

/*
 * Populates @s2tt with assigned_ram s2ttes that refer to a
 * contiguous memory block starting at @pa, and mapped at level @level.
 *
 * The granule is populated before it is made a table,
 * hence, don't use s2tte_write for access.
 */
void s2tt_init_assigned_ram(unsigned long *s2tt, unsigned long pa, long level)
{
	assert(level >= S2TT_MIN_BLOCK_LEVEL);
	assert(level <= S2TT_PAGE_LEVEL);
	assert(s2tt != NULL);
	assert(s2tte_is_addr_lvl_aligned(pa, level));

	const unsigned long map_size = s2tte_map_size(level);

	for (unsigned int i = 0U; i < S2TTES_PER_S2TT; i++) {
		s2tt[i] = s2tte_create_assigned_ram(pa, level);
		pa += map_size;
	}
	dsb(ish);
}

/*
 * Populates @s2tt with NS attributes @attrs that refer to a
 * contiguous memory block starting at @pa, and mapped at level @level.
 *
 * The granule is populated before it is made a table,
 * hence, don't use s2tte_write for access.
 */
void s2tt_init_assigned_ns(unsigned long *s2tt, unsigned long attrs,
			   unsigned long pa, long level)
{
	assert(level >= S2TT_MIN_BLOCK_LEVEL);
	assert(level <= S2TT_PAGE_LEVEL);
	assert(s2tt != NULL);
	assert(s2tte_is_addr_lvl_aligned(pa, level));

	const unsigned long map_size = s2tte_map_size(level);

	for (unsigned int i = 0U; i < S2TTES_PER_S2TT; i++) {
		unsigned long s2tte = attrs & S2TTE_NS_ATTR_HOST_MASK;

		s2tt[i] = s2tte_create_assigned_ns(s2tte | pa, level);
		pa += map_size;
	}

	dsb(ish);
}

/*
 * Returns true if s2tte has 'output address' field, namely, if it is one of:
 * - assigned_empty
 * - assigned_ram
 * - assigned_ns
 * - assigned_destroyed
 * - table
 */
static bool s2tte_has_pa(unsigned long s2tte, long level)
{
	unsigned long desc_type = s2tte & S2TT_DESC_TYPE_MASK;

	return ((desc_type != S2TTE_INVALID) ||	/* block, page or table */
		s2tte_is_assigned_empty(s2tte, level) ||
		s2tte_is_assigned_destroyed(s2tte, level));
}

/*
 * Returns true if s2tte is a live RTTE entry. i.e.,
 * HIPAS is ASSIGNED.
 *
 * NOTE: For now, only the RTTE with PA are live.
 * This could change with EXPORT/IMPORT support.
 */
static bool s2tte_is_live(unsigned long s2tte, long level)
{
	return s2tte_has_pa(s2tte, level);
}

/* Returns physical address of a S2TTE */
unsigned long s2tte_pa(unsigned long s2tte, long level)
{
	assert(level <= S2TT_PAGE_LEVEL);
	assert(level >= S2TT_MIN_STARTING_LEVEL);

	if (!s2tte_has_pa(s2tte, level)) {
		assert(false);
	}

	if (s2tte_is_table(s2tte, level)) {
		return addr_level_mask(s2tte, S2TT_PAGE_LEVEL);
	}

	return addr_level_mask(s2tte, level);
}

bool s2tte_is_addr_lvl_aligned(unsigned long addr, long level)
{
	return (addr == addr_level_mask(addr, level));
}

typedef bool (*s2tte_type_checker)(unsigned long s2tte);

static bool table_is_uniform_block(unsigned long *table,
				   s2tte_type_checker s2tte_is_x)
{
	for (unsigned int i = 0U; i < S2TTES_PER_S2TT; i++) {
		unsigned long s2tte = s2tte_read(&table[i]);

		if (!s2tte_is_x(s2tte)) {
			return false;
		}
	}

	return true;
}

/*
 * Returns true if all s2ttes in @table are unassigned_empty.
 */
bool s2tt_is_unassigned_empty_block(unsigned long *table)
{
	assert(table != NULL);

	return table_is_uniform_block(table, s2tte_is_unassigned_empty);
}

/*
 * Returns true if all s2ttes in @table are unassigned_ram.
 */
bool s2tt_is_unassigned_ram_block(unsigned long *table)
{
	assert(table != NULL);

	return table_is_uniform_block(table, s2tte_is_unassigned_ram);
}

/*
 * Returns true if all s2ttes in @table are unassigned_ns
 */
bool s2tt_is_unassigned_ns_block(unsigned long *table)
{
	assert(table != NULL);

	return table_is_uniform_block(table, s2tte_is_unassigned_ns);
}

/*
 * Returns true if all s2ttes in @table are unassigned_destroyed
 */
bool s2tt_is_unassigned_destroyed_block(unsigned long *table)
{
	assert(table != NULL);

	return table_is_uniform_block(table, s2tte_is_unassigned_destroyed);
}

typedef bool (*s2tte_type_level_checker)(unsigned long s2tte, long level);

static bool table_maps_block(unsigned long *table,
			     long level,
			     s2tte_type_level_checker s2tte_is_x,
			     bool check_ns_attrs)
{
	assert(table != NULL);

	unsigned long base_pa;
	unsigned long map_size = s2tte_map_size(level);
	unsigned long s2tte = s2tte_read(&table[0]);
	unsigned int i;

	if (!s2tte_is_x(s2tte, level)) {
		return false;
	}

	base_pa = s2tte_pa(s2tte, level);
	if (!s2tte_is_addr_lvl_aligned(base_pa, level - 1L)) {
		return false;
	}

	for (i = 1U; i < S2TTES_PER_S2TT; i++) {
		unsigned long expected_pa = base_pa + (i * map_size);

		s2tte = s2tte_read(&table[i]);

		if (!s2tte_is_x(s2tte, level)) {
			return false;
		}

		if (s2tte_pa(s2tte, level) != expected_pa) {
			return false;
		}

		if (check_ns_attrs) {
			unsigned long ns_attrs =
					s2tte & S2TTE_NS_ATTR_HOST_MASK;

			/*
			 * We match all the attributes in the S2TTE
			 * except for the AF bit.
			 */
			if ((s2tte & S2TTE_NS_ATTR_HOST_MASK) != ns_attrs) {
				return false;
			}
		}
	}

	return true;
}

/*
 * Returns true if all s2ttes are assigned_empty
 * and refer to a contiguous block of granules aligned to @level - 1.
 */
bool s2tt_maps_assigned_empty_block(unsigned long *table, long level)
{
	return table_maps_block(table, level, s2tte_is_assigned_empty,
				  false);
}

/*
 * Returns true if all s2ttes are assigned_ram and
 * refer to a contiguous block of granules aligned to @level - 1.
 */
bool s2tt_maps_assigned_ram_block(unsigned long *table, long level)
{
	return table_maps_block(table, level, s2tte_is_assigned_ram, false);
}

/*
 * Returns true if
 *    - all s2ttes in @table are assigned_ns s2ttes and
 *    - they refer to a contiguous block of granules aligned to @level - 1 and
 *    - all the s2tte attributes in @table controlled by the host are identical
 *
 * @pre: @table maps IPA outside PAR.
 */
bool s2tt_maps_assigned_ns_block(unsigned long *table, long level)
{
	return table_maps_block(table, level, s2tte_is_assigned_ns, true);
}

/*
 * Returns true if all s2ttes are assigned_destroyed and
 * refer to a contiguous block of granules aligned to @level - 1.
 */
bool s2tt_maps_assigned_destroyed_block(unsigned long *table, long level)
{
	return table_maps_block(table, level, s2tte_is_assigned_destroyed,
				  false);
}

/*
 * Scan the RTT @s2tt (which is @wi.level), from the entry (@wi.index) and
 * skip the non-live entries (i.e., HIPAS=UNASSIGNED).
 * In other words, the scanning stops when a live RTTE is encountered or we
 * reach the end of this RTT.
 *
 * For now an RTTE can be considered non-live if it doesn't have a PA.
 * NOTE: This would change with EXPORT/IMPORT where we may have metadata stored
 * in the RTTE.
 *
 * @addr is not necessarily aligned to the wi.last_level (e.g., if we were called
 * with RMI_ERROR_RTT).
 *
 * Returns:
 * - If the entry @wi.index is live, returns @addr.
 * - If none of the entries in the @s2tt are "live", returns the address of the
 *   first entry in the next table.
 * - Otherwise, the address of the first live entry in @s2tt
 */
unsigned long s2tt_skip_non_live_entries(unsigned long addr,
					 unsigned long *table,
					 const struct s2tt_walk *wi)
{
	assert(table != NULL);
	assert(wi != NULL);
	assert(wi->index <= S2TTES_PER_S2TT);
	assert(wi->last_level >= S2TT_MIN_STARTING_LEVEL);
	assert(wi->last_level <= S2TT_PAGE_LEVEL);

	unsigned long i, index = wi->index;
	long level = wi->last_level;
	unsigned long map_size;

	/*
	 * If the entry for the map_addr is live,
	 * return @addr.
	 */
	if (s2tte_is_live(s2tte_read(&table[index]), level)) {
		return addr;
	}

	/*
	 * Align the address DOWN to the map_size, as expected for the @level,
	 * so that we can compute the correct address by using the index.
	 */
	map_size = s2tte_map_size(level);
	addr &= ~(map_size - 1UL);

	/* Skip the "index" */
	for (i = index + 1UL; i < S2TTES_PER_S2TT; i++) {
		unsigned long s2tte = s2tte_read(&table[i]);

		if (s2tte_is_live(s2tte, level)) {
			break;
		}
	}

	return (addr + ((i - index) * map_size));
}
