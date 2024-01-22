/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include "granule.h"
#include "realm.h"
#include "ripas.h"
#include "smc-rmi.h"
#include "tb_common.h"
#include "tb_granules.h"
#include "tb_measurement.h"
#include "tb_realm.h"
#include "tb_rtt.h"

#define VMID8_COUNT				(U(1) << 8)
#define VMID16_COUNT				(U(1) << 16)
#define MAX_ROOT_RTT_IN_CBMC_VERIFICATION	2

bool VmidIsFree(uint16_t vmid)
{
	unsigned int offset = vmid / BITS_PER_UL;
	unsigned int vmid_bit = vmid % BITS_PER_UL;
	uint64_t bit_mask = (uint64_t)(1UL << vmid_bit);
	/* return TRUE if the bit at the bit_mask is ZERO. */
	return (vmids[offset] & bit_mask) == 0;
}

struct rmm_realm Realm(uint64_t addr)
{
	size_t i;

	/*
	 * TODO: change to a unified function call
	 * Find the realm ptr related to `addr`.
	 * If it is NULL, return the `nondet_realm` realm.
	 */
	if (!valid_pa(addr)) {
		return nondet_struct_rmm_realm();
	}

	struct rd *rd_ptr = pa_to_granule_buffer_ptr(addr);

	__CPROVER_assert(rd_ptr, "internal: `_Realm` rd_ptr is not null");


	/* convert the type */
	struct rmm_realm spec_rd = {
		.ipa_width = rd_ptr->s2_ctx.ipa_bits,
		.hash_algo = rd_ptr->algorithm,
		.rec_index = rd_ptr->rec_count,
		.rtt_base = granule_metadata_ptr_to_pa(rd_ptr->s2_ctx.g_rtt),
		.rtt_level_start = rd_ptr->s2_ctx.s2_starting_level,
		.rtt_num_start = rd_ptr->s2_ctx.num_root_rtts,
		.state = rd_ptr->state,
		.vmid = rd_ptr->s2_ctx.vmid
	};

	for (i = 0; i < MEASUREMENT_SLOT_NR; ++i) {
		spec_rd.measurements[i] = (uint64_t)(rd_ptr->measurement[i]);
	}
	for (i = 0; i < sizeof(spec_rd.rpv); ++i) {
		spec_rd.rpv[i] = rd_ptr->rpv[i];
	}

	return spec_rd;
}

bool valid_realm_state(uint64_t value)
{
	return value == (uint64_t)REALM_NEW
		|| value == (uint64_t)REALM_ACTIVE
		|| value == (uint64_t)REALM_SYSTEM_OFF;
}

/* Detail of the valid state */
bool valid_realm_s2_context(struct realm_s2_context value)
{
	unsigned int vmid_count = is_feat_vmid16_present() ? VMID16_COUNT : VMID8_COUNT;

	return  value.s2_starting_level >= 0
		&& value.s2_starting_level <= 3
		/* TODO focus on standard size of root rtt for now */
		&& value.num_root_rtts >= 1
		/* && value.num_root_rtts <= 16 */
		&& value.num_root_rtts <= MAX_ROOT_RTT_IN_CBMC_VERIFICATION
		&& valid_granule_metadata_ptr(value.g_rtt)
		&& value.g_rtt->state == GRANULE_STATE_RTT
		/* TODO: what is the ranges here */
		&& value.ipa_bits == (3 - value.s2_starting_level + 1) *
			S2TTE_STRIDE + value.num_root_rtts
		/* TODO check */
		&& value.vmid < vmid_count;
}

bool valid_rd(struct rd value)
{
	return valid_realm_state(value.state)
		&& valid_realm_s2_context(value.s2_ctx)
		&& valid_hash_algo(value.algorithm)
		&& value.num_rec_aux == MAX_REC_AUX_GRANULES;
}

struct rd init_rd(void)
{
	struct rd value = nondet_struct_rd();

	unsigned int num_root_rtts = nondet_unsigned_int();

	__CPROVER_assume(valid_num_root_rtts(num_root_rtts));
	struct granule *g_root_rtt = init_rtt_root_page(num_root_rtts);

	value.s2_ctx.num_root_rtts = num_root_rtts;
	value.s2_ctx.g_rtt = g_root_rtt;
	value.rpv[0] = 0;
	/*
	 * If the `g_root_rtt` does not satisfy the assume condition, all
	 * following `cover` checks fail.
	 */
	__CPROVER_assume(valid_rd(value));

	/* Non-deterministically if the vmid is registered. */
	uint64_t vmid = value.s2_ctx.vmid;
	unsigned int offset = vmid / BITS_PER_UL;

	vmid %= BITS_PER_UL;
	uint64_t bit_mask = (uint64_t)(1UL << vmid);

	if (nondet_bool()) {
		vmids[offset] |= bit_mask;
	}

	return value;
}

struct granule *init_realm_descriptor_page(void)
{
	struct granule g = init_granule();

	__CPROVER_assume(g.state == GRANULE_STATE_RD);
	struct rd rd = init_rd();

	/*
	 * This assert is necessary because the COMPILER_ASSERT in realm.h is
	 * disabled for CBMC.
	 */
	__CPROVER_assert(sizeof(struct rd) <= GRANULE_SIZE, "check rd size");

	struct granule *rd_granule = inject_granule(&g, &rd, sizeof(rd));

	return rd_granule;
}

/* TODO if the implementation is correct? */
bool RealmIsLive(uint64_t rd_addr)
{
	/*
	 * TODO either update or remove
	 * From Alp05 spec:
	 * R 0013:  A Realm is live if any of the following is true:
	 *     - The number of RECs owned by the Realm is not zero
	 *     - The level 0 RTT of the Realm is live
	 *
	 * I 0014:
	 *   If a Realm owns a non-zero number of Data Granules,
	 *   this implies that its level 0 RTT is live,
	 *   and therefore that the Realm itself is live.
	 */

	/* TODO find a better way to assert the rd_addr. */
	if (!valid_pa(rd_addr)) {
		return nondet_bool();
	}

	struct granule *g_rd = pa_to_granule_metadata_ptr(rd_addr);

	__ASSERT(g_rd, "internal: `_RealmIsLive`, rd is not null");

	if (g_rd->refcount != 0) {
		return true;
	}

	struct rd *rd = pa_to_granule_buffer_ptr(rd_addr);

	__ASSERT(rd, "internal: `_RealmIsLive`, rd is not null");

	for (size_t i = 0;
	    i < rd->s2_ctx.num_root_rtts && i < MAX_ROOT_RTT_IN_CBMC_VERIFICATION;
	    ++i) {
		if (((rd->s2_ctx.g_rtt) + i)->refcount != 0) {
			return true;
		}
	}

	return false;
}
bool RttsStateEqual(uint64_t base, uint64_t number_start, uint64_t state)
{
	if (!valid_pa(base)) {
		return nondet_bool();
	}

	struct granule *g_base = pa_to_granule_metadata_ptr(base);

	__ASSERT(g_base, "internal: `_RttsStateEqual`, base is not null");
	/* hardcode the max number of root rtts */
	/* TODO find a macro */
	for (int i = 0; i < number_start && i < 16; i++) {
		if ((g_base + i)->state != state) {
			return false;
		}
	}
	return true;
}

uint64_t RecAuxCount(uint64_t rd_addr)
{
	return MAX_REC_AUX_GRANULES;
}
