/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch_features.h>
#include <assert.h>
#include <buffer.h>
#include <debug.h>
#include <feature.h>
#include <granule.h>
#include <measurement.h>
#include <realm.h>
#include <s2tt.h>
#include <simd.h>
#include <smc-handler.h>
#include <smc-rmi.h>
#include <smc.h>
#include <stddef.h>
#include <string.h>
#include <vmid.h>

#define RMM_FEATURE_MIN_IPA_SIZE	PARANGE_0000_WIDTH

unsigned long smc_realm_activate(unsigned long rd_addr)
{
	struct rd *rd;
	struct granule *g_rd;
	unsigned long ret;

	g_rd = find_lock_granule(rd_addr, GRANULE_STATE_RD);
	if (g_rd == NULL) {
		return RMI_ERROR_INPUT;
	}

	rd = buffer_granule_map(g_rd, SLOT_RD);
	assert(rd != NULL);

	if (get_rd_state_locked(rd) == REALM_NEW) {
		set_rd_state(rd, REALM_ACTIVE);
		ret = RMI_SUCCESS;
	} else {
		ret = RMI_ERROR_REALM;
	}
	buffer_unmap(rd);

	granule_unlock(g_rd);

	return ret;
}

static bool get_realm_params(struct rmi_realm_params *realm_params,
				unsigned long realm_params_addr)
{
	bool ns_access_ok;
	struct granule *g_realm_params;

	g_realm_params = find_granule(realm_params_addr);
	if ((g_realm_params == NULL) || (g_realm_params->state != GRANULE_STATE_NS)) {
		return false;
	}

	ns_access_ok = ns_buffer_read(SLOT_NS, g_realm_params, 0U,
				      sizeof(*realm_params), realm_params);

	return ns_access_ok;
}

static bool is_lpa2_requested(struct rmi_realm_params *p)
{
	return (EXTRACT(RMI_REALM_FLAGS_LPA2, p->flags) == RMI_FEATURE_TRUE);
}

/*
 * See the library pseudocode
 * aarch64/translation/vmsa_faults/AArch64.S2InconsistentSL on which this is
 * modeled.
 */
static bool s2_inconsistent_sl(unsigned int ipa_bits, int sl, bool lpa2)
{
	unsigned int levels = (unsigned int)(S2TT_PAGE_LEVEL - sl);
	unsigned int sl_min_ipa_bits, sl_max_ipa_bits;

	sl_min_ipa_bits = (levels * S2TTE_STRIDE) + GRANULE_SHIFT + 1U;

	/*
	 * The stride for level -1 is only four bits, and we cannot have
	 * concatenated tables at this level, so adjust sl_max_ipa_bits
	 * accordingly.
	 */
	if ((sl == S2TT_MIN_STARTING_LEVEL_LPA2) && (lpa2 == true)) {
		sl_max_ipa_bits = sl_min_ipa_bits + (S2TTE_STRIDE_LM1 - 1U);
	} else {
		sl_max_ipa_bits = sl_min_ipa_bits + (S2TTE_STRIDE - 1U);
	}

	/*
	 * The maximum number of concatenated tables is 16,
	 * hence we are adding 4 to the 'sl_max_ipa_bits' for sl > 0 or
	 * sl == 0 when FEAT_LPA2 is enabled.
	 */
	if ((sl > 0) || ((sl == 0) && (lpa2 == true))) {
		sl_max_ipa_bits += 4U;
	}

	return ((ipa_bits < sl_min_ipa_bits) || (ipa_bits > sl_max_ipa_bits));
}

static bool validate_ipa_bits_and_sl(unsigned int ipa_bits, long sl, bool lpa2)
{
	long min_starting_level;
	unsigned int max_ipa_bits;

	max_ipa_bits = (lpa2 == true) ?
				S2TT_MAX_IPA_BITS_LPA2 : S2TT_MAX_IPA_BITS;

	/* cppcheck-suppress misra-c2012-10.6 */
	min_starting_level = (lpa2 == true) ?
				S2TT_MIN_STARTING_LEVEL_LPA2 : S2TT_MIN_STARTING_LEVEL;

	if ((ipa_bits < S2TT_MIN_IPA_BITS) || (ipa_bits > max_ipa_bits)) {
		return false;
	}

	if ((sl < min_starting_level) || (sl > S2TT_PAGE_LEVEL)) {
		return false;
	}

	/*
	 * We assume ARMv8.4-TTST is supported with RME so the only SL
	 * configuration we need to check with 4K granules is SL == 0 following
	 * the library pseudocode aarch64/translation/vmsa_faults/AArch64.S2InvalidSL.
	 *
	 * Note that this only checks invalid SL values against the properties
	 * of the hardware platform, other misconfigurations between IPA size
	 * and SL is checked in s2_inconsistent_sl.
	 */
	if ((sl == 0L) && (arch_feat_get_pa_width() < 44U)) {
		return false;
	}

	return !s2_inconsistent_sl(ipa_bits, (int)sl, lpa2);
}

/*
 * Calculate the number of s2 root translation tables needed given the
 * starting level and the IPA size in bits. This function assumes that
 * the 'sl' and 'ipa_bits' are consistent with each other and 'ipa_bits'
 * is within architectural boundaries.
 */
static unsigned int s2_num_root_rtts(unsigned int ipa_bits, int sl)
{
	unsigned int levels = (unsigned int)(S2TT_PAGE_LEVEL - sl);
	unsigned int sl_ipa_bits;

	/* First calculate how many bits can be resolved without concatenation */
	sl_ipa_bits = (levels * S2TTE_STRIDE) /* Bits resolved by table walk without SL */
		      + GRANULE_SHIFT	      /* Bits directly mapped to OA */
		      + S2TTE_STRIDE;	      /* Bits resolved by single SL */

	/*
	 * If 'sl' were < 0, sl_ipa_bits would already be at least >= than
	 * 'ipa_bits' as the latter is assumed to be within boundary limits.
	 * This will make the check below pass and return 1U as the number of
	 * s2 root tables, which is the only valid value for a start level < 0.
	 */
	if ((sl_ipa_bits >= ipa_bits)) {
		return U(1);
	}

	return (U(1) << (ipa_bits - sl_ipa_bits));
}

/*
 * Initialize the starting level of stage 2 translation tables.
 *
 * The protected half of the IPA space is initialized to
 * unassigned_empty type of s2tte.
 * The unprotected half of the IPA space is initialized to
 * unassigned_ns type of s2tte.
 * The remaining entries are not initialized.
 */
static void init_s2_starting_level(struct rd *rd, unsigned int rtt_index)
{
	unsigned long current_ipa = 0U;
	struct s2tt_context *s2tt_ctx = index_to_s2_context(rd, rtt_index);
	struct granule *g_rtt = s2tt_ctx->g_rtt;
	unsigned int num_root_rtts;
	unsigned int s2ttes_per_s2tt = (unsigned int)(
		(s2tt_ctx->s2_starting_level == S2TT_MIN_STARTING_LEVEL_LPA2) ?
			S2TTES_PER_S2TT_LM1 : S2TTES_PER_S2TT);
	unsigned int levels = (unsigned int)(S2TT_PAGE_LEVEL -
						s2tt_ctx->s2_starting_level);
	/*
	 * The size of the IPA space that is covered by one S2TTE at
	 * the starting level.
	 */
	unsigned long sl_entry_map_size =
			(UL(1)) << U(U(levels * S2TTE_STRIDE) + U(GRANULE_SHIFT));

	num_root_rtts = s2tt_ctx->num_root_rtts;
	for (unsigned int rtt = 0U; rtt < num_root_rtts; rtt++) {
		unsigned long *s2tt = buffer_granule_map(g_rtt, SLOT_RTT);

		assert(s2tt != NULL);

		for (unsigned int rtte = 0U; rtte < s2ttes_per_s2tt; rtte++) {
			if (addr_in_par(rd, current_ipa)) {
				s2tt[rtte] = s2tte_create_unassigned_empty(s2tt_ctx,
							S2TTE_DEFAULT_IPA_AP);
			} else {
				s2tt[rtte] = s2tte_create_unassigned_ns(s2tt_ctx);
			}

			current_ipa += sl_entry_map_size;
			if (current_ipa == realm_ipa_size(rd)) {
				buffer_unmap(s2tt);
				return;
			}

		}
		buffer_unmap(s2tt);
		g_rtt++;
	}

	/*
	 * We have come to the end of starting level s2tts but we haven't
	 * reached the ipa size.
	 */
	assert(false);
}

static bool validate_realm_params(struct rmi_realm_params *p)
{
	unsigned long feat_reg0 = get_feature_register_0();

	/* Validate LPA2 flag */
	if (is_lpa2_requested(p)  &&
	    (EXTRACT(RMM_FEATURE_REGISTER_0_LPA2, feat_reg0) ==
							RMI_FEATURE_FALSE)) {
		return false;
	}

	/* Validate S2SZ field */
	if ((p->s2sz < RMM_FEATURE_MIN_IPA_SIZE) ||
	    (p->s2sz > EXTRACT(RMM_FEATURE_REGISTER_0_S2SZ, feat_reg0))) {
		return false;
	}

	/* Validate number of breakpoints */
	if ((p->num_bps >
		EXTRACT(RMM_FEATURE_REGISTER_0_NUM_BPS, feat_reg0)) ||
	    (p->num_wps >
		EXTRACT(RMM_FEATURE_REGISTER_0_NUM_WPS, feat_reg0))) {
		return false;
	}

	/* Validate RMI_REALM_FLAGS_SVE flag */
	if (EXTRACT(RMI_REALM_FLAGS_SVE, p->flags) == RMI_FEATURE_TRUE) {
		if (EXTRACT(RMM_FEATURE_REGISTER_0_SVE_EN, feat_reg0) ==
						      RMI_FEATURE_FALSE) {
			return false;
		}

		/* Validate SVE_VL value */
		if (p->sve_vl >
			EXTRACT(RMM_FEATURE_REGISTER_0_SVE_VL, feat_reg0)) {
			return false;
		}
	}

	/*
	 * Skip validation of RMI_REALM_FLAGS_PMU flag
	 * as RMM always assumes that PMUv3p7+ is present.
	 */

	/* Validate number of PMU counters if PMUv3 is enabled */
	if (EXTRACT(RMI_REALM_FLAGS_PMU, p->flags) == RMI_FEATURE_TRUE) {
		if (p->pmu_num_ctrs >
		    EXTRACT(RMM_FEATURE_REGISTER_0_PMU_NUM_CTRS, feat_reg0)) {
			return false;
		}

		/*
		 * Check if number of PMU counters is 0 and
		 * FEAT_HMPN0 is implemented
		 */
		if ((p->pmu_num_ctrs == 0U) && !is_feat_hpmn0_present()) {
			return false;
		}
	}

	if (!validate_ipa_bits_and_sl(p->s2sz, p->rtt_level_start,
						is_lpa2_requested(p))) {
		return false;
	}

	if (s2_num_root_rtts(p->s2sz, (int)p->rtt_level_start) !=
						p->rtt_num_start) {
		return false;
	}

	/*
	 * TODO: Check the VMSA configuration which is either static for the
	 * RMM or per realm with the supplied parameters and store the
	 * configuration on the RD, and it can potentially be copied into RECs
	 * later.
	 */

	switch (p->algorithm) {
	case RMI_HASH_SHA_256:
	case RMI_HASH_SHA_512:
		break;
	default:
		return false;
	}

	return true;
}

static void free_sl_rtts(struct granule *g_rtt, unsigned int num_rtts)
{
	for (unsigned int i = 0U; i < num_rtts; i++) {
		struct granule *g = (struct granule *)((uintptr_t)g_rtt +
						(i * sizeof(struct granule)));

		granule_lock(g, GRANULE_STATE_RTT);
		buffer_granule_memzero(g, SLOT_RTT);
		granule_unlock_transition(g, GRANULE_STATE_DELEGATED);
	}
}

static void free_vmids(unsigned short *vmid_list, unsigned int vmid_cnt)
{
	for (unsigned int i = 0U; i < vmid_cnt; i++) {
		vmid_free(vmid_list[i]);
	}
}

static void revert_sl_rtts(unsigned long *rtt_base,
			   unsigned int rtt_root_cnt,
			   unsigned int rtt_tree_cnt)
{
	for (int rtt_tree_id = 0U; rtt_tree_id < rtt_tree_cnt; rtt_tree_id++) {
		struct granule *g;
		g = find_granule(rtt_base[rtt_tree_id]);
		assert(g != NULL);
		free_sl_rtts(g, rtt_root_cnt);
	}
}

static bool transition_sl_rtts(unsigned long *rtt_base,
			       unsigned int rtt_root_cnt,
			       unsigned int rtt_tree_cnt)
{
	int rtt_id, rtt_tree_id;
	unsigned long rtt_addr;
	struct granule* g;

	for (rtt_tree_id = 0; rtt_tree_id < rtt_tree_cnt; rtt_tree_id++) {
		rtt_addr = rtt_base[rtt_tree_id];
		for (rtt_id = 0; rtt_id < rtt_root_cnt; rtt_id++) {
			g = find_lock_granule(rtt_addr, GRANULE_STATE_DELEGATED);
			if (g == NULL) {
				goto error_out;
			}
			granule_unlock_transition(g, GRANULE_STATE_RTT);
			rtt_addr += GRANULE_SIZE;
		}
	}
	return true;

error_out:
	/* Revert partially transitioned root tree. */
	if (rtt_id > 0U) {
		g = find_granule(rtt_base[rtt_tree_id]);
		assert(g != NULL);
		free_sl_rtts(g, rtt_id);
	}

	/* Revert fully transitioned root trees. */
	revert_sl_rtts(rtt_base, rtt_root_cnt, rtt_tree_id);

	return false;
}

unsigned long smc_realm_create(unsigned long rd_addr,
			       unsigned long realm_params_addr)
{
	struct granule *g_rd;
	struct rd *rd;
	struct rmi_realm_params p;
	unsigned int vmids_cnt;
	unsigned short vmid[MAX_S2_CTXS];
	unsigned long rtt_base[MAX_S2_CTXS];
	unsigned int num_planes;

	if (!get_realm_params(&p, realm_params_addr)) {
		return RMI_ERROR_INPUT;
	}

	/* coverity[uninit_use_in_call:SUPPRESS] */
	if (!validate_realm_params(&p)) {
		return RMI_ERROR_INPUT;
	}

	/* Only primary plane supported */
	num_planes = 1U;

	/* Make a local copy of all VMIDs, then reserve them all */
	/* @TODO. Only primary plane supported at the time */
	vmids_cnt = num_planes;
	vmid[0U] = p.vmid;

	for (int i = 0; i < vmids_cnt; i++) {
		if (!vmid_reserve(vmid[i])) {
			return RMI_ERROR_INPUT;
		}
	}

	/*
	 * At this point VMID is reserved for the Realm
	 *
	 * Check for aliasing between rd_addr and
	 * starting level RTT address(es)
	 */
	if (addr_is_contained(p.rtt_base,
			      p.rtt_base + (p.rtt_num_start * GRANULE_SIZE),
			      rd_addr)) {

		/* Free reserved VMID before returning */
		free_vmids(vmid, vmids_cnt);
		return RMI_ERROR_INPUT;
	}

	/* Make a local copy of all the root level RTTs */
	/* @TODO only primary plane supported at the moment */
	rtt_base[0U] = p.rtt_base;

	/*
	 * Transition the root RTT granules. They are unlocked after the
	 * transition, therefore we will not violate the locking order when
	 * we acquire the lock for the RD granule further down.
	 * This will fail if there is any aliasing among these granules
	 * because the granule will not be in the expected delegated state.
	 */
	if (!transition_sl_rtts(rtt_base, p.rtt_num_start, num_planes)) {
		free_vmids(vmid, vmids_cnt);
		return RMI_ERROR_INPUT;
	}

	/*
	 * Transition the RD granule. This will fail if there is any aliasing
	 * between this granule and RTT root granules, because the granule will
	 * not be in the expected delegated state.
	 */
	g_rd = find_lock_granule(rd_addr, GRANULE_STATE_DELEGATED);
	if (!g_rd) {
		revert_sl_rtts(rtt_base, p.rtt_num_start, num_planes);
		free_vmids(vmid, vmids_cnt);
		return RMI_ERROR_INPUT;
	}

	rd = buffer_granule_map(g_rd, SLOT_RD);
	assert(rd != NULL);

	set_rd_state(rd, REALM_NEW);
	set_rd_rec_count(rd, 0UL);

	/* Only primary plane is supported */
	rd->num_aux_planes = 0U;

	/*
	 * There is no permission indirection support and, in addition to
	 * that, there is no support for planes on the FEAT_REGISTER either.
	 */
	rd->rtt_tree_pp = true;

	for (unsigned int i = 0U; i < realm_num_planes(rd); i++) {
		struct s2tt_context *s2tt_ctx = plane_to_s2_context(rd, i);

		/*
		 * @TODO: Only primary plane supported at the time, so all
		 * the S2 contexts point to the same g_rtt.
		 */
		s2tt_ctx->g_rtt = find_granule(p.rtt_base);
		s2tt_ctx->ipa_bits = p.s2sz;
		s2tt_ctx->s2_starting_level = (int)p.rtt_level_start;
		s2tt_ctx->num_root_rtts = p.rtt_num_start;
		s2tt_ctx->enable_lpa2 = is_lpa2_requested(&p);
		s2tt_ctx->vmid = vmid[i];
	}

	(void)memcpy(&rd->rpv[0], &p.rpv[0], RPV_SIZE);

	rd->num_rec_aux = MAX_REC_AUX_GRANULES;

	rd->simd_cfg.sve_en = EXTRACT(RMI_REALM_FLAGS_SVE, p.flags) != 0UL;
	if (rd->simd_cfg.sve_en) {
		rd->simd_cfg.sve_vq = (uint32_t)p.sve_vl;
	}

	if (p.algorithm == RMI_HASH_SHA_256) {
		rd->algorithm = HASH_SHA_256;
	} else {
		rd->algorithm = HASH_SHA_512;
	}

	rd->pmu_enabled = EXTRACT(RMI_REALM_FLAGS_PMU, p.flags) != 0UL;
	rd->pmu_num_ctrs = p.pmu_num_ctrs;

	for (unsigned int i = 0U; i < realm_num_s2_rtts(rd); i++) {
		init_s2_starting_level(rd, i);
	}

	measurement_realm_params_measure(rd->measurement[RIM_MEASUREMENT_SLOT],
					 rd->algorithm,
					 &p);
	buffer_unmap(rd);

	granule_unlock_transition(g_rd, GRANULE_STATE_RD);

	return RMI_SUCCESS;
}

static unsigned long total_root_rtt_refcount(struct granule *g_rtt,
					     unsigned int num_rtts)
{
	unsigned long refcount = 0UL;

	for (unsigned int i = 0U; i < num_rtts; i++) {
		struct granule *g = (struct granule *)((uintptr_t)g_rtt +
					(i * sizeof(struct granule)));
	       /*
		* Lock starting from the RTT root.
		* Enforcing locking order RD->RTT is enough to ensure
		* deadlock free locking guarentee.
		*/
		granule_lock(g, GRANULE_STATE_RTT);
		refcount += g->refcount;
		granule_unlock(g);
	}

	return refcount;
}

unsigned long smc_realm_destroy(unsigned long rd_addr)
{
	struct granule *g_rd;
	struct granule *g_rtt;
	struct rd *rd;
	unsigned int num_rtts;
	int res;

	/* RD should not be destroyed if refcount != 0. */
	res = find_lock_unused_granule(rd_addr, GRANULE_STATE_RD, &g_rd);
	if (res != 0) {
		switch (res) {
		case -EINVAL:
			return RMI_ERROR_INPUT;
		default:
			assert(res == -EBUSY);
			return RMI_ERROR_REALM;
		}
	}

	rd = buffer_granule_map(g_rd, SLOT_RD);
	assert(rd != NULL);

	num_rtts = primary_s2_context(rd)->num_root_rtts;

	/* Check that root tables from all RTT trees don't hold any references */
	for (unsigned int i = 0U; i < realm_num_s2_rtts(rd); i++) {
		struct s2tt_context *s2tt_ctx = index_to_s2_context(rd, i);

		g_rtt = s2tt_ctx->g_rtt;

		if (total_root_rtt_refcount(g_rtt, num_rtts) != 0UL) {
			buffer_unmap(rd);
			granule_unlock(g_rd);
			return RMI_ERROR_REALM;
		}
	}

	/* Free root tables in al RTT trees */
	for (unsigned int i = 0U; i < realm_num_s2_rtts(rd); i++) {
		struct s2tt_context *s2tt_ctx = index_to_s2_context(rd, i);

		g_rtt = s2tt_ctx->g_rtt;
		free_sl_rtts(g_rtt, num_rtts);
	}

	/*
	 * All the mappings in the Realm have been removed and the TLB caches
	 * are invalidated. Therefore, there are no TLB entries tagged with
	 * this Realm's VMID (in this security state).
	 * Just release the VMIDs value so they can be used in another Realm.
	 */
	for (unsigned int i = 0U; i < realm_num_planes(rd); i++) {
		vmid_free(index_to_s2_context(rd, i)->vmid);
	}

	buffer_unmap(rd);

	/* This implicitly destroys the measurement */
	buffer_granule_memzero(g_rd, SLOT_RD);
	granule_unlock_transition(g_rd, GRANULE_STATE_DELEGATED);

	return RMI_SUCCESS;
}
