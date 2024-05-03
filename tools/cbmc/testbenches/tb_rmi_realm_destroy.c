/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 *
 * This file was AUTOGENERATED from the RMM specification.
 * RMM specification source version: 790fd539
 */

#include "tb.h"
#include "tb_rmi_realm_destroy.h"

bool tb_rmi_realm_destroy(
	uint64_t rd)
{
	/*
	 * Initialize registers
	 */

	struct tb_regs __tb_regs = __tb_arb_regs();

	__tb_regs.X0 = SMC_RMI_REALM_DESTROY;
	__tb_regs.X1 = (uint64_t)rd;

	/*
	 * Initialize global state
	 */

	__init_global_state(__tb_regs.X0);

	/*
	 * Declare context variables
	 */

	struct rmm_realm realm;

	/*
	 * Assign context variables before command execution
	 */

	realm = Realm(rd);

	/*
	 * Pre-conditions
	 */

	bool failure_rd_align_pre = !AddrIsGranuleAligned(rd);
	bool failure_rd_bound_pre = !PaIsDelegable(rd);
	bool failure_rd_state_pre = Granule(rd).state != RD;
	bool failure_realm_live_pre = RealmIsLive(rd);
	bool no_failures_pre = !failure_rd_align_pre
		&& !failure_rd_bound_pre
		&& !failure_rd_state_pre
		&& !failure_realm_live_pre;

	/*
	 * Execute command and read the result.
	 */

	tb_handle_smc(&__tb_regs);
	uint64_t result = __tb_regs.X0;

	/*
	 * Post-conditions
	 */

	bool failure_rd_align_post = ResultEqual_2(result, RMI_ERROR_INPUT);
	bool failure_rd_bound_post = ResultEqual_2(result, RMI_ERROR_INPUT);
	bool failure_rd_state_post = ResultEqual_2(result, RMI_ERROR_INPUT);
	bool failure_realm_live_post = ResultEqual_2(result, RMI_ERROR_REALM);
	bool success_rtt_state_post = RttsStateEqual(realm.rtt_base, realm.rtt_num_start, DELEGATED);
	bool success_rd_state_post = Granule(rd).state == DELEGATED;
	bool success_vmid_post = VmidIsFree(realm.vmid);

	/*
	 * Failure condition assertions
	 */

	bool prop_failure_rd_align_ante = failure_rd_align_pre;

	__COVER(prop_failure_rd_align_ante);
	if (prop_failure_rd_align_ante) {
		bool prop_failure_rd_align_cons = failure_rd_align_post;

		__COVER(prop_failure_rd_align_cons);
		__ASSERT(prop_failure_rd_align_cons, "prop_failure_rd_align_cons");
	}

	bool prop_failure_rd_bound_ante = !failure_rd_align_pre
		&& failure_rd_bound_pre;

	__COVER(prop_failure_rd_bound_ante);
	if (prop_failure_rd_bound_ante) {
		bool prop_failure_rd_bound_cons = failure_rd_bound_post;

		__COVER(prop_failure_rd_bound_cons);
		__ASSERT(prop_failure_rd_bound_cons, "prop_failure_rd_bound_cons");
	}

	bool prop_failure_rd_state_ante = !failure_rd_align_pre
		&& !failure_rd_bound_pre
		&& failure_rd_state_pre;

	__COVER(prop_failure_rd_state_ante);
	if (prop_failure_rd_state_ante) {
		bool prop_failure_rd_state_cons = failure_rd_state_post;

		__COVER(prop_failure_rd_state_cons);
		__ASSERT(prop_failure_rd_state_cons, "prop_failure_rd_state_cons");
	}

	bool prop_failure_realm_live_ante = !failure_rd_align_pre
		&& !failure_rd_bound_pre
		&& !failure_rd_state_pre
		&& failure_realm_live_pre;

	__COVER(prop_failure_realm_live_ante);
	if (prop_failure_realm_live_ante) {
		bool prop_failure_realm_live_cons = failure_realm_live_post;

		__COVER(prop_failure_realm_live_cons);
		__ASSERT(prop_failure_realm_live_cons, "prop_failure_realm_live_cons");
	}

	/*
	 * Result assertion
	 */

	bool prop_result_ante = no_failures_pre;

	__COVER(prop_result_ante);
	if (prop_result_ante) {
		bool prop_result_cons = result == RMI_SUCCESS;

		__COVER(prop_result_cons);
		__ASSERT(prop_result_cons, "prop_result_cons");
	}

	/*
	 * Success condition assertions
	 */

	bool prop_success_rtt_state_ante = no_failures_pre;

	__COVER(prop_success_rtt_state_ante);
	if (prop_success_rtt_state_ante) {
		bool prop_success_rtt_state_cons = success_rtt_state_post
		&& (result == RMI_SUCCESS);

		__COVER(prop_success_rtt_state_cons);
		__ASSERT(prop_success_rtt_state_cons, "prop_success_rtt_state_cons");
	}

	bool prop_success_rd_state_ante = no_failures_pre;

	__COVER(prop_success_rd_state_ante);
	if (prop_success_rd_state_ante) {
		bool prop_success_rd_state_cons = success_rd_state_post
		&& (result == RMI_SUCCESS);

		__COVER(prop_success_rd_state_cons);
		__ASSERT(prop_success_rd_state_cons, "prop_success_rd_state_cons");
	}

	bool prop_success_vmid_ante = no_failures_pre;

	__COVER(prop_success_vmid_ante);
	if (prop_success_vmid_ante) {
		bool prop_success_vmid_cons = success_vmid_post
		&& (result == RMI_SUCCESS);

		__COVER(prop_success_vmid_cons);
		__ASSERT(prop_success_vmid_cons, "prop_success_vmid_cons");
	}

	/*
	 * Assertion used to check consistency of the testbench
	 */
	__tb_expect_fail();

	return no_failures_pre;
}
