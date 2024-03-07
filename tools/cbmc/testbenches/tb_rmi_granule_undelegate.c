/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 *
 * This file was AUTOGENERATED from the RMM specification.
 * RMM specification source version: 790fd539
 */

#include "tb.h"
#include "tb_rmi_granule_undelegate.h"

bool tb_rmi_granule_undelegate(
	uint64_t addr)
{
	/*
	 * Initialize registers
	 */

	struct tb_regs __tb_regs = __tb_arb_regs();

	__tb_regs.X0 = SMC_RMM_GRANULE_UNDELEGATE;
	__tb_regs.X1 = (uint64_t)addr;

	/*
	 * Initialize global state
	 */

	__init_global_state(__tb_regs.X0);

	/*
	 * Pre-conditions
	 */

	bool failure_gran_align_pre = !AddrIsGranuleAligned(addr);
	bool failure_gran_bound_pre = !PaIsDelegable(addr);
	bool failure_gran_state_pre = Granule(addr).state != DELEGATED;
	bool no_failures_pre = !failure_gran_align_pre
		&& !failure_gran_bound_pre
		&& !failure_gran_state_pre;

	/*
	 * Execute command and read the result.
	 */

	tb_handle_smc(&__tb_regs);
	uint64_t result = __tb_regs.X0;

	/*
	 * Post-conditions
	 */

	bool failure_gran_align_post = ResultEqual_2(result, RMI_ERROR_INPUT);
	bool failure_gran_bound_post = ResultEqual_2(result, RMI_ERROR_INPUT);
	bool failure_gran_state_post = ResultEqual_2(result, RMI_ERROR_INPUT);
	bool success_gran_gpt_post = Granule(addr).gpt == GPT_NS;
	bool success_gran_state_post = Granule(addr).state == UNDELEGATED;
	bool success_gran_content_post = true;

	/*
	 * Failure condition assertions
	 */

	bool prop_failure_gran_align_ante = failure_gran_align_pre;

	__COVER(prop_failure_gran_align_ante);
	if (prop_failure_gran_align_ante) {
		bool prop_failure_gran_align_cons = failure_gran_align_post;

		__COVER(prop_failure_gran_align_cons);
		__ASSERT(prop_failure_gran_align_cons, "prop_failure_gran_align_cons");
	}

	bool prop_failure_gran_bound_ante = !failure_gran_align_pre
		&& failure_gran_bound_pre;

	__COVER(prop_failure_gran_bound_ante);
	if (prop_failure_gran_bound_ante) {
		bool prop_failure_gran_bound_cons = failure_gran_bound_post;

		__COVER(prop_failure_gran_bound_cons);
		__ASSERT(prop_failure_gran_bound_cons, "prop_failure_gran_bound_cons");
	}

	bool prop_failure_gran_state_ante = !failure_gran_align_pre
		&& !failure_gran_bound_pre
		&& failure_gran_state_pre;

	__COVER(prop_failure_gran_state_ante);
	if (prop_failure_gran_state_ante) {
		bool prop_failure_gran_state_cons = failure_gran_state_post;

		__COVER(prop_failure_gran_state_cons);
		__ASSERT(prop_failure_gran_state_cons, "prop_failure_gran_state_cons");
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

	bool prop_success_gran_gpt_ante = no_failures_pre;

	__COVER(prop_success_gran_gpt_ante);
	if (prop_success_gran_gpt_ante) {
		bool prop_success_gran_gpt_cons = success_gran_gpt_post
		&& (result == RMI_SUCCESS);

		__COVER(prop_success_gran_gpt_cons);
		__ASSERT(prop_success_gran_gpt_cons, "prop_success_gran_gpt_cons");
	}

	bool prop_success_gran_state_ante = no_failures_pre;

	__COVER(prop_success_gran_state_ante);
	if (prop_success_gran_state_ante) {
		bool prop_success_gran_state_cons = success_gran_state_post
		&& (result == RMI_SUCCESS);

		__COVER(prop_success_gran_state_cons);
		__ASSERT(prop_success_gran_state_cons, "prop_success_gran_state_cons");
	}

	bool prop_success_gran_content_ante = no_failures_pre;

	__COVER(prop_success_gran_content_ante);
	if (prop_success_gran_content_ante) {
		bool prop_success_gran_content_cons = success_gran_content_post
		&& (result == RMI_SUCCESS);

		__COVER(prop_success_gran_content_cons);
		__ASSERT(prop_success_gran_content_cons, "prop_success_gran_content_cons");
	}

	/*
	 * Assertion used to check consistency of the testbench
	 */
	__tb_expect_fail();

	return no_failures_pre;
}