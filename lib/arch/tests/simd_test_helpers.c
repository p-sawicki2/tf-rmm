/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <host_utils.h>
#include <simd_test_helpers.h>
#include <test_helpers.h>

static void simd_test_helpers_setup_sysregs(void)
{
	int ret;

	(void)host_util_set_default_sysreg_cb("fpcr", 0UL);
	ret = host_util_set_default_sysreg_cb("fpsr", 0UL);

	assert(ret == 0);
}

void simd_test_helpers_init(void)
{
	test_helpers_init();
	test_helpers_rmm_start(true);
	simd_test_helpers_setup_sysregs();
	host_util_set_cpuid(0U);
	test_helpers_expect_assert_fail(false);
}

void simd_test_helpers_teardown(void)
{
	host_util_zero_sysregs_and_cbs();
}

void simd_test_helpers_set_state_saved(bool state)
{
	if (simd_is_state_saved() != state) {
		struct simd_context simd_ctx = { .sflags = 0 };

		simd_ctx.sflags |= SIMD_SFLAG_INIT_DONE;
		simd_ctx.tflags &= ~SIMD_TFLAG_SVE;
		simd_ctx.tflags &= ~SIMD_TFLAG_SME;
		simd_ctx.owner = SIMD_OWNER_REL1;

		if (state) {
			simd_ctx.sflags &= ~SIMD_SFLAG_SAVED;
			simd_context_switch(&simd_ctx, NULL);
		} else {
			simd_ctx.sflags |= SIMD_SFLAG_SAVED;
			simd_context_switch(NULL, &simd_ctx);
		}

		assert(simd_is_state_saved() == state);
	}
}
