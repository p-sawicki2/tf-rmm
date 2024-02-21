/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <host_utils.h>
#include <simd_callbacks.h>
#include <simd_test_helpers.h>
#include <simd_test_private.h>
#include <test_helpers.h>

static void simd_test_helpers_setup_sysregs(void)
{
	int ret;

	(void)host_util_set_default_sysreg_cb("cptr_el2", 0UL);
	(void)host_util_set_default_sysreg_cb("id_aa64pfr0_el1", 0UL);
	(void)host_util_set_default_sysreg_cb("id_aa64pfr1_el1", 0UL);
	ret = host_util_set_default_sysreg_cb("zcr_el2", 0UL);

	assert(ret == 0);
}

void simd_test_helpers_init(void)
{
	test_helpers_init();
	test_helpers_rmm_start(true);
	reset_g_simd_cfg();
	simd_test_helpers_setup_sysregs();
	host_util_set_cpuid(0U);
	test_helpers_expect_assert_fail(false);
}

void simd_test_helpers_teardown(void)
{
	host_util_zero_sysregs_and_cbs();

	for (unsigned int id = 0U; id < SIMD_CB_IDS; id++) {
		simd_test_unregister_callback(id);
	}
}

void simd_test_helpers_set_state_saved(bool state)
{
	if (simd_is_state_saved() != state) {
		struct simd_context simd_ctx = { .sflags = 0 };
		struct simd_config simd_cfg = { 0 };
		int ret;

		if (state) {
			ret = simd_context_init(SIMD_OWNER_NWD, &simd_ctx, &simd_cfg);
			assert(ret == 0);
			(void)simd_context_switch(&simd_ctx, NULL);
		} else {
			ret = simd_context_init(SIMD_OWNER_REL1, &simd_ctx, &simd_cfg);
			assert(ret == 0);
			(void)simd_context_switch(NULL, &simd_ctx);
		}

		assert(simd_is_state_saved() == state);
	}
}
