/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <CppUTest/CommandLineTestRunner.h>
#include <CppUTest/TestHarness.h>

extern "C"
{
	#include <arch_helpers.h>
	#include <simd.h>	  /* API to test */
	#include <simd_private.h>
	#include <simd_test_helpers.h>
	#include <stdlib.h>
	#include <string.h>
	#include <test_helpers.h>
	#include <utils_def.h>
}

TEST_GROUP(simd) {
	TEST_SETUP()
	{
		simd_test_helpers_init();
	}

	TEST_TEARDOWN()
	{
		simd_test_helpers_teardown();
	}
};

ASSERT_TEST(simd, simd_get_cpu_config_TC1)
{
	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Call simd_get_cpu_config() with NULL. Expect assertion to fail.
	 ******************************************************************/

	test_helpers_expect_assert_fail(true);

	(void)simd_get_cpu_config(NULL);

	test_helpers_fail_if_no_assert_failed();
}

TEST(simd, simd_context_init_TC1)
{
	int ret;
	struct simd_config test_simd_cfg = { 0 };
	struct simd_context test_simd_ctx = { .sflags = 0 };

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Call simd_context_init() twice with the same context. Expect the
	 * second call to exit early with return code -1.
	 ******************************************************************/

	ret = simd_context_init(SIMD_OWNER_NWD, &test_simd_ctx, &test_simd_cfg);

	CHECK_TRUE(ret == 0);

	ret = simd_context_init(SIMD_OWNER_NWD, &test_simd_ctx, &test_simd_cfg);

	CHECK_TRUE(ret == -1);
}

TEST(simd, simd_context_init_TC2)
{
	int ret;
	struct simd_config test_simd_cfg = { 0 };
	struct simd_context test_simd_ctx = { .sflags = 0 };

	/******************************************************************
	 * TEST CASE 2:
	 *
	 * Call simd_context_init() with an invalid owner. Expect the
	 * function to exit early with return code -1.
	 ******************************************************************/

	test_simd_ctx.sflags &= ~SIMD_SFLAG_INIT_DONE;

	/* Generate a random integer greater than 2. */
	int invalid_owner = rand() % (INT_MAX - 2) + 3;

	ret = simd_context_init((simd_owner_t)invalid_owner, &test_simd_ctx,
				&test_simd_cfg);

	CHECK_TRUE(ret == -1);
}

TEST(simd, simd_context_switch_TC1)
{
	struct simd_context test_simd_ctx = { .sflags = 0 };
	struct simd_config test_simd_cfg = { 0 };
	u_register_t cptr_el2;
	int ret;

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Initialise a test SIMD FPU context that belongs to NS world.
	 * Call simd_context_switch() with this test context as the
	 * ctx_save. Expect the save to complete successfully.
	 ******************************************************************/

	/*
	 * Need to ensure g_simd_state_saved[my_cpuid()] is set to false prior
	 * to calling simd_context_switch(). This allows us to verify that the
	 * save completes correctly when this is the case.
	 */
	simd_test_helpers_set_state_saved(false);

	cptr_el2 = read_cptr_el2();

	ret = simd_context_init(SIMD_OWNER_NWD, &test_simd_ctx, &test_simd_cfg);

	CHECK_TRUE(ret == 0);

	(void)simd_context_switch(&test_simd_ctx, NULL);

	CHECK_TRUE(simd_is_state_saved());

	/* Check that CPTR_EL2 was restored correctly. */
	BYTES_EQUAL(cptr_el2, read_cptr_el2());
}

ASSERT_TEST(simd, simd_context_switch_TC2)
{
	struct simd_context test_simd_ctx = { .sflags = 0 };

	/******************************************************************
	 * TEST CASE 2:
	 *
	 * Call simd_context_switch with an uninitialised ctx_save. Expect
	 * an assertion to fail.
	 ******************************************************************/

	simd_test_helpers_set_state_saved(false);

	test_helpers_expect_assert_fail(true);
	(void)simd_context_switch(&test_simd_ctx, NULL);
	test_helpers_fail_if_no_assert_failed();
}

ASSERT_TEST(simd, simd_context_switch_TC3)
{
	struct simd_context test_simd_ctx = { .sflags = 0 };
	struct simd_config test_simd_cfg = { 0 };
	int ret;

	/******************************************************************
	 * TEST CASE 3:
	 *
	 * Initialise a test SIMD FPU context that belongs to Realm. Call
	 * simd_context_switch() with this test context as the ctx_save.
	 * Expect an assertion to fail.
	 ******************************************************************/

	simd_test_helpers_set_state_saved(false);

	ret = simd_context_init(SIMD_OWNER_REL1, &test_simd_ctx, &test_simd_cfg);

	CHECK_TRUE(ret == 0);

	test_helpers_expect_assert_fail(true);
	(void)simd_context_switch(&test_simd_ctx, NULL);
	test_helpers_fail_if_no_assert_failed();
}

ASSERT_TEST(simd, simd_context_switch_TC4)
{
	struct simd_context test_simd_ctx = { .sflags = 0 };
	struct simd_config test_simd_cfg = { 0 };
	int ret;

	/******************************************************************
	 * TEST CASE 4:
	 *
	 * Call simd_context_switch() twice on the same ctx_save. Expect an
	 * assertion to fail on the second call.
	 ******************************************************************/

	simd_test_helpers_set_state_saved(false);

	ret = simd_context_init(SIMD_OWNER_NWD, &test_simd_ctx, &test_simd_cfg);

	CHECK_TRUE(ret == 0);

	(void)simd_context_switch(&test_simd_ctx, NULL);

	CHECK_TRUE(simd_is_state_saved());

	test_helpers_expect_assert_fail(true);
	(void)simd_context_switch(&test_simd_ctx, NULL);
	test_helpers_fail_if_no_assert_failed();
}
