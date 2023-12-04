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
