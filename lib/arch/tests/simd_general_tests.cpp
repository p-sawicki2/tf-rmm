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
	#include <simd_test_helpers.h>
	#include <stdlib.h>
	#include <string.h>
	#include <test_helpers.h>
	#include <utils_def.h>
}

TEST_GROUP(simd_general) {
	TEST_SETUP()
	{
		simd_test_helpers_init();
	}

	TEST_TEARDOWN()
	{
	}
};

TEST(simd_general, simd_get_cpu_config_TC1)
{
	int ret;
	struct simd_config discovered_cfg;

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Call simd_get_cpu_config() with a non-NULL simd_cfg to get the
	 * SIMD config that was discovered during init. Expect the function
	 * to complete successfully with return code 0.
	 ******************************************************************/

	ret = simd_get_cpu_config(&discovered_cfg);

	CHECK_TRUE(ret == 0);
}

ASSERT_TEST(simd_general, simd_get_cpu_config_TC2)
{
	/******************************************************************
	 * TEST CASE 2:
	 *
	 * Call simd_get_cpu_config() with NULL. Expect assertion to fail.
	 ******************************************************************/

	test_helpers_expect_assert_fail(true);

	(void)simd_get_cpu_config(NULL);

	test_helpers_fail_if_no_assert_failed();
}
