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
	struct simd_config expected_cfg = { 0 };

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Call simd_get_cpu_config() with a non-NULL simd_cfg to get the
	 * SIMD config that was discovered during init. Check that the
	 * config fields are correct for FPU.
	 ******************************************************************/

	ret = simd_get_cpu_config(&discovered_cfg);

	CHECK_TRUE(ret == 0);

	/*
	 * For FPU, expected SIMD config to be zero for all fields.
	 */
	CHECK_TRUE(expected_cfg.sve_en == discovered_cfg.sve_en);
	CHECK_TRUE(expected_cfg.sve_vq == discovered_cfg.sve_vq);
	CHECK_TRUE(expected_cfg.sme_en == discovered_cfg.sme_en);
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
