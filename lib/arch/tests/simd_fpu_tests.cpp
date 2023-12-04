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

TEST_GROUP(simd_fpu) {
	TEST_SETUP()
	{
		simd_test_helpers_init();
	}

	TEST_TEARDOWN()
	{
	}
};

TEST(simd_fpu, simd_context_init_TC1)
{
	int ret;
	uint64_t expected_cptr_el2;
	simd_owner_t expected_owner;
	struct simd_config test_simd_cfg = { 0 };
	struct simd_context test_simd_ctx = { .sflags = 0 };

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Call simd_context_init() with a valid owner and configuration.
	 * Expect the function to complete successfully with return code 0.
	 * Check that the SIMD context was initialised correctly, based on
	 * the provided config.
	 ******************************************************************/

	test_simd_ctx.sflags &= ~SIMD_SFLAG_INIT_DONE;

	expected_owner = (simd_owner_t)((rand() % 2) + 1);

	ret = simd_context_init(expected_owner, &test_simd_ctx, &test_simd_cfg);

	CHECK_TRUE(ret == 0);

	if (expected_owner == SIMD_OWNER_REL1) {
		CHECK_TRUE(test_simd_ctx.sflags & SIMD_SFLAG_SAVED);
	} else {
		CHECK_TRUE(test_simd_ctx.sflags & ~SIMD_SFLAG_SAVED);
	}

	CHECK_TRUE(test_simd_ctx.owner == expected_owner);

	/*
	 * Set up expected cptr_el2 value
	 */
	expected_cptr_el2 = CPTR_EL2_VHE_INIT;
	SIMD_ENABLE_CPTR_FLAGS(&test_simd_cfg, expected_cptr_el2);

	CHECK_TRUE(test_simd_ctx.cptr_el2 == expected_cptr_el2);

	/*
	 * Check that the INIT_DONE bit has been set in the SIMD context sflags.
	 */
	CHECK_TRUE(test_simd_ctx.sflags & SIMD_SFLAG_INIT_DONE);
}

TEST(simd_fpu, simd_context_init_TC2)
{
	int ret;
	struct simd_config test_simd_cfg = { 0 };
	struct simd_context test_simd_ctx = { .sflags = 0 };

	/******************************************************************
	 * TEST CASE 2:
	 *
	 * Call simd_context_init() with a context which has the INIT_DONE
	 * bit set. Expect the function to exit early with return code -1.
	 ******************************************************************/

	test_simd_ctx.sflags |= SIMD_SFLAG_INIT_DONE;

	ret = simd_context_init(SIMD_OWNER_NWD, &test_simd_ctx, &test_simd_cfg);

	CHECK_TRUE(ret == -1);
}

TEST(simd_fpu, simd_context_init_TC3)
{
	int ret;
	struct simd_config test_simd_cfg = { 0 };
	struct simd_context test_simd_ctx = { .sflags = 0 };

	/******************************************************************
	 * TEST CASE 3:
	 *
	 * Call simd_context_init() with an invalid owner. Expect the
	 * function to exit early with return code -1.
	 ******************************************************************/

	test_simd_ctx.sflags &= ~SIMD_SFLAG_INIT_DONE;

	int invalid_owner = rand() % (INT_MAX - 2) + 3;

	ret = simd_context_init((simd_owner_t)invalid_owner, &test_simd_ctx,
				&test_simd_cfg);

	CHECK_TRUE(ret == -1);
}
