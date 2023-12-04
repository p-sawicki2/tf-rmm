/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <CppUTest/CommandLineTestRunner.h>
#include <CppUTest/TestHarness.h>

extern "C"
{
	#include <arch_helpers.h>
	#include <host_utils.h>
	#include <simd.h>	  /* API to test */
	#include <simd_private.h> /* API to test */
	#include <simd_test_helpers.h>
	#include <stdlib.h>
	#include <string.h>
	#include <test_helpers.h>
	#include <utils_def.h>
}

TEST_GROUP(fpu) {
	TEST_SETUP()
	{
		test_helpers_init();
		test_helpers_rmm_start(true);
		host_util_set_cpuid(0U);
		test_helpers_expect_assert_fail(false);
	}

	TEST_TEARDOWN()
	{
		host_util_zero_simd_vregs();
	}
};

TEST(fpu, fpu_save_registers_TC1)
{
	simd_vreg expected_vecs[NUM_VREGS];
	struct fpu_regs test_vecs;

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Update the current SIMD vreg values, then save them with
	 * fpu_save_registers().
	 ******************************************************************/

	for (unsigned int i = 0U; i < NUM_VREGS; i++) {
		simd_vreg rand_vec = simd_test_helpers_get_rand_vector();

		expected_vecs[i] = rand_vec;
		host_write_simd_vreg(FPU, i, rand_vec);
	}

	fpu_save_registers(&test_vecs);

	for (unsigned int i = 0U; i < NUM_VREGS; i++) {
		simd_vreg expected_vec = expected_vecs[i];

		for (unsigned int j = 0U; j < FPU_VEC_REG_SIZE; j++) {
			uint8_t test_val =
					test_vecs.q[i * FPU_VEC_REG_SIZE + j];

			BYTES_EQUAL(expected_vec.q[j], test_val);
		}
	}
}

TEST(fpu, fpu_restore_registers_TC1)
{
	struct fpu_regs expected_vecs = { 0 };

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Generate a set of random vreg values, then use
	 * fpu_restore_registers() to update the current vreg values.
	 ******************************************************************/

	for (size_t i = 0; i < NUM_VREGS; i++) {
		simd_vreg random_vec = simd_test_helpers_get_rand_vector();

		(void)memcpy(&expected_vecs.q[i * FPU_VEC_REG_SIZE],
			     &random_vec.q,
			     FPU_VEC_REG_SIZE);
	}

	fpu_restore_registers(&expected_vecs);

	for (size_t i = 0; i < NUM_VREGS; i++) {
		simd_vreg test_vec = host_read_simd_vreg(FPU, i);

		for (size_t j = 0; j < FPU_VEC_REG_SIZE; j++) {
			uint8_t test_val = test_vec.q[j];
			uint8_t expected_val =
				     expected_vecs.q[i * FPU_VEC_REG_SIZE + j];

			BYTES_EQUAL(expected_val, test_val);
		}
	}
}

TEST(fpu, simd_context_init_TC1)
{
	int ret;
	uint64_t expected_cptr_el2;
	simd_owner_t expected_owner;
	struct simd_config test_simd_cfg = { 0 };
	struct simd_context test_simd_ctx = { .sflags = 0 };

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Call simd_context_init() with a valid owner and configuration. Expect
	 * the function to complete successfully with return 0. Check that the
	 * SIMD context was initialised correctly, based on the provided config.
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

TEST(fpu, simd_context_init_TC2)
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

TEST(fpu, simd_context_init_TC3)
{
	int ret;
	struct simd_config test_simd_cfg = { 0 };
	struct simd_context test_simd_ctx = { .sflags = 0 };

	/******************************************************************
	 * TEST CASE 3:
	 *
	 * Call simd_context_init() with an invalid owner. Expect the function
	 * to exit early with return code -1.
	 ******************************************************************/

	test_simd_ctx.sflags &= ~SIMD_SFLAG_INIT_DONE;

	ret = simd_context_init((simd_owner_t)3, &test_simd_ctx, &test_simd_cfg);

	CHECK_TRUE(ret == -1);
}
