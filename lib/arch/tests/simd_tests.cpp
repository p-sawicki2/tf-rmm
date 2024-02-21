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
	#include <simd_callbacks.h>
	#include <simd_private.h>
	#include <simd_test_helpers.h>
	#include <simd_test_private.h>
	#include <stdlib.h>
	#include <string.h>
	#include <test_helpers.h>
	#include <utils_def.h>
}

static unsigned int helpers_times_called[SIMD_CB_IDS];

static void increment_times_called(enum simd_cb_ids id)
{
	helpers_times_called[id]++;
}

void fpu_save_regs_cb(struct fpu_regs *regs)
{
	increment_times_called(FPU_SAVE_REGS);
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

TEST(simd, simd_init_TC1)
{
	u_register_t id_aa64pfr0_el1;
	u_register_t id_aa64pfr1_el1;
	int ret;
	struct simd_config simd_cfg = { 0 };

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Call simd_init() when SVE and SME are disabled. Expect that the
	 * discovered CPU SIMD configuration will have SVE and SME
	 * disabled.
	 ******************************************************************/

	/*
	 * Set g_simd_init_done to false. This allows us to call the simd_init
	 * function without early exiting, so we can test the initialisation for
	 * different configurations.
	 */
	set_g_simd_init_done(false);

	id_aa64pfr0_el1 = read_id_aa64pfr0_el1();
	id_aa64pfr0_el1 |= INPLACE(ID_AA64PFR0_EL1_SVE, 0UL);
	write_id_aa64pfr0_el1(id_aa64pfr0_el1);

	id_aa64pfr1_el1 = read_id_aa64pfr1_el1();
	id_aa64pfr1_el1 |= INPLACE(ID_AA64PFR1_EL1_SME, 0UL);
	write_id_aa64pfr1_el1(id_aa64pfr1_el1);

	simd_init();

	ret = simd_get_cpu_config(&simd_cfg);

	CHECK_TRUE(ret == 0);

	CHECK_TRUE(!simd_cfg.sve_en);
	CHECK_TRUE(simd_cfg.sve_vq == 0);
	CHECK_TRUE(!simd_cfg.sme_en);
}

TEST(simd, simd_init_TC2)
{
	u_register_t saved_cptr;
	u_register_t id_aa64pfr0_el1;
	u_register_t id_aa64pfr1_el1;
	int ret;
	struct simd_config simd_cfg = { 0 };

	/******************************************************************
	 * TEST CASE 2:
	 *
	 * Call simd_init() when SVE is enabled. Expect that the discovered
	 * CPU SIMD configuration will have SVE enabled, and the LEN field
	 * of ZCR_EL2 will have the correct value.
	 ******************************************************************/

	set_g_simd_init_done(false);

	saved_cptr = read_cptr_el2();

	id_aa64pfr0_el1 = read_id_aa64pfr0_el1();
	id_aa64pfr0_el1 |= INPLACE(ID_AA64PFR0_EL1_SVE, 1UL);
	write_id_aa64pfr0_el1(id_aa64pfr0_el1);

	id_aa64pfr1_el1 = read_id_aa64pfr1_el1();
	id_aa64pfr1_el1 |= INPLACE(ID_AA64PFR1_EL1_SME, 0UL);
	write_id_aa64pfr1_el1(id_aa64pfr1_el1);

	simd_init();

	ret = simd_get_cpu_config(&simd_cfg);

	CHECK_TRUE(ret == 0);

	CHECK_TRUE(simd_cfg.sve_en);
	CHECK_TRUE(!simd_cfg.sme_en);
	BYTES_EQUAL(SVE_VQ_ARCH_MAX, EXTRACT(ZCR_EL2_LEN, read_zcr_el2()));

	/* Verify that CPTR_EL2 was restored correctly after init */
	BYTES_EQUAL(saved_cptr, read_cptr_el2());
}

/*
 * Custom read callback for SMCR_EL2. Since we are interested in unit testing
 * simd.c rather than exactly emulating the hardware behaviour, we simply return
 * the max architecturally supported SVQ, regardless of the value that was
 * written.
 *
 * This custom callback is required to pass the assert() in sme_init_once().
 */
static u_register_t smcr_el2_rd_cb(u_register_t *reg)
{
	u_register_t smcr_el2_ret = *reg & ~MASK(SMCR_EL2_RAZ_LEN);

	smcr_el2_ret |= INPLACE(SMCR_EL2_RAZ_LEN, SVE_VQ_ARCH_MAX);

	return smcr_el2_ret;
}

/*
 * Write callback for SMCR_EL2. This simply writes a value to the register.
 */
static void smcr_el2_wr_cb(u_register_t val, u_register_t *reg)
{
	*reg = val;
}

TEST(simd, simd_init_TC3)
{
	u_register_t saved_cptr;
	uint64_t id_aa64pfr1_el1;
	int ret1;
	int ret2;
	struct simd_config simd_cfg = { 0 };

	/******************************************************************
	 * TEST CASE 3:
	 *
	 * Call simd_init() when SME is enabled. Expect that the discovered
	 * CPU SIMD configuration will have SME enabled.
	 ******************************************************************/

	set_g_simd_init_done(false);

	saved_cptr = read_cptr_el2();

	id_aa64pfr1_el1 = read_id_aa64pfr1_el1();
	id_aa64pfr1_el1 |= INPLACE(ID_AA64PFR1_EL1_SME, 1UL);
	write_id_aa64pfr1_el1(id_aa64pfr1_el1);

	/*
	 * Install custom read callback for smcr_el2 to pass the assert() in
	 * sme_init_once().
	 */
	ret1 = host_util_set_sysreg_cb("smcr_el2", &smcr_el2_rd_cb,
				&smcr_el2_wr_cb, 0UL);

	assert(ret1 == 0);

	simd_init();

	ret2 = simd_get_cpu_config(&simd_cfg);

	CHECK_TRUE(ret2 == 0);

	CHECK_TRUE(simd_cfg.sme_en);
	BYTES_EQUAL(saved_cptr, read_cptr_el2());
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
	union simd_cbs cb;
	int times_called_prev;

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Initialise a test SIMD FPU context that belongs to NS world.
	 * Call simd_context_switch() with this test context as the
	 * ctx_save. Expect the save to complete successfully. In addition,
	 * the SIMD helper function fpu_save_registers() should be called
	 * exactly once.
	 ******************************************************************/

	/*
	 * Need to ensure g_simd_state_saved[my_cpuid()] is set to false prior
	 * to calling simd_context_switch(). This allows us to verify that the
	 * save completes correctly when this is the case.
	 */
	simd_test_helpers_set_state_saved(false);

	cptr_el2 = read_cptr_el2();
	times_called_prev = helpers_times_called[FPU_SAVE_REGS];

	ret = simd_context_init(SIMD_OWNER_NWD, &test_simd_ctx, &test_simd_cfg);

	CHECK_TRUE(ret == 0);

	cb.fpu_save_restore_regs = fpu_save_regs_cb;
	simd_test_register_callback(FPU_SAVE_REGS, cb);

	(void)simd_context_switch(&test_simd_ctx, NULL);

	CHECK_TRUE(helpers_times_called[FPU_SAVE_REGS] - times_called_prev == 1);
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
