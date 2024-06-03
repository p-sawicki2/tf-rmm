/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <CppUTest/CommandLineTestRunner.h>
#include <CppUTest/TestHarness.h>

extern "C" {
#include <cpuid.h>
#include <granule_types.h>
#include <host_harness.h>
#include <host_utils.h>
#include <status.h>
#include <stdlib.h>
#include <string.h>
#include <s2tt_pvt_defs.h>
#include <s2tt_test_helpers.h>
#include <ripas.h>
#include <s2tt.h>	/* Interface to exercise */
#include <test_helpers.h>
#include <unistd.h>
#include <utils_def.h>
}

void s2tte_is_addr_lvl_aligned_tc1(void)
{
	/***************************************************************
	 * TEST CASE 1:
	 *
	 * For every valid level, generate an aligned valid PA and
	 * validate that add_is_level_aligned() returns the right
	 * result.
	 ***************************************************************/
	struct s2tt_context s2tt_ctx = { 0UL };

	/*
	 * Generate an s2tt context to be used for the test. Only
	 * enable_lpa2 field is needed for the current test.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();

	for (long level = s2tt_test_helpers_min_table_lvl();
	     level <= S2TT_TEST_HELPERS_MAX_LVL; level++) {
		unsigned long pa = s2tt_test_helpers_gen_pa(level, true);

		CHECK_TRUE(s2tte_is_addr_lvl_aligned(
					(const struct s2tt_context *)&s2tt_ctx,
					pa, level));
	}
}

void s2tte_is_addr_lvl_aligned_tc2(void)
{
	/***************************************************************
	 * TEST CASE 2:
	 *
	 * Negative tests: for every valid level, generate an unaligned
	 * PA and validate that add_is_level_aligned() returns the
	 * right result.
	 ***************************************************************/
	struct s2tt_context s2tt_ctx = { 0UL };

	/*
	 * Generate an s2tt context to be used for the test. Only
	 * enable_lpa2 field is needed for the current test.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();

	for (long level = s2tt_test_helpers_min_table_lvl();
	     level <= S2TT_TEST_HELPERS_MAX_LVL; level++) {
		unsigned long pa = s2tt_test_helpers_gen_pa(level, true);

		pa += test_helpers_get_rand_in_range(1UL, (unsigned long)GRANULE_SIZE - 1UL);

		CHECK_TRUE(s2tte_is_addr_lvl_aligned(
					(const struct s2tt_context *)&s2tt_ctx,
					pa, level) == false);
	}
}

void s2tte_is_addr_lvl_aligned_tc3(void)
{
	/***************************************************************
	 * TEST CASE 3:
	 *
	 * Given a valid PA, call s2tte_is_addr_lvl_aligned() with a level
	 * above the maximum permitted one.
	 ***************************************************************/

	long level = S2TT_TEST_HELPERS_MAX_LVL + 1L;
	unsigned long pa = 0UL; /* Aligned to any level */
	struct s2tt_context s2tt_ctx = { 0UL };

	/*
	 * Generate an s2tt context to be used for the test. Only
	 * enable_lpa2 field is needed for the current test.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();

	test_helpers_expect_assert_fail(true);
	(void)s2tte_is_addr_lvl_aligned((const struct s2tt_context *)&s2tt_ctx,
				    pa, level);
	test_helpers_fail_if_no_assert_failed();
}

void s2tte_is_addr_lvl_aligned_tc4(void)
{
	/***************************************************************
	 * TEST CASE 4:
	 *
	 * Given a valid PA, call s2tte_is_addr_lvl_aligned() with a level
	 * below the minimum permitted one.
	 ***************************************************************/

	long level = s2tt_test_helpers_min_table_lvl() - 1L;
	unsigned long pa = 0UL; /* Aligned to any level */
	struct s2tt_context s2tt_ctx = { 0UL };

	/*
	 * Generate an s2tt context to be used for the test. Only
	 * enable_lpa2 field is needed for the current test.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();

	test_helpers_expect_assert_fail(true);
	(void)s2tte_is_addr_lvl_aligned((const struct s2tt_context *)&s2tt_ctx,
				    pa, level);
	test_helpers_fail_if_no_assert_failed();
}

void s2tte_is_addr_lvl_aligned_tc5(void)
{
	/***************************************************************
	 * TEST CASE 5:
	 *
	 * Test s2tte_is_addr_lvl_aligned() with a NULL
	 * s2tt_context pointer.
	 ***************************************************************/

	long level = s2tt_test_helpers_min_table_lvl();
	unsigned long pa = 0UL; /* Aligned to any level */

	test_helpers_expect_assert_fail(true);
	(void)s2tte_is_addr_lvl_aligned((const struct s2tt_context *)NULL,
				    pa, level);
	test_helpers_fail_if_no_assert_failed();
}

void s2tte_map_size_tc1(void)
{
	/***************************************************************
	 * TEST CASE 1:
	 *
	 * For each valid level, invoke s2tte_map_size() and validate
	 * its output.
	 ***************************************************************/

	for (long level = s2tt_test_helpers_min_table_lvl();
	     level <= S2TT_TEST_HELPERS_MAX_LVL; level++) {
		unsigned long expected_size =
			s2tt_test_helpers_get_entry_va_space_size(level);

		UNSIGNED_LONGS_EQUAL(expected_size, s2tte_map_size(level));
	}
}

void s2tt_invalidate_page_tc1(void)
{
	/***************************************************************
	 * TEST CASE 1:
	 *
	 * Invoke s2tt_invalidate_page() with a valid address and a NULL
	 * s2tt_context.
	 ***************************************************************/

	test_helpers_expect_assert_fail(true);
	s2tt_invalidate_page(NULL, 0UL);
	test_helpers_fail_if_no_assert_failed();

}

void s2tt_invalidate_block_tc1(void)
{
	/***************************************************************
	 * TEST CASE 1:
	 *
	 * Invoke s2tt_invalidate_block() with a valid address and a NULL
	 * s2tt_context.
	 ***************************************************************/

	test_helpers_expect_assert_fail(true);
	s2tt_invalidate_block(NULL, 0UL);
	test_helpers_fail_if_no_assert_failed();

}

void s2tt_invalidate_pages_in_block_tc1(void)
{
	/***************************************************************
	 * TEST CASE 1:
	 *
	 * Invoke s2tt_invalidate_pages_in_block() with a valid address
	 * and a NULL s2tt_context.
	 ***************************************************************/

	test_helpers_expect_assert_fail(true);
	s2tt_invalidate_pages_in_block(NULL, 0UL);
	test_helpers_fail_if_no_assert_failed();

}

void s2tt_is_unassigned_empty_block_tc1(void)
{
	/***************************************************************
	 * TEST CASE 1:
	 *
	 * Create an unassigned empty block and validate that
	 * s2tt_is_unassigned_empty_block() returns the expected
	 * value
	 ***************************************************************/

	unsigned long s2tt[S2TTES_PER_S2TT];

	s2tt_init_unassigned_empty((const struct s2tt_context *)NULL, &s2tt[0]);

	CHECK_TRUE(s2tt_is_unassigned_empty_block(
				(const struct s2tt_context *)NULL, &s2tt[0U]));
}

void s2tt_is_unassigned_empty_block_tc2(void)
{
	/***************************************************************
	 * TEST CASE 2:
	 *
	 * Set of negative tests:
	 *	- Validate s2tt_is_unassigned_empty_block() with an
	 *	  unassigned empty block in which a random TTE is of
	 *	  a different unassigned type.
	 *	- Validate s2tt_is_unassigned_empty_block() with an
	 *	  unassigned empty block in which a random TTE is of
	 *	  a different assigned type.
	 ***************************************************************/

	unsigned long unassigned_ripas[] = {S2TTE_INVALID_RIPAS_RAM,
					    S2TTE_NS,
					    S2TTE_INVALID_RIPAS_DESTROYED};
	unsigned long assigned_ripas[] = {S2TTE_INVALID_RIPAS_EMPTY,
					  S2TTE_INVALID_RIPAS_RAM,
					  S2TTE_NS,
					  S2TTE_INVALID_RIPAS_DESTROYED};
	long level = test_helpers_get_rand_in_range(
			s2tt_test_helpers_min_block_lvl(),
			S2TT_TEST_HELPERS_MAX_LVL);
	unsigned long pa = s2tt_test_helpers_gen_pa(level, true);

	/* pickup a random type of unassigned S2TTE to test with */
	unsigned int idx = (unsigned int)test_helpers_get_rand_in_range(
					0UL, ARRAY_SIZE(unassigned_ripas) - 1UL);
	unsigned long s2tt[S2TTES_PER_S2TT];
	unsigned int tte_idx = (unsigned int)test_helpers_get_rand_in_range(0UL,
					     S2TTES_PER_S2TT - 1UL);
	struct s2tt_context s2tt_ctx = { 0UL };

	/*
	 * Initialize an s2tt_context structure for the test.
	 * Only 'enable_lpa2' is used by the API, so the rest of fields
	 * can be left untouched.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();

	s2tt_init_unassigned_empty(
			(const struct s2tt_context *)&s2tt_ctx, &s2tt[0]);

	/*
	 * Modify a random entry on the S2TT with a different
	 * unassigned S2TTE
	 */
	s2tt[tte_idx] = s2tt_test_create_unassigned(
				(const struct s2tt_context *)&s2tt_ctx,
				unassigned_ripas[idx]);
	CHECK_FALSE(s2tt_is_unassigned_empty_block(
				(const struct s2tt_context *)&s2tt_ctx,
				&s2tt[0U]));

	/* pickup a random type of assigned S2TTE to test with */
	idx = (unsigned int)test_helpers_get_rand_in_range(
					0UL, ARRAY_SIZE(assigned_ripas) - 1UL);

	/*
	 * Modify a random entry on the S2TT with an assigned S2TTE
	 */
	s2tt[tte_idx] = s2tt_test_create_assigned(
			(const struct s2tt_context *)&s2tt_ctx,
			pa, level, assigned_ripas[idx]);
	CHECK_FALSE(s2tt_is_unassigned_empty_block(
			(const struct s2tt_context *)&s2tt_ctx, &s2tt[0U]));
}

void s2tt_is_unassigned_empty_block_tc3(void)
{
	/***************************************************************
	 * TEST CASE 3:
	 *
	 * Invoke s2tt_is_unassigned_empty_block() with a NULL table.
	 ***************************************************************/

	test_helpers_expect_assert_fail(true);
	(void)s2tt_is_unassigned_empty_block(
			(const struct s2tt_context *)NULL, NULL);
	test_helpers_fail_if_no_assert_failed();
}

void s2tt_is_unassigned_ram_block_tc1(void)
{
	/***************************************************************
	 * TEST CASE 1:
	 *
	 * Create an unassigned ram block and validate that
	 * s2tt_is_unassigned_ram_block() returns the expected value
	 ***************************************************************/

	unsigned long s2tt[S2TTES_PER_S2TT];

	s2tt_init_unassigned_ram((const struct s2tt_context *)NULL, &s2tt[0]);

	CHECK_TRUE(s2tt_is_unassigned_ram_block(
				(const struct s2tt_context *)NULL, &s2tt[0U]));
}

void s2tt_is_unassigned_ram_block_tc2(void)
{
	/***************************************************************
	 * TEST CASE 2:
	 *
	 * Set of negative tests:
	 *	- Validate s2tt_is_unassigned_ram_block() with an
	 *	  unassigned ram block in which a random TTE is of
	 *	  a different unassigned type.
	 *	- Validate s2tt_is_unassigned_ram_block() with an
	 *	  unassigned ram block in which a random TTE is of
	 *	  a different assigned type.
	 ***************************************************************/

	unsigned long unassigned_ripas[] = {S2TTE_INVALID_RIPAS_EMPTY,
					    S2TTE_NS,
					    S2TTE_INVALID_RIPAS_DESTROYED};
	unsigned long assigned_ripas[] = {S2TTE_INVALID_RIPAS_EMPTY,
					  S2TTE_INVALID_RIPAS_RAM,
					  S2TTE_NS,
					  S2TTE_INVALID_RIPAS_DESTROYED};
	long level = test_helpers_get_rand_in_range(
			s2tt_test_helpers_min_block_lvl(),
			S2TT_TEST_HELPERS_MAX_LVL);
	unsigned long pa = s2tt_test_helpers_gen_pa(level, true);

	/* pickup a random type of unassigned S2TTE to test with */
	unsigned int idx = (unsigned int)test_helpers_get_rand_in_range(
				0UL, ARRAY_SIZE(unassigned_ripas) - 1UL);
	unsigned long s2tt[S2TTES_PER_S2TT];
	unsigned int tte_idx = (unsigned int)test_helpers_get_rand_in_range(0UL,
					     S2TTES_PER_S2TT - 1UL);

	s2tt_context s2tt_ctx = { 0UL };

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 is of use on this API, so
	 * the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();

	s2tt_init_unassigned_ram((const struct s2tt_context *)&s2tt_ctx, &s2tt[0]);

	/*
	 * Modify a random entry on the S2TT with a different
	 * unassigned S2TTE
	 */
	s2tt[tte_idx] = s2tt_test_create_unassigned(
				(const struct s2tt_context *)&s2tt_ctx,
				unassigned_ripas[idx]);
	CHECK_FALSE(s2tt_is_unassigned_ram_block(
				(const struct s2tt_context *)&s2tt_ctx, &s2tt[0U]));

	/* pickup a random type of assigned S2TTE to test with */
	idx = (unsigned int)test_helpers_get_rand_in_range(
					0UL, ARRAY_SIZE(assigned_ripas) - 1UL);

	/*
	 * Modify a random entry on the S2TT with an assigned S2TTE
	 */
	s2tt[tte_idx] = s2tt_test_create_assigned((const struct s2tt_context *)&s2tt_ctx,
					     pa, level, assigned_ripas[idx]);
	CHECK_FALSE(s2tt_is_unassigned_ram_block(
				(const struct s2tt_context *)&s2tt_ctx,
				&s2tt[0U]));
}

void s2tt_is_unassigned_ram_block_tc3(void)
{
	/***************************************************************
	 * TEST CASE 3:
	 *
	 * Invoke s2tt_is_unassigned_ram_block() with a NULL table.
	 ***************************************************************/

	test_helpers_expect_assert_fail(true);
	(void)s2tt_is_unassigned_ram_block(
			(const struct s2tt_context *)NULL, NULL);
	test_helpers_fail_if_no_assert_failed();
}

void s2tt_is_unassigned_ns_block_tc1(void)
{
	/***************************************************************
	 * TEST CASE 1:
	 *
	 * Create an unassigned ns block and validate that
	 * s2tt_is_unassigned_ns_block() returns the expected value
	 ***************************************************************/

	unsigned long s2tt[S2TTES_PER_S2TT];

	s2tt_init_unassigned_ns((const struct s2tt_context *)NULL, &s2tt[0]);

	CHECK_TRUE(s2tt_is_unassigned_ns_block((const struct s2tt_context *)NULL,
						&s2tt[0U]));
}

void s2tt_is_unassigned_ns_block_tc2(void)
{
	/***************************************************************
	 * TEST CASE 2:
	 *
	 * Set of negative tests:
	 *	- Validate s2tt_is_unassigned_ns_block() with an
	 *	  unassigned ns block in which a random TTE is of
	 *	  a different unassigned type.
	 *	- Validate s2tt_is_unassigned_ns_block() with an
	 *	  unassigned ns block in which a random TTE is of
	 *	  a different assigned type.
	 ***************************************************************/

	unsigned long unassigned_ripas[] = {S2TTE_INVALID_RIPAS_RAM,
					    S2TTE_INVALID_RIPAS_EMPTY,
					    S2TTE_INVALID_RIPAS_DESTROYED};
	unsigned long assigned_ripas[] = {S2TTE_INVALID_RIPAS_EMPTY,
					  S2TTE_INVALID_RIPAS_RAM,
					  S2TTE_NS,
					  S2TTE_INVALID_RIPAS_DESTROYED};
	long level = test_helpers_get_rand_in_range(
			s2tt_test_helpers_min_block_lvl(),
			S2TT_TEST_HELPERS_MAX_LVL);
	unsigned long pa = s2tt_test_helpers_gen_pa(level, true);

	/* pickup a random type of unassigned S2TTE to test with */
	unsigned int idx = (unsigned int)test_helpers_get_rand_in_range(
				0UL, ARRAY_SIZE(unassigned_ripas) - 1UL);
	unsigned long s2tt[S2TTES_PER_S2TT];
	unsigned int tte_idx = (unsigned int)test_helpers_get_rand_in_range(0UL,
					     S2TTES_PER_S2TT - 1UL);
	s2tt_context s2tt_ctx = { 0UL };

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 is of use on this API, so
	 * the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();

	s2tt_init_unassigned_ns((const struct s2tt_context *)&s2tt_ctx, &s2tt[0]);

	/*
	 * Modify a random entry on the S2TT with a different
	 * unassigned S2TTE
	 */
	s2tt[tte_idx] = s2tt_test_create_unassigned(
				(const struct s2tt_context *)&s2tt_ctx,
				unassigned_ripas[idx]);
	CHECK_FALSE(s2tt_is_unassigned_ns_block(
				(const struct s2tt_context *)&s2tt_ctx,
				&s2tt[0U]));

	/* pickup a random type of assigned S2TTE to test with */
	idx = (unsigned int)test_helpers_get_rand_in_range(
					0UL, ARRAY_SIZE(assigned_ripas) - 1UL);

	/*
	 * Modify a random entry on the S2TT with an assigned S2TTE
	 */
	s2tt[tte_idx] = s2tt_test_create_assigned(
				(const struct s2tt_context *)&s2tt_ctx,
				pa, level, assigned_ripas[idx]);
	CHECK_FALSE(s2tt_is_unassigned_ns_block(
				(const struct s2tt_context *)&s2tt_ctx,
				&s2tt[0U]));
}

void s2tt_is_unassigned_ns_block_tc3(void)
{
	/***************************************************************
	 * TEST CASE 3:
	 *
	 * Invoke s2tt_is_unassigned_ns_block() with a NULL table.
	 ***************************************************************/

	test_helpers_expect_assert_fail(true);
	(void)s2tt_is_unassigned_ns_block((const struct s2tt_context *)NULL, NULL);
	test_helpers_fail_if_no_assert_failed();
}

void s2tt_is_unassigned_destroyed_block_tc1(void)
{
	/***************************************************************
	 * TEST CASE 1:
	 *
	 * Create an unassigned destroyed block and validate that
	 * s2tt_is_unassigned_destroyed_block() returns the
	 * expected value
	 ***************************************************************/

	unsigned long s2tt[S2TTES_PER_S2TT];

	s2tt_init_unassigned_destroyed((const struct s2tt_context *)NULL, &s2tt[0]);

	CHECK_TRUE(s2tt_is_unassigned_destroyed_block(
				(const struct s2tt_context *)NULL, &s2tt[0U]));
}

void s2tt_is_unassigned_destroyed_block_tc2(void)
{
	/***************************************************************
	 * TEST CASE 2:
	 *
	 * Set of negative tests:
	 *	- Validate s2tt_is_unassigned_destroyed_block() with
	 *	  an unassigned ns block in which a random TTE is of
	 *	  a different unassigned type.
	 *	- Validate s2tt_is_unassigned_destroyed_block() with
	 *	  an unassigned ns block in which a random TTE is of
	 *	  a different assigned type.
	 ***************************************************************/

	unsigned long unassigned_ripas[] = {S2TTE_INVALID_RIPAS_RAM,
					    S2TTE_INVALID_RIPAS_EMPTY,
					    S2TTE_NS};
	unsigned long assigned_ripas[] = {S2TTE_INVALID_RIPAS_EMPTY,
					  S2TTE_INVALID_RIPAS_RAM,
					  S2TTE_NS,
					  S2TTE_INVALID_RIPAS_DESTROYED};
	long level = test_helpers_get_rand_in_range(
			s2tt_test_helpers_min_block_lvl(),
			S2TT_TEST_HELPERS_MAX_LVL);
	unsigned long pa = s2tt_test_helpers_gen_pa(level, true);

	/* pickup a random type of unassigned S2TTE to test with */
	unsigned int idx = (unsigned int)test_helpers_get_rand_in_range(
				0UL, ARRAY_SIZE(unassigned_ripas) - 1UL);
	unsigned long s2tt[S2TTES_PER_S2TT];
	unsigned int tte_idx = (unsigned int)test_helpers_get_rand_in_range(0UL,
					     S2TTES_PER_S2TT - 1UL);
	s2tt_context s2tt_ctx = { 0UL };

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 is of use on this API, so
	 * the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();

	s2tt_init_unassigned_destroyed((const struct s2tt_context *)&s2tt_ctx,
					&s2tt[0]);

	/*
	 * Modify a random entry on the S2TT with a different
	 * unassigned S2TTE
	 */
	s2tt[tte_idx] = s2tt_test_create_unassigned(
				(const struct s2tt_context *)&s2tt_ctx,
				unassigned_ripas[idx]);
	CHECK_FALSE(s2tt_is_unassigned_destroyed_block(
			(const struct s2tt_context *)&s2tt_ctx,	&s2tt[0U]));

	/* pickup a random type of assigned S2TTE to test with */
	idx = (unsigned int)test_helpers_get_rand_in_range(
					0UL, ARRAY_SIZE(assigned_ripas) - 1UL);

	/*
	 * Modify a random entry on the S2TT with an assigned S2TTE
	 */
	s2tt[tte_idx] = s2tt_test_create_assigned(
				(const struct s2tt_context *)&s2tt_ctx,
				pa, level, assigned_ripas[idx]);
	CHECK_FALSE(s2tt_is_unassigned_destroyed_block(
				(const struct s2tt_context *)&s2tt_ctx,
				&s2tt[0U]));
}

void s2tt_is_unassigned_destroyed_block_tc3(void)
{
	/***************************************************************
	 * TEST CASE 3:
	 *
	 * Invoke s2tt_is_unassigned_destroyed_block() with a NULL table.
	 ***************************************************************/

	test_helpers_expect_assert_fail(true);
	(void)s2tt_is_unassigned_destroyed_block(
				(const struct s2tt_context *)NULL, NULL);
	test_helpers_fail_if_no_assert_failed();
}

void s2tt_maps_assigned_empty_block_tc1(void)
{
	/***************************************************************
	 * TEST CASE 1:
	 *
	 * For each valid level, create an assigned empty block and
	 * validate that s2tt_maps_assigned_empty_block() returns
	 * the expected value
	 ***************************************************************/

	s2tt_context s2tt_ctx = { 0UL };

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 is of use on this API, so
	 * the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();

	for (long level = s2tt_test_helpers_min_block_lvl();
	     level <= S2TT_TEST_HELPERS_MAX_TABLE_LVL; level++) {

		unsigned long s2tt[S2TTES_PER_S2TT];
		unsigned long pa = s2tt_test_helpers_gen_pa(level - 1L, true);

		/* Generate the table */
		s2tt_init_assigned_empty((const struct s2tt_context *)&s2tt_ctx,
					 &s2tt[0U], pa, level);

		CHECK_TRUE(s2tt_maps_assigned_empty_block(
					(const struct s2tt_context *)&s2tt_ctx,
					&s2tt[0U], level));
	}
}

void s2tt_maps_assigned_empty_block_tc2(void)
{
	/***************************************************************
	 * TEST CASE 2:
	 *
	 * For each valid level, create an assigned empty block and
	 * then change a random TTE to a different type to validate
	 * that s2tt_maps_assigned_empty_block() returns the expected
	 * value
	 ***************************************************************/

	unsigned long unassigned_ripas[] = {S2TTE_INVALID_RIPAS_EMPTY,
					    S2TTE_INVALID_RIPAS_RAM,
					    S2TTE_NS,
					    S2TTE_INVALID_RIPAS_DESTROYED};
	unsigned long assigned_ripas[] = {S2TTE_INVALID_RIPAS_RAM,
					  S2TTE_NS,
					  S2TTE_INVALID_RIPAS_DESTROYED};
	s2tt_context s2tt_ctx = { 0UL };

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 is of use on this API, so
	 * the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();

	for (long level = s2tt_test_helpers_min_block_lvl();
	     level <= S2TT_TEST_HELPERS_MAX_TABLE_LVL; level++) {

		unsigned int tte_idx =
			(unsigned int)test_helpers_get_rand_in_range(0UL,
					     S2TTES_PER_S2TT - 1UL);
		/* pickup a random type of unassigned S2TTE to test with */
		unsigned int idx =
			(unsigned int)test_helpers_get_rand_in_range(0UL,
					ARRAY_SIZE(unassigned_ripas) - 1UL);
		unsigned long s2tt[S2TTES_PER_S2TT];
		unsigned long pa = s2tt_test_helpers_gen_pa(level - 1L, true);

		/* Generate the table */
		s2tt_init_assigned_empty((const struct s2tt_context *)&s2tt_ctx,
					 &s2tt[0U], pa, level);

		/* Alter a random S2TTE on the table */
		s2tt[tte_idx] = s2tt_test_create_unassigned(
					(const struct s2tt_context *)&s2tt_ctx,
					unassigned_ripas[idx]);
		CHECK_FALSE(s2tt_maps_assigned_empty_block(
					(const struct s2tt_context *)&s2tt_ctx,
					&s2tt[0U], level));

		/* pickup a random type of assigned S2TTE to test with */
		idx = (unsigned int)test_helpers_get_rand_in_range(0UL,
					ARRAY_SIZE(assigned_ripas) - 1UL);

		/* Alter a random S2TTE on the table */
		s2tt[tte_idx] = s2tt_test_create_assigned(
				(const struct s2tt_context *)&s2tt_ctx, pa, level,
				assigned_ripas[idx]);
		CHECK_FALSE(s2tt_maps_assigned_empty_block(
					(const struct s2tt_context *)&s2tt_ctx,
					&s2tt[0U], level));
	}
}

void s2tt_maps_assigned_empty_block_tc3(void)
{
	/***************************************************************
	 * TEST CASE 3:
	 *
	 * Invoke s2tt_maps_assigned_empty_block() with the incorrect
	 * level.
	 ***************************************************************/

	long level = s2tt_test_helpers_min_block_lvl();
	unsigned long s2tt[S2TTES_PER_S2TT];
	unsigned long pa;
	s2tt_context s2tt_ctx = { 0UL };

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 is of use on this API, so
	 * the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();

	/*
	 * Get a PA aligned @level - 1 so we can create a table
	 * @level starting at such PA.
	 */
	pa = s2tt_test_helpers_gen_pa(level - 1L, true);

	/* Generate a valid table */
	s2tt_init_assigned_empty((const struct s2tt_context *)&s2tt_ctx,
				 &s2tt[0U], pa, level);

	CHECK_FALSE(s2tt_maps_assigned_empty_block(
				(const struct s2tt_context *)&s2tt_ctx,
				&s2tt[0U], level + 1L));
}

void s2tt_maps_assigned_empty_block_tc4(void)
{
	/***************************************************************
	 * TEST CASE 4:
	 *
	 * Invoke s2tt_maps_assigned_empty_block() with a valid level
	 * and a NULL table pointer.
	 ***************************************************************/

	long level = s2tt_test_helpers_min_block_lvl();
	s2tt_context s2tt_ctx = { 0UL };

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 is of use on this API, so
	 * the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();


	test_helpers_expect_assert_fail(true);
	(void)s2tt_maps_assigned_empty_block(
			(const struct s2tt_context *)&s2tt_ctx, NULL, level);
	test_helpers_fail_if_no_assert_failed();
}

void s2tt_maps_assigned_empty_block_tc5(void)
{
	/***************************************************************
	 * TEST CASE 5:
	 *
	 * Invoke s2tt_maps_assigned_empty_block() with a level above
	 * the maximum allowed.
	 ***************************************************************/

	long level = S2TT_TEST_HELPERS_MAX_LVL;
	unsigned long s2tt[S2TTES_PER_S2TT];
	unsigned long pa = s2tt_test_helpers_gen_pa(level - 1L, true);
	s2tt_context s2tt_ctx = { 0UL };

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 is of use on this API, so
	 * the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();

	/* Generate a valid table */
	s2tt_init_assigned_empty((const struct s2tt_context *)&s2tt_ctx,
				 &s2tt[0U], pa, level);

	test_helpers_expect_assert_fail(true);
	(void)s2tt_maps_assigned_empty_block(
			(const struct s2tt_context *)&s2tt_ctx,
			&s2tt[0U], level + 1UL);
	test_helpers_fail_if_no_assert_failed();
}

void s2tt_maps_assigned_empty_block_tc6(void)
{
	/***************************************************************
	 * TEST CASE 6:
	 *
	 * Invoke s2tt_maps_assigned_empty_block() with a level below
	 * the minimum allowed.
	 ***************************************************************/

	long level = s2tt_test_helpers_min_block_lvl();
	unsigned long s2tt[S2TTES_PER_S2TT];
	unsigned long pa = s2tt_test_helpers_gen_pa(level - 1L, true);
	s2tt_context s2tt_ctx = { 0UL };

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 is of use on this API, so
	 * the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();

	/* Generate a valid table */
	s2tt_init_assigned_empty((const struct s2tt_context *)&s2tt_ctx,
				 &s2tt[0U], pa, level);

	level = s2tt_test_helpers_min_table_lvl() - 1L;
	test_helpers_expect_assert_fail(true);
	(void)s2tt_maps_assigned_empty_block(
				(const struct s2tt_context *)&s2tt_ctx,
				&s2tt[0U], level - 1UL);
	test_helpers_fail_if_no_assert_failed();
}

void s2tt_maps_assigned_empty_block_tc7(void)
{
	/***************************************************************
	 * TEST CASE 7:
	 *
	 * Invoke s2tt_maps_assigned_empty_block() with a NULL pointer
	 * to a s2tt_context structure.
	 ***************************************************************/

	long level = s2tt_test_helpers_min_block_lvl();
	unsigned long s2tt[S2TTES_PER_S2TT];
	unsigned long pa = s2tt_test_helpers_gen_pa(level - 1L, true);
	s2tt_context s2tt_ctx = { 0UL };

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 is of use on this API, so
	 * the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();

	/* Generate a valid table */
	s2tt_init_assigned_empty((const struct s2tt_context *)&s2tt_ctx,
				 &s2tt[0U], pa, level);

	test_helpers_expect_assert_fail(true);
	(void)s2tt_maps_assigned_empty_block(
					(const struct s2tt_context *)NULL,
					&s2tt[0U], level);
	test_helpers_fail_if_no_assert_failed();
}

void s2tt_maps_assigned_ram_block_tc1(void)
{
	/***************************************************************
	 * TEST CASE 1:
	 *
	 * For each valid level, create an assigned ram block and
	 * validate that s2tt_maps_assigned_ram_block() returns
	 * the expected value
	 ***************************************************************/

	s2tt_context s2tt_ctx = { 0UL };

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 is of use on this API, so
	 * the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();

	for (long level = s2tt_test_helpers_min_block_lvl();
	     level <= S2TT_TEST_HELPERS_MAX_TABLE_LVL; level++) {

		unsigned long s2tt[S2TTES_PER_S2TT];
		unsigned long pa = s2tt_test_helpers_gen_pa(level - 1L, true);

		/* Generate the table */
		s2tt_init_assigned_ram((const struct s2tt_context *)&s2tt_ctx,
					&s2tt[0U], pa, level);

		CHECK_TRUE(s2tt_maps_assigned_ram_block(
					(const struct s2tt_context *)&s2tt_ctx,
					&s2tt[0U], level));
	}
}

void s2tt_maps_assigned_ram_block_tc2(void)
{
	/***************************************************************
	 * TEST CASE 2:
	 *
	 * For each valid level, create an assigned ram block and
	 * then change a random TTE to a different type to validate
	 * that s2tt_maps_assigned_ram_block() returns the expected
	 * value
	 ***************************************************************/

	unsigned long unassigned_ripas[] = {S2TTE_INVALID_RIPAS_EMPTY,
					    S2TTE_INVALID_RIPAS_RAM,
					    S2TTE_NS,
					    S2TTE_INVALID_RIPAS_DESTROYED};
	unsigned long assigned_ripas[] = {S2TTE_INVALID_RIPAS_EMPTY,
					  S2TTE_NS,
					  S2TTE_INVALID_RIPAS_DESTROYED};
	s2tt_context s2tt_ctx = { 0UL };

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 is of use on this API, so
	 * the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();

	for (long level = s2tt_test_helpers_min_block_lvl();
	     level <= S2TT_TEST_HELPERS_MAX_TABLE_LVL; level++) {

		unsigned int tte_idx =
			(unsigned int)test_helpers_get_rand_in_range(0UL,
					     S2TTES_PER_S2TT - 1UL);
		/* pickup a random type of unassigned S2TTE to test with */
		unsigned int idx =
			(unsigned int)test_helpers_get_rand_in_range(0UL,
					ARRAY_SIZE(unassigned_ripas) - 1UL);
		unsigned long s2tt[S2TTES_PER_S2TT];
		unsigned long pa = s2tt_test_helpers_gen_pa(level - 1L, true);

		/* Generate the table */
		s2tt_init_assigned_ram((const struct s2tt_context *)&s2tt_ctx,
					&s2tt[0U], pa, level);

		/* Alter a random S2TTE on the table */
		s2tt[tte_idx] = s2tt_test_create_unassigned(
					(const struct s2tt_context *)&s2tt_ctx,
					unassigned_ripas[idx]);
		CHECK_FALSE(s2tt_maps_assigned_ram_block(
					(const struct s2tt_context *)&s2tt_ctx,
					&s2tt[0U], level));

		/* pickup a random type of assigned S2TTE to test with */
		idx = (unsigned int)test_helpers_get_rand_in_range(0UL,
					ARRAY_SIZE(assigned_ripas) - 1UL);

		/* Alter a random S2TTE on the table */
		s2tt[tte_idx] = s2tt_test_create_assigned(
				(const struct s2tt_context *)&s2tt_ctx,
				pa, level, assigned_ripas[idx]);
		CHECK_FALSE(s2tt_maps_assigned_ram_block(
					(const struct s2tt_context *)&s2tt_ctx,
					&s2tt[0U], level));
	}
}

void s2tt_maps_assigned_ram_block_tc3(void)
{
	/***************************************************************
	 * TEST CASE 3:
	 *
	 * Invoke s2tt_maps_assigned_ram_block() with the incorrect
	 * level.
	 ***************************************************************/

	long level = s2tt_test_helpers_min_block_lvl();
	unsigned long s2tt[S2TTES_PER_S2TT];
	unsigned long pa;
	s2tt_context s2tt_ctx = { 0UL };

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 is of use on this API, so
	 * the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();

	/*
	 * Get a PA aligned @level - 1 so we can create a table
	 * @level starting at such PA.
	 */
	pa = s2tt_test_helpers_gen_pa(level - 1L, true);

	/* Generate a valid table */
	s2tt_init_assigned_ram((const struct s2tt_context *)&s2tt_ctx,
				&s2tt[0U], pa, level);

	CHECK_FALSE(s2tt_maps_assigned_ram_block(
					(const struct s2tt_context *)&s2tt_ctx,
					&s2tt[0U], level + 1L));
}

void s2tt_maps_assigned_ram_block_tc4(void)
{
	/***************************************************************
	 * TEST CASE 4:
	 *
	 * Invoke s2tt_maps_assigned_ram_block() with a valid level
	 * and a NULL table pointer.
	 ***************************************************************/

	long level = s2tt_test_helpers_min_block_lvl();
	s2tt_context s2tt_ctx = { 0UL };

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 is of use on this API, so
	 * the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();

	test_helpers_expect_assert_fail(true);
	(void)s2tt_maps_assigned_ram_block(
			(const struct s2tt_context *)&s2tt_ctx, NULL, level);
	test_helpers_fail_if_no_assert_failed();
}

void s2tt_maps_assigned_ram_block_tc5(void)
{
	/***************************************************************
	 * TEST CASE 5:
	 *
	 * Invoke s2tt_maps_assigned_ram_block() with a level above
	 * the maximum allowed.
	 ***************************************************************/

	long level = S2TT_TEST_HELPERS_MAX_LVL;
	unsigned long s2tt[S2TTES_PER_S2TT];
	unsigned long pa = s2tt_test_helpers_gen_pa(level - 1L, true);
	s2tt_context s2tt_ctx = { 0UL };

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 is of use on this API, so
	 * the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();

	/* Generate a valid table */
	s2tt_init_assigned_ram((const struct s2tt_context *)&s2tt_ctx,
				&s2tt[0U], pa, level);

	test_helpers_expect_assert_fail(true);
	(void)s2tt_maps_assigned_ram_block(
				(const struct s2tt_context *)&s2tt_ctx,
				&s2tt[0U], level + 1UL);
	test_helpers_fail_if_no_assert_failed();
}

void s2tt_maps_assigned_ram_block_tc6(void)
{
	/***************************************************************
	 * TEST CASE 6:
	 *
	 * Invoke s2tt_maps_assigned_ram_block() with a level below
	 * the minimum allowed.
	 ***************************************************************/

	long level = s2tt_test_helpers_min_block_lvl();
	unsigned long s2tt[S2TTES_PER_S2TT];
	unsigned long pa = s2tt_test_helpers_gen_pa(level - 1L, true);
	s2tt_context s2tt_ctx = { 0UL };

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 is of use on this API, so
	 * the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();

	/* Generate a valid table */
	s2tt_init_assigned_ram((const struct s2tt_context *)&s2tt_ctx,
				&s2tt[0U], pa, level);

	level = s2tt_test_helpers_min_table_lvl() - 1L;
	test_helpers_expect_assert_fail(true);
	(void)s2tt_maps_assigned_ram_block((const struct s2tt_context *)&s2tt_ctx,
					   &s2tt[0U], level);
	test_helpers_fail_if_no_assert_failed();
}

void s2tt_maps_assigned_ram_block_tc7(void)
{
	/***************************************************************
	 * TEST CASE 7:
	 *
	 * Invoke s2tt_maps_assigned_ram_block() with a NULL pointer to
	 * s2tt_context structure.
	 ***************************************************************/

	long level = s2tt_test_helpers_min_block_lvl();
	unsigned long s2tt[S2TTES_PER_S2TT];
	unsigned long pa = s2tt_test_helpers_gen_pa(level - 1L, true);
	s2tt_context s2tt_ctx = { 0UL };

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 is of use on this API, so
	 * the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();

	/* Generate a valid table */
	s2tt_init_assigned_ram((const struct s2tt_context *)&s2tt_ctx,
				&s2tt[0U], pa, level);

	test_helpers_expect_assert_fail(true);
	(void)s2tt_maps_assigned_ram_block((const struct s2tt_context *)NULL,
					   &s2tt[0U], level);
	test_helpers_fail_if_no_assert_failed();
}

void s2tt_maps_assigned_ns_block_tc1(void)
{
	/***************************************************************
	 * TEST CASE 1:
	 *
	 * For each valid level, create an assigned ns block and
	 * validate that s2tt_maps_assigned_ns_block() returns
	 * the expected value
	 ***************************************************************/

	s2tt_context s2tt_ctx = { 0UL };

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 is of use on this API, so
	 * the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();

	for (long level = s2tt_test_helpers_min_block_lvl();
	     level <= S2TT_TEST_HELPERS_MAX_TABLE_LVL; level++) {

		unsigned long s2tt[S2TTES_PER_S2TT];
		unsigned long pa = s2tt_test_helpers_gen_pa(level - 1L, true);
		unsigned long attrs =
			s2tt_test_helpers_gen_ns_attrs(true, false);

		/* Generate the table */
		s2tt_init_assigned_ns((const struct s2tt_context *)&s2tt_ctx,
				      &s2tt[0U], attrs, pa, level);

		CHECK_TRUE(s2tt_maps_assigned_ns_block(
					(const struct s2tt_context *)&s2tt_ctx,
					&s2tt[0U], level));
	}
}

void s2tt_maps_assigned_ns_block_tc2(void)
{
	/***************************************************************
	 * TEST CASE 2:
	 *
	 * For each valid level, create an assigned ns block and
	 * alter the NS attributes of a random TTE with a random value.
	 * Then verify that s2tt_maps_assigned_ns_block() returns
	 * the expected value.
	 ***************************************************************/

	s2tt_context s2tt_ctx = { 0UL };

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 is of use on this API, so
	 * the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();

	for (long level = s2tt_test_helpers_min_block_lvl();
	     level <= S2TT_TEST_HELPERS_MAX_TABLE_LVL; level++) {

		unsigned long s2tt[S2TTES_PER_S2TT];
		unsigned int index = test_helpers_get_rand_in_range(0UL,
							S2TTES_PER_S2TT - 1UL);
		unsigned long pa = s2tt_test_helpers_gen_pa(level - 1L, true);
		unsigned long new_attrs, attrs =
			s2tt_test_helpers_gen_ns_attrs(true, false);
		unsigned long ns_mask = (s2tt_ctx.enable_lpa2 == true) ?
			S2TT_TEST_TTE_HOST_NS_ATTRS_LPA2_MASK :
			S2TT_TEST_TTE_HOST_NS_ATTRS_MASK;

		/* Generate the table */
		s2tt_init_assigned_ns((const struct s2tt_context *)&s2tt_ctx,
				      &s2tt[0U], attrs, pa, level);

		/* Generate the offending set of NS attrs */
		do {
			new_attrs = test_helpers_get_rand_in_range(0UL, ULONG_MAX);
			new_attrs &= ns_mask;
		} while (new_attrs == (s2tt[0U] & ns_mask));

		/* Alter the NS attributes on a random TTE */
		s2tt[index] &= ~ns_mask;
		s2tt[index] |= new_attrs;

		CHECK_FALSE(s2tt_maps_assigned_ns_block(
					(const struct s2tt_context *)&s2tt_ctx,
					&s2tt[0U], level));
	}
}

void s2tt_maps_assigned_ns_block_tc3(void)
{
	/***************************************************************
	 * TEST CASE 3:
	 *
	 * For each valid level, create an assigned ns block and
	 * then change a random TTE to a different type to validate
	 * that s2tt_maps_assigned_ns_block() returns the expected
	 * value
	 ***************************************************************/

	unsigned long unassigned_ripas[] = {S2TTE_INVALID_RIPAS_EMPTY,
					    S2TTE_INVALID_RIPAS_RAM,
					    S2TTE_NS,
					    S2TTE_INVALID_RIPAS_DESTROYED};
	unsigned long assigned_ripas[] = {S2TTE_INVALID_RIPAS_EMPTY,
					  S2TTE_INVALID_RIPAS_RAM,
					  S2TTE_INVALID_RIPAS_DESTROYED};

	unsigned long attrs = s2tt_test_helpers_gen_ns_attrs(true, false);
	s2tt_context s2tt_ctx = { 0UL };

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 is of use on this API, so
	 * the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();

	for (long level = s2tt_test_helpers_min_block_lvl();
	     level <= S2TT_TEST_HELPERS_MAX_TABLE_LVL; level++) {

		unsigned int tte_idx =
			(unsigned int)test_helpers_get_rand_in_range(0UL,
					     S2TTES_PER_S2TT - 1UL);
		/* pickup a random type of unassigned S2TTE to test with */
		unsigned int idx =
			(unsigned int)test_helpers_get_rand_in_range(0UL,
					ARRAY_SIZE(unassigned_ripas) - 1UL);
		unsigned long s2tt[S2TTES_PER_S2TT];
		unsigned long pa = s2tt_test_helpers_gen_pa(level - 1L, true);

		/* Generate the table */
		s2tt_init_assigned_ns((const struct s2tt_context *)&s2tt_ctx,
				      &s2tt[0U], attrs, pa, level);

		/* Alter a random S2TTE on the table */
		s2tt[tte_idx] = s2tt_test_create_unassigned(
					(const struct s2tt_context *)&s2tt_ctx,
					unassigned_ripas[idx]);
		CHECK_FALSE(s2tt_maps_assigned_ns_block(
					(const struct s2tt_context *)&s2tt_ctx,
					&s2tt[0U], level));

		/* pickup a random type of assigned S2TTE to test with */
		idx = (unsigned int)test_helpers_get_rand_in_range(0UL,
					ARRAY_SIZE(assigned_ripas) - 1UL);

		/* Alter a random S2TTE on the table */
		s2tt[tte_idx] = s2tt_test_create_assigned(
					(const struct s2tt_context *)&s2tt_ctx,
					pa, level, assigned_ripas[idx]);
		CHECK_FALSE(s2tt_maps_assigned_ns_block(
					(const struct s2tt_context *)&s2tt_ctx,
					&s2tt[0U], level));
	}
}

void s2tt_maps_assigned_ns_block_tc4(void)
{
	/***************************************************************
	 * TEST CASE 4:
	 *
	 * Invoke s2tt_maps_assigned_ns_block() with the incorrect
	 * level.
	 ***************************************************************/

	long level = s2tt_test_helpers_min_block_lvl();
	unsigned long s2tt[S2TTES_PER_S2TT];
	unsigned long attrs = s2tt_test_helpers_gen_ns_attrs(true, false);
	unsigned long pa;
	s2tt_context s2tt_ctx = { 0UL };

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 is of use on this API, so
	 * the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();

	/* Get a PA aligned only to 'level' */
	do {
		pa = s2tt_test_helpers_gen_pa(level, true);

	} while (s2tte_is_addr_lvl_aligned((const struct s2tt_context *)&s2tt_ctx,
					   pa, level - 1L));

	/* Generate a valid table */
	s2tt_init_assigned_ns((const struct s2tt_context *)&s2tt_ctx,
			      &s2tt[0U], attrs, pa, level);

	CHECK_FALSE(s2tt_maps_assigned_ns_block(
					(const struct s2tt_context *)&s2tt_ctx,
					&s2tt[0U], level));
}

void s2tt_maps_assigned_ns_block_tc5(void)
{
	/***************************************************************
	 * TEST CASE 5:
	 *
	 * Invoke s2tt_maps_assigned_ns_block() with a valid level
	 * and a NULL table pointer.
	 ***************************************************************/

	long level = s2tt_test_helpers_min_block_lvl();
	s2tt_context s2tt_ctx = { 0UL };

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 is of use on this API, so
	 * the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();

	test_helpers_expect_assert_fail(true);
	(void)s2tt_maps_assigned_ns_block(
			(const struct s2tt_context *)&s2tt_ctx, NULL, level);
	test_helpers_fail_if_no_assert_failed();
}

void s2tt_maps_assigned_ns_block_tc6(void)
{
	/***************************************************************
	 * TEST CASE 6:
	 *
	 * Invoke s2tt_maps_assigned_ns_block() with a level above
	 * the maximum allowed.
	 ***************************************************************/

	long level = S2TT_TEST_HELPERS_MAX_LVL;
	unsigned long s2tt[S2TTES_PER_S2TT];
	unsigned long pa = s2tt_test_helpers_gen_pa(level - 1L, true);
	unsigned long attrs = s2tt_test_helpers_gen_ns_attrs(true, false);
	s2tt_context s2tt_ctx = { 0UL };

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 is of use on this API, so
	 * the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();

	/* Generate a valid table */
	s2tt_init_assigned_ns((const struct s2tt_context *)&s2tt_ctx,
			      &s2tt[0U], attrs, pa, level);

	test_helpers_expect_assert_fail(true);
	(void)s2tt_maps_assigned_ram_block((const struct s2tt_context *)&s2tt_ctx,
			&s2tt[0U], level + 1UL);
	test_helpers_fail_if_no_assert_failed();
}

void s2tt_maps_assigned_ns_block_tc7(void)
{
	/***************************************************************
	 * TEST CASE 7:
	 *
	 * Invoke s2tt_maps_assigned_ram_block() with a level below
	 * the minimum allowed.
	 ***************************************************************/

	long level = s2tt_test_helpers_min_block_lvl();
	unsigned long s2tt[S2TTES_PER_S2TT];
	unsigned long pa = s2tt_test_helpers_gen_pa(level - 1L, true);
	unsigned long attrs = s2tt_test_helpers_gen_ns_attrs(true, false);
	s2tt_context s2tt_ctx = { 0UL };

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 is of use on this API, so
	 * the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();

	/* Generate a valid table */
	s2tt_init_assigned_ns((const struct s2tt_context *)&s2tt_ctx,
			      &s2tt[0U], attrs, pa, level);

	level = s2tt_test_helpers_min_table_lvl() - 1L;
	test_helpers_expect_assert_fail(true);
	(void)s2tt_maps_assigned_ns_block((const struct s2tt_context *)&s2tt_ctx,
					  &s2tt[0U], level);
	test_helpers_fail_if_no_assert_failed();
}

void s2tt_maps_assigned_ns_block_tc8(void)
{
	/***************************************************************
	 * TEST CASE 8:
	 *
	 * Invoke s2tt_maps_assigned_ram_block() with a NULL pointer to
	 * s2tt_context structure.
	 ***************************************************************/

	long level = s2tt_test_helpers_min_block_lvl();
	unsigned long s2tt[S2TTES_PER_S2TT];
	unsigned long pa = s2tt_test_helpers_gen_pa(level - 1L, true);
	unsigned long attrs = s2tt_test_helpers_gen_ns_attrs(true, false);
	s2tt_context s2tt_ctx = { 0UL };

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 is of use on this API, so
	 * the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();

	/* Generate a valid table */
	s2tt_init_assigned_ns((const struct s2tt_context *)&s2tt_ctx,
			      &s2tt[0U], attrs, pa, level);

	test_helpers_expect_assert_fail(true);
	(void)s2tt_maps_assigned_ns_block((const struct s2tt_context *)NULL,
					  &s2tt[0U], level);
	test_helpers_fail_if_no_assert_failed();
}

void s2tt_maps_assigned_destroyed_block_tc1(void)
{
	/***************************************************************
	 * TEST CASE 1:
	 *
	 * For each valid level, create an assigned destroyed block and
	 * validate that s2tt_maps_assigned_destroyed_block() returns
	 * the expected value
	 ***************************************************************/

	s2tt_context s2tt_ctx = { 0UL };

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 is of use on this API, so
	 * the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();

	for (long level = s2tt_test_helpers_min_block_lvl();
	     level <= S2TT_TEST_HELPERS_MAX_TABLE_LVL; level++) {

		unsigned long s2tt[S2TTES_PER_S2TT];
		unsigned long pa = s2tt_test_helpers_gen_pa(level - 1L, true);

		/* Generate the table */
		s2tt_init_assigned_destroyed(
				(const struct s2tt_context *)&s2tt_ctx,
				&s2tt[0U], pa, level);

		CHECK_TRUE(s2tt_maps_assigned_destroyed_block(
					(const struct s2tt_context *)&s2tt_ctx,
					&s2tt[0U], level));
	}
}

void s2tt_maps_assigned_destroyed_block_tc2(void)
{
	/***************************************************************
	 * TEST CASE 2:
	 *
	 * For each valid level, create an assigned destroyed block and
	 * then change a random TTE to a different type to validate
	 * that s2tt_maps_assigned_destroyed_block() returns the
	 * expected value
	 ***************************************************************/

	unsigned long unassigned_ripas[] = {S2TTE_INVALID_RIPAS_EMPTY,
					    S2TTE_INVALID_RIPAS_RAM,
					    S2TTE_NS,
					    S2TTE_INVALID_RIPAS_DESTROYED};
	unsigned long assigned_ripas[] = {S2TTE_INVALID_RIPAS_EMPTY,
					  S2TTE_NS,
					  S2TTE_INVALID_RIPAS_RAM};
	s2tt_context s2tt_ctx = { 0UL };

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 is of use on this API, so
	 * the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();

	for (long level = s2tt_test_helpers_min_block_lvl();
	     level <= S2TT_TEST_HELPERS_MAX_TABLE_LVL; level++) {

		unsigned int tte_idx =
			(unsigned int)test_helpers_get_rand_in_range(0UL,
					     S2TTES_PER_S2TT - 1UL);
		/* pickup a random type of unassigned S2TTE to test with */
		unsigned int idx =
			(unsigned int)test_helpers_get_rand_in_range(0UL,
					ARRAY_SIZE(unassigned_ripas) - 1UL);
		unsigned long s2tt[S2TTES_PER_S2TT];
		unsigned long pa = s2tt_test_helpers_gen_pa(level - 1L, true);

		/* Generate the table */
		s2tt_init_assigned_destroyed(
				(const struct s2tt_context *)&s2tt_ctx,
				&s2tt[0U], pa, level);

		/* Alter a random S2TTE on the table */
		s2tt[tte_idx] = s2tt_test_create_unassigned(
				(const struct s2tt_context *)&s2tt_ctx,
				unassigned_ripas[idx]);
		CHECK_FALSE(s2tt_maps_assigned_destroyed_block(
					(const struct s2tt_context *)&s2tt_ctx,
					&s2tt[0U], level));

		/* pickup a random type of assigned S2TTE to test with */
		idx = (unsigned int)test_helpers_get_rand_in_range(0UL,
					ARRAY_SIZE(assigned_ripas) - 1UL);

		/* Alter a random S2TTE on the table */
		s2tt[tte_idx] = s2tt_test_create_assigned(
				(const struct s2tt_context *)&s2tt_ctx,
				pa, level, assigned_ripas[idx]);
		CHECK_FALSE(s2tt_maps_assigned_destroyed_block(
					(const struct s2tt_context *)&s2tt_ctx,
					&s2tt[0U], level));
	}
}

void s2tt_maps_assigned_destroyed_block_tc3(void)
{
	/***************************************************************
	 * TEST CASE 3:
	 *
	 * Invoke s2tt_maps_assigned_destroyed_block() with the
	 * incorrect level.
	 ***************************************************************/

	long level = s2tt_test_helpers_min_block_lvl();
	unsigned long s2tt[S2TTES_PER_S2TT];
	unsigned long pa;
	s2tt_context s2tt_ctx = { 0UL };

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 is of use on this API, so
	 * the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();

	/*
	 * Get a PA aligned only to 'level' - 1 so we can spawn a table
	 * at level 'level' starting on that PA.
	 */
	pa = s2tt_test_helpers_gen_pa(level - 1L, true);

	/* Generate a valid table */
	s2tt_init_assigned_destroyed((const struct s2tt_context *)&s2tt_ctx,
				     &s2tt[0U], pa, level);

	CHECK_FALSE(s2tt_maps_assigned_destroyed_block(
				(const struct s2tt_context *)&s2tt_ctx,
				&s2tt[0U], level + 1L));
}

void s2tt_maps_assigned_destroyed_block_tc4(void)
{
	/***************************************************************
	 * TEST CASE 4:
	 *
	 * Invoke s2tt_maps_assigned_destroyed_block() with a valid
	 * level and a NULL table pointer.
	 ***************************************************************/

	long level = s2tt_test_helpers_min_block_lvl();
	s2tt_context s2tt_ctx = { 0UL };

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 is of use on this API, so
	 * the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();

	test_helpers_expect_assert_fail(true);
	(void)s2tt_maps_assigned_destroyed_block((
					const struct s2tt_context *)&s2tt_ctx,
					NULL, level);
	test_helpers_fail_if_no_assert_failed();
}

void s2tt_maps_assigned_destroyed_block_tc5(void)
{
	/***************************************************************
	 * TEST CASE 5:
	 *
	 * Invoke s2tt_maps_assigned_destroyed_block() with a level
	 * above the maximum allowed.
	 ***************************************************************/

	long level = S2TT_TEST_HELPERS_MAX_LVL;
	unsigned long s2tt[S2TTES_PER_S2TT];
	unsigned long pa = s2tt_test_helpers_gen_pa(level - 1L, true);
	s2tt_context s2tt_ctx = { 0UL };

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 is of use on this API, so
	 * the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();

	/* Generate a valid table */
	s2tt_init_assigned_destroyed((const struct s2tt_context *)&s2tt_ctx,
				     &s2tt[0U], pa, level);

	test_helpers_expect_assert_fail(true);
	(void)s2tt_maps_assigned_destroyed_block(
				(const struct s2tt_context *)&s2tt_ctx,
				&s2tt[0U], level + 1L);
	test_helpers_fail_if_no_assert_failed();
}

void s2tt_maps_assigned_destroyed_block_tc6(void)
{
	/***************************************************************
	 * TEST CASE 6:
	 *
	 * Invoke s2tt_maps_assigned_destroyed_block() with a level
	 * below the minimum allowed.
	 ***************************************************************/

	long level = s2tt_test_helpers_min_block_lvl();
	unsigned long s2tt[S2TTES_PER_S2TT];
	unsigned long pa = s2tt_test_helpers_gen_pa(level - 1L, true);
	s2tt_context s2tt_ctx = { 0UL };

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 is of use on this API, so
	 * the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();

	/* Generate a valid table */
	s2tt_init_assigned_destroyed((const struct s2tt_context *)&s2tt_ctx,
				     &s2tt[0U], pa, level);

	test_helpers_expect_assert_fail(true);
	level = s2tt_test_helpers_min_table_lvl() - 1L;
	(void)s2tt_maps_assigned_destroyed_block(
					(const struct s2tt_context *)&s2tt_ctx,
					&s2tt[0U], level);
	test_helpers_fail_if_no_assert_failed();
}

void s2tt_maps_assigned_destroyed_block_tc7(void)
{
	/***************************************************************
	 * TEST CASE 7:
	 *
	 * Invoke s2tt_maps_assigned_destroyed_block() with a NULL
	 * pointer to a s2tt_context structure.
	 ***************************************************************/

	long level = s2tt_test_helpers_min_block_lvl();
	unsigned long s2tt[S2TTES_PER_S2TT];
	unsigned long pa = s2tt_test_helpers_gen_pa(level - 1L, true);
	s2tt_context s2tt_ctx = { 0UL };

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 is of use on this API, so
	 * the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();

	/* Generate a valid table */
	s2tt_init_assigned_destroyed((const struct s2tt_context *)&s2tt_ctx,
				     &s2tt[0U], pa, level);

	test_helpers_expect_assert_fail(true);
	(void)s2tt_maps_assigned_destroyed_block(
					(const struct s2tt_context *)NULL,
					&s2tt[0U], level);
	test_helpers_fail_if_no_assert_failed();
}

/*
 * Ancillary function to generate a set of IPAs used to test
 * s2tt_skip_non_live_entries()
 *	- Arguments:
 *		iter: Iteration number. Used to know whether we are
 *		      generating a live S2TTE above, at or below
 *		      wi.index.
 *		wi: s2tt_walk structure to pass to s2tt_skip_non_live_entries().
 *		    wi.level needs to be setup up. The rest of the fields
 *		    are setup by this helper.
 *		tte_idx: Pointer where to store a random index above,
 *			 at or below wi.index, depending on 'iter' value.
 *		entry_ipa: Pointer were to store the IPA for the
 *			   'table_ipa[tte_idx]' entry.
 *		ipa: Pointer where to store a valid address for the
 *		     'table_ipa[wi.index]' block/page. It does not need
 *		     to be aligned to any given level. This address will
 *		     be feed to s2tt_skip_non_live_entries() to test.
 *
 *	- Returns: The expected address that should be returned by
 *		   s2tt_skip_non_live_entries() as per the given 'iter'
 *		   and generated set of IPAs.
 */
static unsigned long s2tt_skip_non_live_entries_gen_ipas(unsigned int iter,
						    struct s2tt_walk *wi,
						    unsigned int *tte_idx,
						    unsigned long *entry_ipa,
						    unsigned long *ipa)
{
	long level = wi->last_level;
	unsigned long table_ipa, next_stt_ipa;

	/*
	 * Initialize wi.index with a value
	 * in the middle range of the valid indexes
	 * Note that level -1 has only 16 entries.
	 */
	if (level == S2TT_TEST_HELPERS_MIN_LVL_LPA2) {
		wi->index = test_helpers_get_rand_in_range(5UL, 10UL);
	} else {
		wi->index = test_helpers_get_rand_in_range(100UL, 200UL);
	}

	switch (iter) {
	case 0U:
		/* Get a random index above wi.index */
		*tte_idx =
			(unsigned int)test_helpers_get_rand_in_range(
					wi->index + 1UL, S2TTES_PER_S2TT - 1UL);
		break;
	case 1U:
		/* Test index will be wi.index */
		*tte_idx = wi->index;
		break;
	case 2U:
		/* Get a random index below wi.index */
		*tte_idx = (unsigned int)test_helpers_get_rand_in_range(
						0UL, wi->index - 1UL);
		break;
	default:
		/* Not allowed */
		assert(false);
	}

	/*
	 * Get an IPA aligned @level - 1, so we would have a table
	 * @level starting at such IPA.
	 */
	table_ipa = s2tt_test_helpers_gen_pa(level - 1L, true);

	/*
	 * Calculate the IPA of the entry on the table
	 * indexed by tte_idx
	 */
	*entry_ipa = table_ipa + (s2tte_map_size(level) * (*tte_idx));

	/* Calculate the IPA for the next table */
	next_stt_ipa = table_ipa + (s2tte_map_size(level) * S2TTES_PER_S2TT);

	/* Calculate a non-aligned valid IPA at wi.index used to test */
	*ipa = table_ipa + (s2tte_map_size(level) * wi->index) +
				test_helpers_get_rand_in_range(1UL,
					s2tte_map_size(level) - 1UL);

	return ((iter == 0U) ? *entry_ipa :
		((iter == 1U) ? *ipa : next_stt_ipa));
}

typedef void(*init_unassigned_cb)(const struct s2tt_context *s2tt_ctx,
				  unsigned long *s2tt);

void s2tt_skip_non_live_entries_tc1(void)
{
	/***************************************************************
	 * TEST CASE 1:
	 *
	 * For every valid level, generate a set of tests for
	 * s2tt_skip_non_live_entries():
	 *	- Test with an unassigned entry/table with a live
	 *	  entry ABOVE wi.index.
	 *	- Test with an unassigned entry/table with the entry
	 *	  at possition wi.index being live.
	 *	- Test with an unassigned entry/table with a random
	 *	  live entry at a random index BELOW wi.index.
	 *	- Test with an unassigned entry/table with no live
	 *	  entries.
	 ***************************************************************/

	unsigned long ripas[] = {S2TTE_INVALID_RIPAS_EMPTY,
				 S2TTE_NS,
				 S2TTE_INVALID_RIPAS_RAM,
				 S2TTE_INVALID_RIPAS_DESTROYED};

	init_unassigned_cb init_unassigned_cbs[] = {
		s2tt_init_unassigned_empty,
		s2tt_init_unassigned_ns,
		s2tt_init_unassigned_ram,
		s2tt_init_unassigned_destroyed
	};
	s2tt_context s2tt_ctx = { 0UL };

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 is of use on this API, so
	 * the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();

	for (long level = s2tt_test_helpers_min_table_lvl();
	     level <= S2TT_TEST_HELPERS_MAX_LVL; level++) {

		unsigned long entry_ipa, ret_ipa, expected_ipa, ipa;
		unsigned long s2tt[S2TTES_PER_S2TT];
		unsigned int tte_idx, cb_idx = 0U;
		struct s2tt_walk wi = {
			NULL,  /* Not needed */
			0UL,
			level};

		for (unsigned int i = 0U; i < 3U; i++) {

			expected_ipa = s2tt_skip_non_live_entries_gen_ipas(
					i, &wi, &tte_idx, &entry_ipa, &ipa);

			if (level < s2tt_test_helpers_min_block_lvl()) {
				/* Table */

				/*
				 * Clear the s2tt so there are no valid
				 * table entries
				 */
				(void)memset((void *)&s2tt[0], 0, sizeof(s2tt));

				/* Generate a live entry at the random index */
				s2tt[tte_idx] =
					s2tte_create_table(
						(const struct s2tt_context *)&s2tt_ctx,
						entry_ipa, level);
			} else {
				/* Block or page */

				/*
				 * Generate an unassigned table of a random
				 * RIPAS type and add an assigned entry of a
				 * random RIPAS type at the random index.
				 */
				cb_idx = (unsigned int)test_helpers_get_rand_in_range(0UL,
						ARRAY_SIZE(init_unassigned_cbs) - 1UL);
				init_unassigned_cbs[cb_idx](
					(const struct s2tt_context *)&s2tt_ctx,
					&s2tt[0U]);

				cb_idx = (unsigned int)test_helpers_get_rand_in_range(0UL,
						ARRAY_SIZE(ripas) - 1UL);
				s2tt[tte_idx] =
					s2tt_test_create_assigned(
						(const struct s2tt_context *)&s2tt_ctx,
						entry_ipa, level, ripas[cb_idx]);
			}

			/* Validate s2tt_skip_non_live_entries() with current params */
			ret_ipa = s2tt_skip_non_live_entries(
					(const struct s2tt_context *)&s2tt_ctx,
					ipa, &s2tt[0U], &wi);
			CHECK_TRUE(expected_ipa == ret_ipa);
		} /* TEST ID */

		/*
		 * Test with a table without live entries. By recycling the
		 * arguments from the last test before this, we should also
		 * get the same results.
		 */
		if (level < s2tt_test_helpers_min_block_lvl()) {
			/* Table */
			(void)memset((void *)&s2tt[0], 0, sizeof(s2tt));
		} else {
			/* Block or Page */
			init_unassigned_cbs[cb_idx](
				(const struct s2tt_context *)&s2tt_ctx, &s2tt[0U]);
		}

		/* Validate s2tt_skip_non_live_entries() with current params */
		ret_ipa = s2tt_skip_non_live_entries(
				(const struct s2tt_context *)&s2tt_ctx,
				ipa, &s2tt[0U], &wi);
		UNSIGNED_LONGS_EQUAL(expected_ipa, ret_ipa);
	} /* LEVEL */
}

void s2tt_skip_non_live_entries_tc2(void)
{
	/***************************************************************
	 * TEST CASE 2:
	 *
	 * Call s2tt_skip_non_live_entries() with a NULL s2tt pointer.
	 ***************************************************************/

	struct s2tt_context s2tt_ctx = { 0UL };
	struct s2tt_walk wi = {
		NULL,  /* Not needed */
		0UL,
		0UL};

	/*
	 * Generate an s2tt context to be used for the test. Only
	 * enable_lpa2 field is needed for the current test.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();

	test_helpers_expect_assert_fail(true);
	(void)s2tt_skip_non_live_entries((const struct s2tt_context *)&s2tt_ctx,
					 0UL, NULL, &wi);
	test_helpers_fail_if_no_assert_failed();
}

void s2tt_skip_non_live_entries_tc3(void)
{
	/***************************************************************
	 * TEST CASE 3:
	 *
	 * Call s2tt_skip_non_live_entries() with a NULL s2tt_walk struct
	 * pointer.
	 ***************************************************************/

	unsigned long s2tt[S2TTES_PER_S2TT];
	struct s2tt_context s2tt_ctx = { 0UL };

	/*
	 * Generate an s2tt context to be used for the test. Only
	 * enable_lpa2 field is needed for the current test.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();

	test_helpers_expect_assert_fail(true);
	(void)s2tt_skip_non_live_entries((const struct s2tt_context *)&s2tt_ctx,
					 0UL, &s2tt[0U], NULL);
	test_helpers_fail_if_no_assert_failed();
}

void s2tt_skip_non_live_entries_tc4(void)
{
	/***************************************************************
	 * TEST CASE 4:
	 *
	 * Call s2tt_skip_non_live_entries() with a s2tt_walk struct in
	 * which the level is below the minimum allowed.
	 ***************************************************************/

	unsigned long s2tt[S2TTES_PER_S2TT];
	struct s2tt_context s2tt_ctx = { 0UL };
	struct s2tt_walk wi = {
		NULL,  /* Not needed */
		0UL,
		s2tt_test_helpers_min_table_lvl() - 1U};

	/*
	 * Generate an s2tt context to be used for the test. Only
	 * enable_lpa2 field is needed for the current test.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	test_helpers_expect_assert_fail(true);
	(void)s2tt_skip_non_live_entries((const struct s2tt_context *)&s2tt_ctx,
					 0UL, &s2tt[0U], &wi);
	test_helpers_fail_if_no_assert_failed();
}

void s2tt_skip_non_live_entries_tc5(void)
{
	/***************************************************************
	 * TEST CASE 5:
	 *
	 * Call s2tt_skip_non_live_entries() with a s2tt_walk struct in
	 * which the level is above the maximum allowed.
	 ***************************************************************/

	unsigned long s2tt[S2TTES_PER_S2TT];
	struct s2tt_context s2tt_ctx = { 0UL };
	struct s2tt_walk wi = {
		NULL,  /* Not needed */
		0UL,
		S2TT_TEST_HELPERS_MAX_LVL + 1U};

	/*
	 * Generate an s2tt context to be used for the test. Only
	 * enable_lpa2 field is needed for the current test.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	test_helpers_expect_assert_fail(true);
	(void)s2tt_skip_non_live_entries((const struct s2tt_context *)&s2tt_ctx,
					 0UL, &s2tt[0U], &wi);
	test_helpers_fail_if_no_assert_failed();
}

void s2tt_skip_non_live_entries_tc6(void)
{
	/***************************************************************
	 * TEST CASE 6:
	 *
	 * Call s2tt_skip_non_live_entries() with a s2tt_walk struct in
	 * which the index is above the maximum permitted
	 ***************************************************************/

	unsigned long s2tt[S2TTES_PER_S2TT];
	struct s2tt_context s2tt_ctx = { 0UL };
	struct s2tt_walk wi = {
		NULL,  /* Not needed */
		S2TTES_PER_S2TT + 1UL,
		s2tt_test_helpers_min_table_lvl()};

	/*
	 * Generate an s2tt context to be used for the test. Only
	 * enable_lpa2 field is needed for the current test.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	test_helpers_expect_assert_fail(true);
	(void)s2tt_skip_non_live_entries((const struct s2tt_context *)&s2tt_ctx,
					 0UL, &s2tt[0U], &wi);
	test_helpers_fail_if_no_assert_failed();
}

void s2tt_skip_non_live_entries_tc7(void)
{
	/***************************************************************
	 * TEST CASE 7:
	 *
	 * Call s2tt_skip_non_live_entries() with a NULL pointer to
	 * s2tt_context structure.
	 ***************************************************************/

	unsigned long s2tt[S2TTES_PER_S2TT];
	struct s2tt_walk wi = {
		NULL,  /* Not needed */
		0UL,
		s2tt_test_helpers_min_table_lvl()};

	test_helpers_expect_assert_fail(true);
	(void)s2tt_skip_non_live_entries((const struct s2tt_context *)NULL,
					 0UL, &s2tt[0U], &wi);
	test_helpers_fail_if_no_assert_failed();
}

/*
 * Ancillary function to populate a set of S2 translation tables given an IPA.
 *
 * Arguments:
 *	- ipa: IPA mapped to the translation table.
 *	- idx_per_lvl: Array used to store the indexes per level
 *		       used to walk the tables.
 *	- tables_per_lvl: Array used to store the address of the translation
 *			  tables per index.
 *	- end_lvl: Level at which the walk would finish. The SL is always
 *		   expected to be the lower level supported by the
 *		   architecture.
 *	- granules: Array used to store the pointers to the granule
 *		    structures corresponding to the 'tables_per_lvl' tables.
 *	- val_granule: Pointer to store the address of the expected
 *	               granule at the end of the walk.
 *	- granule_base: Address for the base granule where the SL table
 *			will be stored. The rest of the tables will be
 *			stored in subsequent granules.
 *	- str_granule_base: Pointer to the struct granule corresponding to
 *			    'granule_base'.
 *
 * This function creates a set of S2TTE_MAX_CONCAT_TABLES at the level after
 * the SL one so a set of concatenated tables at start level can be tested as
 * well. As an example, the layout of an array of granules corresponding to a
 * set of S2TTs spawning from level 0 to level 3 would be as follows:
 *
 *			 --------------------------
 *	str_granule_base | Level -1 S2TT          | (Unused on this example)
 *			 --------------------------
 *			 | Level 0 S2TT           |
 *			 -------------------------- ---
 *			 | 1st Level 1 S2TT       |    \
 *			 --------------------------     \
 *			 | 2nd Level 1 S2TT       |      \
 *			 --------------------------       \
 *			 | (...)                  |        | Concatenated tables
 *			 --------------------------       /
 *			 | 15th Level 1 S2TT      |      /
 *			 --------------------------     /
 *			 | 16th Level 1 S2T       |    /
 *                       -------------------------- ---
 *			 | Level 2 S2TT           |
 *                       --------------------------
 *			 | Level 3 S2TT           |
 *                       --------------------------
 *
 * It is the caller responsibility to ensure that all the arrays passed to this
 * function have enough space to store the translation tables as well as any
 * other outputs needed.
 *
 * Also note that when FEAT_LPA2 is available, the architectural minimum start
 * level supported by stage 2 lookup will be '-1', therefore an offset of one
 * possition will be added to all the indexes used to index the
 * *_per_lvl arrays to offset the negative value. For simplicity, the offset
 * will be applied even when FEAT_LPA2 is not available and the SL is '0'.
 */
static void populate_s2tts(struct s2tt_context *s2tt_ctx,
			   unsigned long ipa, unsigned long *idx_per_lvl,
			   unsigned long *tables_per_lvl, long end_lvl,
			   struct granule **granules,
			   struct granule **val_granule,
			   unsigned long granule_base,
			   struct granule *str_granule_base)
{
	long sl = s2tt_test_helpers_min_table_lvl();
	unsigned int next_granule;
	unsigned long child_pa;
	unsigned long *table;
	unsigned long *parent_table;
	long level;
	unsigned int n_granules = S2TTE_MAX_CONCAT_TABLES +
					(S2TT_TEST_HELPERS_MAX_LVL -
					 S2TT_TEST_HELPERS_MIN_LVL_LPA2 + 1U);

	/* Initialize the granules for the translaton tables */
	for (unsigned int i = 0U; i < n_granules; i++) {
		granules[i] = str_granule_base + i;
		granules[i]->state = GRANULE_STATE_RTT;
		granules[i]->lock.val = 0U;
	};

	/* Root granule must be locked. */
	next_granule = sl + 1L;
	granules[next_granule]->lock.val = 1U;

	/* Iterate over all the levels and generate the translatation tables */
	for (level = sl; level <= end_lvl; level++) {
		idx_per_lvl[level + 1L] =
			s2tt_test_helpers_get_idx_from_addr(ipa, level);

		if (level == sl) {
			/*
			 * Start Level. Get and initialize a table
			 * for this level.
			 */
			tables_per_lvl[level + 1L] = (granule_base +
					(GRANULE_SIZE * next_granule++));
			table = (unsigned long *)tables_per_lvl[level + 1L];
			(void)memset((void *)table, 0, GRANULE_SIZE);
		} else if (level == sl + 1L) {
			/*
			 * Level after the SL. This level will include the
			 * set of concatenated tables.
			 *
			 * At the SL, we will populate the first
			 * 'S2TTE_MAX_CONCAT_TABLES' entries to point to a
			 * table each, so we can use those tables as
			 * concatenated ones.
			 */
			parent_table = (unsigned long *)tables_per_lvl[level];

			/* Create the set of concatenated tables */
			for (unsigned int i = 0U;
			     i < S2TTE_MAX_CONCAT_TABLES; i++) {
				child_pa = (granule_base +
					(GRANULE_SIZE * next_granule++));
				parent_table[i] =
					s2tte_create_table(
						(const struct s2tt_context *)s2tt_ctx,
						child_pa, level);

				/* Clean this level tables */
				(void)memset((void *)child_pa, 0, GRANULE_SIZE);
			}

			/*
			 * Now there are S2TTE_MAX_CONCAT_TABLES concatenated
			 * tables on this level, of which only one will be used
			 * during the table walk. Get that table and assign it
			 * to the current level.
			 */
			tables_per_lvl[level + 1L] = (granule_base +
				((sl + 2 + idx_per_lvl[level]) * GRANULE_SIZE));
		} else if (level < S2TT_TEST_HELPERS_MAX_LVL) {
			/*
			 * Tables between the start level + 1 and the
			 * page level.
			 */
			parent_table = (unsigned long *)tables_per_lvl[level];

			/* Get, store and initialize the table on this level */
			child_pa = (granule_base +
					(GRANULE_SIZE * next_granule++));
			tables_per_lvl[level + 1L] = child_pa;
			(void)memset((void *)child_pa, 0, GRANULE_SIZE);

			/* And map the child table to the parent one */
			parent_table[idx_per_lvl[level]] =
					s2tte_create_table(
						(const struct s2tt_context *)s2tt_ctx,
						child_pa, level - 1L);
		} else {
			/* Page Level */
			parent_table = (unsigned long *)tables_per_lvl[level];

			/* Get, store and initialize the table on this level */
			child_pa = (granule_base +
					(GRANULE_SIZE * next_granule++));
			tables_per_lvl[level + 1L] = child_pa;

			/*
			 * Initialize the table as a page table
			 * We initialize as assigned-ram for no particular
			 * reason.
			 */
			table = (unsigned long *)child_pa;
			s2tt_init_assigned_ram((const struct s2tt_context *)s2tt_ctx,
				table, (ipa & s2tt_test_helpers_oa_mask(level)), level);

			/* And map the child table to the parent one */
			parent_table[idx_per_lvl[level]] =
					s2tte_create_table(
						(const struct s2tt_context *)s2tt_ctx,
						child_pa, level - 1L);
		}
	}

	/*
	 * Calculate the expected validation granule based on the last level
	 * keeping into account that the level after the start one has
	 * 'S2TTE_MAX_CONCAT_TABLES' tables allocated.
	 */
	*val_granule = granules[0U] + end_lvl + 1U;
	if (end_lvl == (sl + 1U)) {
		/* End Level is the level after the start one */
		*val_granule += s2tt_test_helpers_get_idx_from_addr(ipa, sl + 1L);
	} else if (level > (sl + 1U)) {
		/* End level is after the set of concatenated tables */
		*val_granule += (S2TTE_MAX_CONCAT_TABLES - 1U);
	}
}

void s2tt_walk_lock_unlock_tc1(void)
{
	/***************************************************************
	 * TEST CASE 1:
	 *
	 * Several positive tests:
	 *	- Generate a random mapping spawning from the minimum
	 *	  possible level to the maximum one and use
	 *	  s2tt_walk_lock_unlock() to walk the translation
	 *	  table and validate its output.
	 *	- Repeat the test above, but starting the walk at a
	 *	  level above the original starting level so to test
	 *	  the concatenated tables support.
	 *	- Repeat the two tests above, but finalising the walk
	 *	  at a level below the maximum one.
	 *	- Repeat the first two tests, but completing the tables
	 *	  up to a level below the maximum one and calling
	 *	  s2tt_walk_lock_unlock() with a level above the last
	 *	  one mapped on the translation tables.
	 *
	 * The level after the starting one will have
	 * S2TTE_MAX_CONCAT_TABLES concatenated granules so to test the
	 * concatenated starting levels.
	 ***************************************************************/

	long sl = s2tt_test_helpers_min_table_lvl();
	long end_level = S2TT_TEST_HELPERS_MAX_LVL;
	unsigned long pa, sl_index;
	unsigned long idx_per_lvl[end_level - S2TT_TEST_HELPERS_MIN_LVL_LPA2 + 1U];
	unsigned long tables_per_lvl[end_level - S2TT_TEST_HELPERS_MIN_LVL_LPA2 + 1U];
	struct s2tt_walk wi;
	struct granule *val_granule;
	struct s2tt_context s2tt_ctx = { 0UL };

	/* Total number of granules, included the concatenated ones */
	unsigned int granules = S2TTE_MAX_CONCAT_TABLES +
				(end_level - S2TT_TEST_HELPERS_MIN_LVL_LPA2 + 1U);

	/*
	 * Granules to hold the translation tables,
	 * including concatenated ones.
	 */
	struct granule *g_tables[granules];

	/*
	 * Generate a random address that spawns across the whole IPA size.
	 * The address doesn't need to have any alignment.
	 *
	 * As per the Arm ARM, the maximum number of concatenated tables
	 * at the start level of the S2 translation is
	 * S2TTE_MAX_CONCAT_TABLES, so create an address that does not
	 * exceed that index on the starting level.
	 */
	do {
		pa = test_helpers_get_rand_in_range(1UL,
						(1UL << arch_feat_get_pa_width()) - 1UL);
		sl_index = s2tt_test_helpers_get_idx_from_addr(pa, sl);
	} while (sl_index >= S2TTE_MAX_CONCAT_TABLES);

	/* Generate an s2tt context to be used for the test */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();

	populate_s2tts(&s2tt_ctx, pa, &idx_per_lvl[0U], &tables_per_lvl[0U],
		       end_level, &g_tables[0U], &val_granule,
		       host_util_get_granule_base(),
		       test_helpers_granule_struct_base());

	/* Finish the creation of the s2tt_context */
	s2tt_ctx.ipa_bits = arch_feat_get_pa_width();
	s2tt_ctx.s2_starting_level = sl;
	s2tt_ctx.g_rtt = g_tables[sl + 1UL];
	s2tt_ctx.num_root_rtts = 1U;

	/* Invoke s2tt_walk_lock_unlock() with the generated translation tables */
	s2tt_walk_lock_unlock((const struct s2tt_context *)&s2tt_ctx,
			      pa, end_level, &wi);

	LONGS_EQUAL(end_level, wi.last_level);
	CHECK_TRUE(val_granule == wi.g_llt);
	UNSIGNED_LONGS_EQUAL(idx_per_lvl[end_level + 1U], wi.index);

	for (unsigned int i = sl + 1U; i < granules; i++) {
		if (g_tables[i] == wi.g_llt) {
			/* Granule must be locked */
			CHECK_FALSE(wi.g_llt->lock.val == 0U);
		} else {
			/* Granule must be unlocked */
			CHECK_TRUE(g_tables[i]->lock.val == 0U);
		}
	}

	/*
	 * Repeat the test, but this time starting from the next level after
	 * the starting one, so we can test the concatenated tables.
	 */
	(void)memset(&wi, 0, sizeof(wi));

	/* Initialize the granules for the translaton tables */
	for (unsigned int i = 0U; i < granules; i++) {
		g_tables[i]->lock.val = 0U;
	};

	/*
	 * Root granule must be locked. In this case, the root granule is
	 * the granule after the minimum level one
	 */
	g_tables[sl + 2UL]->lock.val = 1U;

	/*
	 * Invoke s2tt_walk_lock_unlock() with the generated translation tables
	 * starting on the next starting level.
	 */
	s2tt_ctx.s2_starting_level = sl + 1L;
	s2tt_ctx.g_rtt = g_tables[sl + 2UL];
	s2tt_ctx.num_root_rtts = S2TTE_MAX_CONCAT_TABLES;

	s2tt_walk_lock_unlock((const struct s2tt_context *)&s2tt_ctx,
			      pa, end_level, &wi);

	LONGS_EQUAL(end_level, wi.last_level);
	CHECK_TRUE(val_granule == wi.g_llt);
	LONGS_EQUAL(idx_per_lvl[end_level + 1U], wi.index);

	for (unsigned int i = sl + 1U; i < granules; i++) {
		if (g_tables[i] == wi.g_llt) {
			/* Granule must be locked */
			CHECK_FALSE(wi.g_llt->lock.val == 0U);
		} else {
			/* Granule must be unlocked */
			CHECK_TRUE(g_tables[i]->lock.val == 0U);
		}
	}

	/*
	 * Repeat both the tests above, but this time finilizing the walk
	 * a level below the maximum one. Reuse the structures initialized
	 * on the test before.
	 */
	(void)memset(&wi, 0, sizeof(wi));

	/* Initialize the granules for the translaton tables */
	for (unsigned int i = 0U; i < granules; i++) {
		g_tables[i]->lock.val = 0U;
	};

	/* Root granule must be locked */
	g_tables[sl + 1]->lock.val = 1U;

	s2tt_ctx.s2_starting_level = sl;
	s2tt_ctx.g_rtt = g_tables[sl + 1UL];
	s2tt_ctx.num_root_rtts = 1U;

	s2tt_walk_lock_unlock((const struct s2tt_context *)&s2tt_ctx,
			      pa, end_level - 1L, &wi);

	/* Update the expected end_level and validation granule */
	end_level--;
	val_granule--;

	LONGS_EQUAL(end_level, wi.last_level);
	CHECK_TRUE(val_granule == wi.g_llt);
	LONGS_EQUAL(idx_per_lvl[end_level + 1U], wi.index);

	for (unsigned int i = sl + 1U; i < granules; i++) {
		if (g_tables[i] == wi.g_llt) {
			/* Granule must be locked */
			CHECK_FALSE(wi.g_llt->lock.val == 0U);
		} else {
			/* Granule must be unlocked */
			CHECK_TRUE(g_tables[i]->lock.val == 0U);
		}
	}

	/*
	 * Repeat the test, but this time starting from the next level after
	 * the starting one, so we can test the concatenated tables.
	 */
	(void)memset(&wi, 0, sizeof(wi));

	/* Initialize the granules for the translaton tables */
	for (unsigned int i = 0U; i < granules; i++) {
		g_tables[i]->lock.val = 0U;
	};

	/* Update the expected end_level and validation granule */
	end_level++;
	val_granule++;

	/* Root granule must be locked */
	g_tables[sl + 2L]->lock.val = 1U;

	/*
	 * Invoke s2tt_walk_lock_unlock() with the generated translation tables
	 * starting on the next starting level.
	 */
	s2tt_ctx.s2_starting_level = sl + 1L;
	s2tt_ctx.g_rtt = g_tables[sl + 2UL];
	s2tt_ctx.num_root_rtts = S2TTE_MAX_CONCAT_TABLES;

	s2tt_walk_lock_unlock((const struct s2tt_context *)&s2tt_ctx,
			      pa, end_level, &wi);

	LONGS_EQUAL(end_level, wi.last_level);
	CHECK_TRUE(val_granule == wi.g_llt);
	LONGS_EQUAL(idx_per_lvl[end_level + 1U], wi.index);

	for (unsigned int i = sl + 1U; i < granules; i++) {
		if (g_tables[i] == wi.g_llt) {
			/* Granule must be locked */
			CHECK_FALSE(wi.g_llt->lock.val == 0U);
		} else {
			/* Granule must be unlocked */
			CHECK_TRUE(g_tables[i]->lock.val == 0U);
		}
	}

	/*
	 * Repeat the two first tests, but this time the mapping will
	 * be finalizing a level below the maximum one and
	 * s2tt_walk_lock_unlock() will be called to walk up to the
	 * maximum level.
	 */
	end_level = S2TT_TEST_HELPERS_MAX_LVL;
	(void)memset(&wi, 0, sizeof(wi));

	populate_s2tts(&s2tt_ctx, pa, &idx_per_lvl[0U], &tables_per_lvl[0U],
		       end_level - 1L, &g_tables[0U], &val_granule,
		       host_util_get_granule_base(),
		       test_helpers_granule_struct_base());

	s2tt_ctx.s2_starting_level = sl;
	s2tt_ctx.g_rtt = g_tables[sl + 1UL];
	s2tt_ctx.num_root_rtts = 1;

	s2tt_walk_lock_unlock((const struct s2tt_context *)&s2tt_ctx,
			     pa, end_level, &wi);

	LONGS_EQUAL((end_level - 1L), wi.last_level);
	CHECK_TRUE(val_granule == wi.g_llt);
	LONGS_EQUAL(idx_per_lvl[end_level], wi.index);

	for (unsigned int i = sl + 1U; i < granules; i++) {
		if (g_tables[i] == wi.g_llt) {
			/* Granule must be locked */
			CHECK_FALSE(wi.g_llt->lock.val == 0U);
		} else {
			/* Granule must be unlocked */
			CHECK_TRUE(g_tables[i]->lock.val == 0U);
		}
	}

	/*
	 * Repeat the test, but this time starting from the next level after
	 * the starting one, so we can test the concatenated tables.
	 */
	(void)memset(&wi, 0, sizeof(wi));

	/* Initialize the granules for the translaton tables */
	for (unsigned int i = 0U; i < granules; i++) {
		g_tables[i]->lock.val = 0U;
	};

	/* Root granule must be locked */
	g_tables[sl + 2U]->lock.val = 1U;

	/*
	 * Invoke s2tt_walk_lock_unlock() with the generated translation tables
	 * starting on the next starting level.
	 */
	s2tt_ctx.s2_starting_level = sl + 1L;
	s2tt_ctx.g_rtt = g_tables[sl + 2UL];
	s2tt_ctx.num_root_rtts = S2TTE_MAX_CONCAT_TABLES;

	s2tt_walk_lock_unlock((const struct s2tt_context *)&s2tt_ctx,
			     pa, end_level, &wi);

	LONGS_EQUAL((end_level - 1L), wi.last_level);
	CHECK_TRUE(val_granule == wi.g_llt);
	LONGS_EQUAL(idx_per_lvl[end_level], wi.index);

	for (unsigned int i = sl + 1U; i < granules; i++) {
		if (g_tables[i] == wi.g_llt) {
			/* Granule must be locked */
			CHECK_FALSE(wi.g_llt->lock.val == 0U);
		} else {
			/* Granule must be unlocked */
			CHECK_TRUE(g_tables[i]->lock.val == 0U);
		}
	}
}

void s2tt_walk_lock_unlock_tc2(void)
{
	/***************************************************************
	 * TEST CASE 2:
	 *
	 * Test s2tt_walk_lock_unlock() with a set of tables in wich
	 * the granule of one of them is not set to 'GRANULE_STATE_RTT'
	 ***************************************************************/

	long sl = s2tt_test_helpers_min_table_lvl();
	long end_level = S2TT_TEST_HELPERS_MAX_LVL;
	unsigned long pa;
	unsigned long sl_index;
	unsigned long idx_per_lvl[end_level - S2TT_TEST_HELPERS_MIN_LVL_LPA2 + 1U];
	unsigned long tables_per_lvl[end_level - S2TT_TEST_HELPERS_MIN_LVL_LPA2 + 1U];
	struct s2tt_walk wi;
	struct granule *val_granule;
	struct s2tt_context s2tt_ctx;

	/* Total number of granules, included the concatenated ones */
	unsigned int granules = S2TTE_MAX_CONCAT_TABLES +
				(end_level - S2TT_TEST_HELPERS_MIN_LVL_LPA2 + 1U);

	/*
	 * Granules to hold the translation tables,
	 * including concatenated ones.
	 */
	struct granule *g_tables[granules];

	/*
	 * Generate a random address that spawns across the whole IPA size.
	 * The address doesn't need to have any alignment.
	 *
	 * As per the Arm ARM, the maximum number of concatenated tables
	 * on the start level of the S2 translation is 16, so create an
	 * address that does not exceed that index on the starting level.
	 * We don't need to test concatenated tables here, but accounting
	 * for them will help to make the tests consistent.
	 */
	do {
		pa = test_helpers_get_rand_in_range(1UL,
						(1UL << arch_feat_get_pa_width()) - 1UL);
		sl_index = s2tt_test_helpers_get_idx_from_addr(pa, sl);
	} while (sl_index >= S2TTE_MAX_CONCAT_TABLES);

	/* Generate an s2tt context to be used for the test */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	populate_s2tts(&s2tt_ctx, pa, &idx_per_lvl[0U], &tables_per_lvl[0U],
		       end_level, &g_tables[0U], &val_granule,
		       host_util_get_granule_base(),
		       test_helpers_granule_struct_base());

	/* Finish the creation of the s2tt_context */
	s2tt_ctx.ipa_bits = arch_feat_get_pa_width();
	s2tt_ctx.s2_starting_level = sl;
	s2tt_ctx.g_rtt = g_tables[sl + 1UL];
	s2tt_ctx.num_root_rtts = 1U;

	/*
	 * Change the granule state for an arbitrary level. In this case, we
	 * choose Level 2 for simplicity and convenience. The new granule
	 * state is also chosen arbitrarily.
	 *
	 * Note that index '0' corresponds to level '-1' and one of the
	 * intermediate levels (the level after the starting one) has
	 * 'S2TTE_MAX_CONCAT_TABLES' tables.
	 */
	g_tables[3U + S2TTE_MAX_CONCAT_TABLES]->state = GRANULE_STATE_RD;

	/* The call should cause an assertion failure */
	test_helpers_expect_assert_fail(true);
	s2tt_walk_lock_unlock((const struct s2tt_context *)&s2tt_ctx,
			      pa, end_level, &wi);
	test_helpers_fail_if_no_assert_failed();
}

void s2tt_walk_lock_unlock_tc3(void)
{
	/***************************************************************
	 * TEST CASE 3:
	 *
	 * Test s2tt_walk_lock_unlock() with a set of tables in wich
	 * one of the granules is already locked.
	 ***************************************************************/

	long sl = s2tt_test_helpers_min_table_lvl();
	long end_level = S2TT_TEST_HELPERS_MAX_LVL;
	unsigned long pa;
	unsigned long idx_per_lvl[end_level - S2TT_TEST_HELPERS_MIN_LVL_LPA2 + 1U];
	unsigned long tables_per_lvl[end_level - S2TT_TEST_HELPERS_MIN_LVL_LPA2 + 1U];
	struct s2tt_walk wi;
	struct granule *val_granule;
	struct s2tt_context s2tt_ctx;

	/* Total number of granules, included the concatenated ones */
	unsigned int granules = S2TTE_MAX_CONCAT_TABLES +
				(end_level - S2TT_TEST_HELPERS_MIN_LVL_LPA2 + 1U);

	/*
	 * Granules to hold the translation tables,
	 * including concatenated ones.
	 */
	struct granule *g_tables[granules];

	/* Generate an s2tt context to be used for the test */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();

	pa = 0UL; /* Valid on any level */
	populate_s2tts(&s2tt_ctx, pa, &idx_per_lvl[0U], &tables_per_lvl[0U],
		       end_level, &g_tables[0U], &val_granule,
		       host_util_get_granule_base(),
		       test_helpers_granule_struct_base());

	/* Finish the creation of the s2tt_context */
	s2tt_ctx.ipa_bits = arch_feat_get_pa_width();
	s2tt_ctx.s2_starting_level = sl;
	s2tt_ctx.g_rtt = g_tables[sl + 1UL];
	s2tt_ctx.num_root_rtts = 1U;

	/*
	 * Lock the granule of an arbitrary level. In this case, we
	 * choose Level 2 for simplicity and convenience.
	 *
	 * Note that index '0' corresponds to level '-1' and one of the
	 * intermediate levels (the level after the starting one) has
	 * 'S2TTE_MAX_CONCAT_TABLES' tables.
	 */
	g_tables[3U + S2TTE_MAX_CONCAT_TABLES]->lock.val = 1U;

	/* The call should cause an assertion failure */
	test_helpers_expect_assert_fail(true);
	s2tt_walk_lock_unlock((const struct s2tt_context *)&s2tt_ctx,
			      pa, end_level, &wi);
	test_helpers_fail_if_no_assert_failed();
}

void s2tt_walk_lock_unlock_tc4(void)
{
	/***************************************************************
	 * TEST CASE 4:
	 *
	 * Test s2tt_walk_lock_unlock() with a null array of granules.
	 ***************************************************************/

	long sl = s2tt_test_helpers_min_table_lvl();
	long end_level = S2TT_TEST_HELPERS_MAX_LVL;
	unsigned long pa;
	struct s2tt_walk wi;
	struct s2tt_context s2tt_ctx;

	pa = 0UL;

	/* Generate an s2tt context to be used for the test */
	s2tt_ctx.ipa_bits = arch_feat_get_pa_width();
	s2tt_ctx.s2_starting_level = sl;
	s2tt_ctx.g_rtt = NULL;
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.num_root_rtts = 1U;

	/* The call should cause an assertion failure */
	test_helpers_expect_assert_fail(true);
	s2tt_walk_lock_unlock((const struct s2tt_context *)&s2tt_ctx,
			      pa, end_level, &wi);
	test_helpers_fail_if_no_assert_failed();
}

void s2tt_walk_lock_unlock_tc5(void)
{
	/***************************************************************
	 * TEST CASE 5:
	 *
	 * Test s2tt_walk_lock_unlock() with a null s2tt_walk structure.
	 ***************************************************************/

	long sl = s2tt_test_helpers_min_table_lvl();
	long end_level = S2TT_TEST_HELPERS_MAX_LVL;
	unsigned long pa;
	unsigned long idx_per_lvl[end_level - S2TT_TEST_HELPERS_MIN_LVL_LPA2 + 1U];
	unsigned long tables_per_lvl[end_level - S2TT_TEST_HELPERS_MIN_LVL_LPA2 + 1U];
	struct granule *val_granule;
	struct s2tt_context s2tt_ctx;

	/* Total number of granules, included the concatenated ones */
	unsigned int granules = S2TTE_MAX_CONCAT_TABLES +
				(end_level - S2TT_TEST_HELPERS_MIN_LVL_LPA2 + 1U);

	/*
	 * Granules to hold the translation tables,
	 * including concatenated ones.
	 */
	struct granule *g_tables[granules];

	/* Generate an s2tt context to be used for the test */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();

	pa = 0UL; /* Valid on any level */
	populate_s2tts(&s2tt_ctx, pa, &idx_per_lvl[0U], &tables_per_lvl[0U],
		       end_level, &g_tables[0U], &val_granule,
		       host_util_get_granule_base(),
		       test_helpers_granule_struct_base());

	/* Finish the creation of the s2tt_context */
	s2tt_ctx.ipa_bits = arch_feat_get_pa_width();
	s2tt_ctx.s2_starting_level = sl;
	s2tt_ctx.g_rtt = NULL;
	s2tt_ctx.num_root_rtts = 1U;

	/* The call should cause an assertion failure */
	test_helpers_expect_assert_fail(true);
	s2tt_walk_lock_unlock((const struct s2tt_context *)&s2tt_ctx,
			      pa, end_level, NULL);
	test_helpers_fail_if_no_assert_failed();
}

void s2tt_walk_lock_unlock_tc6(void)
{
	/***************************************************************
	 * TEST CASE 6:
	 *
	 * Test s2tt_walk_lock_unlock() with a start level below the
	 * minimum permitted.
	 ***************************************************************/

	long sl = s2tt_test_helpers_min_table_lvl();
	long end_level = S2TT_TEST_HELPERS_MAX_LVL;
	unsigned long pa;
	unsigned long idx_per_lvl[end_level - S2TT_TEST_HELPERS_MIN_LVL_LPA2 + 1U];
	unsigned long tables_per_lvl[end_level - S2TT_TEST_HELPERS_MIN_LVL_LPA2 + 1U];
	struct s2tt_walk wi;
	struct granule *val_granule;
	struct s2tt_context s2tt_ctx;

	/* Total number of granules, included the concatenated ones */
	unsigned int granules = S2TTE_MAX_CONCAT_TABLES +
				(end_level - S2TT_TEST_HELPERS_MIN_LVL_LPA2 + 1U);

	/*
	 * Granules to hold the translation tables,
	 * including concatenated ones.
	 */
	struct granule *g_tables[granules];

	/* Generate an s2tt context to be used for the test */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();

	pa = 0UL; /* Valid on any level */
	populate_s2tts(&s2tt_ctx, pa, &idx_per_lvl[0U], &tables_per_lvl[0U],
		       end_level, &g_tables[0U], &val_granule,
		       host_util_get_granule_base(),
		       test_helpers_granule_struct_base());

	/* Finish the creation of the s2tt_context */
	s2tt_ctx.ipa_bits = arch_feat_get_pa_width();
	s2tt_ctx.s2_starting_level = sl - 1L;
	s2tt_ctx.g_rtt = g_tables[sl + 1U];
	s2tt_ctx.num_root_rtts = 1U;

	/* The call should cause an assertion failure */
	test_helpers_expect_assert_fail(true);
	s2tt_walk_lock_unlock((const struct s2tt_context *)&s2tt_ctx,
			      pa, end_level, &wi);
	test_helpers_fail_if_no_assert_failed();
}

void s2tt_walk_lock_unlock_tc7(void)
{
	/***************************************************************
	 * TEST CASE 7:
	 *
	 * Test s2tt_walk_lock_unlock() with a start level above the
	 * maximum permitted.
	 ***************************************************************/

	long sl = s2tt_test_helpers_min_table_lvl();
	long end_level = S2TT_TEST_HELPERS_MAX_LVL;
	unsigned long pa;
	unsigned long idx_per_lvl[end_level - S2TT_TEST_HELPERS_MIN_LVL_LPA2 + 1U];
	unsigned long tables_per_lvl[end_level - S2TT_TEST_HELPERS_MIN_LVL_LPA2 + 1U];
	struct s2tt_walk wi;
	struct granule *val_granule;
	struct s2tt_context s2tt_ctx;

	/* Total number of granules, included the concatenated ones */
	unsigned int granules = S2TTE_MAX_CONCAT_TABLES +
				(end_level - S2TT_TEST_HELPERS_MIN_LVL_LPA2);

	/*
	 * Granules to hold the translation tables,
	 * including concatenated ones.
	 */
	struct granule *g_tables[granules];

	/* Generate an s2tt context to be used for the test */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();

	pa = 0UL; /* Valid on any level */
	populate_s2tts(&s2tt_ctx, pa, &idx_per_lvl[0U], &tables_per_lvl[0U],
		       end_level, &g_tables[0U], &val_granule,
		       host_util_get_granule_base(),
		       test_helpers_granule_struct_base());

	/* Finish the creation of the s2tt_context */
	s2tt_ctx.ipa_bits = arch_feat_get_pa_width();
	s2tt_ctx.s2_starting_level = end_level +  1L;
	s2tt_ctx.g_rtt = g_tables[sl + 1U];
	s2tt_ctx.num_root_rtts = 1U;

	/* The call should cause an assertion failure */
	test_helpers_expect_assert_fail(true);
	s2tt_walk_lock_unlock((const struct s2tt_context *)&s2tt_ctx,
			      pa, end_level, &wi);
	test_helpers_fail_if_no_assert_failed();
}

void s2tt_walk_lock_unlock_tc8(void)
{
	/***************************************************************
	 * TEST CASE 8:
	 *
	 * Test s2tt_walk_lock_unlock() with a walk end level below the
	 * start level.
	 ***************************************************************/

	long sl = s2tt_test_helpers_min_table_lvl();
	long end_level = S2TT_TEST_HELPERS_MAX_LVL;
	unsigned long pa;
	unsigned long idx_per_lvl[end_level - S2TT_TEST_HELPERS_MIN_LVL_LPA2 + 1U];
	unsigned long tables_per_lvl[end_level - S2TT_TEST_HELPERS_MIN_LVL_LPA2 + 1U];
	struct s2tt_walk wi;
	struct granule *val_granule;
	struct s2tt_context s2tt_ctx;

	/* Total number of granules, included the concatenated ones */
	unsigned int granules = S2TTE_MAX_CONCAT_TABLES +
				(end_level - S2TT_TEST_HELPERS_MIN_LVL_LPA2 + 1U);

	/*
	 * Granules to hold the translation tables,
	 * including concatenated ones.
	 */
	struct granule *g_tables[granules];

	/* Generate an s2tt context to be used for the test */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();

	pa = 0UL; /* Valid on any level */
	populate_s2tts(&s2tt_ctx, pa, &idx_per_lvl[0U], &tables_per_lvl[0U],
		       end_level, &g_tables[0U], &val_granule,
		       host_util_get_granule_base(),
		       test_helpers_granule_struct_base());

	/* Finish the creation of the s2tt_context */
	s2tt_ctx.ipa_bits = arch_feat_get_pa_width();
	s2tt_ctx.s2_starting_level = sl;
	s2tt_ctx.g_rtt = g_tables[sl + 1U];
	s2tt_ctx.num_root_rtts = 1U;

	/* The call should cause an assertion failure */
	test_helpers_expect_assert_fail(true);
	s2tt_walk_lock_unlock((const struct s2tt_context *)&s2tt_ctx,
			      pa, sl - 1U, &wi);
	test_helpers_fail_if_no_assert_failed();
}

void s2tt_walk_lock_unlock_tc9(void)
{
	/***************************************************************
	 * TEST CASE 9:
	 *
	 * Test s2tt_walk_lock_unlock() with an end walk level above the
	 * maximum permitted.
	 ***************************************************************/

	long sl = s2tt_test_helpers_min_table_lvl();
	long end_level = S2TT_TEST_HELPERS_MAX_LVL;
	unsigned long pa;
	unsigned long idx_per_lvl[end_level - S2TT_TEST_HELPERS_MIN_LVL_LPA2 + 1U];
	unsigned long tables_per_lvl[end_level - S2TT_TEST_HELPERS_MIN_LVL_LPA2 + 1U];
	struct s2tt_walk wi;
	struct granule *val_granule;
	struct s2tt_context s2tt_ctx;

	/* Total number of granules, included the concatenated ones */
	unsigned int granules = S2TTE_MAX_CONCAT_TABLES +
				(end_level - S2TT_TEST_HELPERS_MIN_LVL_LPA2 + 1U);

	/*
	 * Granules to hold the translation tables,
	 * including concatenated ones.
	 */
	struct granule *g_tables[granules];

	/* Generate an s2tt context to be used for the test */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();

	pa = 0UL; /* Valid on any level */
	populate_s2tts(&s2tt_ctx, pa, &idx_per_lvl[0U], &tables_per_lvl[0U],
		       end_level, &g_tables[0U], &val_granule,
		       host_util_get_granule_base(),
		       test_helpers_granule_struct_base());

	/* Finish the creation of the s2tt_context */
	s2tt_ctx.ipa_bits = arch_feat_get_pa_width();
	s2tt_ctx.s2_starting_level = sl;
	s2tt_ctx.g_rtt = g_tables[sl + 1U];
	s2tt_ctx.num_root_rtts = 1U;

	/* The call should cause an assertion failure */
	test_helpers_expect_assert_fail(true);
	s2tt_walk_lock_unlock((const struct s2tt_context *)&s2tt_ctx,
			      pa, end_level + 1, &wi);
	test_helpers_fail_if_no_assert_failed();
}

void s2tt_walk_lock_unlock_tc10(void)
{
	/***************************************************************
	 * TEST CASE 10:
	 *
	 * Test s2tt_walk_lock_unlock() with a PA above the maximum
	 * supported IPA size.
	 ***************************************************************/

	long sl = s2tt_test_helpers_min_table_lvl();
	long end_level = S2TT_TEST_HELPERS_MAX_LVL;
	unsigned long pa;
	unsigned long idx_per_lvl[end_level - S2TT_TEST_HELPERS_MIN_LVL_LPA2 + 1U];
	unsigned long tables_per_lvl[end_level - S2TT_TEST_HELPERS_MIN_LVL_LPA2 + 1U];
	struct s2tt_walk wi;
	struct granule *val_granule;
	s2tt_context s2tt_ctx;

	/* Total number of granules, included the concatenated ones */
	unsigned int granules = S2TTE_MAX_CONCAT_TABLES +
		(end_level - S2TT_TEST_HELPERS_MIN_LVL_LPA2 + 1U);

	/*
	 * Granules to hold the translation tables,
	 * including concatenated ones.
	 */
	struct granule *g_tables[granules];

	/* Generate an s2tt context to be used for the test */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();

	pa = 0UL; /* Valid on any level */

	populate_s2tts(&s2tt_ctx, pa, &idx_per_lvl[0U], &tables_per_lvl[0U],
		       end_level, &g_tables[0U], &val_granule,
		       host_util_get_granule_base(),
		       test_helpers_granule_struct_base());

	/* Finish the creation of the s2tt_context */
	s2tt_ctx.ipa_bits = arch_feat_get_pa_width();
	s2tt_ctx.s2_starting_level = sl;
	s2tt_ctx.g_rtt = g_tables[sl + 1U];
	s2tt_ctx.num_root_rtts = 1U;

	/* Generate an address larger than the maximum allowable size */
	pa = 1UL << s2tt_ctx.ipa_bits;

	/* The call should cause an assertion failure */
	test_helpers_expect_assert_fail(true);
	s2tt_walk_lock_unlock((const struct s2tt_context *)&s2tt_ctx,
			      pa, end_level, &wi);
	test_helpers_fail_if_no_assert_failed();
}

void s2tt_walk_lock_unlock_tc11(void)
{
	/***************************************************************
	 * TEST CASE 11:
	 *
	 * Test s2tt_walk_lock_unlock() with an invalid max ipa size.
	 ***************************************************************/

	long sl = s2tt_test_helpers_min_table_lvl();
	long end_level = S2TT_TEST_HELPERS_MAX_LVL;
	unsigned long pa;
	unsigned long idx_per_lvl[end_level - S2TT_TEST_HELPERS_MIN_LVL_LPA2 + 1U];
	unsigned long tables_per_lvl[end_level - S2TT_TEST_HELPERS_MIN_LVL_LPA2 + 1U];
	struct s2tt_walk wi;
	struct granule *val_granule;
	struct s2tt_context s2tt_ctx;

	/* Total number of granules, included the concatenated ones */
	unsigned int granules = S2TTE_MAX_CONCAT_TABLES +
				(end_level - S2TT_TEST_HELPERS_MIN_LVL_LPA2 + 1U);

	/*
	 * Granules to hold the translation tables,
	 * including concatenated ones.
	 */
	struct granule *g_tables[granules];

	/* Generate an s2tt context to be used for the test */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();

	pa = 0UL; /* Valid on any level */

	populate_s2tts(&s2tt_ctx, pa, &idx_per_lvl[0U], &tables_per_lvl[0U],
		       end_level, &g_tables[0U], &val_granule,
		       host_util_get_granule_base(),
		       test_helpers_granule_struct_base());

	/* Finish the creation of the s2tt_context */
	s2tt_ctx.ipa_bits = arch_feat_get_pa_width() + 1UL;
	s2tt_ctx.s2_starting_level = sl;
	s2tt_ctx.g_rtt = g_tables[sl + 1U];
	s2tt_ctx.num_root_rtts = 1U;

	/* The call should cause an assertion failure */
	test_helpers_expect_assert_fail(true);
	s2tt_walk_lock_unlock((const struct s2tt_context *)&s2tt_ctx,
			      pa, end_level, &wi);
	test_helpers_fail_if_no_assert_failed();
}

void s2tt_walk_lock_unlock_tc12(void)
{
	/***************************************************************
	 * TEST CASE 12:
	 *
	 * Test s2tt_walk_lock_unlock() with a combination of first
	 * look-up level and root tables in which the number of
	 * concatenated tables would result larger than the maximum
	 * permitted.
	 ***************************************************************/

	long sl = s2tt_test_helpers_min_table_lvl();
	long end_level = S2TT_TEST_HELPERS_MAX_LVL;
	unsigned long pa;
	unsigned long sl_index;
	unsigned long idx_per_lvl[end_level - S2TT_TEST_HELPERS_MIN_LVL_LPA2 + 1U];
	unsigned long tables_per_lvl[end_level - S2TT_TEST_HELPERS_MIN_LVL_LPA2 + 1U];
	struct s2tt_walk wi;
	struct granule *val_granule;
	struct s2tt_context s2tt_ctx;

	/* Total number of granules, included the concatenated ones */
	unsigned int granules = S2TTE_MAX_CONCAT_TABLES +
				(end_level - S2TT_TEST_HELPERS_MIN_LVL_LPA2 + 1U);

	/*
	 * Granules to hold the translation tables,
	 * including concatenated ones.
	 */
	struct granule *g_tables[granules];

	/*
	 * Generate a random address that spawns across the whole IPA size.
	 * The address doesn't need to have any alignment.
	 *
	 * As per the Arm ARM, the maximum number of concatenated tables
	 * on the start level of the S2 translation is 16, so create an
	 * address such the number of "concatenated tables" two levels
	 * above the starting one would suppass the maximum allowable.
	 */
	do {
		pa = test_helpers_get_rand_in_range(1UL,
						(1UL << arch_feat_get_pa_width()) - 1UL);
		sl_index = s2tt_test_helpers_get_idx_from_addr(pa, sl) *
			   s2tt_test_helpers_get_idx_from_addr(pa, sl + 1L);
	} while (sl_index <= S2TTE_MAX_CONCAT_TABLES);

	/* Generate an s2tt context to be used for the test */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();

	populate_s2tts(&s2tt_ctx, pa, &idx_per_lvl[0U], &tables_per_lvl[0U],
		       end_level, &g_tables[0U], &val_granule,
		       host_util_get_granule_base(),
		       test_helpers_granule_struct_base());

	/* Finish the creation of the s2tt_context */
	s2tt_ctx.ipa_bits = arch_feat_get_pa_width();
	s2tt_ctx.s2_starting_level = sl + 2L;
	s2tt_ctx.g_rtt = g_tables[sl + 2U];
	s2tt_ctx.num_root_rtts = S2TTE_MAX_CONCAT_TABLES;

	/* The call should cause an assertion failure */
	test_helpers_expect_assert_fail(true);
	s2tt_walk_lock_unlock((const struct s2tt_context *)&s2tt_ctx,
			      pa, end_level, &wi);
	test_helpers_fail_if_no_assert_failed();
}

void s2tt_walk_lock_unlock_tc13(void)
{
	/***************************************************************
	 * TEST CASE 13:
	 *
	 * Test s2tt_walk_lock_unlock() with a null s2tt_context.
	 ***************************************************************/

	long end_level = S2TT_TEST_HELPERS_MAX_LVL;
	unsigned long pa;
	struct s2tt_walk wi;

	pa = 0UL;

	/* The call should cause an assertion failure */
	test_helpers_expect_assert_fail(true);
	s2tt_walk_lock_unlock((const struct s2tt_context *)NULL,
			      pa, end_level, &wi);
	test_helpers_fail_if_no_assert_failed();
}
