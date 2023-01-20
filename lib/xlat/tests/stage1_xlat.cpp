/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <CppUTest/CommandLineTestRunner.h>
#include <CppUTest/TestHarness.h>

extern "C" {
#include <arch_helpers.h>
#include <host_utils.h>
#include <st1_xlat_test_defs.h>
#include <st1_xlat_test_helpers.h>
#include <stdlib.h>
#include <string.h>
#include <test_helpers.h>
#include <utils_def.h>
#include <xlat_contexts.h>	/* API to test */
#include <xlat_defs.h>
#include <xlat_tables.h>	/* API to test */
}

/* Maximum number of tables to use on tests */
#define STAGE1_XLAT_TEST_MAX_TABLES	(10U)

/* Maximum number of mmap regions to use on tests */
#define STAGE1_XLAT_TEST_MAX_MMAPS	(20U)

/*
 * Helper function to shuffle the content of a buffer
 * with a given stride.
 *
 * This function performs very basic randomization for the
 * shuffle.
 */
static void buffer_suffle(unsigned char *buf, size_t size, unsigned int stride)
{

/* Maximum stride allowed */
#define MAX_STRIDE	(50U)

	unsigned int items = (unsigned int)(size / stride);
	unsigned int index_i, index_j;
	unsigned char tmp_buf[MAX_STRIDE];

	assert(stride <= MAX_STRIDE);

	if (items > 1U) {
		for (unsigned int i = 0U; i <= items; i++) {

			/* Shuffle random indexes */
			do {
				index_i = test_helpers_get_rand_in_range(0,
								items - 1);
				index_j = test_helpers_get_rand_in_range(0,
								items - 1);
			} while (index_i == index_j);

			memcpy((void *)&tmp_buf[0],
			       (void *)&buf[stride * index_i],
			       (size_t)stride);
			memcpy((void *)&buf[stride * index_i],
			       (void *)&buf[stride * index_j],
			       (size_t)stride);
			memcpy((void *)&buf[stride * index_j],
			       (void *)&tmp_buf[0],
			       (size_t)stride);
		}
	}
}

/* Helper function to generate a set of random attributes for a mmap region */
static uint64_t get_mmap_attrs(void)
{
	const uint64_t attrs[] = {MT_CODE, MT_RO_DATA,
				  MT_RW_DATA, MT_TRANSIENT};
	const uint64_t protection[] = {MT_REALM, MT_NS};
	uint64_t ret_attrs;
	unsigned int index;

	index = (unsigned int)test_helpers_get_rand_in_range(0,
				(sizeof(attrs) / sizeof(uint64_t)) - 1);

	ret_attrs = attrs[index];

	if (ret_attrs != MT_TRANSIENT) {
		index = (unsigned int)test_helpers_get_rand_in_range(0,
				(sizeof(protection) / sizeof(uint64_t)) - 1);
		ret_attrs |= protection[index];
	}

	return ret_attrs;
}

/* Generate a random list of mmap structures ordered by ascending VA */
static void gen_rand_mmap_array(struct xlat_mmap_region *mmap, size_t size,
				uintptr_t min_va, uintptr_t max_va)
{

/* Maximum number of pages allowed per region */
#define MAX_PAGES_PER_REGION	(100U)

	unsigned int region_pages;
	size_t region_size;
	uintptr_t next_va_start = min_va;

	assert(mmap != NULL);
	assert(size > 0);
	assert(max_va > min_va);
	assert((min_va + (MAX_PAGES_PER_REGION * size *
			  ST1_XLAT_TESTS_GRANULARITY_SIZE)) <= max_va);

	/* Randomize the base VA for the first memory region */
	region_pages = test_helpers_get_rand_in_range(0, MAX_PAGES_PER_REGION);
	next_va_start += (region_pages * ST1_XLAT_TESTS_GRANULARITY_SIZE);

	/* Generate an ordered list of mmap regions */
	for (unsigned int i = 0U; i < (unsigned int)size; i++) {
		/* Pages of memory to use for the current region */
		region_pages = test_helpers_get_rand_in_range(2,
							MAX_PAGES_PER_REGION);
		region_size = region_pages * ST1_XLAT_TESTS_GRANULARITY_SIZE;

		mmap[i].attr = get_mmap_attrs();
		mmap[i].granularity = ST1_XLAT_MAX_BLOCK_SIZE;
		mmap[i].base_va = next_va_start;
		mmap[i].base_pa = next_va_start & ST1_XLAT_TEST_PA_MASK;
		mmap[i].size = region_size;

		next_va_start += region_size;

		assert(next_va_start < max_va);
	}
}

/* Return the base VA according to the region */
static uintptr_t get_start_va(xlat_addr_region_id_t region, size_t va_size)
{
	return (region == VA_LOW_REGION) ?
			0ULL : (ULONG_MAX - va_size + 1UL);
}

/*
 * Helper function to initialize and setup all the data
 * structures used for xlat_ctx_cfg_init(). This function initializes the
 * context with a validaton mmap array containing the expected values after
 * xlat_ctx_cfg_init() has been called to initialize the context and generates
 * an mmap array to be used for the xlat_ctx_cfg_init() invocation.
 */
static void xlat_ctx_cfg_init_setup(struct xlat_ctx_cfg *cfg,
				    struct xlat_mmap_region *init_mmap,
				    struct xlat_mmap_region *val_mmap,
				    unsigned int mmaps,
				    size_t va_size,
				    xlat_addr_region_id_t region)
{
	uintptr_t start_va, end_va;
	uintptr_t max_mapped_va_offset, max_mapped_pa;

	/* Clean the data structures */
	memset((void *)cfg, 0, sizeof(struct xlat_ctx_cfg));
	memset((void *)val_mmap, 0, sizeof(struct xlat_mmap_region) * mmaps);
	memset((void *)init_mmap, 0, sizeof(struct xlat_mmap_region) * mmaps);

	/* Calculate VA boundaries for the region */
	start_va = get_start_va(region, va_size);
	end_va = start_va + va_size - 1ULL;

	/*
	 * Generate a validation mmap array with random boundaries.
	 * The array will be sorted in ascending order of VA, as expected
	 * by xlat_ctx_cfg_init().
	 */
	gen_rand_mmap_array(&val_mmap[0], mmaps, start_va, end_va);

	/*
	 * Copy the validation memory regions array into the init one, so the
	 * latter can be used to initialize xlat_ctx_cfg_init() and the former
	 * to validate the result if needed.
	 *
	 * xlat_ctx_cfg_init() adjusts the VA base of the mmap region passed
	 * by subtracting the base VA, so all the VAs will look the same
	 * regardless of the memory region where they belong. This helps to
	 * simplify the xlat tables creation.
	 */
	memcpy((void *)init_mmap, (void *)val_mmap,
		sizeof(struct xlat_mmap_region) * mmaps);

	/* Adjust the base VA of the regions passed on the mmap array */
	for (unsigned int i = 0U; i < mmaps; i++) {
		val_mmap[i].base_va -= start_va;
	}

	/* The maximum mapped va offset can never go beyond the VA size */
	max_mapped_va_offset = (val_mmap[mmaps - 1U].base_va +
				val_mmap[mmaps - 1U].size - 1U) &
					ST1_XLAT_LOW_REGION_MASK;

	max_mapped_pa = val_mmap[mmaps - 1U].base_pa +
			val_mmap[mmaps - 1U].size - 1U;

	/* Initialize the xlat_ctx_cfg structure */
	st1_xlat_test_helpers_init_ctx_cfg(cfg, va_size, start_va,
					   max_mapped_pa, max_mapped_va_offset,
					   ST1_XLAT_GET_BASE_TABLE_LVL(va_size),
					   region, init_mmap, mmaps, true);
}

TEST_GROUP(stage1_xlat) {
	TEST_SETUP()
	{
		static int random_seed = 0;

		/* Make sure current cpu id is 0 (primary processor) */
		host_util_set_cpuid(0U);

		/* Initialize the random seed */
		while (random_seed == 0) {
			random_seed = (int)time(NULL);
			srand(random_seed);
		}

		st1_xlat_test_helpers_init_registers();
		test_helpers_expect_assert_fail(false);
	}

	TEST_TEARDOWN()
	{
		host_util_reset_all_sysreg_cb();
	}
};

TEST(stage1_xlat, MAP_REGION_FULL_SPEC_TC1)
{
	/***************************************************************
	 * TEST CASE 1:
	 *
	 * Instantiate a struct xlat_mmap_region structure and populate
	 * it using MAP_REGION_FULL_SPEC macro. Verify that the
	 * structure fields are right.
	 ***************************************************************/
	struct xlat_mmap_region validation_mmap =
	{
		.base_pa = (uintptr_t)rand(),
		.base_va = (uintptr_t)rand(),
		.size = (size_t)rand(),
		.attr = (uint64_t)rand(),
		.granularity = (size_t)rand()
	};

	struct xlat_mmap_region test_mmap = MAP_REGION_FULL_SPEC (
		validation_mmap.base_pa,
		validation_mmap.base_va,
		validation_mmap.size,
		validation_mmap.attr,
		validation_mmap.granularity
	);

	MEMCMP_EQUAL((void *)&validation_mmap,
		     (void *)&test_mmap,
		     sizeof(struct xlat_mmap_region));
}

TEST(stage1_xlat, MAP_REGION_TC1)
{
	/***************************************************************
	 * TEST CASE 1:
	 *
	 * Instantiate a struct xlat_mmap_region structure and populate
	 * it using MAP_REGION macro. Verify that the structure fields
	 * are right.
	 ***************************************************************/

	struct xlat_mmap_region validation_mmap =
	{
		.base_pa = (uintptr_t)rand(),
		.base_va = (uintptr_t)rand(),
		.size = (size_t)rand(),
		.attr = (uint64_t)rand(),
		.granularity = ST1_XLAT_MAX_BLOCK_SIZE
	};

	/*
	 * Test structure. Fill it using the validation structure
	 * through MAP_REGION macro.
	 */
	struct xlat_mmap_region test_mmap = MAP_REGION (
		validation_mmap.base_pa,
		validation_mmap.base_va,
		validation_mmap.size,
		validation_mmap.attr
	);

	MEMCMP_EQUAL((void *)&validation_mmap,
		     (void *)&test_mmap,
		     sizeof(struct xlat_mmap_region));
}

TEST(stage1_xlat, MAP_REGION_FLAT_TC1)
{
	/***************************************************************
	 * TEST CASE 1:
	 *
	 * Instantiate a struct xlat_mmap_region structure and populate
	 * it using MAP_REGION_FLAT macro. Verify that the structure
	 * fields are right.
	 ***************************************************************/

	/* Validation structure. Fill it with random data */
	uintptr_t base_addr = rand();

	struct xlat_mmap_region validation_mmap =
	{
		.base_pa = base_addr,
		.base_va = base_addr,
		.size = (size_t)rand(),
		.attr = (uint64_t)rand(),
		.granularity = ST1_XLAT_MAX_BLOCK_SIZE
	};

	/*
	 * Test structure. Fill it using the validation structure
	 * through MAP_REGION_FLAT macro.
	 */
	struct xlat_mmap_region test_mmap = MAP_REGION_FLAT (
		base_addr,
		validation_mmap.size,
		validation_mmap.attr
	);

	MEMCMP_EQUAL((void *)&validation_mmap,
		     (void *)&test_mmap,
		     sizeof(struct xlat_mmap_region));
}

TEST(stage1_xlat, MAP_REGION_TRANSIENT_TC1)
{
	/***************************************************************
	 * TEST CASE 1:
	 *
	 * Instantiate a struct xlat_mmap_region structure and populate
	 * it using MAP_REGION_TRANSIENT macro. Verify that the
	 * structure fields are right.
	 ***************************************************************/

	/* Validation structure. Fill it with random data */
	struct xlat_mmap_region validation_mmap =
	{
		/* XLAT_MAP_REGION_TRANSIENT sets base_pa to 0 */
		.base_pa = 0ULL,
		.base_va = (uintptr_t)rand(),
		.size = (size_t)rand(),

		/*
		 * XLAT_MAP_REGION_TRANSIENT sets attr to
		 * MT_TRANSIENT
		 */
		.attr = MT_TRANSIENT,
		.granularity = (size_t)rand()
	};

	/*
	 * Test structure. Fill it using the validation structure
	 * through MAP_REGION_TRANSIENT macro.
	 */
	struct xlat_mmap_region test_mmap = MAP_REGION_TRANSIENT (
		validation_mmap.base_va,
		validation_mmap.size,
		validation_mmap.granularity
	);

	MEMCMP_EQUAL((void *)&validation_mmap,
		     (void *)&test_mmap,
		     sizeof(struct xlat_mmap_region));
}

TEST(stage1_xlat, xlat_ctx_cfg_init_TC1)
{
	struct xlat_ctx_cfg expected_cfg, test_cfg;
	struct xlat_mmap_region init_mmap[STAGE1_XLAT_TEST_MAX_MMAPS];
	struct xlat_mmap_region val_mmap[STAGE1_XLAT_TEST_MAX_MMAPS];
	unsigned int mmap_count;
	xlat_addr_region_id_t region;
	int retval;

	/***************************************************************
	 * TEST CASE 1:
	 *
	 * Initialize a xlat_ctx_cfg structure with random data through
	 * xlat_ctx_cfg_init(). Then verify that the initialization
	 * was as expected.
	 ***************************************************************/
	/* Initialize some parameters with random data */
	mmap_count = test_helpers_get_rand_in_range(1,
						STAGE1_XLAT_TEST_MAX_MMAPS);
	region = (xlat_addr_region_id_t)test_helpers_get_rand_in_range(0,
							VA_REGIONS - 1U);

	/* Clean the data structures */
	memset((void *)&test_cfg, 0, sizeof(struct xlat_ctx_cfg));

	/* Initialize the test structures with the expected values */
	xlat_ctx_cfg_init_setup(&expected_cfg, &init_mmap[0],
				&val_mmap[0], mmap_count,
				ST1_XLAT_TEST_MAX_VA_SIZE, region);

	/* Initialize the test structure */
	retval = xlat_ctx_cfg_init(&test_cfg, region, &init_mmap[0],
				   mmap_count, ST1_XLAT_TEST_MAX_VA_SIZE);

	/* Verify the result */
	CHECK_TRUE(retval == 0);

	/*
	 * Verify that the memory regions array used with xlat_ctx_cfg_init()
	 * has been properly optimized.
	 */
	MEMCMP_EQUAL((void *)&val_mmap[0], (void *)&init_mmap[0],
		     sizeof(struct xlat_mmap_region) * mmap_count);

	/* Tets that the xlat_ctx_cfg structure is properly initialized */
	MEMCMP_EQUAL((void *)&expected_cfg, (void *)&test_cfg,
		     sizeof(struct xlat_ctx_cfg));
}

TEST(stage1_xlat, xlat_ctx_cfg_init_TC2)
{
	struct xlat_ctx_cfg foo_cfg;
	struct xlat_mmap_region init_mmap[STAGE1_XLAT_TEST_MAX_MMAPS];
	struct xlat_mmap_region val_mmap[STAGE1_XLAT_TEST_MAX_MMAPS];
	unsigned int mmap_count;
	xlat_addr_region_id_t region;
	int retval;

	/***************************************************************
	 * TEST CASE 2:
	 *
	 * Try to initialize a NULL xlat_ctx_cfg structure.
	 * All the rest of parameters will be valid.
	 ***************************************************************/

	/* Initialize some parameters with random data */
	mmap_count = test_helpers_get_rand_in_range(1,
						STAGE1_XLAT_TEST_MAX_MMAPS);
	region = (xlat_addr_region_id_t)test_helpers_get_rand_in_range(0,
							VA_REGIONS - 1U);

	/* Initialize the test structures with the expected values */
	xlat_ctx_cfg_init_setup(&foo_cfg, &init_mmap[0], &val_mmap[0],
				mmap_count, ST1_XLAT_TEST_MAX_VA_SIZE, region);

	/* Initialize the test structure */
	retval = xlat_ctx_cfg_init(NULL, region, &init_mmap[0], mmap_count,
					ST1_XLAT_TEST_MAX_VA_SIZE);

	/* Verify the result */
	CHECK_TRUE(retval == -EINVAL);
}

TEST(stage1_xlat, xlat_ctx_cfg_init_TC3)
{
	struct xlat_ctx_cfg test_cfg;
	xlat_addr_region_id_t region;
	unsigned int mmap_count;
	int retval;

	/***************************************************************
	 * TEST CASE 3:
	 *
	 * Try to initialize a xlat_ctx_cfg structure with a NULL list
	 * of mmap regions.
	 * All the rest of parameters will be valid.
	 ***************************************************************/

	/* Initialize some parameters with random data */
	region = (xlat_addr_region_id_t)test_helpers_get_rand_in_range(0,
							VA_REGIONS - 1U);
	mmap_count = test_helpers_get_rand_in_range(1,
						STAGE1_XLAT_TEST_MAX_MMAPS);

	/* Clean the data structures */
	memset((void *)&test_cfg, 0, sizeof(struct xlat_ctx_cfg));

	/* Initialize the test structure */
	retval = xlat_ctx_cfg_init(&test_cfg, region, NULL, mmap_count,
					ST1_XLAT_TEST_MAX_VA_SIZE);

	/* Verify the result */
	CHECK_TRUE(retval == -EINVAL);
}

TEST(stage1_xlat, xlat_ctx_cfg_init_TC4)
{
	struct xlat_ctx_cfg foo_cfg, test_cfg;
	struct xlat_mmap_region test_mmap[STAGE1_XLAT_TEST_MAX_MMAPS];
	struct xlat_mmap_region init_mmap[STAGE1_XLAT_TEST_MAX_MMAPS];
	unsigned int mmap_count;
	xlat_addr_region_id_t mmap_region, cfg_region;
	int retval;

	/***************************************************************
	 * TEST CASE 4:
	 *
	 * Try to initialize a xlat_ctx_cfg structure with random data
	 * where the memory region on the mmap structures does not match
	 * the memory region setup on the configuration.
	 ***************************************************************/

	for (unsigned int i = 0U; i < (unsigned int)VA_REGIONS; i++) {
		mmap_region = (xlat_addr_region_id_t)i;
		cfg_region = (xlat_addr_region_id_t)((i + 1U) % VA_REGIONS);

		/* Initialize some parameters with random data */
		mmap_count = test_helpers_get_rand_in_range(1,
						STAGE1_XLAT_TEST_MAX_MMAPS);

		/* Clean the data structures */
		memset((void *)&test_cfg, 0, sizeof(struct xlat_ctx_cfg));

		/* Initialize the test structures with the expected values */
		xlat_ctx_cfg_init_setup(&foo_cfg, &init_mmap[0], &test_mmap[0],
				mmap_count, ST1_XLAT_TEST_MAX_VA_SIZE,
				mmap_region);

		/* Initialize the test structure */
		retval = xlat_ctx_cfg_init(&test_cfg, cfg_region,
					   &init_mmap[0], mmap_count,
					   ST1_XLAT_TEST_MAX_VA_SIZE);

		/* Verify the result */
		CHECK_TRUE(retval == -EINVAL);
	}
}

TEST(stage1_xlat, xlat_ctx_cfg_init_TC5)
{
	struct xlat_ctx_cfg test_cfg;
	struct xlat_mmap_region init_mmap[STAGE1_XLAT_TEST_MAX_MMAPS];
	xlat_addr_region_id_t region;
	int retval;

	/***************************************************************
	 * TEST CASE 5:
	 *
	 * Try to initialize a xlat_ctx_cfg structure with an empty mmap
	 * region array.
	 ***************************************************************/

	for (unsigned int i = 0U; i < (unsigned int)VA_REGIONS; i++) {
		region = (xlat_addr_region_id_t)i;

		/* Clean the data structures */
		memset((void *)&test_cfg, 0, sizeof(struct xlat_ctx_cfg));
		memset((void *)&init_mmap[0], 0,
			sizeof(xlat_mmap_region) * STAGE1_XLAT_TEST_MAX_MMAPS);

		/* Initialize the test structure */
		retval = xlat_ctx_cfg_init(&test_cfg, region, &init_mmap[0], 0U,
						ST1_XLAT_TEST_MAX_VA_SIZE);

		/* Verify the result */
		CHECK_TRUE(retval == -EINVAL);
	}
}

TEST(stage1_xlat, xlat_ctx_cfg_init_TC6)
{
	struct xlat_ctx_cfg test_cfg, foo_cfg;
	struct xlat_mmap_region init_mmap[STAGE1_XLAT_TEST_MAX_MMAPS];
	struct xlat_mmap_region val_mmap[STAGE1_XLAT_TEST_MAX_MMAPS];
	xlat_addr_region_id_t region;
	int retval;
	size_t misaligned_va;

	/***************************************************************
	 * TEST CASE 6:
	 *
	 * Try to initialize a xlat_ctx_cfg structure with a misaligned
	 * va size.
	 * The rest of the arguments to xlat_ctx_cfg_init() are as
	 * expected.
	 ***************************************************************/
	for (unsigned int i = 0U; i < (unsigned int)VA_REGIONS; i++) {
		region = (xlat_addr_region_id_t)i;

		/*
		 * Get a VA large enough to be higher than the maximum mapped
		 * VA but not that an offset added to it will cause it to be
		 * out of boundaries.
		 */
		misaligned_va =
			ST1_XLAT_TESTS_GRANULARITY_SIZE *
				(ST1_XLAT_TEST_MAX_VA_PAGES - 1);

		/* Add a random offset to it to misalign */
		misaligned_va += test_helpers_get_rand_in_range(1,
					ST1_XLAT_TESTS_GRANULARITY_SIZE - 1);

		/* Clean the data structures */
		memset((void *)&test_cfg, 0, sizeof(struct xlat_ctx_cfg));

		/* Initialize the test structures with the expected values */
		xlat_ctx_cfg_init_setup(&foo_cfg, &init_mmap[0], &val_mmap[0],
					STAGE1_XLAT_TEST_MAX_MMAPS,
					ST1_XLAT_TEST_MAX_VA_SIZE, region);

		/* Initialize the test structure */
		retval = xlat_ctx_cfg_init(&test_cfg, region, &init_mmap[0],
					   STAGE1_XLAT_TEST_MAX_MMAPS,
					   misaligned_va);

		/* Verify the result */
		CHECK_TRUE(retval == -EINVAL);
	}
}

TEST(stage1_xlat, xlat_ctx_cfg_init_TC7)
{
	struct xlat_ctx_cfg test_cfg, foo_cfg;
	struct xlat_mmap_region init_mmap[STAGE1_XLAT_TEST_MAX_MMAPS];
	struct xlat_mmap_region test_mmap[STAGE1_XLAT_TEST_MAX_MMAPS];
	xlat_addr_region_id_t region;
	int retval;
	size_t va_size;

	/***************************************************************
	 * TEST CASE 7:
	 *
	 * Try to initialize a xlat_ctx_cfg structure with a VA size
	 * larger than the maximum allowed.
	 * The rest of the arguments to xlat_ctx_cfg_init() are as
	 * expected.
	 ***************************************************************/

	for (unsigned int i = 0U; i < (unsigned int)VA_REGIONS; i++) {
		region = (xlat_addr_region_id_t)i;

		va_size = (ST1_XLAT_TESTS_GRANULARITY_SIZE *
					(ST1_XLAT_TEST_MAX_VA_PAGES + 1U));

		/* Clean the data structures */
		memset((void *)&test_cfg, 0, sizeof(struct xlat_ctx_cfg));

		/* Initialize the test structures with the expected values */
		xlat_ctx_cfg_init_setup(&foo_cfg, &init_mmap[0], &test_mmap[0],
					STAGE1_XLAT_TEST_MAX_MMAPS,
					ST1_XLAT_TEST_MAX_VA_SIZE, region);

		/* Initialize the test structure */
		retval = xlat_ctx_cfg_init(&test_cfg, region, &init_mmap[0],
					   STAGE1_XLAT_TEST_MAX_MMAPS,
					   va_size);

		/* Verify the result */
		CHECK_TRUE(retval == -EINVAL);
	}
}

TEST(stage1_xlat, xlat_ctx_cfg_init_TC8)
{
	struct xlat_ctx_cfg test_cfg, foo_cfg;
	struct xlat_mmap_region init_mmap[STAGE1_XLAT_TEST_MAX_MMAPS];
	struct xlat_mmap_region val_mmap[STAGE1_XLAT_TEST_MAX_MMAPS];
	xlat_addr_region_id_t region;
	int retval;
	size_t va_size;

	/***************************************************************
	 * TEST CASE 8:
	 *
	 * Try to initialize a xlat_ctx_cfg structure with a VA size
	 * shorter than the minimum allowed.
	 * The rest of the arguments to xlat_ctx_cfg_init() are as
	 * expected.
	 ***************************************************************/

	for (unsigned int i = 0U; i < (unsigned int)VA_REGIONS; i++) {
		region = (xlat_addr_region_id_t)i;

		va_size = (ST1_XLAT_TESTS_GRANULARITY_SIZE *
					(ST1_XLAT_TEST_MIN_VA_PAGES - 1U));

		/* Clean the data structures */
		memset((void *)&test_cfg, 0, sizeof(struct xlat_ctx_cfg));

		/* Initialize the test structures with the expected values */
		xlat_ctx_cfg_init_setup(&foo_cfg, &init_mmap[0], &val_mmap[0],
					STAGE1_XLAT_TEST_MAX_MMAPS,
					ST1_XLAT_TEST_MAX_VA_SIZE, region);

		/* Initialize the test structure */
		retval = xlat_ctx_cfg_init(&test_cfg, region, &init_mmap[0],
					   STAGE1_XLAT_TEST_MAX_MMAPS,
					   va_size);

		/* Verify the result */
		CHECK_TRUE(retval == -EINVAL);
	}
}

TEST(stage1_xlat, xlat_ctx_cfg_init_TC9)
{
	struct xlat_ctx_cfg test_cfg;
	struct xlat_mmap_region init_mmap[STAGE1_XLAT_TEST_MAX_MMAPS];
	struct xlat_mmap_region val_mmap[STAGE1_XLAT_TEST_MAX_MMAPS];
	xlat_addr_region_id_t region;
	int retval;

	/******************************************************************
	 * TEST CASE 9:
	 *
	 * Try to initialize an already initialized xlat_ctx_cfg structure
	 *****************************************************************/

	for (unsigned int i = 0U; i < (unsigned int)VA_REGIONS; i++) {
		region = (xlat_addr_region_id_t)i;

		/*
		 * Initialize the test structures with the expected.
		 * test_cfg will be marked as initialized.
		 */
		xlat_ctx_cfg_init_setup(&test_cfg, &init_mmap[0], &val_mmap[0],
					STAGE1_XLAT_TEST_MAX_MMAPS,
					ST1_XLAT_TEST_MAX_VA_SIZE, region);

		/* Initialize the test structure */
		retval = xlat_ctx_cfg_init(&test_cfg, region, &init_mmap[0],
					   STAGE1_XLAT_TEST_MAX_MMAPS,
					   ST1_XLAT_TEST_MAX_VA_SIZE);

		/* Verify the result */
		CHECK_TRUE(retval == -EALREADY);
	}
}

TEST(stage1_xlat, xlat_ctx_cfg_init_TC10)
{
	struct xlat_ctx_cfg test_cfg, foo_cfg;
	struct xlat_mmap_region init_mmap[STAGE1_XLAT_TEST_MAX_MMAPS];
	struct xlat_mmap_region val_mmap[STAGE1_XLAT_TEST_MAX_MMAPS];
	xlat_addr_region_id_t region;
	unsigned int mmap_index;
	int retval;

	/***************************************************************
	 * TEST CASE 10:
	 *
	 * Try to initialize a xlat_ctx_cfg structure with mmap areas
	 * in which the VAs overlap.
	 ***************************************************************/

	for (unsigned int i = 0U; i < (unsigned int)VA_REGIONS; i++) {
		region = (xlat_addr_region_id_t)i;

		/* Clean the data structures */
		memset((void *)&test_cfg, 0, sizeof(struct xlat_ctx_cfg));

		/* Initialize the test structures with the expected values */
		xlat_ctx_cfg_init_setup(&foo_cfg, &init_mmap[0], &val_mmap[0],
					STAGE1_XLAT_TEST_MAX_MMAPS,
					ST1_XLAT_TEST_MAX_VA_SIZE, region);

		/* Overwrite the mmap structures to make the VAs overlap */
		mmap_index = (unsigned int)test_helpers_get_rand_in_range(1,
					STAGE1_XLAT_TEST_MAX_MMAPS - 1);
		init_mmap[mmap_index].base_va =
			init_mmap[mmap_index - 1U].base_va +
					 ST1_XLAT_TESTS_GRANULARITY_SIZE;

		/* Initialize the test structure */
		retval = xlat_ctx_cfg_init(&test_cfg, region, &init_mmap[0],
					   STAGE1_XLAT_TEST_MAX_MMAPS,
					   ST1_XLAT_TEST_MAX_VA_SIZE);

		/* Verify the result */
		CHECK_TRUE(retval == -EPERM);
	}
}

TEST(stage1_xlat, xlat_ctx_cfg_init_TC11)
{
	struct xlat_ctx_cfg test_cfg, foo_cfg;
	struct xlat_mmap_region init_mmap[STAGE1_XLAT_TEST_MAX_MMAPS];
	struct xlat_mmap_region val_mmap[STAGE1_XLAT_TEST_MAX_MMAPS];
	unsigned int mmap_index;
	xlat_addr_region_id_t region;
	int retval;

	/***************************************************************
	 * TEST CASE 11:
	 *
	 * Try to initialize a xlat_ctx_cfg structure with mmap areas
	 * in which the PAs overlap.
	 ***************************************************************/

	for (unsigned int i = 0U; i < (unsigned int)VA_REGIONS; i++) {
		region = (xlat_addr_region_id_t)i;

		/* Clean the data structures */
		memset((void *)&test_cfg, 0, sizeof(struct xlat_ctx_cfg));

		/* Initialize the test structures with the expected values */
		xlat_ctx_cfg_init_setup(&foo_cfg, &init_mmap[0], &val_mmap[0],
					STAGE1_XLAT_TEST_MAX_MMAPS,
					ST1_XLAT_TEST_MAX_VA_SIZE, region);

		/* Overwrite the mmap structures to make the PAs overlap */
		mmap_index = (unsigned int)test_helpers_get_rand_in_range(1,
					STAGE1_XLAT_TEST_MAX_MMAPS - 1);
		init_mmap[mmap_index].base_pa =
			init_mmap[mmap_index - 1U].base_pa +
					 ST1_XLAT_TESTS_GRANULARITY_SIZE;

		/* Initialize the test structure */
		retval = xlat_ctx_cfg_init(&test_cfg, region, &init_mmap[0],
					   STAGE1_XLAT_TEST_MAX_MMAPS,
					   ST1_XLAT_TEST_MAX_VA_SIZE);

		/* Verify the result */
		CHECK_TRUE(retval == -EPERM);
	}
}

TEST(stage1_xlat, xlat_ctx_cfg_init_TC12)
{
	struct xlat_ctx_cfg test_cfg, foo_cfg;
	struct xlat_mmap_region init_mmap[STAGE1_XLAT_TEST_MAX_MMAPS];
	struct xlat_mmap_region val_mmap[STAGE1_XLAT_TEST_MAX_MMAPS];
	xlat_addr_region_id_t region;
	unsigned int mmap_index;
	int retval;
	unsigned int pa_range_bits_arr[] = {
		PARANGE_0000_WIDTH, PARANGE_0001_WIDTH, PARANGE_0010_WIDTH,
		PARANGE_0011_WIDTH, PARANGE_0100_WIDTH, PARANGE_0101_WIDTH,
	};
	unsigned int index = test_helpers_get_rand_in_range(0,
		sizeof(pa_range_bits_arr)/sizeof(pa_range_bits_arr[0]) - 1U);

	/***************************************************************
	 * TEST CASE 12:
	 *
	 * Try to initialize a xlat_ctx_cfg structure with mmap areas
	 * in which the PA is higher than the maximum PA supported.
	 ***************************************************************/

	/* Configure a random maximum PA supported */
	write_id_aa64mmfr0_el1(INPLACE(ID_AA64MMFR0_EL1_PARANGE, index));

	for (unsigned int i = 0U; i < (unsigned int)VA_REGIONS; i++) {
		region = (xlat_addr_region_id_t)i;

		/* Clean the data structures */
		memset((void *)&test_cfg, 0, sizeof(struct xlat_ctx_cfg));

		/* Initialize the test structures with the expected values */
		xlat_ctx_cfg_init_setup(&foo_cfg, &init_mmap[0], &val_mmap[0],
					STAGE1_XLAT_TEST_MAX_MMAPS,
					ST1_XLAT_TEST_MAX_VA_SIZE, region);

		/*
		 * Overwrite the PA on one of the memory map regions to
		 * be higher than the maximum PA supported.
		 */
		mmap_index = (unsigned int)test_helpers_get_rand_in_range(0,
					STAGE1_XLAT_TEST_MAX_MMAPS - 1);

		init_mmap[mmap_index].base_pa =
					1ULL << pa_range_bits_arr[index];

		/* Initialize the test structure */
		retval = xlat_ctx_cfg_init(&test_cfg, region, &init_mmap[0],
					   STAGE1_XLAT_TEST_MAX_MMAPS,
					   ST1_XLAT_TEST_MAX_VA_SIZE);

		/* Verify the result */
		CHECK_TRUE(retval == -ERANGE);
	}
}

TEST(stage1_xlat, xlat_ctx_cfg_init_TC13)
{
	struct xlat_ctx_cfg test_cfg, foo_cfg;
	struct xlat_mmap_region init_mmap[STAGE1_XLAT_TEST_MAX_MMAPS];
	struct xlat_mmap_region val_mmap[STAGE1_XLAT_TEST_MAX_MMAPS];
	xlat_addr_region_id_t region;
	unsigned int mmap_index;
	int retval;

	/***************************************************************
	 * TEST CASE 13:
	 *
	 * Try to initialize a xlat_ctx_cfg structure with mmap areas
	 * in which the PA is misaligned.
	 ***************************************************************/

	for (unsigned int i = 0U; i < (unsigned int)VA_REGIONS; i++) {
		region = (xlat_addr_region_id_t)i;

		/* Clean the data structures */
		memset((void *)&test_cfg, 0, sizeof(struct xlat_ctx_cfg));

		/*
		 * Initialize the test structures with the expected values and
		 * generate a shuffled array of random memory mapping regions.
		 */
		xlat_ctx_cfg_init_setup(&foo_cfg, &init_mmap[0], &val_mmap[0],
					STAGE1_XLAT_TEST_MAX_MMAPS,
					ST1_XLAT_TEST_MAX_VA_SIZE, region);

		/*
		 * Overwrite the PA on one of the memory map regions to
		 * make it misaligned.
		 */
		mmap_index = (unsigned int)test_helpers_get_rand_in_range(0,
					STAGE1_XLAT_TEST_MAX_MMAPS - 1);
		init_mmap[mmap_index].base_pa +=
				test_helpers_get_rand_in_range(1,
					ST1_XLAT_TESTS_GRANULARITY_SIZE - 1);

		/* Initialize the test structure */
		retval = xlat_ctx_cfg_init(&test_cfg, region, &init_mmap[0],
					   STAGE1_XLAT_TEST_MAX_MMAPS,
					   ST1_XLAT_TEST_MAX_VA_SIZE);

		/* Verify the result */
		CHECK_TRUE(retval == -EFAULT);
	}
}

TEST(stage1_xlat, xlat_ctx_cfg_init_TC14)
{
	struct xlat_ctx_cfg test_cfg, foo_cfg;
	struct xlat_mmap_region init_mmap[STAGE1_XLAT_TEST_MAX_MMAPS];
	struct xlat_mmap_region val_mmap[STAGE1_XLAT_TEST_MAX_MMAPS];
	xlat_addr_region_id_t region;
	unsigned int mmap_index;
	int retval;

	/***************************************************************
	 * TEST CASE 14:
	 *
	 * Try to initialize a xlat_ctx_cfg structure with mmap areas
	 * in which the VA is misaligned.
	 ***************************************************************/

	for (unsigned int i = 0U; i < (unsigned int)VA_REGIONS; i++) {
		region = (xlat_addr_region_id_t)i;

		/* Clean the data structures */
		memset((void *)&test_cfg, 0, sizeof(struct xlat_ctx_cfg));

		/* Initialize the test structures with the expected values */
		xlat_ctx_cfg_init_setup(&foo_cfg, &init_mmap[0], &val_mmap[0],
					STAGE1_XLAT_TEST_MAX_MMAPS,
					ST1_XLAT_TEST_MAX_VA_SIZE, region);

		/*
		 * Overwrite the VA on one of the memory map regions to
		 * make it misaligned.
		 */
		mmap_index = (unsigned int)test_helpers_get_rand_in_range(0,
					STAGE1_XLAT_TEST_MAX_MMAPS - 1);
		init_mmap[mmap_index].base_va +=
				test_helpers_get_rand_in_range(1,
					ST1_XLAT_TESTS_GRANULARITY_SIZE - 1);

		/* Initialize the test structure */
		retval = xlat_ctx_cfg_init(&test_cfg, region, &init_mmap[0],
					   STAGE1_XLAT_TEST_MAX_MMAPS,
					   ST1_XLAT_TEST_MAX_VA_SIZE);

		/* Verify the result */
		CHECK_TRUE(retval == -EFAULT);
	}
}

TEST(stage1_xlat, xlat_ctx_cfg_init_TC15)
{
	struct xlat_ctx_cfg test_cfg, foo_cfg;
	struct xlat_mmap_region init_mmap[STAGE1_XLAT_TEST_MAX_MMAPS];
	struct xlat_mmap_region val_mmap[STAGE1_XLAT_TEST_MAX_MMAPS];
	xlat_addr_region_id_t region;
	unsigned int mmap_index;
	int retval;

	/***************************************************************
	 * TEST CASE 15:
	 *
	 * Try to initialize a xlat_ctx_cfg structure with mmap areas
	 * in which the size is misaligned.
	 ***************************************************************/

	for (unsigned int i = 0U; i < (unsigned int)VA_REGIONS; i++) {
		region = (xlat_addr_region_id_t)i;

		/* Clean the data structures */
		memset((void *)&test_cfg, 0, sizeof(struct xlat_ctx_cfg));

		/* Initialize the test structures with the expected values */
		xlat_ctx_cfg_init_setup(&foo_cfg, &init_mmap[0], &val_mmap[0],
					STAGE1_XLAT_TEST_MAX_MMAPS,
					ST1_XLAT_TEST_MAX_VA_SIZE, region);

		/*
		 * Overwrite the size on one of the memory map regions to
		 * make it misaligned.
		 */
		mmap_index = (unsigned int)test_helpers_get_rand_in_range(0,
					STAGE1_XLAT_TEST_MAX_MMAPS - 1);
		init_mmap[mmap_index].size -= test_helpers_get_rand_in_range(1,
					ST1_XLAT_TESTS_GRANULARITY_SIZE - 1);

		/* Initialize the test structure */
		retval = xlat_ctx_cfg_init(&test_cfg, region, &init_mmap[0],
					   STAGE1_XLAT_TEST_MAX_MMAPS,
					   ST1_XLAT_TEST_MAX_VA_SIZE);

		/* Verify the result */
		CHECK_TRUE(retval == -EFAULT);
	}
}

TEST(stage1_xlat, xlat_ctx_cfg_init_TC16)
{
	struct xlat_ctx_cfg test_cfg, foo_cfg;
	struct xlat_mmap_region init_mmap[STAGE1_XLAT_TEST_MAX_MMAPS];
	struct xlat_mmap_region val_mmap[STAGE1_XLAT_TEST_MAX_MMAPS];
	xlat_addr_region_id_t region;
	unsigned int mmap_index;
	int retval;

	/***************************************************************
	 * TEST CASE 16:
	 *
	 * Try to initialize a xlat_ctx_cfg structure with repeated
	 * memory mapping areas.
	 ***************************************************************/

	for (unsigned int i = 0U; i < (unsigned int)VA_REGIONS; i++) {
		region = (xlat_addr_region_id_t)i;

		/* Clean the data structures */
		memset((void *)&test_cfg, 0, sizeof(struct xlat_ctx_cfg));

		/* Initialize the test structures with the expected values */
		xlat_ctx_cfg_init_setup(&foo_cfg, &init_mmap[0], &val_mmap[0],
					STAGE1_XLAT_TEST_MAX_MMAPS,
					ST1_XLAT_TEST_MAX_VA_SIZE, region);

		/*
		 * Overwrite a memory mapping region to make it a duplicate
		 * of the previous one.
		 */
		mmap_index = (unsigned int)test_helpers_get_rand_in_range(1,
					STAGE1_XLAT_TEST_MAX_MMAPS - 1);
		memcpy((void *)&init_mmap[mmap_index],
		       (void *)&init_mmap[mmap_index - 1U],
		       sizeof (struct xlat_mmap_region));

		/* Initialize the test structure */
		retval = xlat_ctx_cfg_init(&test_cfg, region, &init_mmap[0],
					   STAGE1_XLAT_TEST_MAX_MMAPS,
					   ST1_XLAT_TEST_MAX_VA_SIZE);

		/* Verify the result */
		CHECK_TRUE(retval == -EPERM);
	}
}

TEST(stage1_xlat, xlat_ctx_cfg_init_TC17)
{
	struct xlat_ctx_cfg test_cfg, foo_cfg;
	struct xlat_mmap_region init_mmap[STAGE1_XLAT_TEST_MAX_MMAPS];
	struct xlat_mmap_region val_mmap[STAGE1_XLAT_TEST_MAX_MMAPS];
	xlat_addr_region_id_t region;
	int retval;

	/***************************************************************
	 * TEST CASE 17:
	 *
	 * Try to initialize a xlat_ctx_cfg structure with out of order
	 * memory mapping areas.
	 ***************************************************************/

	for (unsigned int i = 0U; i < (unsigned int)VA_REGIONS; i++) {
		region = (xlat_addr_region_id_t)i;

		/* Clean the data structures */
		memset((void *)&test_cfg, 0, sizeof(struct xlat_ctx_cfg));

		/* Initialize the test structures with the expected values */
		xlat_ctx_cfg_init_setup(&foo_cfg, &init_mmap[0], &val_mmap[0],
					STAGE1_XLAT_TEST_MAX_MMAPS,
					ST1_XLAT_TEST_MAX_VA_SIZE, region);

		/* Randomly shuffle the memory mapping areas */
		buffer_suffle((unsigned char *)&init_mmap[0],
				sizeof(struct xlat_mmap_region) *
						STAGE1_XLAT_TEST_MAX_MMAPS,
				sizeof(struct xlat_mmap_region));

		/* Initialize the test structure */
		retval = xlat_ctx_cfg_init(&test_cfg, region, &init_mmap[0],
					   STAGE1_XLAT_TEST_MAX_MMAPS,
					   ST1_XLAT_TEST_MAX_VA_SIZE);

		/* Verify the result */
		CHECK_TRUE(retval == -EPERM);
	}
}

TEST(stage1_xlat, xlat_ctx_init_TC1)
{
	struct xlat_ctx ctx;
	struct xlat_ctx_cfg cfg, val_cfg;
	struct xlat_ctx_tbls tbls;
	uintptr_t start_va, end_va;
	unsigned int mmap_count;
	xlat_addr_region_id_t region;
	int retval;
	struct xlat_mmap_region init_mmap[STAGE1_XLAT_TEST_MAX_MMAPS];
	uint64_t xlat_tables[ST1_XLAT_TESTS_TBL_ENTRIES
				* STAGE1_XLAT_TEST_MAX_TABLES]
				__aligned(ST1_XLAT_TESTS_TBL_ALIGNMENT);

	/***************************************************************
	 * TEST CASE 1:
	 *
	 * Initialize a context with a random number of valid random
	 * memory mapping areas and generate the corresponding
	 * translation tables.
	 * Verify that the return code from xlat_ctx_init() is as
	 * expected and the context is properly generated.
	 * This test does not perform any check on the translation
	 * tables themselves.
	 ***************************************************************/

	for (unsigned int i = 0U; i < (unsigned int)VA_REGIONS; i++) {
		region = (xlat_addr_region_id_t)i;

		/* Initialize some parameters with random data */
		mmap_count = test_helpers_get_rand_in_range(1,
						STAGE1_XLAT_TEST_MAX_MMAPS);

		/* Clean the data structures */
		memset((void *)&ctx, 0, sizeof(struct xlat_ctx));
		memset((void *)&cfg, 0, sizeof(struct xlat_ctx_cfg));
		memset((void *)&tbls, 0, sizeof(struct xlat_ctx_tbls));

		/* VA space boundaries */
		start_va = get_start_va(region, ST1_XLAT_TEST_MAX_VA_SIZE);
		end_va = start_va + ST1_XLAT_TEST_MAX_VA_SIZE - 1ULL;

		gen_rand_mmap_array(&init_mmap[0], mmap_count, start_va,
				    end_va);

		/* Initialize the test structure */
		retval = xlat_ctx_cfg_init(&cfg, region, &init_mmap[0],
					mmap_count, ST1_XLAT_TEST_MAX_VA_SIZE);

		/* Verify that the context cfg is properly created */
		CHECK_TRUE(retval == 0);

		memcpy((void *)&val_cfg, (void *)&cfg,
			sizeof(struct xlat_ctx_cfg));

		/* Test xlat_ctx_init() */
		retval = xlat_ctx_init(&ctx, &cfg, &tbls, &xlat_tables[0],
				STAGE1_XLAT_TEST_MAX_TABLES);

		/* Verify the result */
		CHECK_TRUE(retval == 0);

		/* Validate that the configuration has not been altered */
		MEMCMP_EQUAL((void *)&val_cfg, (void *)&cfg,
			     sizeof(struct xlat_ctx_cfg));

		/* Validate the xlat_ctx structure */
		CHECK_TRUE(ctx.cfg == &cfg);
		CHECK_TRUE(ctx.tbls == &tbls);

		/*
		 * Validate the xlat_ctx_tbls structure.
		 *
		 * NOTE: As the number of memory regions and the regions
		 * themselves are random, the `next_table` field is not
		 * validated here. Instead, it will be validated for each
		 * especific test later.
		 */
		CHECK_TRUE(tbls.initialized == true);
		CHECK_TRUE(tbls.tables == &xlat_tables[0]);
		CHECK_TRUE(tbls.tables_num == STAGE1_XLAT_TEST_MAX_TABLES);
	}
}

TEST(stage1_xlat, xlat_ctx_init_TC2)
{
	struct xlat_ctx ctx;
	struct xlat_ctx_cfg cfg;
	struct xlat_ctx_tbls tbls;
	int retval;
	uint64_t xlat_tables[ST1_XLAT_TESTS_TBL_ENTRIES
				* STAGE1_XLAT_TEST_MAX_TABLES]
				__aligned(ST1_XLAT_TESTS_TBL_ALIGNMENT);

	/***************************************************************
	 * TEST CASE 2:
	 *
	 * Try to initialize a context with an invalid configuration
	 ***************************************************************/

	/* Clean the data structures */
	memset((void *)&ctx, 0, sizeof(struct xlat_ctx));
	memset((void *)&cfg, 0, sizeof(struct xlat_ctx_cfg));
	memset((void *)&tbls, 0, sizeof(struct xlat_ctx_tbls));

	/* Test xlat_ctx_init() */
	retval = xlat_ctx_init(&ctx, &cfg, &tbls, &xlat_tables[0],
				STAGE1_XLAT_TEST_MAX_TABLES);

	/* Verify the result */
	CHECK_TRUE(retval == -EINVAL);
}

TEST(stage1_xlat, xlat_ctx_init_TC3)
{
	struct xlat_ctx ctx;
	struct xlat_ctx_tbls tbls;
	int retval;
	uint64_t xlat_tables[ST1_XLAT_TESTS_TBL_ENTRIES
				* STAGE1_XLAT_TEST_MAX_TABLES]
				__aligned(ST1_XLAT_TESTS_TBL_ALIGNMENT);

	/***************************************************************
	 * TEST CASE 3:
	 *
	 * Try to initialize a context with a NULL configuration
	 ***************************************************************/

	/* Clean the data structures */
	memset((void *)&ctx, 0, sizeof(struct xlat_ctx));
	memset((void *)&tbls, 0, sizeof(struct xlat_ctx_tbls));

	/* Test xlat_ctx_init() */
	retval = xlat_ctx_init(&ctx, NULL, &tbls, &xlat_tables[0],
				STAGE1_XLAT_TEST_MAX_TABLES);

	/* Verify the result */
	CHECK_TRUE(retval == -EINVAL);
}

TEST(stage1_xlat, xlat_ctx_init_TC4)
{
	struct xlat_ctx ctx;
	struct xlat_ctx_cfg cfg;
	uintptr_t start_va, end_va;
	unsigned int mmap_count;
	xlat_addr_region_id_t region;
	int retval;
	struct xlat_mmap_region init_mmap[STAGE1_XLAT_TEST_MAX_MMAPS];
	uint64_t xlat_tables[ST1_XLAT_TESTS_TBL_ENTRIES
				* STAGE1_XLAT_TEST_MAX_TABLES]
				__aligned(ST1_XLAT_TESTS_TBL_ALIGNMENT);

	/***************************************************************
	 * TEST CASE 4:
	 *
	 * Try to initialize a context with a NULL xlat_ctx_tbls
	 * structure
	 ***************************************************************/

	for (unsigned int i = 0U; i < (unsigned int)VA_REGIONS; i++) {
		region = (xlat_addr_region_id_t)i;

		/* Initialize some parameters with random data */
		mmap_count = test_helpers_get_rand_in_range(1,
						STAGE1_XLAT_TEST_MAX_MMAPS);

		/* Clean the data structures */
		memset((void *)&ctx, 0, sizeof(struct xlat_ctx));
		memset((void *)&cfg, 0, sizeof(struct xlat_ctx_cfg));

		/* VA space boundaries */
		start_va = get_start_va(region, ST1_XLAT_TEST_MAX_VA_SIZE);
		end_va = start_va + ST1_XLAT_TEST_MAX_VA_SIZE - 1ULL;

		gen_rand_mmap_array(&init_mmap[0], mmap_count, start_va,
				    end_va);

		/* Initialize the test structure */
		retval = xlat_ctx_cfg_init(&cfg, region, &init_mmap[0],
					mmap_count, ST1_XLAT_TEST_MAX_VA_SIZE);

		/* Verify that the context cfg is properly created */
		CHECK_TRUE(retval == 0);

		/* Test xlat_ctx_init() */
		retval = xlat_ctx_init(&ctx, &cfg, NULL, &xlat_tables[0],
					STAGE1_XLAT_TEST_MAX_TABLES);

		/* Verify the result */
		CHECK_TRUE(retval == -EINVAL);
	}
}

TEST(stage1_xlat, xlat_ctx_init_TC5)
{
	struct xlat_ctx ctx;
	struct xlat_ctx_cfg cfg;
	struct xlat_ctx_tbls tbls;
	uintptr_t start_va, end_va;
	unsigned int mmap_count;
	xlat_addr_region_id_t region;
	int retval;
	struct xlat_mmap_region init_mmap[STAGE1_XLAT_TEST_MAX_MMAPS];

	/***************************************************************
	 * TEST CASE 5:
	 *
	 * Try to initialize a context with a NULL set of translation
	 * tables
	 ***************************************************************/

	for (unsigned int i = 0U; i < (unsigned int)VA_REGIONS; i++) {
		region = (xlat_addr_region_id_t)i;

		/* Initialize some parameters with random data */
		mmap_count = test_helpers_get_rand_in_range(1,
						STAGE1_XLAT_TEST_MAX_MMAPS);

		/* Clean the data structures */
		memset((void *)&ctx, 0, sizeof(struct xlat_ctx));
		memset((void *)&cfg, 0, sizeof(struct xlat_ctx_cfg));
		memset((void *)&tbls, 0, sizeof(struct xlat_ctx_tbls));

		/* VA space boundaries */
		start_va = get_start_va(region, ST1_XLAT_TEST_MAX_VA_SIZE);
		end_va = start_va + ST1_XLAT_TEST_MAX_VA_SIZE - 1ULL;

		gen_rand_mmap_array(&init_mmap[0], mmap_count, start_va,
				    end_va);

		/* Initialize the test structure */
		retval = xlat_ctx_cfg_init(&cfg, region, &init_mmap[0],
					mmap_count, ST1_XLAT_TEST_MAX_VA_SIZE);

		/* Verify that the context cfg is properly created */
		CHECK_TRUE(retval == 0);

		/* Test xlat_ctx_init() */
		retval = xlat_ctx_init(&ctx, &cfg, &tbls, NULL,
					STAGE1_XLAT_TEST_MAX_TABLES);

		/* Verify the result */
		CHECK_TRUE(retval == -EINVAL);
	}
}

TEST(stage1_xlat, xlat_ctx_init_TC6)
{
	struct xlat_ctx_cfg cfg;
	struct xlat_ctx_tbls tbls;
	uintptr_t start_va, end_va;
	unsigned int mmap_count;
	xlat_addr_region_id_t region;
	int retval;
	struct xlat_mmap_region init_mmap[STAGE1_XLAT_TEST_MAX_MMAPS];
	uint64_t xlat_tables[ST1_XLAT_TESTS_TBL_ENTRIES
				* STAGE1_XLAT_TEST_MAX_TABLES]
				__aligned(ST1_XLAT_TESTS_TBL_ALIGNMENT >> 2U);

	/***************************************************************
	 * TEST CASE 6:
	 *
	 * Try to initialize a NULL context
	 ***************************************************************/

	for (unsigned int i = 0U; i < (unsigned int)VA_REGIONS; i++) {
		region = (xlat_addr_region_id_t)i;

		/* Initialize some parameters with random data */
		mmap_count = test_helpers_get_rand_in_range(1,
						STAGE1_XLAT_TEST_MAX_MMAPS);

		/* Clean the data structures */
		memset((void *)&cfg, 0, sizeof(struct xlat_ctx_cfg));
		memset((void *)&tbls, 0, sizeof(struct xlat_ctx_tbls));

		/* VA space boundaries */
		start_va = get_start_va(region, ST1_XLAT_TEST_MAX_VA_SIZE);
		end_va = start_va + ST1_XLAT_TEST_MAX_VA_SIZE - 1ULL;

		gen_rand_mmap_array(&init_mmap[0], mmap_count, start_va,
				    end_va);

		/* Initialize the test structure */
		retval = xlat_ctx_cfg_init(&cfg, region, &init_mmap[0],
					mmap_count, ST1_XLAT_TEST_MAX_VA_SIZE);

		/* Verify that the context cfg is properly created */
		CHECK_TRUE(retval == 0);

		/* Test xlat_ctx_init() */
		retval = xlat_ctx_init(NULL, &cfg, &tbls, &xlat_tables[0],
					STAGE1_XLAT_TEST_MAX_TABLES);

		/* Verify the result */
		CHECK_TRUE(retval == -EINVAL);
	}
}

TEST(stage1_xlat, xlat_ctx_init_TC7)
{
	struct xlat_ctx ctx;
	struct xlat_ctx_cfg cfg;
	struct xlat_ctx_tbls tbls;
	uintptr_t start_va, end_va;
	unsigned int mmap_count;
	unsigned int offset;
	xlat_addr_region_id_t region;
	int retval;
	struct xlat_mmap_region init_mmap[STAGE1_XLAT_TEST_MAX_MMAPS];
	uint64_t xlat_tables[ST1_XLAT_TESTS_TBL_ENTRIES
				* STAGE1_XLAT_TEST_MAX_TABLES]
				__aligned(ST1_XLAT_TESTS_TBL_ALIGNMENT);

	/***************************************************************
	 * TEST CASE 7:
	 *
	 * Try to initialize a context with a set of unaligned
	 * translation tables
	 ***************************************************************/

	for (unsigned int i = 0U; i < (unsigned int)VA_REGIONS; i++) {
		region = (xlat_addr_region_id_t)i;

		/* Initialize some parameters with random data */
		mmap_count = test_helpers_get_rand_in_range(1,
						STAGE1_XLAT_TEST_MAX_MMAPS);
		offset = test_helpers_get_rand_in_range(1,
						ST1_XLAT_TESTS_TBL_ENTRIES - 1);

		/* Clean the data structures */
		memset((void *)&ctx, 0, sizeof(struct xlat_ctx));
		memset((void *)&cfg, 0, sizeof(struct xlat_ctx_cfg));
		memset((void *)&tbls, 0, sizeof(struct xlat_ctx_tbls));

		/* VA space boundaries */
		start_va = get_start_va(region, ST1_XLAT_TEST_MAX_VA_SIZE);
		end_va = start_va + ST1_XLAT_TEST_MAX_VA_SIZE - 1ULL;

		gen_rand_mmap_array(&init_mmap[0], mmap_count, start_va,
				    end_va);

		/* Initialize the test structure */
		retval = xlat_ctx_cfg_init(&cfg, region, &init_mmap[0],
					mmap_count, ST1_XLAT_TEST_MAX_VA_SIZE);

		/* Verify that the context cfg is properly created */
		CHECK_TRUE(retval == 0);

		/* Test xlat_ctx_init() */
		retval = xlat_ctx_init(&ctx, &cfg, &tbls, &xlat_tables[offset],
					STAGE1_XLAT_TEST_MAX_TABLES);

		/* Verify the result */
		CHECK_TRUE(retval == -EINVAL);
	}
}

/* Generate a start va given a walk start level and a region */
static unsigned long long gen_start_va_by_level(unsigned int level,
						xlat_addr_region_id_t region,
						size_t *va_size)
{
	assert(level <= XLAT_TABLE_LEVEL_MAX);
	assert(va_size != NULL);

	*va_size = (1ULL << (ST1_XLAT_TABLE_LVL_SHIFT(level) +
				ST1_XLAT_TESTS_TBL_ENTRIES_SHIFT));

	return get_start_va(region, *va_size);
}

/*
 * Define a limit on the maximum entry index we can use on a table,
 * so we have room for extra mmap regions on that table if needed.
 */
#define STAGE1_XLAT_TEST_LAST_RANDOM_ENTRY			\
					(ST1_XLAT_TESTS_TBL_ENTRIES - 20)

/*
 * Generate a mmap array containing a set of mmap regions defined by
 * 'start_va', 'level' and 'region. The mmap array will have three regions:
 *
 *	- First region mapped at the beginning of a table which final
 *	  lookup level is 'level'
 *	- Second region mapped at a random tte of a table which final
 *	  lookup level is 'level'
 *	- Third region mapped at the end of a table which final
 *	  lookup level is 'level'
 *
 * For all the mmap regions, the granularity is setup to the minimum
 * granularity needed to map a block at level 'level'.
 *
 * This function also returns two arrays:
 *
 *	- An array with the the final lookup level for each mmap region.
 *	- An array with the tte indexes used on the last lookup level
 *	  to map the mmap region.
 * */
static int gen_mmap_array_by_level(xlat_mmap_region *mmap,
				   unsigned int *page_idxs,
				   unsigned int *levels,
				   unsigned int mmap_size,
				   unsigned int level,
				   size_t *granularity,
				   unsigned long long start_va,
				   xlat_addr_region_id_t region)
{
	uint64_t attrs;
	assert(mmap_size >= 3U);
	assert(level <= XLAT_TABLE_LEVEL_MAX);
	assert(mmap != NULL);
	assert(page_idxs != NULL);
	assert(granularity != NULL);
	assert(levels != NULL);

	/* Generate a mapping at the beginning of the table */
	page_idxs[0U] = 0U;

	/*
	 * Generate a mapping in a random possition of the table.
	 * Leave some room at the end of the table for extra entries
	 * that might be needed later.
	 */
	page_idxs[1U] = test_helpers_get_rand_in_range(1,
					STAGE1_XLAT_TEST_LAST_RANDOM_ENTRY);

	/* Generate a mapping at the end of the table */
	page_idxs[2U] = ST1_XLAT_TESTS_TBL_ENTRIES - 1U;

	do {
		attrs = get_mmap_attrs();
	} while (attrs == MT_TRANSIENT);

	*granularity = 1ULL << ST1_XLAT_TABLE_LVL_SHIFT(level);

	/* Generate the memory mapping areas to test */
	for (unsigned i = 0U; i < 3U; i++) {
		mmap[i].base_va = start_va +
					(page_idxs[i] * (*granularity));
		mmap[i].base_pa = mmap[i].base_va &
						ST1_XLAT_TEST_PA_MASK;
		mmap[i].size = *granularity;
		mmap[i].attr = attrs;
		mmap[i].granularity = *granularity;

		/* Store the expected level */
		levels[i] = level;
	}

	return 0;
}

/*
 * Given a context and a set of expected indexes and levels for the last walk,
 * validate that the translation tables in the context are valid.
 * Note that this function expects a valid and initialized context.
 */
static void validate_xlat_tables(xlat_ctx *ctx, unsigned int *expected_idxs,
				 unsigned int *expected_levels)
{
	uint64_t tte;
	unsigned int level;
	unsigned int index;
	unsigned int granularity;
	unsigned int page_offset;
	unsigned long long test_va;
	unsigned long long pa;
	unsigned int retval;
	uint64_t attrs;
	unsigned long long pa_mask;

	assert(ctx != NULL);
	assert(expected_idxs != NULL);
	assert(expected_levels != NULL);

	for (unsigned int i = 0U; i < ctx->cfg->mmap_regions; i++) {
		granularity = ctx->cfg->mmap[i].granularity;
		page_offset = test_helpers_get_rand_in_range(0,
							granularity - 1U);
		test_va = ctx->cfg->base_va + ctx->cfg->mmap[i].base_va +
								page_offset;
		pa = ctx->cfg->mmap[i].base_pa + page_offset;

		/* Perform a table walk */
		retval = st1_xlat_test_helpers_table_walk(ctx, test_va,
							  &tte, &level,
							  &index);

		/* Return value */
		CHECK_EQUAL(0, retval);

		/* Last table level */
		CHECK_EQUAL(expected_levels[i], level);

		/* tte index on the page */
		CHECK_EQUAL(expected_idxs[i], index);

		/* Expected tte attributes */
		retval = st1_xlat_test_helpers_gen_attrs(ctx, test_va, &attrs);

		/* Return value */
		CHECK_EQUAL(0, retval);

		/* Validate that the attributes are as expected */
		CHECK_EQUAL((tte & ST1_XLAT_TABLE_ATTRS_MASK), attrs);

		/* Validate the PA */
		pa_mask = (1ULL << ST1_XLAT_TABLE_LVL_SHIFT(level)) - 1ULL;
		CHECK_EQUAL((tte & ST1_XLAT_TABLE_OA_MASK), (pa & ~pa_mask));
	}
}

TEST(stage1_xlat, xlat_ctx_init_TC8)
{
	struct xlat_ctx ctx;
	struct xlat_ctx_cfg cfg;
	struct xlat_ctx_tbls tbls;
	uintptr_t start_va;
	size_t va_size, granularity;
	unsigned int mmap_count;
	xlat_addr_region_id_t region;
	int retval;
	struct xlat_mmap_region init_mmap[3U];
	uint64_t xlat_tables[ST1_XLAT_TESTS_TBL_ENTRIES
				* STAGE1_XLAT_TEST_MAX_TABLES]
				__aligned(ST1_XLAT_TESTS_TBL_ALIGNMENT);
	unsigned int page_idx[3U];
	unsigned int expected_lvls[3U];
	unsigned int start_lvl, end_lvl;

	/***************************************************************
	 * TEST CASE 8:
	 *
	 * For each possible initial lookup level, create a set of
	 * random mappings starting at such lookup level and with
	 * granularities ranging from level 1 (lower level supporting
	 * blocks) to XLAT_TABLE_LEVEL_MAX.
	 * Then verify that the tables can be walked and that the levels,
	 * offsets and attributes on the ttes are as expected.
	 * This test validates that the xlat library is able to create
	 * tables starting on any valid initial lookup level and
	 * finishing on any valid lookup level as well.
	 ***************************************************************/

	mmap_count = 3U;

	/* The first look-up level that supports blocks is L1 */
	for (end_lvl = 1U; end_lvl <= XLAT_TABLE_LEVEL_MAX; end_lvl++) {
		for (unsigned int i = 0U; i < (unsigned int)VA_REGIONS; i++) {
			region = (xlat_addr_region_id_t)i;

			for (start_lvl = 0U;
			     start_lvl <= end_lvl;
			     start_lvl++) {

				start_va = gen_start_va_by_level(start_lvl,
								 region,
								 &va_size);

				retval = gen_mmap_array_by_level(&init_mmap[0U],
								 &page_idx[0U],
								 &expected_lvls[0U],
								 mmap_count,
								 end_lvl,
								 &granularity,
								 start_va, region);

				/* Clean the data structures */
				memset((void *)&ctx, 0,
						sizeof(struct xlat_ctx));
				memset((void *)&cfg, 0,
						sizeof(struct xlat_ctx_cfg));
				memset((void *)&tbls, 0,
						sizeof(struct xlat_ctx_tbls));

				/* Initialize the test structure */
				retval = xlat_ctx_cfg_init(&cfg, region,
							   &init_mmap[0U],
							   mmap_count, va_size);

				/*
				 * Verify that the context cfg is
				 * properly created
				 */
				CHECK_TRUE(retval == 0);

				/* Test xlat_ctx_init() */
				retval = xlat_ctx_init(&ctx, &cfg, &tbls,
						       &xlat_tables[0U],
						       STAGE1_XLAT_TEST_MAX_TABLES);

				/* Verify the result */
				CHECK_TRUE(retval == 0);

				validate_xlat_tables(&ctx, &page_idx[0U],
						     &expected_lvls[0U]);
			}
		}
	}
}
