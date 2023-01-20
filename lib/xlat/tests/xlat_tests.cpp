/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <CppUTest/CommandLineTestRunner.h>
#include <CppUTest/TestHarness.h>

extern "C" {
#include <arch_helpers.h>
#include <debug.h>
#include <host_utils.h>
#include <stdlib.h>
#include <string.h>
#include <test_helpers.h>
#include <utils_def.h>
#include <xlat_contexts.h>	/* API to test */
#include <xlat_defs.h>
#include <xlat_tables.h>	/* API to test */
#include <xlat_test_defs.h>
#include <xlat_test_helpers.h>
}

/* Maximum number of tables to use on tests */
#define XLAT_TESTS_MAX_TABLES	(10U)

/* Maximum number of mmap regions to use on tests */
#define XLAT_TESTS_MAX_MMAPS	(20U)

/* Reserve some memory to be used for the translation tables */
static uint64_t xlat_tables[XLAT_TESTS_TBL_ENTRIES * XLAT_TESTS_MAX_TABLES]
					__aligned(XLAT_TESTS_TBL_ALIGNMENT);

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
				  MT_RW_DATA, MT_DEVICE, MT_TRANSIENT};
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
			  XLAT_TESTS_GRANULARITY_SIZE)) <= max_va);

	/* Randomize the base VA for the first memory region */
	region_pages = test_helpers_get_rand_in_range(0, MAX_PAGES_PER_REGION);
	next_va_start += (region_pages * XLAT_TESTS_GRANULARITY_SIZE);

	/* Generate an ordered list of mmap regions */
	for (unsigned int i = 0U; i < (unsigned int)size; i++) {
		/* Pages of memory to use for the current region */
		region_pages = test_helpers_get_rand_in_range(2,
							MAX_PAGES_PER_REGION);
		region_size = region_pages * XLAT_TESTS_GRANULARITY_SIZE;

		mmap[i].attr = get_mmap_attrs();
		mmap[i].granularity = XLAT_TESTS_MAX_BLOCK_SIZE;
		mmap[i].base_va = next_va_start;
		mmap[i].base_pa = next_va_start & XLAT_TESTS_PA_MASK;
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
static void xlat_test_cfg_init_setup(struct xlat_ctx_cfg *cfg,
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
	 */
	memcpy((void *)init_mmap, (void *)val_mmap,
		sizeof(struct xlat_mmap_region) * mmaps);

	/*
	 * xlat_ctx_cfg_init() adjusts the VA base of the mmap region passed
	 * by subtracting the base VA, so all the VAs will be on the same range
	 * regardless of the memory region where they belong. This helps to
	 * simplify the xlat tables creation.
	 */
	for (unsigned int i = 0U; i < mmaps; i++) {
		val_mmap[i].base_va -= start_va;
	}

	/* The maximum mapped va offset can never go beyond the VA size */
	max_mapped_va_offset = (val_mmap[mmaps - 1U].base_va +
				val_mmap[mmaps - 1U].size - 1U) &
					XLAT_TESTS_LOW_REGION_MASK;

	max_mapped_pa = val_mmap[mmaps - 1U].base_pa +
			val_mmap[mmaps - 1U].size - 1U;

	/* Initialize the xlat_ctx_cfg structure */
	xlat_test_helpers_init_ctx_cfg(cfg, va_size, start_va,
					   max_mapped_pa, max_mapped_va_offset,
					   XLAT_TESTS_GET_BASE_TABLE_LVL(va_size),
					   region, init_mmap, mmaps, true);
}

TEST_GROUP(xlat_tests) {
	TEST_SETUP()
	{
		static int random_seed = 0;

		/* Initialize the random seed */
		while (random_seed == 0) {
			random_seed = (int)time(NULL);
			srand(random_seed);
		}

		xlat_test_hepers_arch_init();
	}

	TEST_TEARDOWN()
	{}
};

TEST(xlat_tests, MAP_REGION_FULL_SPEC_TC1)
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

TEST(xlat_tests, MAP_REGION_TC1)
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
		.granularity = XLAT_TESTS_MAX_BLOCK_SIZE
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

TEST(xlat_tests, MAP_REGION_FLAT_TC1)
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
		.granularity = XLAT_TESTS_MAX_BLOCK_SIZE
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

TEST(xlat_tests, MAP_REGION_TRANSIENT_TC1)
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

TEST(xlat_tests, xlat_ctx_cfg_init_TC1)
{
	struct xlat_ctx_cfg expected_cfg, test_cfg;
	struct xlat_mmap_region init_mmap[XLAT_TESTS_MAX_MMAPS];
	struct xlat_mmap_region val_mmap[XLAT_TESTS_MAX_MMAPS];
	xlat_addr_region_id_t region;
	int retval;

	/***************************************************************
	 * TEST CASE 1:
	 *
	 * Initialize a xlat_ctx_cfg structure with random data through
	 * xlat_ctx_cfg_init(). Then verify that the initialization
	 * was as expected.
	 ***************************************************************/

	for (unsigned int i = 0U; i < (unsigned int)VA_REGIONS; i++) {
		region = (xlat_addr_region_id_t)i;

		/* Clean the data structures */
		memset((void *)&test_cfg, 0, sizeof(struct xlat_ctx_cfg));

		/* Initialize the test structures with the expected values */
		xlat_test_cfg_init_setup(&expected_cfg, &init_mmap[0],
					 &val_mmap[0], XLAT_TESTS_MAX_MMAPS,
					 XLAT_TESTS_MAX_VA_SIZE, region);

		/* Initialize the test structure */
		retval = xlat_ctx_cfg_init(&test_cfg, region, &init_mmap[0],
					   XLAT_TESTS_MAX_MMAPS,
					   XLAT_TESTS_MAX_VA_SIZE);

		/* Verify the result */
		CHECK_TRUE(retval == 0);

		/*
		 * Verify that the memory regions array used with
		 * xlat_ctx_cfg_init() has been properly normalized.
		 */
		MEMCMP_EQUAL((void *)&val_mmap[0], (void *)&init_mmap[0],
		     sizeof(struct xlat_mmap_region) * XLAT_TESTS_MAX_MMAPS);

		/*
		 * Test that the xlat_ctx_cfg structure is
		 * properly initialized.
		 */
		MEMCMP_EQUAL((void *)&expected_cfg, (void *)&test_cfg,
			     sizeof(struct xlat_ctx_cfg));
	}
}

TEST(xlat_tests, xlat_ctx_cfg_init_TC2)
{
	struct xlat_ctx_cfg foo_cfg;
	struct xlat_mmap_region init_mmap[XLAT_TESTS_MAX_MMAPS];
	struct xlat_mmap_region val_mmap[XLAT_TESTS_MAX_MMAPS];
	xlat_addr_region_id_t region;
	int retval;

	/***************************************************************
	 * TEST CASE 2:
	 *
	 * Try to initialize a NULL xlat_ctx_cfg structure.
	 * All the rest of parameters will be valid.
	 ***************************************************************/

	for (unsigned int i = 0U; i < (unsigned int)VA_REGIONS; i++) {
		region = (xlat_addr_region_id_t)i;

		/* Initialize the test structures with the expected values */
		xlat_test_cfg_init_setup(&foo_cfg, &init_mmap[0], &val_mmap[0],
					 XLAT_TESTS_MAX_MMAPS,
					 XLAT_TESTS_MAX_VA_SIZE,
					 region);

		/* Initialize the test structure */
		retval = xlat_ctx_cfg_init(NULL, region, &init_mmap[0],
					   XLAT_TESTS_MAX_MMAPS,
					   XLAT_TESTS_MAX_VA_SIZE);

		/* Verify the result */
		CHECK_TRUE(retval == -EINVAL);
	}
}

TEST(xlat_tests, xlat_ctx_cfg_init_TC3)
{
	struct xlat_ctx_cfg test_cfg;
	xlat_addr_region_id_t region;
	int retval;

	/***************************************************************
	 * TEST CASE 3:
	 *
	 * Try to initialize a xlat_ctx_cfg structure with a NULL list
	 * of mmap regions.
	 * All the rest of parameters will be valid.
	 ***************************************************************/

	for (unsigned int i = 0U; i < (unsigned int)VA_REGIONS; i++) {
		region = (xlat_addr_region_id_t)i;

		/* Clean the data structures */
		memset((void *)&test_cfg, 0, sizeof(struct xlat_ctx_cfg));

		/* Initialize the test structure */
		retval = xlat_ctx_cfg_init(&test_cfg, region, NULL,
					   XLAT_TESTS_MAX_MMAPS,
					   XLAT_TESTS_MAX_VA_SIZE);

		/* Verify the result */
		CHECK_TRUE(retval == -EINVAL);
	}
}

TEST(xlat_tests, xlat_ctx_cfg_init_TC4)
{
	struct xlat_ctx_cfg foo_cfg, test_cfg;
	struct xlat_mmap_region test_mmap[XLAT_TESTS_MAX_MMAPS];
	struct xlat_mmap_region init_mmap[XLAT_TESTS_MAX_MMAPS];
	xlat_addr_region_id_t mmap_region, cfg_region;
	int retval;

	/***************************************************************
	 * TEST CASE 4:
	 *
	 * Try to initialize a xlat_ctx_cfg structure with random data
	 * where the xlat_addr_region_id_t does not match the mmap
	 * regions.
	 ***************************************************************/

	for (unsigned int i = 0U; i < (unsigned int)VA_REGIONS; i++) {
		mmap_region = (xlat_addr_region_id_t)i;
		cfg_region = (xlat_addr_region_id_t)((i + 1U) % VA_REGIONS);

		/* Clean the data structures */
		memset((void *)&test_cfg, 0, sizeof(struct xlat_ctx_cfg));

		/* Initialize the test structures with the expected values */
		xlat_test_cfg_init_setup(&foo_cfg, &init_mmap[0], &test_mmap[0],
				XLAT_TESTS_MAX_MMAPS, XLAT_TESTS_MAX_VA_SIZE,
				mmap_region);

		/* Initialize the test structure */
		retval = xlat_ctx_cfg_init(&test_cfg, cfg_region,
					   &init_mmap[0], XLAT_TESTS_MAX_MMAPS,
					   XLAT_TESTS_MAX_VA_SIZE);

		/* Verify the result */
		CHECK_TRUE(retval == -EINVAL);
	}
}

TEST(xlat_tests, xlat_ctx_cfg_init_TC5)
{
	struct xlat_ctx_cfg test_cfg;
	struct xlat_mmap_region init_mmap[XLAT_TESTS_MAX_MMAPS];
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
			sizeof(xlat_mmap_region) * XLAT_TESTS_MAX_MMAPS);

		/* Initialize the test structure */
		retval = xlat_ctx_cfg_init(&test_cfg, region, &init_mmap[0], 0U,
						XLAT_TESTS_MAX_VA_SIZE);

		/* Verify the result */
		CHECK_TRUE(retval == -EINVAL);
	}
}

TEST(xlat_tests, xlat_ctx_cfg_init_TC6)
{
	struct xlat_ctx_cfg test_cfg, foo_cfg;
	struct xlat_mmap_region init_mmap[XLAT_TESTS_MAX_MMAPS];
	struct xlat_mmap_region val_mmap[XLAT_TESTS_MAX_MMAPS];
	xlat_addr_region_id_t region;
	int retval;
	size_t misaligned_va;

	/***************************************************************
	 * TEST CASE 6:
	 *
	 * Try to initialize a xlat_ctx_cfg structure with an unaligned
	 * va space size.
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
		misaligned_va =	XLAT_TESTS_GRANULARITY_SIZE *
				(XLAT_TESTS_MAX_VA_PAGES - 1);

		/* Add a random offset to it to misalign */
		misaligned_va += test_helpers_get_rand_in_range(1,
					XLAT_TESTS_GRANULARITY_SIZE - 1);

		/* Clean the data structures */
		memset((void *)&test_cfg, 0, sizeof(struct xlat_ctx_cfg));

		/* Initialize the test structures with the expected values */
		xlat_test_cfg_init_setup(&foo_cfg, &init_mmap[0], &val_mmap[0],
					XLAT_TESTS_MAX_MMAPS,
					XLAT_TESTS_MAX_VA_SIZE, region);

		/* Initialize the test structure */
		retval = xlat_ctx_cfg_init(&test_cfg, region, &init_mmap[0],
					   XLAT_TESTS_MAX_MMAPS,
					   misaligned_va);

		/* Verify the result */
		CHECK_TRUE(retval == -EINVAL);
	}
}

TEST(xlat_tests, xlat_ctx_cfg_init_TC7)
{
	struct xlat_ctx_cfg test_cfg, foo_cfg;
	struct xlat_mmap_region init_mmap[XLAT_TESTS_MAX_MMAPS];
	struct xlat_mmap_region test_mmap[XLAT_TESTS_MAX_MMAPS];
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

		va_size = (XLAT_TESTS_GRANULARITY_SIZE *
					(XLAT_TESTS_MAX_VA_PAGES + 1U));

		/* Clean the data structures */
		memset((void *)&test_cfg, 0, sizeof(struct xlat_ctx_cfg));

		/* Initialize the test structures with the expected values */
		xlat_test_cfg_init_setup(&foo_cfg, &init_mmap[0], &test_mmap[0],
					XLAT_TESTS_MAX_MMAPS,
					XLAT_TESTS_MAX_VA_SIZE, region);

		/* Initialize the test structure */
		retval = xlat_ctx_cfg_init(&test_cfg, region, &init_mmap[0],
					   XLAT_TESTS_MAX_MMAPS,
					   va_size);

		/* Verify the result */
		CHECK_TRUE(retval == -EINVAL);
	}
}

TEST(xlat_tests, xlat_ctx_cfg_init_TC8)
{
	struct xlat_ctx_cfg test_cfg, foo_cfg;
	struct xlat_mmap_region init_mmap[XLAT_TESTS_MAX_MMAPS];
	struct xlat_mmap_region val_mmap[XLAT_TESTS_MAX_MMAPS];
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

		va_size = (XLAT_TESTS_GRANULARITY_SIZE *
					(XLAT_TESTS_MIN_VA_PAGES - 1U));

		/* Clean the data structures */
		memset((void *)&test_cfg, 0, sizeof(struct xlat_ctx_cfg));

		/* Initialize the test structures with the expected values */
		xlat_test_cfg_init_setup(&foo_cfg, &init_mmap[0], &val_mmap[0],
					XLAT_TESTS_MAX_MMAPS,
					XLAT_TESTS_MAX_VA_SIZE, region);

		/* Initialize the test structure */
		retval = xlat_ctx_cfg_init(&test_cfg, region, &init_mmap[0],
					   XLAT_TESTS_MAX_MMAPS,
					   va_size);

		/* Verify the result */
		CHECK_TRUE(retval == -EINVAL);
	}
}

TEST(xlat_tests, xlat_ctx_cfg_init_TC9)
{
	struct xlat_ctx_cfg test_cfg;
	struct xlat_mmap_region init_mmap[XLAT_TESTS_MAX_MMAPS];
	struct xlat_mmap_region val_mmap[XLAT_TESTS_MAX_MMAPS];
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
		xlat_test_cfg_init_setup(&test_cfg, &init_mmap[0], &val_mmap[0],
					XLAT_TESTS_MAX_MMAPS,
					XLAT_TESTS_MAX_VA_SIZE, region);

		/* Initialize the test structure */
		retval = xlat_ctx_cfg_init(&test_cfg, region, &init_mmap[0],
					   XLAT_TESTS_MAX_MMAPS,
					   XLAT_TESTS_MAX_VA_SIZE);

		/* Verify the result */
		CHECK_TRUE(retval == -EALREADY);
	}
}

TEST(xlat_tests, xlat_ctx_cfg_init_TC10)
{
	struct xlat_ctx_cfg test_cfg, foo_cfg;
	struct xlat_mmap_region init_mmap[XLAT_TESTS_MAX_MMAPS];
	struct xlat_mmap_region val_mmap[XLAT_TESTS_MAX_MMAPS];
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
		xlat_test_cfg_init_setup(&foo_cfg, &init_mmap[0], &val_mmap[0],
					XLAT_TESTS_MAX_MMAPS,
					XLAT_TESTS_MAX_VA_SIZE, region);

		/* Overwrite the mmap structures to make the VAs overlap */
		mmap_index = (unsigned int)test_helpers_get_rand_in_range(1,
					XLAT_TESTS_MAX_MMAPS - 1);
		/*
		 * The base_va of mmap entry at 'mmap_index' is adjusted to an
		 * offset of 'XLAT_TESTS_GRANULARITY_SIZE' of previous entry.
		 * Each entry is at least 2 pages size, so the regions will
		 * overlap whilst keeping in ascending order of VA.
		 */
		init_mmap[mmap_index].base_va =
			init_mmap[mmap_index - 1U].base_va +
					 XLAT_TESTS_GRANULARITY_SIZE;

		/* Initialize the test structure */
		retval = xlat_ctx_cfg_init(&test_cfg, region, &init_mmap[0],
					   XLAT_TESTS_MAX_MMAPS,
					   XLAT_TESTS_MAX_VA_SIZE);

		/* Verify the result */
		CHECK_TRUE(retval == -EPERM);
	}
}

TEST(xlat_tests, xlat_ctx_cfg_init_TC11)
{
	struct xlat_ctx_cfg test_cfg, foo_cfg;
	struct xlat_mmap_region init_mmap[XLAT_TESTS_MAX_MMAPS];
	struct xlat_mmap_region val_mmap[XLAT_TESTS_MAX_MMAPS];
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
		xlat_test_cfg_init_setup(&foo_cfg, &init_mmap[0], &val_mmap[0],
					XLAT_TESTS_MAX_MMAPS,
					XLAT_TESTS_MAX_VA_SIZE, region);

		/* Overwrite the mmap structures to make the PAs overlap */
		mmap_index = (unsigned int)test_helpers_get_rand_in_range(1,
					XLAT_TESTS_MAX_MMAPS - 1);
		/*
		 * The base_pa of mmap entry at 'mmap_index' is adjusted to an
		 * offset of 'XLAT_TESTS_GRANULARITY_SIZE' of previous entry
		 * ('base_pa' is set to the same value as 'base_va').
		 * Each entry is at least 2 pages size, so the PA regions will
		 * overlap.
		 */
		init_mmap[mmap_index].base_pa =
			init_mmap[mmap_index - 1U].base_pa +
					 XLAT_TESTS_GRANULARITY_SIZE;

		/* Initialize the test structure */
		retval = xlat_ctx_cfg_init(&test_cfg, region, &init_mmap[0],
					   XLAT_TESTS_MAX_MMAPS,
					   XLAT_TESTS_MAX_VA_SIZE);

		/* Verify the result */
		CHECK_TRUE(retval == -EPERM);
	}
}

TEST(xlat_tests, xlat_ctx_cfg_init_TC12)
{
	struct xlat_ctx_cfg test_cfg, foo_cfg;
	struct xlat_mmap_region init_mmap[XLAT_TESTS_MAX_MMAPS];
	struct xlat_mmap_region val_mmap[XLAT_TESTS_MAX_MMAPS];
	xlat_addr_region_id_t region;
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
	host_write_sysreg("id_aa64mmfr0_el1",
			  INPLACE(ID_AA64MMFR0_EL1_PARANGE, index));

	for (unsigned int i = 0U; i < (unsigned int)VA_REGIONS; i++) {
		region = (xlat_addr_region_id_t)i;

		/* Clean the data structures */
		memset((void *)&test_cfg, 0, sizeof(struct xlat_ctx_cfg));

		/* Initialize the test structures with the expected values */
		xlat_test_cfg_init_setup(&foo_cfg, &init_mmap[0], &val_mmap[0],
					XLAT_TESTS_MAX_MMAPS,
					XLAT_TESTS_MAX_VA_SIZE, region);

		/*
		 * Overwrite the PA of the last memory map region to
		 * be higher than the maximum PA supported.
		 */
		init_mmap[XLAT_TESTS_MAX_MMAPS - 1U].base_pa =
					1ULL << pa_range_bits_arr[index];

		/* Initialize the test structure */
		retval = xlat_ctx_cfg_init(&test_cfg, region, &init_mmap[0],
					   XLAT_TESTS_MAX_MMAPS,
					   XLAT_TESTS_MAX_VA_SIZE);

		/* Verify the result */
		CHECK_TRUE(retval == -ERANGE);
	}
}

TEST(xlat_tests, xlat_ctx_cfg_init_TC13)
{
	struct xlat_ctx_cfg test_cfg, foo_cfg;
	struct xlat_mmap_region init_mmap[XLAT_TESTS_MAX_MMAPS];
	struct xlat_mmap_region val_mmap[XLAT_TESTS_MAX_MMAPS];
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
		 * generate an array of random memory mapping regions.
		 */
		xlat_test_cfg_init_setup(&foo_cfg, &init_mmap[0], &val_mmap[0],
					XLAT_TESTS_MAX_MMAPS,
					XLAT_TESTS_MAX_VA_SIZE, region);

		/*
		 * Overwrite the PA on one of the memory map regions to
		 * make it misaligned.
		 */
		mmap_index = (unsigned int)test_helpers_get_rand_in_range(0,
					XLAT_TESTS_MAX_MMAPS - 1);
		init_mmap[mmap_index].base_pa +=
				test_helpers_get_rand_in_range(1,
					XLAT_TESTS_GRANULARITY_SIZE - 1);

		/* Initialize the test structure */
		retval = xlat_ctx_cfg_init(&test_cfg, region, &init_mmap[0],
					   XLAT_TESTS_MAX_MMAPS,
					   XLAT_TESTS_MAX_VA_SIZE);

		/* Verify the result */
		CHECK_TRUE(retval == -EFAULT);
	}
}

TEST(xlat_tests, xlat_ctx_cfg_init_TC14)
{
	struct xlat_ctx_cfg test_cfg, foo_cfg;
	struct xlat_mmap_region init_mmap[XLAT_TESTS_MAX_MMAPS];
	struct xlat_mmap_region val_mmap[XLAT_TESTS_MAX_MMAPS];
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
		xlat_test_cfg_init_setup(&foo_cfg, &init_mmap[0], &val_mmap[0],
					XLAT_TESTS_MAX_MMAPS,
					XLAT_TESTS_MAX_VA_SIZE, region);

		/*
		 * Overwrite the VA on one of the memory map regions to
		 * make it misaligned.
		 */
		mmap_index = (unsigned int)test_helpers_get_rand_in_range(0,
					XLAT_TESTS_MAX_MMAPS - 1);
		init_mmap[mmap_index].base_va +=
				test_helpers_get_rand_in_range(1,
					XLAT_TESTS_GRANULARITY_SIZE - 1);

		/* Initialize the test structure */
		retval = xlat_ctx_cfg_init(&test_cfg, region, &init_mmap[0],
					   XLAT_TESTS_MAX_MMAPS,
					   XLAT_TESTS_MAX_VA_SIZE);

		/* Verify the result */
		CHECK_TRUE(retval == -EFAULT);
	}
}

TEST(xlat_tests, xlat_ctx_cfg_init_TC15)
{
	struct xlat_ctx_cfg test_cfg, foo_cfg;
	struct xlat_mmap_region init_mmap[XLAT_TESTS_MAX_MMAPS];
	struct xlat_mmap_region val_mmap[XLAT_TESTS_MAX_MMAPS];
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
		xlat_test_cfg_init_setup(&foo_cfg, &init_mmap[0], &val_mmap[0],
					XLAT_TESTS_MAX_MMAPS,
					XLAT_TESTS_MAX_VA_SIZE, region);

		/*
		 * Overwrite the size on one of the memory map regions to
		 * make it misaligned.
		 */
		mmap_index = (unsigned int)test_helpers_get_rand_in_range(0,
					XLAT_TESTS_MAX_MMAPS - 1);
		init_mmap[mmap_index].size -= test_helpers_get_rand_in_range(1,
					XLAT_TESTS_GRANULARITY_SIZE - 1);

		/* Initialize the test structure */
		retval = xlat_ctx_cfg_init(&test_cfg, region, &init_mmap[0],
					   XLAT_TESTS_MAX_MMAPS,
					   XLAT_TESTS_MAX_VA_SIZE);

		/* Verify the result */
		CHECK_TRUE(retval == -EFAULT);
	}
}

TEST(xlat_tests, xlat_ctx_cfg_init_TC16)
{
	struct xlat_ctx_cfg test_cfg, foo_cfg;
	struct xlat_mmap_region init_mmap[XLAT_TESTS_MAX_MMAPS];
	struct xlat_mmap_region val_mmap[XLAT_TESTS_MAX_MMAPS];
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
		xlat_test_cfg_init_setup(&foo_cfg, &init_mmap[0], &val_mmap[0],
					XLAT_TESTS_MAX_MMAPS,
					XLAT_TESTS_MAX_VA_SIZE, region);

		/*
		 * Overwrite a memory mapping region to make it a duplicate
		 * of the previous one.
		 */
		mmap_index = (unsigned int)test_helpers_get_rand_in_range(1,
					XLAT_TESTS_MAX_MMAPS - 1);
		memcpy((void *)&init_mmap[mmap_index],
		       (void *)&init_mmap[mmap_index - 1U],
		       sizeof (struct xlat_mmap_region));

		/* Initialize the test structure */
		retval = xlat_ctx_cfg_init(&test_cfg, region, &init_mmap[0],
					   XLAT_TESTS_MAX_MMAPS,
					   XLAT_TESTS_MAX_VA_SIZE);

		/* Verify the result */
		CHECK_TRUE(retval == -EPERM);
	}
}

TEST(xlat_tests, xlat_ctx_cfg_init_TC17)
{
	struct xlat_ctx_cfg test_cfg, foo_cfg;
	struct xlat_mmap_region init_mmap[XLAT_TESTS_MAX_MMAPS];
	struct xlat_mmap_region val_mmap[XLAT_TESTS_MAX_MMAPS];
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
		xlat_test_cfg_init_setup(&foo_cfg, &init_mmap[0], &val_mmap[0],
					XLAT_TESTS_MAX_MMAPS,
					XLAT_TESTS_MAX_VA_SIZE, region);

		/* Randomly shuffle the memory mapping areas */
		buffer_suffle((unsigned char *)&init_mmap[0],
				sizeof(struct xlat_mmap_region) *
						XLAT_TESTS_MAX_MMAPS,
				sizeof(struct xlat_mmap_region));

		/* Initialize the test structure */
		retval = xlat_ctx_cfg_init(&test_cfg, region, &init_mmap[0],
					   XLAT_TESTS_MAX_MMAPS,
					   XLAT_TESTS_MAX_VA_SIZE);

		/* Verify the result */
		CHECK_TRUE(retval == -EPERM);
	}
}

TEST(xlat_tests, xlat_ctx_init_TC1)
{
	struct xlat_ctx ctx;
	struct xlat_ctx_cfg cfg, val_cfg;
	struct xlat_ctx_tbls tbls;
	uintptr_t start_va, end_va;
	xlat_addr_region_id_t region;
	int retval;
	struct xlat_mmap_region init_mmap[XLAT_TESTS_MAX_MMAPS];

	/***************************************************************
	 * TEST CASE 1:
	 *
	 * Initialize a context with a number of valid random
	 * memory mapping areas and generate the corresponding
	 * translation tables.
	 * Verify that the return code from xlat_ctx_init() is as
	 * expected and the context is properly generated.
	 * This test does not perform any check on the translation
	 * tables themselves.
	 ***************************************************************/

	for (unsigned int i = 0U; i < (unsigned int)VA_REGIONS; i++) {
		region = (xlat_addr_region_id_t)i;

		/* Clean the data structures */
		memset((void *)&ctx, 0, sizeof(struct xlat_ctx));
		memset((void *)&cfg, 0, sizeof(struct xlat_ctx_cfg));
		memset((void *)&tbls, 0, sizeof(struct xlat_ctx_tbls));

		/* VA space boundaries */
		start_va = get_start_va(region, XLAT_TESTS_MAX_VA_SIZE);
		end_va = start_va + XLAT_TESTS_MAX_VA_SIZE - 1ULL;

		gen_rand_mmap_array(&init_mmap[0], XLAT_TESTS_MAX_MMAPS,
				    start_va, end_va);

		/* Initialize the test structure */
		retval = xlat_ctx_cfg_init(&cfg, region, &init_mmap[0],
					   XLAT_TESTS_MAX_MMAPS,
					   XLAT_TESTS_MAX_VA_SIZE);

		/* Verify that the context cfg is properly created */
		CHECK_TRUE(retval == 0);

		memcpy((void *)&val_cfg, (void *)&cfg,
			sizeof(struct xlat_ctx_cfg));

		/* Test xlat_ctx_init() */
		retval = xlat_ctx_init(&ctx, &cfg, &tbls, &xlat_tables[0],
				       XLAT_TESTS_MAX_TABLES);

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
		 * NOTE: As the memory regions are random, the `next_table`
		 * field is not validated here. Instead, it will be validated
		 * for each especific test later.
		 */
		CHECK_TRUE(tbls.initialized == true);
		CHECK_TRUE(tbls.tables == &xlat_tables[0]);
		CHECK_TRUE(tbls.tables_num == XLAT_TESTS_MAX_TABLES);
	}
}

TEST(xlat_tests, xlat_ctx_init_TC2)
{
	struct xlat_ctx ctx;
	struct xlat_ctx_cfg cfg;
	struct xlat_ctx_tbls tbls;
	int retval;

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
				XLAT_TESTS_MAX_TABLES);

	/* Verify the result */
	CHECK_TRUE(retval == -EINVAL);
}

TEST(xlat_tests, xlat_ctx_init_TC3)
{
	struct xlat_ctx ctx;
	struct xlat_ctx_tbls tbls;
	int retval;

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
				XLAT_TESTS_MAX_TABLES);

	/* Verify the result */
	CHECK_TRUE(retval == -EINVAL);
}

TEST(xlat_tests, xlat_ctx_init_TC4)
{
	struct xlat_ctx ctx;
	struct xlat_ctx_cfg cfg;
	uintptr_t start_va, end_va;
	xlat_addr_region_id_t region;
	int retval;
	struct xlat_mmap_region init_mmap[XLAT_TESTS_MAX_MMAPS];

	/***************************************************************
	 * TEST CASE 4:
	 *
	 * Try to initialize a context with a NULL xlat_ctx_tbls
	 * structure
	 ***************************************************************/

	for (unsigned int i = 0U; i < (unsigned int)VA_REGIONS; i++) {
		region = (xlat_addr_region_id_t)i;

		/* Clean the data structures */
		memset((void *)&ctx, 0, sizeof(struct xlat_ctx));
		memset((void *)&cfg, 0, sizeof(struct xlat_ctx_cfg));

		/* VA space boundaries */
		start_va = get_start_va(region, XLAT_TESTS_MAX_VA_SIZE);
		end_va = start_va + XLAT_TESTS_MAX_VA_SIZE - 1ULL;

		gen_rand_mmap_array(&init_mmap[0], XLAT_TESTS_MAX_MMAPS,
				    start_va,
				    end_va);

		/* Initialize the test structure */
		retval = xlat_ctx_cfg_init(&cfg, region, &init_mmap[0],
					   XLAT_TESTS_MAX_MMAPS,
					   XLAT_TESTS_MAX_VA_SIZE);

		/* Verify that the context cfg is properly created */
		CHECK_TRUE(retval == 0);

		/* Test xlat_ctx_init() */
		retval = xlat_ctx_init(&ctx, &cfg, NULL, &xlat_tables[0],
					XLAT_TESTS_MAX_TABLES);

		/* Verify the result */
		CHECK_TRUE(retval == -EINVAL);
	}
}

TEST(xlat_tests, xlat_ctx_init_TC5)
{
	struct xlat_ctx ctx;
	struct xlat_ctx_cfg cfg;
	struct xlat_ctx_tbls tbls;
	uintptr_t start_va, end_va;
	xlat_addr_region_id_t region;
	struct xlat_mmap_region init_mmap[XLAT_TESTS_MAX_MMAPS];
	int retval;

	/***************************************************************
	 * TEST CASE 5:
	 *
	 * Try to initialize a context with a NULL set of translation
	 * tables
	 ***************************************************************/

	for (unsigned int i = 0U; i < (unsigned int)VA_REGIONS; i++) {
		region = (xlat_addr_region_id_t)i;

		/* Clean the data structures */
		memset((void *)&ctx, 0, sizeof(struct xlat_ctx));
		memset((void *)&cfg, 0, sizeof(struct xlat_ctx_cfg));
		memset((void *)&tbls, 0, sizeof(struct xlat_ctx_tbls));

		/* VA space boundaries */
		start_va = get_start_va(region, XLAT_TESTS_MAX_VA_SIZE);
		end_va = start_va + XLAT_TESTS_MAX_VA_SIZE - 1ULL;

		gen_rand_mmap_array(&init_mmap[0], XLAT_TESTS_MAX_MMAPS,
				    start_va,
				    end_va);

		/* Initialize the test structure */
		retval = xlat_ctx_cfg_init(&cfg, region, &init_mmap[0],
					   XLAT_TESTS_MAX_MMAPS,
					   XLAT_TESTS_MAX_VA_SIZE);

		/* Verify that the context cfg is properly created */
		CHECK_TRUE(retval == 0);

		/* Test xlat_ctx_init() */
		retval = xlat_ctx_init(&ctx, &cfg, &tbls, NULL,
					XLAT_TESTS_MAX_TABLES);

		/* Verify the result */
		CHECK_TRUE(retval == -EINVAL);
	}
}

TEST(xlat_tests, xlat_ctx_init_TC6)
{
	struct xlat_ctx_cfg cfg;
	struct xlat_ctx_tbls tbls;
	uintptr_t start_va, end_va;
	xlat_addr_region_id_t region;
	int retval;
	struct xlat_mmap_region init_mmap[XLAT_TESTS_MAX_MMAPS];

	/***************************************************************
	 * TEST CASE 6:
	 *
	 * Try to initialize a NULL context
	 ***************************************************************/

	for (unsigned int i = 0U; i < (unsigned int)VA_REGIONS; i++) {
		region = (xlat_addr_region_id_t)i;

		/* Clean the data structures */
		memset((void *)&cfg, 0, sizeof(struct xlat_ctx_cfg));
		memset((void *)&tbls, 0, sizeof(struct xlat_ctx_tbls));

		/* VA space boundaries */
		start_va = get_start_va(region, XLAT_TESTS_MAX_VA_SIZE);
		end_va = start_va + XLAT_TESTS_MAX_VA_SIZE - 1ULL;

		gen_rand_mmap_array(&init_mmap[0], XLAT_TESTS_MAX_MMAPS,
				    start_va,
				    end_va);

		/* Initialize the test structure */
		retval = xlat_ctx_cfg_init(&cfg, region, &init_mmap[0],
					   XLAT_TESTS_MAX_MMAPS,
					   XLAT_TESTS_MAX_VA_SIZE);

		/* Verify that the context cfg is properly created */
		CHECK_TRUE(retval == 0);

		/* Test xlat_ctx_init() */
		retval = xlat_ctx_init(NULL, &cfg, &tbls, &xlat_tables[0],
					XLAT_TESTS_MAX_TABLES);

		/* Verify the result */
		CHECK_TRUE(retval == -EINVAL);
	}
}

TEST(xlat_tests, xlat_ctx_init_TC7)
{
	struct xlat_ctx ctx;
	struct xlat_ctx_cfg cfg;
	struct xlat_ctx_tbls tbls;
	uintptr_t start_va, end_va;
	unsigned int offset;
	xlat_addr_region_id_t region;
	struct xlat_mmap_region init_mmap[XLAT_TESTS_MAX_MMAPS];
	int retval;

	/***************************************************************
	 * TEST CASE 7:
	 *
	 * Try to initialize a context with a set of unaligned
	 * translation tables
	 ***************************************************************/

	for (unsigned int i = 0U; i < (unsigned int)VA_REGIONS; i++) {
		region = (xlat_addr_region_id_t)i;

		/* Initialize some parameters with random data */
		offset = test_helpers_get_rand_in_range(1,
						XLAT_TESTS_TBL_ENTRIES - 1);

		/* Clean the data structures */
		memset((void *)&ctx, 0, sizeof(struct xlat_ctx));
		memset((void *)&cfg, 0, sizeof(struct xlat_ctx_cfg));
		memset((void *)&tbls, 0, sizeof(struct xlat_ctx_tbls));

		/* VA space boundaries */
		start_va = get_start_va(region, XLAT_TESTS_MAX_VA_SIZE);
		end_va = start_va + XLAT_TESTS_MAX_VA_SIZE - 1ULL;

		gen_rand_mmap_array(&init_mmap[0], XLAT_TESTS_MAX_MMAPS,
				    start_va,
				    end_va);

		/* Initialize the test structure */
		retval = xlat_ctx_cfg_init(&cfg, region, &init_mmap[0],
					   XLAT_TESTS_MAX_MMAPS,
					   XLAT_TESTS_MAX_VA_SIZE);

		/* Verify that the context cfg is properly created */
		CHECK_TRUE(retval == 0);

		/* Test xlat_ctx_init() */
		retval = xlat_ctx_init(&ctx, &cfg, &tbls, &xlat_tables[offset],
					XLAT_TESTS_MAX_TABLES);

		/* Verify the result */
		CHECK_TRUE(retval == -EINVAL);
	}
}

ASSERT_TEST(xlat_tests, xlat_ctx_init_TC8)
{
	struct xlat_ctx ctx;
	struct xlat_ctx_cfg cfg;
	struct xlat_ctx_tbls tbls;
	uintptr_t start_va, end_va;
	xlat_addr_region_id_t region;
	struct xlat_mmap_region init_mmap[XLAT_TESTS_MAX_MMAPS];
	int retval;

	/***************************************************************
	 * TEST CASE 8:
	 *
	 * Try to initialize a context with a number of valid
	 * random memory mapping areas but an inssuficient number of
	 * available translation tables.
	 *
	 * NOTE: Current implementation of the xlat library asserts
	 *	 when run out of space to allocate new translation
	 *	 tables. Future improvements on the xlat library should
	 *	 just return an error code and exit gracefully upon
	 *	 this condition.
	 ***************************************************************/

	for (unsigned int i = 0U; i < (unsigned int)VA_REGIONS; i++) {
		region = (xlat_addr_region_id_t)i;

		/* Clean the data structures */
		memset((void *)&ctx, 0, sizeof(struct xlat_ctx));
		memset((void *)&cfg, 0, sizeof(struct xlat_ctx_cfg));
		memset((void *)&tbls, 0, sizeof(struct xlat_ctx_tbls));

		/* VA space boundaries */
		start_va = get_start_va(region, XLAT_TESTS_MAX_VA_SIZE);
		end_va = start_va + XLAT_TESTS_MAX_VA_SIZE - 1ULL;

		gen_rand_mmap_array(&init_mmap[0], XLAT_TESTS_MAX_MMAPS,
				    start_va,
				    end_va);

		/* Initialize the test structure */
		retval = xlat_ctx_cfg_init(&cfg, region, &init_mmap[0],
					   XLAT_TESTS_MAX_MMAPS,
					   XLAT_TESTS_MAX_VA_SIZE);

		/* Verify that the context cfg is properly created */
		CHECK_TRUE(retval == 0);

		/* Test xlat_ctx_init() */
		test_helpers_expect_assert_fail(true);
		retval = xlat_ctx_init(&ctx, &cfg, &tbls, &xlat_tables[0], 1U);
		test_helpers_fail_if_no_assert_failed();
	}
}

TEST(xlat_tests, xlat_ctx_init_TC9)
{
	struct xlat_ctx ctx;
	struct xlat_ctx_cfg cfg;
	struct xlat_ctx_tbls tbls;
	uintptr_t start_va, end_va;
	xlat_addr_region_id_t region;
	int retval;
	struct xlat_mmap_region init_mmap[XLAT_TESTS_MAX_MMAPS];

	/***************************************************************
	 * TEST CASE 9:
	 *
	 * Try to initialize a context with valid random memory mapping
	 * areas and the MMU enabled.
	 ***************************************************************/

	/* Emulate the MMU enabled */
	write_sctlr_el2(SCTLR_EL2_WXN | SCTLR_EL2_M);

	for (unsigned int i = 0U; i < (unsigned int)VA_REGIONS; i++) {
		region = (xlat_addr_region_id_t)i;

		/* Clean the data structures */
		memset((void *)&ctx, 0, sizeof(struct xlat_ctx));
		memset((void *)&cfg, 0, sizeof(struct xlat_ctx_cfg));
		memset((void *)&tbls, 0, sizeof(struct xlat_ctx_tbls));

		/* VA space boundaries */
		start_va = get_start_va(region, XLAT_TESTS_MAX_VA_SIZE);
		end_va = start_va + XLAT_TESTS_MAX_VA_SIZE - 1ULL;

		gen_rand_mmap_array(&init_mmap[0], XLAT_TESTS_MAX_MMAPS,
				    start_va,
				    end_va);

		/* Initialize the test structure */
		retval = xlat_ctx_cfg_init(&cfg, region, &init_mmap[0],
					   XLAT_TESTS_MAX_MMAPS,
					   XLAT_TESTS_MAX_VA_SIZE);

		/* Verify that the context cfg is properly created */
		CHECK_TRUE(retval == 0);

		/* Test xlat_ctx_init() */
		retval = xlat_ctx_init(&ctx, &cfg, &tbls, &xlat_tables[0],
						XLAT_TESTS_MAX_TABLES);
		CHECK_TRUE(retval == -EINVAL);
	}
}

/*
 * Generate VA space parameters given a walk start level and a region.
 * The VA returned will fit in a single table of level `level`, so that
 * there translation can start at that given level.
 */
static unsigned long long gen_va_space_params_by_lvl(unsigned int level,
						xlat_addr_region_id_t region,
						size_t *va_size)
{
	assert(level <= XLAT_TABLE_LEVEL_MAX);
	assert(va_size != NULL);

	*va_size = (1ULL << (XLAT_TESTS_TABLE_LVL_SHIFT(level) +
				XLAT_TESTS_TBL_ENTRIES_SHIFT));

	return get_start_va(region, *va_size);
}

/*
 * Generate a mmap array containing a set of mmap regions defined by
 * 'start_va', 'level' and 'region. The mmap array will have three regions:
 *
 *	- First region mapped at the beginning of a table whose final
 *	  lookup level is 'level'
 *	- Second region mapped at a random tte of a table whose final
 *	  lookup level is 'level'
 *	- Third region mapped at the end of a table whose final
 *	  lookup level is 'level'
 *
 * The base address of the mmap regions can be increased by the
 * specified 'offset'.
 *
 * For all the mmap regions, the granularity is setup to the minimum
 * granularity needed to map a block at level 'level'.
 *
 * This function also returns two arrays:
 *
 *	- An array with the the final lookup level expected for each
 *	  mmap region ('levels').
 *	- An array with the indexes to map the expected TTEs to be used
 *	  on the last lookup level to map the mmap region ('page_idxs').
 * */
static int gen_mmap_array_by_level(xlat_mmap_region *mmap,
				   unsigned int *tbl_idxs,
				   unsigned int *levels,
				   unsigned int mmap_size,
				   unsigned int last_lvl,
				   size_t *granularity,
				   unsigned long long start_va,
				   unsigned long long offset,
				   bool allow_transient)
{
	uint64_t attrs;
	unsigned long long mmap_start_va = start_va;

	assert(mmap_size >= 3U);
	assert(last_lvl <= XLAT_TABLE_LEVEL_MAX);
	assert(mmap != NULL);
	assert(tbl_idxs != NULL);
	assert(granularity != NULL);
	assert(levels != NULL);

	/* Generate a mapping at the beginning of the table */
	tbl_idxs[0U] = 0U;

	/* Generate a mapping in a random possition of the table */
	tbl_idxs[1U] = test_helpers_get_rand_in_range(1,
					(XLAT_TESTS_TBL_ENTRIES - 2));

	/* Generate a mapping at the end of the table */
	tbl_idxs[2U] = XLAT_TESTS_TBL_ENTRIES - 1U;

	do {
		attrs = get_mmap_attrs();
	} while ((attrs == MT_TRANSIENT) && (allow_transient == false));

	*granularity = 1ULL << XLAT_TESTS_TABLE_LVL_SHIFT(last_lvl);

	mmap_start_va += offset;

	for (unsigned i = 0U; i < 3U; i++) {
		mmap[i].base_va = mmap_start_va + (tbl_idxs[i]
							* (*granularity));
		/*
		 * PA can be anyone (as long as there are not overlaps, for
		 * which there is a specific test). For simplicity, use
		 * create an identity mapping using the base_va for the PA.
		 */
		mmap[i].base_pa = mmap[i].base_va & XLAT_TESTS_PA_MASK;
		mmap[i].size = *granularity;
		mmap[i].attr = attrs;
		mmap[i].granularity = *granularity;

		/* Store the expected level */
		levels[i] = last_lvl;
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
	uint64_t tte, attrs, type;
	unsigned int level, index, granularity, page_offset;
	unsigned long long test_va, pa, pa_mask;
	unsigned int retval;

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
		retval = xlat_test_helpers_table_walk(ctx, test_va,
						      &tte, NULL, &level,
						      &index);

		/* Return value */
		CHECK_EQUAL(0, retval);

		/* Last table level */
		CHECK_EQUAL(expected_levels[i], level);

		/* tte index on the page */
		CHECK_EQUAL(expected_idxs[i], index);

		/* Expected tte attributes */
		retval = xlat_test_helpers_gen_attrs_from_va(ctx, test_va,
							     &attrs);

		/* Return value */
		CHECK_EQUAL(0, retval);

		/* Validate that the attributes are as expected */
		CHECK_EQUAL((tte & XLAT_TESTS_TABLE_ATTRS_MASK), attrs);

		/* Validate the PA */
		pa_mask = (1ULL << XLAT_TESTS_TABLE_LVL_SHIFT(level)) - 1ULL;
		CHECK_EQUAL((tte & XLAT_TESTS_TABLE_OA_MASK), (pa & ~pa_mask));

		/* Validate the descriptor type */
		type = (level == XLAT_TESTS_MAX_LEVEL) ? XLAT_TESTS_PAGE_DESC :
							 XLAT_TESTS_BLOCK_DESC;
		CHECK_EQUAL(type, (tte & XLAT_TESTS_DESC_MASK));
	}
}

TEST(xlat_tests, xlat_ctx_init_TC10)
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
	unsigned int page_idx[3U];
	unsigned int expected_lvls[3U];
	unsigned int start_lvl, end_lvl;

	/***************************************************************
	 * TEST CASE 10:
	 *
	 * For each possible initial lookup level, create a set of
	 * random mappings starting at such lookup level and with
	 * granularities ranging from level 1 (lower level supporting
	 * pages/blocks) to XLAT_TABLE_LEVEL_MAX.
	 *
	 * For each possible (region, start_lvl, end_lvl) triplet,
	 * there will be three mmap regions created:
	 *
	 *	- First region mapped at the beginning of a table whose
	 *	  final lookup level is 'end_lvl'
	 *	- Second region mapped at a random tte of a table whose
	 *	  final lookup level is 'end_lvl'
	 *	- Third region mapped at the end of a table whose
	 *	  final lookup level is 'end_lvl'
	 *
	 * Then verify that the tables can be walked and that the levels,
	 * offsets and attributes on the ttes are as expected.
	 *
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

				start_va = gen_va_space_params_by_lvl(start_lvl,
								 region,
								 &va_size);

				retval = gen_mmap_array_by_level(&init_mmap[0U],
								 &page_idx[0U],
								 &expected_lvls[0U],
								 mmap_count,
								 end_lvl,
								 &granularity,
								 start_va, 0ULL,
								 false);
				/*
				 * verify that the test setup is correct so far
				 */
				CHECK_TRUE(retval == 0);

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
				 * verify that the test setup is correct so far
				 */
				CHECK_TRUE(retval == 0);

				/* Test xlat_ctx_init() */
				retval = xlat_ctx_init(&ctx, &cfg, &tbls,
						       &xlat_tables[0U],
						       XLAT_TESTS_MAX_TABLES);

				/*
				 * verify that the test setup is correct so far
				 */
				CHECK_TRUE(retval == 0);

				validate_xlat_tables(&ctx, &page_idx[0U],
						     &expected_lvls[0U]);
			}
		}
	}
}

TEST(xlat_tests, xlat_get_table_from_va_TC1)
{
	struct xlat_ctx ctx;
	struct xlat_ctx_cfg cfg;
	struct xlat_ctx_tbls tbls;
	struct xlat_tbl_info tbl_info, tbl_val;
	struct xlat_mmap_region init_mmap[3U];
	uintptr_t start_va;
	size_t va_size, granularity;
	unsigned int mmap_count, index;
	xlat_addr_region_id_t region;
	int retval;
	unsigned int page_idx[3U];
	unsigned int expected_lvls[3U];
	unsigned int start_lvl, end_lvl;
	uint64_t tte;
	unsigned long long test_va, offset;

	/***************************************************************
	 * TEST CASE 1:
	 *
	 * For each possible initial lookup level, create a random
	 * mapping starting at such lookup level and with granularities
	 * ranging from level 1 (lower level supporting blocks)
	 * to XLAT_TABLE_LEVEL_MAX (last level, which supports pages).
	 *
	 * For each possible (region, start_lvl, end_lvl) triplet,
	 * the mmap region will be mapped at a random tte of a table
	 * whose final lookup level is 'end_lvl'. The mapping will be
	 * such that the 'end_lvl' table will be mapped at an index > 0
	 * in the parent table, so that the base VA mapped by the
	 * 'end_lvl' table will not match the base VA of the whole
	 * context. This will help verifying that xlat_get_table_from_va()
	 * is able to calculate the right base VA of a given table
	 * ('struct xlat_tbl_info.base_va' field).
	 *
	 * Then verify that the call to xlat_get_table_from_va() is able
	 * to return the right xlat_tbl_info structure with the expected
	 * values.
	 ***************************************************************/

	mmap_count = 3U;

	for (unsigned int i = 0U; i < (unsigned int)VA_REGIONS; i++) {
		region = (xlat_addr_region_id_t)i;

		for (end_lvl = 1U;
		     end_lvl <= XLAT_TESTS_MAX_LEVEL;
		     end_lvl++) {

			for (start_lvl = 0U;
			     start_lvl <= end_lvl;
			     start_lvl++) {

				/* Clean the data structures */
				memset((void *)&ctx, 0,
						sizeof(struct xlat_ctx));
				memset((void *)&cfg, 0,
						sizeof(struct xlat_ctx_cfg));
				memset((void *)&tbls, 0,
						sizeof(struct xlat_ctx_tbls));
				memset((void *)&tbl_info, 0,
						sizeof(struct xlat_tbl_info));
				memset((void *)&tbl_val, 0,
						sizeof(struct xlat_tbl_info));

				start_va = gen_va_space_params_by_lvl(start_lvl,
								 region,
								 &va_size);

				/*
				 * Create an offset that will make 'end_lvl'
				 * table to be mapped to an index other than 0
				 * on its parent table, so that the VA mapped
				 * by the 'end_lvl' does not match 'start_va'.
				 */
				offset = test_helpers_get_rand_in_range(1,
						XLAT_TESTS_TBL_ENTRIES - 1);
				offset *= ( end_lvl != start_lvl ) ?
					XLAT_TESTS_TABLE_LVL_BLOCK_SIZE(end_lvl - 1U) :
					0;

				/*
				 * use gen_mmap_array_by_level() to generate
				 * the mmap for convenience, although we will
				 * only use one of the mmap regions
				 * (init_mmap[1]).
				 */
				retval = gen_mmap_array_by_level(&init_mmap[0U],
								&page_idx[0U],
								&expected_lvls[0U],
								mmap_count,
								end_lvl,
								&granularity,
								start_va, offset,
								true);

				/* Ensure that so far the test setup is OK */
				CHECK_TRUE(retval == 0);

				/*
				 * The base VA mapped by the returned tte will
				 * Correspond to the base_va on init_mmap[0]
				 */
				tbl_val.base_va = init_mmap[0U].base_va;
				retval = xlat_ctx_cfg_init(&cfg, region,
							   &init_mmap[0U],
							   mmap_count, va_size);

				/* Ensure that so far the test setup is OK */
				CHECK_TRUE(retval == 0);

				retval = xlat_ctx_init(&ctx, &cfg, &tbls,
						       &xlat_tables[0U],
						       XLAT_TESTS_MAX_TABLES);

				/* Ensure that so far the test setup is OK */
				CHECK_TRUE(retval == 0);

				/*
				 * Get a random test address. This valid address
				 * range is defined by
				 * start_va = init_mmap[0].base_va and a size
				 * equal to the block size of the parent table,
				 * so we select an address within init_mmap[1]
				 * range which is still in the valid range
				 * so xlat_test_helpers_table_walk()
				 * does not fail.
				 */
				test_va = tbl_val.base_va;
				test_va += test_helpers_get_rand_in_range(0,
							init_mmap[1U].size - 1);

				/*
				 * Perform a table walk to retrieve table info.
				 * Store the expected values inside the
				 * validation xlat_tbl_info structure.
				 */
				retval = xlat_test_helpers_table_walk(&ctx,
								test_va,
								&tte,
								&(tbl_val.table),
								&(tbl_val.level),
								&index);

				/* Ensure that so far the test setup is OK */
				CHECK_TRUE(retval == 0);

				tbl_val.entries = (start_lvl == end_lvl) ?
						XLAT_TESTS_GET_BASE_LVL_ENTRIES(
							ctx.cfg->max_mapped_va_offset)
							: XLAT_TESTS_TBL_ENTRIES;

				VERBOSE("\nTesting VA 0x%llx", test_va);
				/* Test xlat_get_table_from_va */
				retval = xlat_get_table_from_va(&tbl_info, &ctx,
								test_va);

				/* Check the return value */
				CHECK_TRUE(retval == 0);

				/*
				 * Validate the structure returned by
				 * xlat_get_table_from_va
				 */
				MEMCMP_EQUAL((void *)&tbl_val,
					     (void *)&tbl_info,
					     sizeof(struct xlat_tbl_info));
				VERBOSE(" : PASS\n\n");
			}
		}
	}
}

TEST(xlat_tests, xlat_get_table_from_va_TC2)
{
	struct xlat_ctx ctx;
	struct xlat_ctx_cfg cfg;
	struct xlat_ctx_tbls tbls;
	struct xlat_tbl_info tbl_info;
	struct xlat_mmap_region init_mmap;
	int offset;
	uintptr_t start_va, end_va, test_va;
	xlat_addr_region_id_t region;
	int retval;

	/***************************************************************
	 * TEST CASE 2:
	 *
	 * Try calling xlat_get_table_from_va() with a VAs ouside
	 * of the mapped VA space.
	 ***************************************************************/

	for (unsigned int i = 0U; i < (unsigned int)VA_REGIONS; i++) {
		region = (xlat_addr_region_id_t)i;

		/*
		 * Repeat the test twice: Once for a VA below the base_va
		 * and another time for an address over the maximum one.
		*/
		for (unsigned int j = 0; j < 2U; j++) {

			/* Clean the data structures */
			memset((void *)&ctx, 0, sizeof(struct xlat_ctx));
			memset((void *)&cfg, 0, sizeof(struct xlat_ctx_cfg));
			memset((void *)&tbls, 0, sizeof(struct xlat_ctx_tbls));
			memset((void *)&tbl_info, 0,
						sizeof(struct xlat_tbl_info));

			/* VA space boundaries */
			start_va = get_start_va(region,
						XLAT_TESTS_MAX_VA_SIZE);
			end_va = start_va + XLAT_TESTS_MAX_VA_SIZE - 1ULL;

			/*
			 * Generate a random mmap area. Leave some room
			 * below the start of the area so that we can test
			 * invalid VAs below the start of the area.
			 */
			do {
				gen_rand_mmap_array(&init_mmap, 1U,
						    start_va, end_va);
			} while (init_mmap.base_va == start_va);

			(void)xlat_ctx_cfg_init(&cfg, region, &init_mmap, 1U,
						XLAT_TESTS_MAX_VA_SIZE);

			(void)xlat_ctx_init(&ctx, &cfg, &tbls,
					    &xlat_tables[0U],
					    XLAT_TESTS_MAX_TABLES);
			VERBOSE("\n");

			test_va = ctx.cfg->base_va;
			test_va += init_mmap.base_va;
			offset = test_helpers_get_rand_in_range(init_mmap.size,
					XLAT_TESTS_GRANULARITY_SIZE - 1);
			test_va = (j == 0U) ?
				test_va + offset : test_va - offset;

			/* Test xlat_get_table_from_va */
			retval = xlat_get_table_from_va(&tbl_info, &ctx,
							test_va);

			/* Check the return value */
			CHECK_VERBOSE((retval == -EFAULT),
				      "Testing VA 0x%lx", test_va);
			VERBOSE("\n");
		}
	}
}

ASSERT_TEST(xlat_tests, xlat_get_table_from_va_TC3)
{
	struct xlat_ctx ctx;
	struct xlat_ctx_cfg cfg;
	struct xlat_ctx_tbls tbls;
	struct xlat_mmap_region init_mmap;
	uintptr_t start_va, end_va, test_va;
	xlat_addr_region_id_t region;

	/***************************************************************
	 * TEST CASE 3:
	 *
	 * Try calling xlat_get_table_from_va() with a NULL
	 * xlat_tbl_info structure
	 ***************************************************************/

	region = (xlat_addr_region_id_t)test_helpers_get_rand_in_range(0,
							VA_REGIONS - 1U);

	/* Clean the data structures */
	memset((void *)&ctx, 0, sizeof(struct xlat_ctx));
	memset((void *)&cfg, 0, sizeof(struct xlat_ctx_cfg));
	memset((void *)&tbls, 0, sizeof(struct xlat_ctx_tbls));

	/* VA space boundaries */
	start_va = get_start_va(region,	XLAT_TESTS_MAX_VA_SIZE);
	end_va = start_va + XLAT_TESTS_MAX_VA_SIZE - 1ULL;

	/* Generate a random mmap area */
	gen_rand_mmap_array(&init_mmap, 1U, start_va, end_va);

	(void)xlat_ctx_cfg_init(&cfg, region, &init_mmap, 1U,
				XLAT_TESTS_MAX_VA_SIZE);

	(void)xlat_ctx_init(&ctx, &cfg, &tbls,
			    &xlat_tables[0U],
			    XLAT_TESTS_MAX_TABLES);

	test_va = ctx.cfg->base_va + init_mmap.base_va;

	/* Test xlat_get_table_from_va */
	test_helpers_expect_assert_fail(true);
	(void)xlat_get_table_from_va(NULL, &ctx, test_va);
	test_helpers_fail_if_no_assert_failed();
}

ASSERT_TEST(xlat_tests, xlat_get_table_from_va_TC4)
{
	struct xlat_tbl_info tbl_info;

	/***************************************************************
	 * TEST CASE 4:
	 *
	 * Try calling xlat_get_table_from_va() with a NULL
	 * xlat_ctx structure.
	 ***************************************************************/

	/* Clean the data structures */
	memset((void *)&tbl_info, 0, sizeof(struct xlat_tbl_info));

	/* Test xlat_get_table_from_va: NULL xlat_ctx */
	test_helpers_expect_assert_fail(true);
	(void)xlat_get_table_from_va(&tbl_info, NULL, 0ULL);
	test_helpers_fail_if_no_assert_failed();
}

ASSERT_TEST(xlat_tests, xlat_get_table_from_va_TC5)
{
	struct xlat_ctx ctx;
	struct xlat_ctx_cfg cfg;
	struct xlat_ctx_tbls tbls;
	struct xlat_tbl_info tbl_info;
	struct xlat_mmap_region init_mmap;
	uintptr_t start_va, end_va, test_va;
	xlat_addr_region_id_t region;

	/***************************************************************
	 * TEST CASE 5:
	 *
	 * Try calling xlat_get_table_from_va() with a NULL
	 * xlat_ctx_cfg structure.
	 ***************************************************************/

	region = (xlat_addr_region_id_t)test_helpers_get_rand_in_range(0,
							VA_REGIONS - 1U);

	/* Clean the data structures */
	memset((void *)&ctx, 0, sizeof(struct xlat_ctx));
	memset((void *)&cfg, 0, sizeof(struct xlat_ctx_cfg));
	memset((void *)&tbls, 0, sizeof(struct xlat_ctx_tbls));
	memset((void *)&tbl_info, 0, sizeof(struct xlat_tbl_info));

	/* VA space boundaries */
	start_va = get_start_va(region,
				XLAT_TESTS_MAX_VA_SIZE);
	end_va = start_va + XLAT_TESTS_MAX_VA_SIZE - 1ULL;

	/* Generate a random mmap area */
	gen_rand_mmap_array(&init_mmap, 1U, start_va, end_va);

	(void)xlat_ctx_cfg_init(&cfg, region, &init_mmap, 1U,
				XLAT_TESTS_MAX_VA_SIZE);

	/*
	 * Initialize the context so we have a full set of
	 * valid translation tables.
	 */
	(void)xlat_ctx_init(&ctx, &cfg, &tbls,
			    &xlat_tables[0U],
			    XLAT_TESTS_MAX_TABLES);

	test_va = ctx.cfg->base_va + init_mmap.base_va;

	/* Test xlat_get_table_from_va: NULL xlat_ctx.cfg */
	ctx.cfg = NULL;
	test_helpers_expect_assert_fail(true);
	(void)xlat_get_table_from_va(&tbl_info, &ctx, test_va);
	test_helpers_fail_if_no_assert_failed();

}

ASSERT_TEST(xlat_tests, xlat_get_table_from_va_TC6)
{
	struct xlat_ctx ctx;
	struct xlat_ctx_cfg cfg;
	struct xlat_ctx_tbls tbls;
	struct xlat_tbl_info tbl_info;
	struct xlat_mmap_region init_mmap;
	uintptr_t start_va, end_va, test_va;
	xlat_addr_region_id_t region;

	/***************************************************************
	 * TEST CASE 6:
	 *
	 * Try calling xlat_get_table_from_va() with a NULL
	 * xlat_ctx_tbls structure.
	 ***************************************************************/

	region = (xlat_addr_region_id_t)test_helpers_get_rand_in_range(0,
							VA_REGIONS - 1U);

	/* Clean the data structures */
	memset((void *)&ctx, 0, sizeof(struct xlat_ctx));
	memset((void *)&cfg, 0, sizeof(struct xlat_ctx_cfg));
	memset((void *)&tbls, 0, sizeof(struct xlat_ctx_tbls));
	memset((void *)&tbl_info, 0, sizeof(struct xlat_tbl_info));

	/* VA space boundaries */
	start_va = get_start_va(region,
				XLAT_TESTS_MAX_VA_SIZE);
	end_va = start_va + XLAT_TESTS_MAX_VA_SIZE - 1ULL;

	/* Generate a random mmap area */
	gen_rand_mmap_array(&init_mmap, 1U, start_va, end_va);

	(void)xlat_ctx_cfg_init(&cfg, region, &init_mmap, 1U,
				XLAT_TESTS_MAX_VA_SIZE);

	(void)xlat_ctx_init(&ctx, &cfg, &tbls,
			    &xlat_tables[0U],
			    XLAT_TESTS_MAX_TABLES);

	test_va = ctx.cfg->base_va + init_mmap.base_va;

	/* Test xlat_get_table_from_va: NULL xlat_ctx.tbls */
	ctx.tbls = NULL;
	test_helpers_expect_assert_fail(true);
	(void)xlat_get_table_from_va(&tbl_info, &ctx, test_va);
	test_helpers_fail_if_no_assert_failed();
}

TEST(xlat_tests, xlat_get_table_from_va_TC7)
{
	struct xlat_ctx ctx;
	struct xlat_ctx_cfg cfg;
	struct xlat_ctx_tbls tbls;
	struct xlat_tbl_info tbl_info;
	struct xlat_mmap_region init_mmap;
	uintptr_t start_va, end_va, test_va;
	xlat_addr_region_id_t region;
	int retval;

	/***************************************************************
	 * TEST CASE 7:
	 *
	 * Try calling xlat_get_table_from_va() with an uninitialized
	 * xlat_ctx_cfg structure
	 ***************************************************************/

	region = (xlat_addr_region_id_t)test_helpers_get_rand_in_range(0,
							VA_REGIONS - 1U);

	/* Clean the data structures */
	memset((void *)&ctx, 0, sizeof(struct xlat_ctx));
	memset((void *)&cfg, 0, sizeof(struct xlat_ctx_cfg));
	memset((void *)&tbls, 0, sizeof(struct xlat_ctx_tbls));
	memset((void *)&tbl_info, 0, sizeof(struct xlat_tbl_info));

	/* VA space boundaries */
	start_va = get_start_va(region,
				XLAT_TESTS_MAX_VA_SIZE);
	end_va = start_va + XLAT_TESTS_MAX_VA_SIZE - 1ULL;

	/* Generate a random mmap area */
	gen_rand_mmap_array(&init_mmap, 1U, start_va, end_va);

	(void)xlat_ctx_cfg_init(&cfg, region, &init_mmap, 1U,
				XLAT_TESTS_MAX_VA_SIZE);

	(void)xlat_ctx_init(&ctx, &cfg, &tbls,
			    &xlat_tables[0U],
			    XLAT_TESTS_MAX_TABLES);

	test_va = ctx.cfg->base_va + init_mmap.base_va;

	/* Mark the cfg structure as not initialized */
	cfg.initialized = false;

	retval = xlat_get_table_from_va(&tbl_info, &ctx, test_va);

	CHECK_TRUE(retval == -EINVAL);
}

TEST(xlat_tests, xlat_get_table_from_va_TC8)
{
	struct xlat_ctx ctx;
	struct xlat_ctx_cfg cfg;
	struct xlat_ctx_tbls tbls;
	struct xlat_tbl_info tbl_info;
	struct xlat_mmap_region init_mmap;
	uintptr_t start_va, end_va, test_va;
	xlat_addr_region_id_t region;
	int retval;

	/***************************************************************
	 * TEST CASE 8:
	 *
	 * Try calling xlat_get_table_from_va() with an uninitialized
	 * xlat_ctx_tbls structure
	 ***************************************************************/

	region = (xlat_addr_region_id_t)test_helpers_get_rand_in_range(0,
							VA_REGIONS - 1U);

	/* Clean the data structures */
	memset((void *)&ctx, 0, sizeof(struct xlat_ctx));
	memset((void *)&cfg, 0, sizeof(struct xlat_ctx_cfg));
	memset((void *)&tbls, 0, sizeof(struct xlat_ctx_tbls));
	memset((void *)&tbl_info, 0, sizeof(struct xlat_tbl_info));

	/* VA space boundaries */
	start_va = get_start_va(region,
				XLAT_TESTS_MAX_VA_SIZE);
	end_va = start_va + XLAT_TESTS_MAX_VA_SIZE - 1ULL;

	/* Generate a random mmap area */
	gen_rand_mmap_array(&init_mmap, 1U, start_va, end_va);

	(void)xlat_ctx_cfg_init(&cfg, region, &init_mmap, 1U,
				XLAT_TESTS_MAX_VA_SIZE);

	(void)xlat_ctx_init(&ctx, &cfg, &tbls,
			    &xlat_tables[0U],
			    XLAT_TESTS_MAX_TABLES);

	test_va = ctx.cfg->base_va + init_mmap.base_va;

	/* Mark the tbls structure as not initialized */
	tbls.initialized = false;

	retval = xlat_get_table_from_va(&tbl_info, &ctx, test_va);

	CHECK_TRUE(retval == -EINVAL);
}

TEST(xlat_tests, xlat_get_tte_ptr_TC1)
{
	struct xlat_ctx ctx;
	struct xlat_ctx_cfg cfg;
	struct xlat_ctx_tbls tbls;
	struct xlat_tbl_info tbl_info;
	struct xlat_mmap_region init_mmap[3U];
	unsigned int page_idx[3U], expected_lvls[3U];
	uintptr_t start_va, test_va;
	xlat_addr_region_id_t region;
	unsigned int level, index;
	uint64_t *tte_ptr, *val_tte, *table;
	uint64_t tte;
	size_t granularity;
	int retval;

	/***************************************************************
	 * TEST CASE 1:
	 *
	 * Initialize a translation context with a given VA space and
	 * random mmap region. Then get a tte using xlat_get_tte_ptr()
	 * and verify that it is the correct entry.
	 *
	 * This test tries three different addresses per VA region:
	 *
	 * 	- An address corresponding to the first entry of the
	 *	  table stored in the xlat_tbls_info structure.
	 *	- An address corresponding to the last entry of the
	 *	  same table.
	 *	- An address corresponding to an intermediate entry
	 *	  of the same table.
	 ***************************************************************/

	for (unsigned int i = 0U; i < (unsigned int)VA_REGIONS; i++) {
		region = (xlat_addr_region_id_t)i;

		/* Clean the data structures */
		memset((void *)&ctx, 0, sizeof(struct xlat_ctx));
		memset((void *)&cfg, 0, sizeof(struct xlat_ctx_cfg));
		memset((void *)&tbls, 0, sizeof(struct xlat_ctx_tbls));
		memset((void *)&tbl_info, 0, sizeof(struct xlat_tbl_info));

		/* VA space boundaries */
		start_va = get_start_va(region, XLAT_TESTS_MAX_VA_SIZE);

		/* Generate the mmap regions */
		retval = gen_mmap_array_by_level(&init_mmap[0U],
						&page_idx[0U],
						&expected_lvls[0U],
						3U, 3U,
						&granularity,
						start_va, 0U, true);

		/* Ensure that so far the test setup is OK */
		CHECK_TRUE(retval == 0);

		retval = xlat_ctx_cfg_init(&cfg, region, &init_mmap[0U], 3U,
					   XLAT_TESTS_MAX_VA_SIZE);

		/* Ensure that so far the test setup is OK */
		CHECK_TRUE(retval == 0);

		retval = xlat_ctx_init(&ctx, &cfg, &tbls,
					&xlat_tables[0U],
					XLAT_TESTS_MAX_TABLES);

		/* Ensure that so far the test setup is OK */
		CHECK_TRUE(retval == 0);

		/* Get the xlat_tbl_info stucture used to look for TTEs */
		test_va = ctx.cfg->base_va + init_mmap[0].base_va;
		retval = xlat_get_table_from_va(&tbl_info, &ctx, test_va);

		/* Ensure that so far the test setup is OK */
		CHECK_TRUE(retval == 0);

		/*
		 * Iterate over all the test indexes to test
		 * xlat_get_tte_ptr(). This ensures that we cover:
		 *
		 * 	- An address corresponding to the first entry of the
		 *	  table stored in the xlat_tbls_info structure.
		 *	- An address corresponding to the last entry of the
		 *	  same table.
		 *	- An address corresponding to an intermediate entry
		 *	  of the same table.
		 */
		VERBOSE("\n");
		for (unsigned int i = 0U; i < 3U; i++) {
			/*
			 * Calculate the test VA based on the random granule
			 * and the selected entry index.
			 */
			test_va = ctx.cfg->base_va + init_mmap[i].base_va +
				test_helpers_get_rand_in_range(0,
					XLAT_TESTS_GRANULARITY_SIZE - 1);

			/*
			 * Perform a table walk to get the table containing
			 * the tte we are insterested in as well as the
			 * index of that tte in the table.
			 */
			retval = xlat_test_helpers_table_walk(&ctx, test_va,
							       &tte, &table,
							       &level, &index);
			/* Ensure that so far the test setup is OK */
			CHECK_TRUE(retval == 0);

			/* Get a pointer to the expected tte */
			val_tte = &table[index];

			/* Test xlat_get_tte_ptr() */
			tte_ptr = xlat_get_tte_ptr(&tbl_info, test_va);

			/* Validate the output */
			CHECK_VERBOSE((val_tte == tte_ptr),
				      "Testing VA 0x%lx", test_va);
		}
		VERBOSE("\n");
	}
}

TEST(xlat_tests, xlat_get_tte_ptr_TC2)
{
	struct xlat_ctx ctx;
	struct xlat_ctx_cfg cfg;
	struct xlat_ctx_tbls tbls;
	struct xlat_tbl_info tbl_info;
	struct xlat_mmap_region init_mmap[3U];
	unsigned int page_idx[3U], expected_lvls[3U];
	size_t va_size, granularity;
	uintptr_t start_va, test_va;
	xlat_addr_region_id_t region;
	int retval;
	unsigned long long offset;
	uint64_t *tte_ptr;

	/***************************************************************
	 * TEST CASE 2:
	 *
	 * Initialize a translation context with a given VA space and
	 * random mmap region. Then try to get a tte using
	 * xlat_get_tte() and a VA outside the range supported by the
	 * table pass to xlat_get_tte().
	 ***************************************************************/

	for (unsigned int i = 0U; i < (unsigned int)VA_REGIONS; i++) {
		region = (xlat_addr_region_id_t)i;

		/* Clean the data structures */
		memset((void *)&ctx, 0, sizeof(struct xlat_ctx));
		memset((void *)&cfg, 0, sizeof(struct xlat_ctx_cfg));
		memset((void *)&tbls, 0, sizeof(struct xlat_ctx_tbls));
		memset((void *)&tbl_info, 0, sizeof(struct xlat_tbl_info));

		start_va = gen_va_space_params_by_lvl(0U, region, &va_size);

		/*
		 * Create an offset that will make the last level table
		 * to be mapped to an index other than 0 on its parent table,
		 * so that the VA mapped by the last level table does not match
		 * 'start_va' which would be 0ULL for the low level region.
		 * This way, we can pick up an address below the minimum VA
		 * mapped by the last level table to test the low boundary of
		 * the allowed region.
		 */
		offset = test_helpers_get_rand_in_range(1,
					XLAT_TESTS_TBL_ENTRIES - 1);
		offset *= XLAT_TESTS_TABLE_LVL_BLOCK_SIZE(2U);

		/*
		 * use gen_mmap_array_by_level() to generate the mmap for
		 * convenience, although we will only need one of the mmap
		 * regions only (that would be init_mmap[1]).
		 */
		retval = gen_mmap_array_by_level(&init_mmap[0U],
						&page_idx[0U],
						&expected_lvls[0U],
						3U, 3U,
						&granularity,
						start_va, offset, true);

		/* Ensure that so far the test setup is OK */
		CHECK_TRUE(retval == 0);

		retval = xlat_ctx_cfg_init(&cfg, region, &init_mmap[0], 3U,
					XLAT_TESTS_MAX_VA_SIZE);

		/* Ensure that so far the test setup is OK */
		CHECK_TRUE(retval == 0);

		retval = xlat_ctx_init(&ctx, &cfg, &tbls, &xlat_tables[0U],
				    XLAT_TESTS_MAX_TABLES);

		/* Ensure that so far the test setup is OK */
		CHECK_TRUE(retval == 0);

		/*
		 * Get the xlat_tbl_info stucture used to look for TTEs so we
		 * can extract the base VA of the table mapping our TTEs.
		 *
		 * 'tbl_info.base_va' will contain the base VA mapped by the
		 * table where the TTE for 'init_mmap[1].base_va' is mapped.
		 */
		test_va = init_mmap[1U].base_va + ctx.cfg->base_va;
		retval = xlat_get_table_from_va(&tbl_info, &ctx, test_va);

		/* Ensure that so far the test setup is OK */
		CHECK_TRUE(retval == 0);

		VERBOSE("\nBase VA mapped by TT at level %u: 0x%lx\n",
				tbl_info.level, tbl_info.base_va);

		/*
		 * Calculate a test VA which is below the minimum VA mapped
		 * by 'tbl_info'. Use this address to test xlat_get_tte_ptr()
		 */
		test_va = tbl_info.base_va;
		test_va -= test_helpers_get_rand_in_range(1,
					XLAT_TESTS_GRANULARITY_SIZE - 1);

		/* Test xlat_get_tte_PTR() */
		tte_ptr = xlat_get_tte_ptr(&tbl_info, test_va);

		/* Validate the output */
		CHECK_VERBOSE((tte_ptr == NULL),
			      "Check address 0x%lx against TT at VA 0x%lx",
			      test_va, tbl_info.base_va);

		/*
		 * Calculate a test VA which is over the maximum VA mapped
		 * by 'tbl_info'. Use this address to test xlat_get_tte_ptr().
		 *
		 * The last look-up level for our mmap regions is level 3, so
		 * the region covered by the table in 'tbl_info' will be of
		 * level 2 size.
		 */
		test_va = tbl_info.base_va + XLAT_TESTS_TABLE_LVL_BLOCK_SIZE(2U);
		test_va += test_helpers_get_rand_in_range(1,
					XLAT_TESTS_GRANULARITY_SIZE - 1);

		/* Test xlat_get_tte_PTR() */
		tte_ptr = xlat_get_tte_ptr(&tbl_info, test_va);

		CHECK_VERBOSE((tte_ptr == NULL),
			      "Check address 0x%lx against TT at VA 0x%lx",
			      test_va, tbl_info.base_va);

		VERBOSE("\n");
	}
}

ASSERT_TEST(xlat_tests, xlat_get_tte_ptr_TC3)
{
	/***************************************************************
	 * TEST CASE 3:
	 *
	 * Try to get a tte using xlat_get_tte() with a NULL
	 * xlat_tbl_info structure.
	 ***************************************************************/

	test_helpers_expect_assert_fail(true);
	(void)xlat_get_tte_ptr(NULL, 0ULL);
	test_helpers_fail_if_no_assert_failed();
}

TEST(xlat_tests, xlat_unmap_memory_page_TC1)
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
	unsigned int page_idx[3U];
	unsigned int expected_lvls[3U];
	unsigned int end_lvl;

	/***************************************************************
	 * TEST CASE 1:
	 *
	 * For each possible end lookup level, create a set transient
	 * valid random mappings.
	 *
	 * For each possible (region, end_lvl) tuple, there will be three
	 * mmap regions created:
	 *
	 *	- First region mapped at the beginning of a table whose
	 *	  final lookup level is 'end_lvl'
	 *	- Second region mapped at a random tte of a table whose
	 *	  final lookup level is 'end_lvl'
	 *	- Third region mapped at the end of a table whose
	 *	  final lookup level is 'end_lvl'
	 *
	 * Then verify that the tables can be unmapped and that the
	 * resulting tte will contain a transient invalid entry.
	 ***************************************************************/

	mmap_count = 3U;

	/* The first look-up level that supports blocks is L1 */
	for (end_lvl = 1U; end_lvl <= XLAT_TABLE_LEVEL_MAX; end_lvl++) {
		for (unsigned int i = 0U; i < (unsigned int)VA_REGIONS; i++) {
			region = (xlat_addr_region_id_t)i;

			start_va = gen_va_space_params_by_lvl(0U, region,
							      &va_size);

			retval = gen_mmap_array_by_level(&init_mmap[0U],
							 &page_idx[0U],
							 &expected_lvls[0U],
							 mmap_count,
							 end_lvl,
							 &granularity,
							 start_va, 0ULL,
							 false);

			/* Verify that the test setup is correct so far */
			CHECK_TRUE(retval == 0);

			/* Clean the data structures */
			memset((void *)&ctx, 0, sizeof(struct xlat_ctx));
			memset((void *)&cfg, 0,	sizeof(struct xlat_ctx_cfg));
			memset((void *)&tbls, 0, sizeof(struct xlat_ctx_tbls));

			/* Initialize the test structure */
			retval = xlat_ctx_cfg_init(&cfg, region,
						   &init_mmap[0U],
						   mmap_count, va_size);

			/* Verify that the test setup is correct so far */
			CHECK_TRUE(retval == 0);

			retval = xlat_ctx_init(&ctx, &cfg, &tbls,
					       &xlat_tables[0U],
					       XLAT_TESTS_MAX_TABLES);

			/* Verify that the test setup is correct so far */
			CHECK_TRUE(retval == 0);

			/*
			 * For each one of the mmap regions:
			 * - get the TTE of a random VA and make it transient
			 * - call xlat_unmap_memory_page() over the same VA
			 * - verify that the TTE is now transient invalid.
			 */
			for (unsigned j = 0U; j < mmap_count; j++) {
				uint64_t tte;
				uint64_t *tbl_ptr;
				unsigned int tte_idx, tte_lvl;
				struct xlat_tbl_info tbl_info;
				uintptr_t offset =
					test_helpers_get_rand_in_range(0,
						XLAT_TESTS_GRANULARITY_SIZE - 1);
				uintptr_t test_va = init_mmap[j].base_va +
						ctx.cfg->base_va + offset;

				/*
				 * Perform a table walk to retrieve the table
				 * where the VA is mapped along with the index
				 * of the TTE within the table.
				 */
				retval = xlat_test_helpers_table_walk(&ctx,
							test_va, &tte,
							&tbl_ptr, &tte_lvl,
							&tte_idx);

				/*
				 * Verify that the test setup is correct so far
				 */
				CHECK_TRUE(retval == 0);

				/*
				 * The TTE is expected to be valid. Make it
				 * transient valid within the table.
				 */
				tbl_ptr[tte_idx] |=
					(1ULL << XLAT_TESTS_TRANSIENT_FLAG_SHIFT);

				/*
				 * Retrieve the xlat_tbl_info structure needed
				 * to feed xlat_unmap_memory_page()
				 */
				retval = xlat_get_table_from_va(&tbl_info, &ctx,
								test_va);

				/*
				 * Verify that the test setup is correct so far
				 */
				CHECK_TRUE(retval == 0);

				/*
				 * Try to unmap the page/block
				 * containing `test_va`
				 */
				retval = xlat_unmap_memory_page(&tbl_info,
								test_va);

				/* Verify that the return is as expected */
				CHECK_TRUE(retval == 0);

				/*
				 * Verify that the TTE is marked as transient
				 * invalid.
				 */
				CHECK_VERBOSE((tbl_ptr[tte_idx] ==
					(1ULL << XLAT_TESTS_TRANSIENT_FLAG_SHIFT)),
					"Verifying TTE for VA 0x%lx is marked as Transient Invalid",
						test_va);
			}
			VERBOSE("\n");
		}
	}
}

TEST(xlat_tests, xlat_unmap_memory_page_TC2)
{
	struct xlat_ctx ctx;
	struct xlat_ctx_cfg cfg;
	struct xlat_ctx_tbls tbls;
	uintptr_t start_va, test_va, offset;
	size_t va_size, granularity;
	unsigned int mmap_count;
	unsigned int tte_idx, tte_lvl;
	xlat_addr_region_id_t region;
	int retval;
	struct xlat_mmap_region init_mmap[3U];
	unsigned int page_idx[3U];
	unsigned int expected_lvls[3U];
	struct xlat_tbl_info tbl_info;
	uint64_t tte, val_tte;
	uint64_t *tbl_ptr;

	/***************************************************************
	 * TEST CASE 2:
	 *
	 * Generate a mmap region with a set of transient valid
	 * mappings. Then run a set of negative tests:
	 *
	 *	- Try addresses below and above the range mapped by the
	 *	  xlat_tbl_info structure on a transient-valid entry.
	 *	- Try unmapping from a valid non-transient entry.
	 *	- Try unmapping from an invalid entry.
	 ***************************************************************/

	mmap_count = 3U;

	for (unsigned int i = 0U; i < (unsigned int)VA_REGIONS; i++) {
		region = (xlat_addr_region_id_t)i;

		start_va = gen_va_space_params_by_lvl(0U, region, &va_size);

		/*
		 * Create an offset that will make the last level table
		 * to be mapped to an index other than 0 on its parent table,
		 * so that the VA mapped by the last level table does not match
		 * 'start_va' which would be 0ULL for the low level region.
		 * This way, we can pick up an address below the minimum VA
		 * mapped by the last level table to test the low boundary of
		 * the allowed region.
		 */
		offset = test_helpers_get_rand_in_range(1,
					XLAT_TESTS_TBL_ENTRIES - 1);
		offset *= XLAT_TESTS_TABLE_LVL_BLOCK_SIZE(2U);

		/*
		 * We generate the mmap regions to use. We will be interested
		 * in init_mmap[1].
		 */
		retval = gen_mmap_array_by_level(&init_mmap[0U], &page_idx[0U],
						 &expected_lvls[0U],
						 mmap_count, 3U, &granularity,
						 start_va, offset, false);

		/* Verify that the test setup is correct so far */
		CHECK_TRUE(retval == 0);

		/* Clean the data structures */
		memset((void *)&ctx, 0, sizeof(struct xlat_ctx));
		memset((void *)&cfg, 0,	sizeof(struct xlat_ctx_cfg));
		memset((void *)&tbls, 0, sizeof(struct xlat_ctx_tbls));

		/* Initialize the test structure */
		retval = xlat_ctx_cfg_init(&cfg, region, &init_mmap[0U],
					   mmap_count, va_size);

		/* Verify that the test setup is correct so far */
		CHECK_TRUE(retval == 0);

		retval = xlat_ctx_init(&ctx, &cfg, &tbls, &xlat_tables[0U],
				       XLAT_TESTS_MAX_TABLES);

		/* Verify that the test setup is correct so far */
		CHECK_TRUE(retval == 0);

		/*
		 * Make the TTEs of the mapped region, which is expected
		 * to be valid, transient valid.
		 */
		test_va = init_mmap[1U].base_va + ctx.cfg->base_va;

		/*
		 * Perform a table walk to retrieve the table where the VA
		 * is mapped along with the index of the TTE within the table.
		 */
		retval = xlat_test_helpers_table_walk(&ctx, test_va, &tte,
						      &tbl_ptr, &tte_lvl,
						      &tte_idx);

		/* Verify that the test setup is correct so far */
		CHECK_TRUE(retval == 0);

		/*
		 * The TTE is expected to be valid. Make it
		 * transient valid within the table.
		 */
		tbl_ptr[tte_idx] |= (1ULL << XLAT_TESTS_TRANSIENT_FLAG_SHIFT);
		val_tte = tbl_ptr[tte_idx];

		/*
		 * Retrieve the xlat_tbl_info structure needed to feed
		 * xlat_unmap_memory_page().
		 */
		retval = xlat_get_table_from_va(&tbl_info, &ctx,
				init_mmap[1U].base_pa + ctx.cfg->base_va);

		/* Verify that the test setup is correct so far */
		CHECK_TRUE(retval == 0);

		/*
		 * Test xlat_unmmap_memory_page() with a valid address
		 * below the start of init_mmap[0U]. This gives us an address
		 * below the range mapped by table we retrieved.
		 */
		test_va = init_mmap[0U].base_va + ctx.cfg->base_va;
		test_va -= test_helpers_get_rand_in_range(1,
					XLAT_TESTS_GRANULARITY_SIZE - 1);

		/* Try to unmap the page/block containing `test_va` */
		retval = xlat_unmap_memory_page(&tbl_info, test_va);

		/* Verify that the return is as expected */
		CHECK_VERBOSE((retval == -EFAULT),
			      "Testing VA 0x%lx on TTE for VA 0x%lx",
			      test_va,
			      init_mmap[1U].base_va + ctx.cfg->base_va);

		/* Verify that the TTE remains unchanged */
		CHECK_EQUAL(val_tte, tbl_ptr[tte_idx]);

		/*
		 * Repeat the process, this time with an address on a page
		 * after the one mapped by init_mmap[2U]. This gives us an
		 * address over the range mapped by table we retrieved.
		 */
		test_va = init_mmap[2U].base_va + ctx.cfg->base_va;
		test_va += XLAT_TESTS_GRANULARITY_SIZE;
		test_va += test_helpers_get_rand_in_range(0,
					XLAT_TESTS_GRANULARITY_SIZE - 1);

		/* Try to unmap the page/block containing `test_va` */
		retval = xlat_unmap_memory_page(&tbl_info, test_va);

		/* Verify that the return is as expected */
		CHECK_VERBOSE((retval == -EFAULT),
			      "Testing VA 0x%lx on TTE for VA 0x%lx",
			      test_va,
			      init_mmap[2U].base_va + ctx.cfg->base_va);

		/* Verify that the TTE remains unchanged */
		CHECK_EQUAL(val_tte, tbl_ptr[tte_idx]);

		/*
		 * Try to unmap an address marked as non-transient
		 */
		tbl_ptr[tte_idx] &= ~(1ULL << XLAT_TESTS_TRANSIENT_FLAG_SHIFT);
		val_tte = tbl_ptr[tte_idx];

		test_va = init_mmap[1U].base_va + ctx.cfg->base_va;
		test_va += test_helpers_get_rand_in_range(0,
					XLAT_TESTS_GRANULARITY_SIZE - 1);

		/* Try to unmap the page/block containing `test_va` */
		retval = xlat_unmap_memory_page(&tbl_info, test_va);

		/* Verify that the return is as expected */
		CHECK_VERBOSE((retval == -EFAULT),
			      "Testing VA 0x%lx on a non-transient valid TTE",
			      test_va);

		/* Verify that the TTE remains unchanged */
		CHECK_EQUAL(val_tte, tbl_ptr[tte_idx]);

		/*
		 * Try to unmap an address marked as invalid.
		 */
		tbl_ptr[tte_idx] = XLAT_TESTS_INVALID_DESC;
		val_tte = tbl_ptr[tte_idx];

		test_va = init_mmap[1U].base_va + ctx.cfg->base_va;
		test_va += test_helpers_get_rand_in_range(0,
					XLAT_TESTS_GRANULARITY_SIZE - 1);

		/* Try to unmap the page/block containing `test_va` */
		retval = xlat_unmap_memory_page(&tbl_info, test_va);

		/* Verify that the return is as expected */
		CHECK_VERBOSE((retval == -EFAULT),
			      "Testing VA 0x%lx on a ninvalid TTE",
			      test_va);

		/* Verify that the TTE remains unchanged */
		CHECK_EQUAL(val_tte, tbl_ptr[tte_idx]);
		VERBOSE("\n");
	}
}

ASSERT_TEST(xlat_tests, xlat_unmap_memory_page_TC3)
{
	/***************************************************************
	 * TEST CASE 3:
	 *
	 * Try calling xlat_unmap_memory_page with a NULL
	 * xlat_tbl_info structure.
	 ***************************************************************/

	test_helpers_expect_assert_fail(true);
	(void)xlat_unmap_memory_page(NULL, 0ULL);
	test_helpers_fail_if_no_assert_failed();
}

TEST(xlat_tests, xlat_map_memory_page_with_attrs_TC1)
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
	unsigned int page_idx[3U];
	unsigned int expected_lvls[3U];
	unsigned int end_lvl;

	/***************************************************************
	 * TEST CASE 1:
	 *
	 * For each possible end lookup level, create a set transient
	 * random mappings.
	 *
	 * For each possible (region, end_lvl) tuple, there will be three
	 * mmap regions created:
	 *
	 *	- First region mapped at the beginning of a table whose
	 *	  final lookup level is 'end_lvl'
	 *	- Second region mapped at a random tte of a table whose
	 *	  final lookup level is 'end_lvl'
	 *	- Third region mapped at the end of a table whose
	 *	  final lookup level is 'end_lvl'
	 *
	 * Then verify that we can map PA areas into the transient
	 * entries using random attributes and that the generated
	 * entry is valid.
	 ***************************************************************/

	mmap_count = 3U;

	/* The first look-up level that supports blocks is L1 */
	for (end_lvl = 1U; end_lvl <= XLAT_TABLE_LEVEL_MAX; end_lvl++) {
		for (unsigned int i = 0U; i < (unsigned int)VA_REGIONS; i++) {
			region = (xlat_addr_region_id_t)i;

			start_va = gen_va_space_params_by_lvl(0U, region,
							      &va_size);

			retval = gen_mmap_array_by_level(&init_mmap[0U],
							 &page_idx[0U],
							 &expected_lvls[0U],
							 mmap_count,
							 end_lvl,
							 &granularity,
							 start_va, 0ULL,
							 false);

			/* Verify that the test setup is correct so far */
			CHECK_TRUE(retval == 0);

			/* Force all the mmap regions to be TRANSIENT */
			for (unsigned int j = 0U; j < mmap_count; j++) {
				init_mmap[j].attr = MT_TRANSIENT;
			}

			/* Clean the data structures */
			memset((void *)&ctx, 0, sizeof(struct xlat_ctx));
			memset((void *)&cfg, 0,	sizeof(struct xlat_ctx_cfg));
			memset((void *)&tbls, 0, sizeof(struct xlat_ctx_tbls));

			/* Initialize the test structure */
			retval = xlat_ctx_cfg_init(&cfg, region,
						   &init_mmap[0U],
						   mmap_count, va_size);

			/* Verify that the test setup is correct so far */
			CHECK_TRUE(retval == 0);

			retval = xlat_ctx_init(&ctx, &cfg, &tbls,
					       &xlat_tables[0U],
					       XLAT_TESTS_MAX_TABLES);

			/* Verify that the test setup is correct so far */
			CHECK_TRUE(retval == 0);

			/*
			 * For each one of the mmap regions:
			 * - Generate a random VA within the mmap VA space.
			 * - generate a set of random attributes.
			 * - Map a random PA to to the generated VA and with
			 *   the generated attributes.
			 * - call xlat_unmap_memory_page_map_with_attrs() to
			 *   create the mapping.
			 * - verify that the new entry is valid.
			 */
			for (unsigned j = 0U; j < mmap_count; j++) {
				uint64_t tte, val_tte, attrs, pa, type;
				uint64_t *tbl_ptr;
				unsigned int tte_idx, tte_lvl;
				struct xlat_tbl_info tbl_info;
				uintptr_t offset =
					test_helpers_get_rand_in_range(0,
						XLAT_TESTS_GRANULARITY_SIZE - 1);
				uintptr_t test_va = init_mmap[j].base_va +
						ctx.cfg->base_va + offset;

				/*
				 * Perform a table walk to retrieve the table
				 * where the VA is mapped along with the index
				 * of the TTE within the table.
				 */
				retval = xlat_test_helpers_table_walk(&ctx,
							test_va, &tte,
							&tbl_ptr, &tte_lvl,
							&tte_idx);

				/*
				 * Verify that the test setup is correct so far
				 */
				CHECK_TRUE(retval == 0);

				/* Generate a random set of attributes.	*/
				do {
					attrs = get_mmap_attrs();
				} while (attrs == MT_TRANSIENT);

				/*
				 * Generate the validation TTE. For convenience,
				 * create an identity mapping.
				 */
				retval = xlat_test_helpers_gen_attrs(&val_tte,
								     attrs);
				pa = init_mmap[j].base_va & XLAT_TESTS_PA_MASK;
				pa += test_helpers_get_rand_in_range(1,
						XLAT_TESTS_GRANULARITY_SIZE - 1);
				val_tte |= pa & XLAT_TESTS_TABLE_OA_MASK;

				/* The TTE will be a transient one */
				val_tte |= (1ULL <<
					XLAT_TESTS_TRANSIENT_FLAG_SHIFT);

				/* TTE type */
				type = (end_lvl == XLAT_TESTS_MAX_LEVEL) ?
							XLAT_TESTS_PAGE_DESC :
							XLAT_TESTS_BLOCK_DESC;
				val_tte |= type;

				/* Verify the test setup */
				CHECK_TRUE(retval == 0);

				/*
				 * Retrieve the xlat_tbl_info structure needed
				 * to feed xlat_map_memory_page_with_attrs()
				 */
				retval = xlat_get_table_from_va(&tbl_info, &ctx,
								test_va);

				/*
				 * Verify that the test setup is correct so far
				 */
				CHECK_TRUE(retval == 0);

				/*
				 * Try to map the PA with the attributes to the
				 * `test_va`
				 */
				retval = xlat_map_memory_page_with_attrs(
							&tbl_info,
							test_va, pa, attrs);

				/* Verify that the return is as expected */
				CHECK_VERBOSE((retval == 0),
					"Mapping PA 0x%.16lx to VA 0x%.16lx with attrs 0x%lx",
					 pa, test_va, attrs);
				CHECK_TRUE(retval == 0);

				/*
				 * Verify that the generated TTE matches
				 * the validation one.
				 */
				CHECK_VERBOSE((val_tte == tbl_ptr[tte_idx]),
					"Verifying TTE 0x%.16lx against 0x%.16lx",
						tbl_ptr[tte_idx], val_tte);
			}
			VERBOSE("\n");
		}
	}
}

TEST(xlat_tests, xlat_map_memory_page_with_attrs_TC2)
{
	struct xlat_ctx ctx;
	struct xlat_ctx_cfg cfg;
	struct xlat_ctx_tbls tbls;
	uintptr_t start_va, test_va, test_pa, offset;
	size_t va_size, granularity;
	unsigned int mmap_count;
	unsigned int tte_idx, tte_lvl;
	xlat_addr_region_id_t region;
	int retval;
	struct xlat_mmap_region init_mmap[3U];
	unsigned int page_idx[3U];
	unsigned int expected_lvls[3U];
	struct xlat_tbl_info tbl_info;
	uint64_t tte, val_tte;
	uint64_t *tbl_ptr;
	unsigned int pa_range_bits_arr[] = {
		PARANGE_0000_WIDTH, PARANGE_0001_WIDTH, PARANGE_0010_WIDTH,
		PARANGE_0011_WIDTH, PARANGE_0100_WIDTH, PARANGE_0101_WIDTH,
	};
	unsigned int index = test_helpers_get_rand_in_range(0,
		sizeof(pa_range_bits_arr)/sizeof(pa_range_bits_arr[0]) - 1U);


	/***************************************************************
	 * TEST CASE 2:
	 *
	 * Generate a mmap region with a set of transient invalid
	 * mappings. Then run a set of negative tests:
	 *
	 *	- Try addresses below and above the range mapped by the
	 *	  xlat_tbl_info structure on a transient-invalid entry.
	 *	- Try mapping a PA lager than the maximum supported PA
	 *	  to a transient-invalid entry.
	 *	- Try mapping to a transient-valid entry.
	 *	- Try mapping to a valid entry.
	 *	- Try mapping to an invalid entry.
	 ***************************************************************/

	mmap_count = 3U;

	for (unsigned int i = 0U; i < (unsigned int)VA_REGIONS; i++) {
		region = (xlat_addr_region_id_t)i;

		start_va = gen_va_space_params_by_lvl(0U, region, &va_size);

		/*
		 * Create an offset that will make the last level table
		 * to be mapped to an index other than 0 on its parent table,
		 * so that the VA mapped by the last level table does not match
		 * 'start_va' which would be 0ULL for the low level region.
		 * This way, we can pick up an address below the minimum VA
		 * mapped by the last level table to test the low boundary of
		 * the allowed region.
		 */
		offset = test_helpers_get_rand_in_range(1,
					XLAT_TESTS_TBL_ENTRIES - 1);
		offset *= XLAT_TESTS_TABLE_LVL_BLOCK_SIZE(2U);

		/*
		 * We generate the mmap regions to use. We will be interested
		 * in init_mmap[1] for the transient-invalid tests and in
		 * init_mmap[0] for the rest of tests.
		 */
		retval = gen_mmap_array_by_level(&init_mmap[0U], &page_idx[0U],
						 &expected_lvls[0U],
						 mmap_count, 3U, &granularity,
						 start_va, offset, false);

		/* Verify that the test setup is correct so far */
		CHECK_TRUE(retval == 0);

		/* Force init_mmap[1] to be TRANSIENT */
		init_mmap[1U].attr = MT_TRANSIENT;

		/* Clean the data structures */
		memset((void *)&ctx, 0, sizeof(struct xlat_ctx));
		memset((void *)&cfg, 0,	sizeof(struct xlat_ctx_cfg));
		memset((void *)&tbls, 0, sizeof(struct xlat_ctx_tbls));

		/* Initialize the test structure */
		retval = xlat_ctx_cfg_init(&cfg, region, &init_mmap[0U],
					   mmap_count, va_size);

		/* Verify that the test setup is correct so far */
		CHECK_TRUE(retval == 0);

		retval = xlat_ctx_init(&ctx, &cfg, &tbls, &xlat_tables[0U],
				       XLAT_TESTS_MAX_TABLES);

		/* Verify that the test setup is correct so far */
		CHECK_TRUE(retval == 0);

		test_va = init_mmap[1U].base_va + ctx.cfg->base_va;

		/*
		 * Perform a table walk to retrieve the table where the VA
		 * is mapped along with the index of the TTE within the table.
		 */
		retval = xlat_test_helpers_table_walk(&ctx, test_va, &tte,
						      &tbl_ptr, &tte_lvl,
						      &tte_idx);

		/* Verify that the test setup is correct so far */
		CHECK_TRUE(retval == 0);

		/*
		 * Make the TTEs of the mapped region, which is expected
		 * to be valid, transient valid.
		 */
		tbl_ptr[tte_idx] |= (1ULL << XLAT_TESTS_TRANSIENT_FLAG_SHIFT);

		/*
		 * Take a snapshot of the TTE. This will be used to verify
		 * that the TTE hasn't been altered.
		 */
		val_tte = tbl_ptr[tte_idx];

		/*
		 * Retrieve the xlat_tbl_info structure needed to feed
		 * xlat_unmap_memory_page().
		 */
		retval = xlat_get_table_from_va(&tbl_info, &ctx, test_va);

		/* Verify that the test setup is correct so far */
		CHECK_TRUE(retval == 0);

		/*
		 * Test xlat_mmap_memory_page_with_attrs() with a valid address
		 * below the start of init_mmap[0U]. This gives us an address
		 * below the range mapped by table we retrieved.
		 * For simplicity, set the attributes and the PA both to 0x0.
		 */
		test_va = init_mmap[0U].base_va + ctx.cfg->base_va;
		test_va -= test_helpers_get_rand_in_range(1,
					XLAT_TESTS_GRANULARITY_SIZE - 1);

		/* Try to map to the page/block containing `test_va` */
		retval = xlat_map_memory_page_with_attrs(&tbl_info, test_va,
							 0ULL, 0ULL);

		/* Verify that the return is as expected */
		CHECK_VERBOSE((retval == -EFAULT),
			      "Testing VA 0x%.16lx on TTE for VA 0x%.16lx",
			      test_va,
			      init_mmap[1U].base_va + ctx.cfg->base_va);

		/* Verify that the TTE remains unchanged */
		CHECK_EQUAL(val_tte, tbl_ptr[tte_idx]);

		/*
		 * Repeat the process, this time with an address on a page
		 * after the one mapped by init_mmap[2U]. This gives us an
		 * address over the range mapped by table we retrieved.
		 */
		test_va = init_mmap[2U].base_va + ctx.cfg->base_va;
		test_va += XLAT_TESTS_GRANULARITY_SIZE;
		test_va += test_helpers_get_rand_in_range(0,
					XLAT_TESTS_GRANULARITY_SIZE - 1);

		/* Try to map to the page/block containing `test_va` */
		retval = xlat_map_memory_page_with_attrs(&tbl_info, test_va,
							 0ULL, 0ULL);

		/* Verify that the return is as expected */
		CHECK_VERBOSE((retval == -EFAULT),
			      "Testing VA 0x%.16lx on TTE for VA 0x%.16lx",
			      test_va,
			      init_mmap[2U].base_va + ctx.cfg->base_va);

		/* Verify that the TTE remains unchanged */
		CHECK_EQUAL(val_tte, tbl_ptr[tte_idx]);

		/*
		 * Test with a PA larger than the maximum PA supported.
		 */

		/* Configure a random maximum PA supported */
		host_write_sysreg("id_aa64mmfr0_el1",
				  INPLACE(ID_AA64MMFR0_EL1_PARANGE, index));
		test_pa = (1ULL << pa_range_bits_arr[index]);

		test_va = init_mmap[2U].base_va + ctx.cfg->base_va;
		test_va += XLAT_TESTS_GRANULARITY_SIZE;
		test_va += test_helpers_get_rand_in_range(0,
					XLAT_TESTS_GRANULARITY_SIZE - 1);

		/* Try to map the PA to the page/block containing `test_va` */
		retval = xlat_map_memory_page_with_attrs(&tbl_info, test_va,
							 test_pa, 0ULL);

		/* Verify that the return is as expected */
		CHECK_VERBOSE((retval == -EFAULT),
			      "Testing PA 0x%.16lx on with a max supported PA of 0x%.16llx",
			      test_pa,
			      (1ULL << pa_range_bits_arr[index]) - 1ULL);

		/* Verify that the TTE remains unchanged */
		CHECK_EQUAL(val_tte, tbl_ptr[tte_idx]);


		/* The rest of the tests will be based on init_mmap[0] */
		test_va = init_mmap[0U].base_va + ctx.cfg->base_va;

		/*
		 * Perform a table walk to retrieve the table where the VA
		 * is mapped along with the index of the TTE within the table.
		 */
		retval = xlat_test_helpers_table_walk(&ctx, test_va, &tte,
						      &tbl_ptr, &tte_lvl,
						      &tte_idx);

		/* Verify that the test setup is correct so far */
		CHECK_TRUE(retval == 0);

		/*
		 * Make the TTEs of the mapped region, which is expected
		 * to be valid, transient valid.
		 */
		tbl_ptr[tte_idx] |= (1ULL << XLAT_TESTS_TRANSIENT_FLAG_SHIFT);

		/*
		 * Take a snapshot of the TTE. This will be used to verify
		 * that the TTE hasn't been altered.
		 */
		val_tte = tbl_ptr[tte_idx];

		/*
		 * Now try to map to a valid VA. In this case the VA
		 * contains a transient valid mapping.
		 */
		test_va = init_mmap[0U].base_va + ctx.cfg->base_va;
		test_va += test_helpers_get_rand_in_range(0,
					XLAT_TESTS_GRANULARITY_SIZE - 1);

		/* Try to map to the page/block containing `test_va` */
		retval = xlat_map_memory_page_with_attrs(&tbl_info, test_va,
							 0ULL, 0ULL);

		/* Verify that the return is as expected */
		CHECK_VERBOSE((retval == -EFAULT),
			      "Testing VA 0x%.16lx on a transient valid TTE",
			      test_va);

		/* Verify that the TTE remains unchanged */
		CHECK_EQUAL(val_tte, tbl_ptr[tte_idx]);

		/*
		 * Repeat the last test but after clearing the TRANSIENT
		 * flag from the TTE. This will test the behaviour with
		 * a non transient TTE.
		 */
		tbl_ptr[tte_idx] &= ~(1ULL << XLAT_TESTS_TRANSIENT_FLAG_SHIFT);
		val_tte = tbl_ptr[tte_idx];

		test_va = init_mmap[0U].base_va + ctx.cfg->base_va;
		test_va += test_helpers_get_rand_in_range(0,
					XLAT_TESTS_GRANULARITY_SIZE - 1);

		/* Try to map to the page/block containing `test_va` */
		retval = xlat_map_memory_page_with_attrs(&tbl_info, test_va,
							 0ULL, 0ULL);

		/* Verify that the return is as expected */
		CHECK_VERBOSE((retval == -EFAULT),
			      "Testing VA 0x%.16lx on a valid TTE",
			      test_va);

		/* Verify that the TTE remains unchanged */
		CHECK_EQUAL(val_tte, tbl_ptr[tte_idx]);

		/*
		 * Repeat the last test on an INVALID TTE.
		 */
		tbl_ptr[tte_idx] = 0ULL;
		val_tte = 0ULL;

		test_va = init_mmap[0U].base_va + ctx.cfg->base_va;
		test_va += test_helpers_get_rand_in_range(0,
					XLAT_TESTS_GRANULARITY_SIZE - 1);

		/* Try to map to the page/block containing `test_va` */
		retval = xlat_map_memory_page_with_attrs(&tbl_info, test_va,
							 0ULL, 0ULL);

		/* Verify that the return is as expected */
		CHECK_VERBOSE((retval == -EFAULT),
			      "Testing VA 0x%.16lx on an invalid TTE",
			      test_va);

		/* Verify that the TTE remains unchanged */
		CHECK_EQUAL(val_tte, tbl_ptr[tte_idx]);

		VERBOSE("\n");
	}
}

ASSERT_TEST(xlat_tests, xlat_map_memory_page_with_attrs_TC3)
{
	/***************************************************************
	 * TEST CASE 3:
	 *
	 * Try calling xlat_map_memory_page_with_attrs with a NULL
	 * xlat_tbl_info structure.
	 ***************************************************************/

	test_helpers_expect_assert_fail(true);
	(void)xlat_map_memory_page_with_attrs(NULL, 0ULL, 0ULL, 0ULL);
	test_helpers_fail_if_no_assert_failed();
}
