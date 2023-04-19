/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <errno.h>
#include <host_utils.h>
#include <stdlib.h>
#include <string.h>
#include <test_helpers.h>
#include <xlat_contexts.h>	/* API to test */
#include <xlat_defs.h>
#include <xlat_tables.h>	/* API to test */
#include <xlat_tables_private.h>
#include <xlat_test_defs.h>
#include <xlat_test_helpers.h>

/* Reserve some memory to be used for the translation tables */
static uint64_t xlat_tables[XLAT_TABLE_ENTRIES * XLAT_TESTS_MAX_TABLES]
					__aligned(XLAT_TABLE_SIZE);

void xlat_test_helpers_init_ctx_tbls(struct xlat_ctx_tbls *ctx_tbls,
				     uint64_t *tbls,
				     unsigned int tables_num,
				     unsigned int next_table,
				     bool initialized)
{
	ctx_tbls->tables = tbls;
	ctx_tbls->tables_num = tables_num;
	ctx_tbls->next_table = next_table;
	ctx_tbls->initialized = initialized;
}

void xlat_test_helpers_init_ctx_cfg(struct xlat_ctx_cfg *ctx_cfg,
				    uintptr_t max_va_size,
				    uintptr_t base_va,
				    uintptr_t max_mapped_pa,
				    uintptr_t max_mapped_va_offset,
				    unsigned int base_level,
				    xlat_addr_region_id_t region,
				    struct xlat_mmap_region *mm,
				    unsigned int mmaps,
				    bool initialized)
{
	ctx_cfg->max_va_size = max_va_size;
	ctx_cfg->mmap = mm;
	ctx_cfg->mmap_regions = mmaps;
	ctx_cfg->base_va = base_va;
	ctx_cfg->max_mapped_pa = max_mapped_pa;
	ctx_cfg->max_mapped_va_offset = max_mapped_va_offset;
	ctx_cfg->base_level = base_level;
	ctx_cfg->region = region;
	ctx_cfg->initialized = initialized;
}

void xlat_test_helpers_init_ctx(struct xlat_ctx *ctx,
				struct xlat_ctx_cfg *cfg,
				struct xlat_ctx_tbls *tbls)
{
	ctx->cfg = cfg;
	ctx->tbls = tbls;
}

void xlat_test_hepers_arch_init(void)
{
	unsigned int retval __unused;

	/* Enable the platform with support for multiple PEs */
	test_helpers_rmm_start(true);

	/*
	 * Reset the sysreg state so that we can setup
	 * custom values for the tests
	 */
	host_util_zero_sysregs_and_cbs();

	/* Setup id_aa64mmfr0_el1 with a PA size of 48 bits */
	retval = host_util_set_default_sysreg_cb("id_aa64mmfr0_el1",
				INPLACE(ID_AA64MMFR0_EL1_PARANGE, 5UL));

	/* Initialize MMU registers to 0 */
	retval = host_util_set_default_sysreg_cb("sctlr_el2", 0UL);
	retval = host_util_set_default_sysreg_cb("mair_el2", 0UL);
	retval = host_util_set_default_sysreg_cb("tcr_el2", 0UL);
	retval = host_util_set_default_sysreg_cb("ttbr0_el2", 0UL);
	retval = host_util_set_default_sysreg_cb("ttbr1_el2", 0UL);

	assert(retval == 0);

	/* Make sure current cpu id is 0 (primary processor) */
	host_util_set_cpuid(0U);

	test_helpers_expect_assert_fail(false);
}

uintptr_t xlat_test_helpers_get_start_va(xlat_addr_region_id_t region,
					 size_t va_size)
{
	return (region == VA_LOW_REGION) ?
			0ULL : (ULONG_MAX - va_size + 1UL);
}

uint64_t xlat_test_helpers_rand_mmap_attrs(void)
{
	const uint64_t attrs[] = {MT_CODE, MT_RO_DATA,
				  MT_RW_DATA, MT_DEVICE, MT_TRANSIENT};
	const uint64_t pas[] = {MT_REALM, MT_NS};
	uint64_t ret_attrs;
	unsigned int index;

	index = (unsigned int)test_helpers_get_rand_in_range(0,
				(sizeof(attrs) / sizeof(uint64_t)) - 1);

	ret_attrs = attrs[index];

	if (ret_attrs != MT_TRANSIENT) {
		if ((ret_attrs != MT_DEVICE) && (rand() & 0x1)) {
			/*
			 * Randomly change shareability for MT_MEMORY types.
			 */
			ret_attrs &= ~(MT_SHAREABILITY_ISH);
			ret_attrs |= MT_SHAREABILITY_OSH;
		}

		index = (unsigned int)test_helpers_get_rand_in_range(0,
				(sizeof(pas) / sizeof(uint64_t)) - 1);
		ret_attrs |= pas[index];
		ret_attrs = (rand() & 0x1) ? (ret_attrs | MT_NG) : ret_attrs;
	}

	return ret_attrs;
}

void xlat_test_helpers_rand_mmap_array(struct xlat_mmap_region *mmap,
					size_t size, uintptr_t min_va,
					uintptr_t max_va)
{

/* Maximum number of pages allowed per region */
#define MAX_PAGES_PER_REGION	(100U)

/* Maximum separation (in pages) between regions */
#define MAX_PAGES_SEPARATION	(10U)

	unsigned int region_pages;
	size_t region_size;
	uintptr_t next_va_start = min_va;

	assert(mmap != NULL);
	assert(size > 0);
	assert(max_va > min_va);
	assert((min_va + (MAX_PAGES_PER_REGION * size * PAGE_SIZE)) <= max_va);

	/* Randomize the base VA for the first memory region */
	region_pages = test_helpers_get_rand_in_range(0, MAX_PAGES_PER_REGION);
	next_va_start += (region_pages * PAGE_SIZE);

	/* Generate an ordered list of mmap regions */
	for (unsigned int i = 0U; i < (unsigned int)size; i++) {
		/* Pages of memory to use for the current region */
		region_pages = test_helpers_get_rand_in_range(2,
							MAX_PAGES_PER_REGION);
		region_size = region_pages * PAGE_SIZE;

		mmap[i].attr = xlat_test_helpers_rand_mmap_attrs();
		mmap[i].granularity = XLAT_TESTS_MAX_BLOCK_SIZE;
		mmap[i].base_va = next_va_start;
		mmap[i].base_pa = next_va_start & XLAT_TESTS_PA_MASK;
		mmap[i].size = region_size;

		/*
		 * Next region start. Add a random offset to the
		 * end of the current region.
		 */
		next_va_start += region_size +
			(test_helpers_get_rand_in_range(0, MAX_PAGES_SEPARATION) *
				PAGE_SIZE);

		assert(next_va_start < max_va);
	}
}

int xlat_test_helpers_table_walk(struct xlat_ctx *ctx,
				 unsigned long long va,
				 uint64_t *tte,
				 uint64_t **table_ptr,
				 unsigned int *level,
				 unsigned int *index)
{
	struct xlat_ctx_cfg *cfg;
	struct xlat_ctx_tbls *tbls;
	uint64_t ctte;
	uint64_t *table;

	assert(ctx != NULL);
	assert(ctx->tbls != NULL);
	assert(ctx->cfg != NULL);
	assert(tte != NULL);
	assert(level != NULL);
	assert(index != NULL);

	cfg = ctx->cfg;
	tbls = ctx->tbls;

	if (tbls->initialized == false) {
		return -EINVAL;
	}

	if (cfg->initialized == false) {
		return -EINVAL;
	}

	if ((tbls->tables == NULL) || (tbls->tables_num == 0U)) {
		return -EINVAL;
	}

	if (va > cfg->base_va + cfg->max_mapped_va_offset) {
		return -ERANGE;
	}

	/* Base table is the first table of the array */
	table = &tbls->tables[0U];
	for (unsigned int i = cfg->base_level;
					i <= XLAT_TABLE_LEVEL_MAX; i++) {
		uint64_t tte_oa;
		unsigned int tindex =
			(unsigned int)(va >> XLAT_ADDR_SHIFT(i)) &
						XLAT_TABLE_ENTRIES_MASK;

		if (tindex >= XLAT_TABLE_ENTRIES) {
			return -ERANGE;
		}

		ctte = table[tindex];
		if (ctte == INVALID_DESC) {
			return -ERANGE;
		}

		if (XLAT_TESTS_IS_TRANSIENT_DESC(ctte)) {
			*tte = ctte;
			*level = i;
			*index = tindex;
			if (table_ptr != NULL) {
				*table_ptr = table;
			}
			return 0;
		}

		switch (i) {
		case 0U:
			/* Only table descriptors allowed here */
			if (!XLAT_TESTS_IS_DESC(ctte, TABLE_DESC)) {
				return -EINVAL;
			}

			if (EXTRACT(UPPER_ATTRS, ctte) != 0ULL) {
				/* Table attributes are expected to be 0x0 */
				return -EINVAL;
			}

			tte_oa = (EXTRACT(TABLE_ADDR, ctte) <<
						TABLE_ADDR_SHIFT);
			table = (uint64_t *)tte_oa;
			break;

		case 1U:
		case 2U:
			if (XLAT_TESTS_IS_DESC(ctte, BLOCK_DESC)) {
				*tte = ctte;
				*level = i;
				*index = tindex;
				if (table_ptr != NULL) {
					*table_ptr = table;
				}
				return 0;
			}

			/* This is a table descriptor */
			tte_oa = (EXTRACT(TABLE_ADDR, ctte) <<
						TABLE_ADDR_SHIFT);
			table = (uint64_t *)tte_oa;
			break;

		case 3U:
			/* Only page descriptors allowed here */
			if (!XLAT_TESTS_IS_DESC(ctte, PAGE_DESC)) {
				return -EINVAL;
			}
			*tte = ctte;
			*level = i;
			*index = tindex;
			if (table_ptr != NULL) {
				*table_ptr = table;
			}
			return 0;

		default:
			return -EINVAL;
		}
	}

	/* We should never get here */
	return -EINVAL;
}

int xlat_test_helpers_gen_attrs(uint64_t *attrs, uint64_t mmap_attrs)
{
	uint64_t mem_type, sh_attr;
	uint64_t lower_attrs, upper_attrs;

	/* Generate the set of descriptor attributes */
	mem_type = EXTRACT(MT_TYPE, mmap_attrs);
	switch (mem_type) {
	case MT_DEVICE:
		lower_attrs = LOWER_ATTRS(ATTR_DEVICE_INDEX | OSH);
		upper_attrs = XLAT_GET_PXN_DESC();
		break;
	case MT_MEMORY:
		lower_attrs = LOWER_ATTRS(ATTR_IWBWA_OWBWA_NTR_INDEX);
		upper_attrs = 0ULL;
		break;
	default:
		return -EINVAL;
	}

	if (mmap_attrs & MT_NG) {
		lower_attrs |= XLAT_GET_NG_HINT();
	}

	/* Set AF */
	lower_attrs |= LOWER_ATTRS(ACCESS_FLAG);

	/* Set the UXN flag */
	upper_attrs |= XLAT_GET_UXN_DESC();

	if (MT_PAS(mmap_attrs) == MT_NS) {
		lower_attrs |= LOWER_ATTRS(NS);
	}

	if (mmap_attrs & MT_RW) {
		lower_attrs |= LOWER_ATTRS(AP_RW);
	} else {
		lower_attrs |= LOWER_ATTRS(AP_RO);
	}

	if (mmap_attrs & MT_EXECUTE_NEVER) {
		upper_attrs |= XLAT_GET_PXN_DESC();
	}

	if (mem_type == MT_DEVICE) {
		*attrs = upper_attrs | lower_attrs;
		return 0;
	}

	sh_attr = MT_SHAREABILITY(mmap_attrs);
	switch (sh_attr) {
	case MT_SHAREABILITY_ISH:
		lower_attrs |= LOWER_ATTRS(ISH);
		break;
	case MT_SHAREABILITY_OSH:
		lower_attrs |= LOWER_ATTRS(OSH);
		break;
	case MT_SHAREABILITY_NSH:
		lower_attrs |= LOWER_ATTRS(NSH);
		break;
	}

	*attrs = upper_attrs | lower_attrs;
	return 0;
}

int xlat_test_helpers_gen_attrs_from_va(struct xlat_ctx *ctx,
					unsigned long long va,
					uint64_t *attrs)
{
	uint64_t mmap_attrs = 0ULL;
	unsigned int i;

	assert(attrs != NULL);

	for (i = 0; i < ctx->cfg->mmap_regions; i++) {
		unsigned long long mmap_min_va =
			ctx->cfg->base_va + ctx->cfg->mmap[i].base_va;
		unsigned long long mmap_max_va = mmap_min_va +
					    ctx->cfg->mmap[i].size - 1ULL;

		if ((va >= mmap_min_va) && (va <= mmap_max_va)) {
			mmap_attrs = ctx->cfg->mmap[i].attr;
			break;
		}
	}

	if (i >= ctx->cfg->mmap_regions) {
		/* VA not found */
		return -EINVAL;
	}

	return xlat_test_helpers_gen_attrs(attrs, mmap_attrs);
}

uint64_t *xlat_test_helpers_tbls(void)
{
	return &xlat_tables[0U];
}
