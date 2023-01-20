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
#include <xlat_test_defs.h>

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
	unsigned int retval;

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
					i <= XLAT_TESTS_MAX_LEVEL; i++) {
		uint64_t tte_oa;
		unsigned int tindex =
			(unsigned int)(va >> XLAT_TESTS_TABLE_LVL_SHIFT(i)) &
						XLAT_TESTS_TBL_ENTRIES_MASK;

		if (tindex >= XLAT_TESTS_TBL_ENTRIES) {
			return -ERANGE;
		}

		ctte = table[tindex];
		if (ctte == XLAT_TESTS_INVALID_DESC) {
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
			if (!XLAT_TESTS_IS_DESC(ctte, XLAT_TESTS_TABLE_DESC)) {
				return -EINVAL;
			}

			if (((ctte >> (XLAT_TESTS_TABLE_DESC_ATTRS_SHIFT)) &
				XLAT_TESTS_TABLE_DESC_ATTRS_MASK) != 0ULL) {

				/* Table attributes are expected to be 0x0 */
				return -EINVAL;
			}

			tte_oa = ctte & (XLAT_TESTS_NEXT_LEVEL_TA_MASK <<
						XLAT_TESTS_NEXT_LEVEL_TA_SHIFT);
			table = (uint64_t *)tte_oa;
			break;

		case 1U:
		case 2U:
			if (XLAT_TESTS_IS_DESC(ctte, XLAT_TESTS_BLOCK_DESC)) {
				*tte = ctte;
				*level = i;
				*index = tindex;
				if (table_ptr != NULL) {
					*table_ptr = table;
				}
				return 0;
			}

			/* This is a table descriptor */
			tte_oa = ctte & (XLAT_TESTS_NEXT_LEVEL_TA_MASK <<
						XLAT_TESTS_NEXT_LEVEL_TA_SHIFT);
			table = (uint64_t *)tte_oa;
			break;

		case 3U:
			/* Only page descriptors allowed here */
			if (!XLAT_TESTS_IS_DESC(ctte, XLAT_TESTS_PAGE_DESC)) {
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
	mem_type = MT_TYPE(mmap_attrs);
	switch (mem_type) {
	case MT_DEVICE:
		lower_attrs =
			((XLAT_TESTS_ATTR_DEVICE_IDX & XLAT_TESTS_ATTR_IDX_MASK) <<
						XLAT_TESTS_ATTR_IDX_SHIFT);
		lower_attrs |=
			((XLAT_TESTS_SHAREABILITY_OSH & XLAT_TESTS_ATTR_SH_MASK) <<
						XLAT_TESTS_ATTR_SH_SHIFT);
		upper_attrs =
			((XLAT_TESTS_EXECUTE_NEVER & XLAT_TESTS_ATTR_PXN_MASK) <<
			 (XLAT_TESTS_ATTR_PXN_SHIFT));
		break;
	case MT_NON_CACHEABLE:
		lower_attrs =
			((XLAT_TESTS_ATTR_NON_CACHEABLE_IDX &
					XLAT_TESTS_ATTR_IDX_MASK) <<
						XLAT_TESTS_ATTR_IDX_SHIFT);
		upper_attrs = 0ULL;
		break;
	case MT_MEMORY:
		lower_attrs =
			((XLAT_TESTS_ATTR_IWBWA_OWBWA_NTR_IDX &
					XLAT_TESTS_ATTR_IDX_MASK) <<
						XLAT_TESTS_ATTR_IDX_SHIFT);
		upper_attrs = 0ULL;
		break;
	default:
		return -EINVAL;
	}

	/* Set AF */
	lower_attrs |= ((XLAT_TESTS_ATTR_AF_MASK) << (XLAT_TESTS_ATTR_AF_SHIFT));

	/* Set the UXN flag */
	upper_attrs |=
		((XLAT_TESTS_EXECUTE_NEVER & XLAT_TESTS_ATTR_UXN_MASK) <<
		 (XLAT_TESTS_ATTR_UXN_SHIFT));

	if (MT_PAS(mmap_attrs) == MT_NS) {
		lower_attrs |=
			((XLAT_TESTS_NON_SECURE & XLAT_TESTS_ATTR_NS_MASK) <<
			 (XLAT_TESTS_ATTR_NS_SHIFT));
	}

	if (mmap_attrs & MT_RW) {
		lower_attrs |=
			((XLAT_TESTS_RW_ACCESS & XLAT_TESTS_ATTR_AP_MASK) <<
			 (XLAT_TESTS_ATTR_AP_SHIFT));
	} else {
		lower_attrs |=
			((XLAT_TESTS_RO_ACCESS & XLAT_TESTS_ATTR_AP_MASK) <<
			 (XLAT_TESTS_ATTR_AP_SHIFT));
	}

	if (mmap_attrs & MT_EXECUTE_NEVER) {
		upper_attrs |=
			((XLAT_TESTS_EXECUTE_NEVER & XLAT_TESTS_ATTR_PXN_MASK) <<
			 (XLAT_TESTS_ATTR_PXN_SHIFT));
	}

	if (mem_type == MT_DEVICE) {
		*attrs = XLAT_TESTS_UPPER_ATTRS(upper_attrs)
					| XLAT_TESTS_LOWER_ATTRS(lower_attrs);
		return 0;
	}

	sh_attr = MT_SHAREABILITY(mmap_attrs);
	switch (sh_attr) {
	case MT_SHAREABILITY_ISH:
		lower_attrs |=
			((XLAT_TESTS_SHAREABILITY_ISH & XLAT_TESTS_ATTR_SH_MASK) <<
						XLAT_TESTS_ATTR_SH_SHIFT);
		break;
	case MT_SHAREABILITY_OSH:
		lower_attrs |=
			((XLAT_TESTS_SHAREABILITY_OSH & XLAT_TESTS_ATTR_SH_MASK) <<
						XLAT_TESTS_ATTR_SH_SHIFT);
		break;
	case MT_SHAREABILITY_NSH:
		lower_attrs |=
			((XLAT_TESTS_SHAREABILITY_NSH & XLAT_TESTS_ATTR_SH_MASK) <<
						XLAT_TESTS_ATTR_SH_SHIFT);
		break;
	}

	*attrs = XLAT_TESTS_UPPER_ATTRS(upper_attrs)
				| XLAT_TESTS_LOWER_ATTRS(lower_attrs);
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
