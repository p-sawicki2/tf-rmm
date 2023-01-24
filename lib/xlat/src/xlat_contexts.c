/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch_helpers.h>
#include <assert.h>
#include <debug.h>
#include <errno.h>
#include <limits.h>
#include <stdbool.h>
#include <stdint.h>
#include <string.h>
#include <utils_def.h>
#include <xlat_contexts.h>
#include <xlat_defs.h>
#include <xlat_tables.h>
#include <xlat_tables_private.h>

/*
 * Function that verifies that a region can be mapped.
 * Returns:
 *        0: Success, the mapping is allowed.
 *   EINVAL: Invalid values were used as arguments.
 *   ERANGE: The memory limits were surpassed.
 *   ENOMEM: There is not enough memory in the mmap array.
 *    EPERM: Region overlaps another one in an invalid way.
 */
static int mmap_add_region_check(const struct xlat_ctx_cfg *cfg,
				 const struct xlat_mmap_region *mm)
{
	uintptr_t base_pa = mm->base_pa;
	uintptr_t base_va = mm->base_va;
	size_t size = mm->size;
	size_t granularity = mm->granularity;
	uintptr_t end_pa = base_pa + size - 1UL;
	uintptr_t end_va = base_va + size - 1UL;
	unsigned int index;

	if (!IS_PAGE_ALIGNED(base_pa) || !IS_PAGE_ALIGNED(base_va) ||
			!IS_PAGE_ALIGNED(size)) {
		return -EFAULT;
	}

	if ((granularity != XLAT_BLOCK_SIZE(1U)) &&
	    (granularity != XLAT_BLOCK_SIZE(2U)) &&
	    (granularity != XLAT_BLOCK_SIZE(3U))) {
		return -EINVAL;
	}

	/* Check for overflows */
	if ((base_pa > end_pa) || (base_va > end_va)) {
		return -ERANGE;
	}

	/*
	 * end_va is calculated as an offset with regards to the base address
	 * for the current context, so compare it against max_va_size to ensure
	 * we are within the allowed range.
	 */
	if (end_va > cfg->max_va_size) {
		return -ERANGE;
	}

	if (end_pa > xlat_arch_get_max_supported_pa()) {
		return -ERANGE;
	}

	/* Check that there is space in the ctx->mmap array */
	if (cfg->mmap[PLAT_CMN_MAX_MMAP_REGIONS - 1U].size != 0UL) {
		return -ENOMEM;
	}

	/* Check for PAs and VAs overlaps with all other regions in this context */
	index = 0U;
	while ((index < PLAT_CMN_MAX_MMAP_REGIONS) &&
	       (cfg->mmap[index].size != 0UL)) {
		uintptr_t mm_cursor_end_va = cfg->mmap[index].base_va +
					     cfg->mmap[index].size - 1UL;

		unsigned long long mm_cursor_end_pa =
				cfg->mmap[index].base_pa
				+ cfg->mmap[index].size - 1UL;

		bool separated_pa = (end_pa < cfg->mmap[index].base_pa) ||
						(base_pa > mm_cursor_end_pa);
		bool separated_va = (end_va < cfg->mmap[index].base_va) ||
						(base_va > mm_cursor_end_va);

		if (!separated_va || !separated_pa) {
			return -EPERM;
		}
		++index;
	}

	return 0;
}

/*
 * Add a memory region with defined base PA and base VA.
 *
 * This function returns 0 on success or an error code otherwise.
 */
static int add_mmap_to_ctx_cfg(struct xlat_ctx_cfg *cfg,
			       struct xlat_mmap_region *mm)
{
	unsigned int mm_last_idx = 0U;
	unsigned int mm_cursor_idx = 0U;
	uintptr_t end_pa;
	uintptr_t end_va;
	int ret;

	/* The context data cannot be initialized */
	if (cfg->initialized == true) {
		return -EINVAL;
	}

	/* Ignore empty regions */
	if (mm->size == 0UL) {
		return 0;
	}

	if (cfg->region == VA_LOW_REGION) {
		/*
		 * Initialize the base_va for the current context if not
		 * initialized yet.
		 *
		 * For the low region, the architecture mandates that
		 * base_va has to be 0.
		 *
		 * Overwriting this field should not be a problem as its value
		 * is expected to be always the same.
		 */
		cfg->base_va = 0ULL;

		if ((mm->base_va & HIGH_REGION_MASK) ||
		     ((mm->base_va + mm->size) & HIGH_REGION_MASK)) {
			ERROR("%s (%u): Base VA and address space do not match: ",
							__func__, __LINE__);
			ERROR("Base va = 0x%lx, Address space = Low region\n",
				mm->base_va);
			return -EINVAL;
		}
	} else {
		/*
		 * Initialize the base_va for the current context if not
		 * initialized yet.
		 *
		 * For the high region, the architecture mandates that
		 * base_va has to be 0xFFFF-FFFF-FFFF-FFFF minus the VA space
		 * size plus one.
		 *
		 * Overwriting this field should not be a problem as its value
		 * is expected to be always the same.
		 */
		cfg->base_va = (ULONG_MAX - cfg->max_va_size + 1ULL);

		if (mm->base_va < cfg->base_va) {
			ERROR("%s (%u): Base VA is not aligned with the high region start: ",
							__func__, __LINE__);
			ERROR("Base VA = 0x%lx, high region start VA = 0x%lx\n",
				mm->base_va, cfg->base_va);
			return -EINVAL;
		}

		/*
		 * If this context is handling the high half region of the VA,
		 * adjust the start address of this area by substracting the
		 * start address of the region as the table entries are
		 * relative to the latter. Once ttbr1_el2 is configured, the
		 * MMU will translate the addresses properly.
		 */
		mm->base_va -= cfg->base_va;
	}

	end_pa = mm->base_pa + mm->size - 1UL;
	end_va = mm->base_va + mm->size - 1UL;

	ret = mmap_add_region_check(cfg, mm);
	if (ret != 0) {
		ERROR("%s (%u): mmap_add_region_check() failed. error %d\n",
					__func__, __LINE__, ret);
		return ret;
	}

	/*
	 * Find correct place in mmap to insert new region.
	 * Overlapping is not allowed.
	 */
	while (((cfg->mmap[mm_cursor_idx].base_va) < mm->base_va)
	       && (cfg->mmap[mm_cursor_idx].size != 0UL)
	       && (mm_cursor_idx < PLAT_CMN_MAX_MMAP_REGIONS)) {
		++mm_cursor_idx;
	}

	/*
	 * Find the last entry marker in the mmap
	 */
	while ((mm_last_idx < PLAT_CMN_MAX_MMAP_REGIONS) &&
	       (cfg->mmap[mm_last_idx].size != 0UL)) {
		++mm_last_idx;
	}

	/*
	 * Check if we have enough space in the memory mapping table.
	 * This shouldn't happen as we have checked in mmap_add_region_check
	 * that there is free space.
	 */
	assert(cfg->mmap[mm_last_idx].size == 0UL);

	/*
	 * Make room for new region by moving other regions up by one place.
	 */
	(void)memmove((void *)(&cfg->mmap[mm_cursor_idx + 1U]),
		      (void *)(&cfg->mmap[mm_cursor_idx]),
		      sizeof(struct xlat_mmap_region) *
						(mm_last_idx - mm_cursor_idx));

	/* Store the memory mapping information into the context. */
	(void)memcpy((void *)(&cfg->mmap[mm_cursor_idx]), (void *)mm,
						sizeof(struct xlat_mmap_region));

	if (end_pa > cfg->max_mapped_pa) {
		cfg->max_mapped_pa = end_pa;
	}

	if (end_va > cfg->max_mapped_va_offset) {
		cfg->max_mapped_va_offset = end_va;
	}

	return 0;
}

/*
 * Add an array of memory regions with defined base PA and base VA.
 *
 * Return 0 on success or a negative error code otherwise.
 */
static int add_mmap_arr_to_ctx_cfg(struct xlat_ctx_cfg *cfg,
				   struct xlat_mmap_region *mm)
{
	struct xlat_mmap_region *mm_cursor = mm;

	while (mm_cursor->size != 0UL) {
		int retval;

		retval = add_mmap_to_ctx_cfg(cfg, mm_cursor);
		if (retval != 0) {
			/*
			 * In case of error, stop an return.
			 * Note, the context might be in an invalid
			 * state and it will need to be restarted.
			 */
			return retval;
		}
		mm_cursor++;
	}

#if LOG_LEVEL >= LOG_LEVEL_VERBOSE
	VERBOSE("Runtime mapings");
	if (cfg->region == VA_LOW_REGION) {
		VERBOSE("(Low Region):\n");
	} else {
		VERBOSE("(High Region):\n");
	}

	for (unsigned int i = 0U; i < PLAT_CMN_MAX_MMAP_REGIONS; i++) {
		if (cfg->mmap[i].size > 0) {
			VERBOSE("\tRegion: 0x%lx - 0x%lx has attributes 0x%lx\n",
				cfg->mmap[i].base_va + cfg->base_va,
				cfg->mmap[i].base_va + cfg->base_va +
							cfg->mmap[i].size - 1U,
				cfg->mmap[i].attr);
		}
	}
#endif /* LOG_LEVEL_VERBOSE */

	return 0;
}

int xlat_ctx_cfg_init(struct xlat_ctx_cfg *cfg,
		      xlat_addr_region_id_t region,
		      struct xlat_mmap_region *mm,
		      size_t va_size)
{
	int retval;

	if (cfg == NULL) {
		return -EINVAL;
	}

	if (mm == NULL) {
		return -EINVAL;
	}

	if (region >= VA_REGIONS) {
		return -EINVAL;
	}

	if ((va_size % GRANULE_SIZE) != 0ULL) {
		return -EINVAL;
	}

	if ((va_size > MAX_VIRT_ADDR_SPACE_SIZE) ||
	    (va_size < MIN_VIRT_ADDR_SPACE_SIZE)) {
		return -EINVAL;
	}

	if (cfg->initialized == true) {
		return -EINVAL;
	}

	/*
	 * Verify that the list of memory regions is not empty.
	 */
	if (mm->base_va == 0ULL) {
		return -EINVAL;
	}

	cfg->max_va_size = va_size;
	cfg->base_va = 0ULL;
	cfg->max_mapped_va_offset = 0ULL;
	cfg->max_mapped_pa = 0ULL;
	cfg->base_level = (GET_XLAT_TABLE_LEVEL_BASE(va_size));
	cfg->region = region;
	cfg->initialized = false;

	retval = add_mmap_arr_to_ctx_cfg(cfg, mm);

	if (retval != 0) {
		return retval;
	}

	cfg->initialized = true;
	flush_dcache_range((uintptr_t)cfg, sizeof(struct xlat_ctx_cfg));

	return 0;
}

int xlat_ctx_init(struct xlat_ctx *ctx,
		  struct xlat_ctx_cfg *cfg,
		  struct xlat_ctx_tbls *tbls_ctx,
		  uint64_t *tables,
		  unsigned int ntables)
{
	if (ctx == NULL) {
		return -EINVAL;
	}

	if (tbls_ctx == NULL) {
		return -EINVAL;
	}

	if (cfg == NULL) {
		return -EINVAL;
	}

	/*
	 * It is allowed to not have intermediate tables, however
	 * the base table is always mandatory.
	 */
	if (tables == NULL || ntables == 0U) {
		return -EINVAL;
	}

	/* Add the configuration to the context */
	XLAT_SETUP_CTX_CFG(ctx, cfg);

	/* Initialize the tables structure */
	XLAT_INIT_CTX_TBLS(tbls_ctx, tables, ntables);

	/* Add the tables to the context */
	XLAT_SETUP_CTX_TBLS(ctx, tbls_ctx);

	flush_dcache_range((uintptr_t)ctx, sizeof(struct xlat_ctx));
	flush_dcache_range((uintptr_t)tbls_ctx, sizeof(struct xlat_ctx_tbls));
	flush_dcache_range((uintptr_t)cfg, sizeof(struct xlat_ctx_cfg));

	return xlat_init_tables_ctx(ctx);
}

bool xlat_ctx_initialized(const struct xlat_ctx * const ctx)
{
	assert(ctx != NULL);
	return (ctx->cfg != NULL) && (ctx->tbls != NULL);
}

bool xlat_ctx_cfg_initialized(const struct xlat_ctx * const ctx)
{
	assert(ctx != NULL);
	assert(ctx->cfg != NULL);
	return ctx->cfg->initialized;
}

bool xlat_ctx_tbls_initialized(const struct xlat_ctx * const ctx)
{
	assert(ctx != NULL);
	assert(ctx->tbls != NULL);
	return ctx->tbls->initialized;
}
