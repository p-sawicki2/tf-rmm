/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <errno.h>
#include <stdbool.h>
#include <stdint.h>
#include <utils_def.h>
#include <xlat_contexts.h>
#include <xlat_defs.h>
#include <xlat_tables.h>
#include <xlat_tables_private.h>

int xlat_ctx_allocate_tables(uintptr_t buf, size_t buf_size,
			     unsigned int t_count, size_t va_size,
			     struct xlat_ctx_tbls *tbls_ctx)
{
	uint64_t *base_ptr;
	uint64_t (*xlat_ptr)[XLAT_TABLE_ENTRIES];

	/* Validate arguments */
	if (buf == (uintptr_t)NULL) {
		return -EFAULT;
	}

	if (t_count  == 0U) {
		return -EINVAL;
	}

	if (tbls_ctx == NULL) {
		return -EINVAL;
	}

	if (!(ALIGNED((void *)buf, (XLAT_TABLES_ALIGNMENT)))) {
		return -EFAULT;
	}

	if (buf_size < XLAT_TABLES_CTX_BUF_SIZE(t_count)) {
		return -ENOMEM;
	}

	if ((va_size % GRANULE_SIZE) != 0ULL) {
		return -EINVAL;
	}

	if (va_size > MAX_VIRT_ADDR_SPACE_SIZE) {
		return -EINVAL;
	}

	/* Base table mapped at the beginning of the buffer. */
	base_ptr = (uint64_t *)buf;

	/* Beginning of the translation tables */
	xlat_ptr = ((uint64_t(*)[XLAT_TABLE_ENTRIES])(base_ptr +
							XLAT_TABLE_ENTRIES));
	XLAT_INIT_CTX_TBLS(tbls_ctx, xlat_ptr, t_count,
			   base_ptr, XLAT_TABLE_ENTRIES);

	return 0;
}

int xlat_ctx_init_config(struct xlat_ctx_cfg *cfg,
			 xlat_addr_region_id_t region,
			 struct xlat_mmap_region *mmap,
			 unsigned int mmap_count,
			 size_t va_size)
{
	if (cfg == NULL) {
		return -EINVAL;
	}

	if (region >= VA_REGIONS) {
		return -EINVAL;
	}

	if ((va_size % GRANULE_SIZE) != 0ULL) {
		return -EINVAL;
	}

	if (va_size > MAX_VIRT_ADDR_SPACE_SIZE) {
		return -EINVAL;
	}

	cfg->max_va_size = va_size;
	cfg->base_va = 0ULL;
	cfg->mmap = mmap;
	cfg->mmap_num = mmap_count;
	cfg->max_mapped_va_offset = 0ULL;
	cfg->max_mapped_pa = 0ULL;
	cfg->base_level = (GET_XLAT_TABLE_LEVEL_BASE(va_size));
	cfg->region = region;
	cfg->initialized = false;

	return 0;
}

int xlat_ctx_register_context(struct xlat_ctx *ctx,
			      struct xlat_ctx_cfg *cfg,
			      struct xlat_ctx_tbls *tbls_ctx,
			      xlat_addr_region_id_t region,
			      struct xlat_mmap_region *mmap,
			      unsigned int mmap_count,
			      size_t va_size)
{
	int retval;

	if (XLAT_TABLES_CTX_CFG_VALID(ctx) &&
	    XLAT_TABLES_CTX_TBL_VALID(ctx)) {
		return -EALREADY;
	}

	/*
	 * Only check these arguments. The rest should be checked by
	 * xlat_context_register_va_space()
	 */
	if ((ctx == NULL) || (tbls_ctx == NULL)) {
		return -EINVAL;
	}

	retval = xlat_ctx_init_config(cfg, region, mmap,
				      mmap_count, va_size);
	if (retval == 0) {
		ctx->cfg = cfg;
		ctx->tbls = tbls_ctx;
	}

	return retval;
}

int xlat_ctx_setup_context(struct xlat_ctx *ctx,
			    struct xlat_ctx_cfg *cfg,
			    struct xlat_ctx_tbls *tbls_ctx,
			    uintptr_t *base_table,
			    unsigned int base_level_entries,
			    uintptr_t *tables_ptr,
			    unsigned int ntables)
{
	if (ctx == NULL) {
		return -EINVAL;
	}

	if (XLAT_TABLES_CTX_CFG_VALID(ctx) &&
	    XLAT_TABLES_CTX_TBL_VALID(ctx)) {
		return -EALREADY;
	}

	/* Add the configuration to the context */
	XLAT_SETUP_CTX_CFG(ctx, cfg);

	/* Initialize the tables structure */
	XLAT_INIT_CTX_TBLS(tbls_ctx,
			   (uint64_t(*)[XLAT_TABLE_ENTRIES])tables_ptr,
			   ntables, (uintptr_t *)base_table,
			   base_level_entries);

	/* Add the tables to the context */
	XLAT_SETUP_CTX_TBLS(ctx, tbls_ctx);

	return 0;
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
