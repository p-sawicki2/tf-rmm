/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <tb_common.h>
#include <xlat_contexts.h>
#include <xlat_tables.h>

uint64_t *xlat_get_tte_ptr(const struct xlat_llt_info * const llt,
			   const uintptr_t va)
{
	ASSERT(false, "xlat_get_tte_ptr");
	return 0;
}

struct xlat_ctx *xlat_get_high_va_xlat_ctx(void)
{
	ASSERT(false, "xlat_get_high_va_xlat_ctx");
	return 0;
}

int xlat_get_llt_from_va(struct xlat_llt_info * const llt,
			 const struct xlat_ctx * const ctx,
			 const uintptr_t va)
{
	ASSERT(false, "xlat_get_llt_from_va");
	return 0;
}

int xlat_map_memory_page_with_attrs(const struct xlat_llt_info * const table,
				    const uintptr_t va,
				    const uintptr_t pa,
				    const uint64_t attrs)
{
	ASSERT(false, "xlat_map_memory_page_with_attrs");
	return 0;
}

int xlat_unmap_memory_page(struct xlat_llt_info * const table,
			   const uintptr_t va)
{
	ASSERT(false, "xlat_unmap_memory_page");
	return 0;
}
