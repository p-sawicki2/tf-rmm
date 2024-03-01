/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch_helpers.h>
#include <string.h>

/*******************************************************************************
 * Cache management
 ******************************************************************************/
void flush_dcache_range(uintptr_t addr, size_t size)
{
	(void)addr;
	(void)size;
}
void clean_dcache_range(uintptr_t addr, size_t size)
{
	(void)addr;
	(void)size;
}
void inv_dcache_range(uintptr_t addr, size_t size)
{
	(void)addr;
	(void)size;
}

/* Emulate DC ZVA instruction */
void dczva(uintptr_t addr)
{
	(void)memset((void *)addr, 0,
		1U << (EXTRACT(DCZID_EL0_BS, read_dczid_el0()) + 2U));
}
