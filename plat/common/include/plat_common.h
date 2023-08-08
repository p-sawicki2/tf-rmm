/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef PLAT_COMMON_H
#define PLAT_COMMON_H

#define CPU_STACK_SIZE		(PLAT_NUM_PAGES_PER_STACK * PAGE_SIZE)

/* Forward declaration */
struct xlat_mmap_region;

int plat_cmn_setup(unsigned long x0, unsigned long x1,
		   unsigned long x2, unsigned long x3,
		   struct xlat_mmap_region *plat_regions,
		   unsigned int nregions);
int plat_cmn_warmboot_setup(void);

/*
 * Initializes and enables the VMSA for the high va region.
 *
 * Create an empty translation context for the current PE.
 * If the context already exists (e.g. current PE was previously
 * turned on and therefore the context is already in memory),
 * nothing happens.
 */
void high_va_setup_xlat(void);

#endif /* PLAT_COMMON_H */
