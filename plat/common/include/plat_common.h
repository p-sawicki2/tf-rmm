/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef PLAT_COMMON_H
#define PLAT_COMMON_H

#include <stdint.h>
#include <rmm_el3_ifc.h>

/* Plat runtime structures */
struct plat_dram_bank {
	uintptr_t start_addr;		/* start address */
	uintptr_t end_addr;		/* end address */
};

struct plat_dram_layout {
	unsigned long num_granules;	/* number of granules */
	unsigned long num_banks;	/* number of banks */
	struct plat_dram_bank bank[RMM_MAX_DRAM_NUM_BANKS];
};

void plat_set_dram_layout(struct ns_dram_info *plat_dram);
struct plat_dram_layout *plat_get_dram_layout(void);

/* Forward declaration */
struct xlat_mmap_region;

int plat_cmn_setup(unsigned long x0, unsigned long x1,
		   unsigned long x2, unsigned long x3,
		   struct xlat_mmap_region *plat_regions,
		   unsigned int nregions);
int plat_cmn_warmboot_setup(void);

#endif /* PLAT_COMMON_H */
