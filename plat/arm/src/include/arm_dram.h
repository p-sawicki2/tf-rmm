/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef ARM_DRAM_H
#define ARM_DRAM_H

#include <rmm_el3_ifc.h>
#include <stddef.h>
#include <stdint.h>

/* Arm runtime structures */
struct arm_dram_bank {
	uint64_t base;				/* bank base address */
	uint64_t size;				/* size of this bank */
	uint64_t cumulative_size;	/* combined size of all previous banks */
};

struct arm_dram_layout {
	unsigned long num_granules;	/* number of granules */
	unsigned long num_banks;	/* number of dram banks */
	struct arm_dram_bank bank[RMM_MAX_NUM_DRAM_BANKS];
};

void arm_set_dram_layout(struct ns_dram_info *plat_dram);
struct arm_dram_layout *arm_get_dram_layout(void);

#endif /* ARM_DRAM_H */
