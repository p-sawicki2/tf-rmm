/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch_helpers.h>
#include <assert.h>
#include <arm_dram.h>
#include <rmm_el3_ifc.h>

#include <debug.h>

void arm_set_dram_layout(struct ns_dram_info *plat_dram)
{
	struct ns_dram_bank *bank_ptr;
	struct arm_dram_layout *dram_ptr = arm_get_dram_layout();

	/* Number of banks */
	dram_ptr->num_banks = plat_dram->num_banks;
	assert(dram_ptr->num_banks <= RMM_MAX_NUM_DRAM_BANKS);

	/* Pointer to dram_bank[] array */
	bank_ptr = plat_dram->banks;

	dram_ptr->num_granules = 0;

	for (unsigned long i = 0UL; i < dram_ptr->num_banks; i++) {
		uintptr_t start = bank_ptr->base;
		uint64_t size = bank_ptr->size;
		uintptr_t end = start + size - 1UL;

		/* Total number of granules */
		dram_ptr->num_granules += (size / GRANULE_SIZE);

		dram_ptr->bank[i].end_addr = end;
		dram_ptr->bank[i].start_addr = start;

		bank_ptr++;
	}

	inv_dcache_range((uintptr_t)dram_ptr, sizeof(struct arm_dram_layout));
}
