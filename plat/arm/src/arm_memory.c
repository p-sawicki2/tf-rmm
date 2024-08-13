/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch_helpers.h>
#include <arm_dram.h>
#include <assert.h>
#include <rmm_el3_ifc.h>

void arm_set_dram_layout(struct ns_dram_info *plat_dram)
{
	struct ns_dram_bank *bank_ptr;
	struct arm_dram_layout *dram_ptr = arm_get_dram_layout();
	uint64_t num_banks, num_granules, cumulative_size;

	/* Number of banks */
	num_banks = plat_dram->num_banks;
	assert(num_banks <= ARM_CMN_MAX_NUM_DRAM_BANKS);

	/* Pointer to dram_bank[] array */
	bank_ptr = plat_dram->banks;

	num_granules = 0UL;
	cumulative_size = 0UL;

	for (unsigned long i = 0UL; i < num_banks; i++) {
		uint64_t base = bank_ptr->base;
		uint64_t size = bank_ptr->size;

		/* Total number of granules */
		num_granules += (size / GRANULE_SIZE);

		dram_ptr->bank[i].base = base;
		dram_ptr->bank[i].size = size;
		dram_ptr->bank[i].cumulative_size = cumulative_size;

		cumulative_size += size;
		bank_ptr++;
	}

	dram_ptr->num_banks = num_banks;
	dram_ptr->num_granules = num_granules;

	inv_dcache_range((uintptr_t)dram_ptr, sizeof(struct arm_dram_layout));
}
