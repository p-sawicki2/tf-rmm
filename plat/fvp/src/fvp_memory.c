/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <debug.h>
#include <fvp_dram.h>
#include <rmm_el3_ifc.h>

COMPILER_ASSERT(MAX_DRAM_NUM_BANKS == 2UL);

void fvp_set_dram_layout(struct dram_info *plat_dram)
{
	uint64_t num_banks, dram_size = 0UL;
	struct dram_bank *bank_ptr;
	struct fvp_dram_layout *fvp_dram = fvp_get_dram_layout();

	/* Number of banks */
	num_banks = plat_dram->num_banks;

	/* Pointer to dram_bank[] array */
	bank_ptr = plat_dram->banks;

	for (unsigned long i = 0UL; i < num_banks; i++) {
		uintptr_t start = bank_ptr->base;
		uint64_t size = bank_ptr->size;
		uintptr_t end = start + size - 1UL;

		if (i == 1UL) {
			/* Start granule index in bank 1 */
			fvp_dram->idx_bank_1 = dram_size / GRANULE_SIZE;
		}

		/* Total size of DRAM */
		dram_size += size;

		fvp_dram->fvp_bank[i].start_addr = start;
		fvp_dram->fvp_bank[i].end_addr = end;

		bank_ptr++;
	}

	/* Check for the maximum number of granules supported */
	fvp_dram->num_granules = dram_size / GRANULE_SIZE;
	if (fvp_dram->num_granules > RMM_MAX_GRANULES) {
		ERROR("Number of granules %lu exceeds maximum of %u\n",
			fvp_dram->num_granules, RMM_MAX_GRANULES);
		rmm_el3_ifc_report_fail_to_el3(E_RMM_BOOT_MANIFEST_DATA_ERROR);
	}

	flush_dcache_range((uintptr_t)fvp_dram, sizeof(fvp_dram));
}
