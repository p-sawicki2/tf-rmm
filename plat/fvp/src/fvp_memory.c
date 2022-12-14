/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <debug.h>
#include <fvp_dram.h>
#include <rmm_el3_ifc.h>
#include <xlat_defs.h>

COMPILER_ASSERT(MAX_DRAM_BANKS_NUM == 2);

void fvp_set_dram_layout(struct dram_info *plat_dram)
{
	uint64_t banks_num, check_sum, dram_size = 0UL;
	struct dram_bank *bank_ptr;
	struct fvp_dram_layout *fvp_dram = fvp_get_dram_layout();

	/* Validate DRAM info pointers */
	if ((plat_dram == NULL) || (plat_dram->dram_data == NULL)) {
		report_fail_to_el3(E_RMM_BOOT_MANIFEST_DATA_ERROR);
	}

	/* Pointer to dram_bank[] array */
	bank_ptr = plat_dram->dram_data;

	/* Number of banks */
	banks_num = plat_dram->banks_num;
	if ((banks_num == 0UL) || (banks_num > MAX_DRAM_BANKS_NUM)) {
		report_fail_to_el3(E_RMM_BOOT_MANIFEST_DATA_ERROR);
	}

	/* Calculate check sum of dram_info structure */
	check_sum = banks_num + (uint64_t)bank_ptr + plat_dram->check_sum;

	for (unsigned long i = 0UL; i < banks_num; i++) {
		uintptr_t start = bank_ptr->base;
		uint64_t size = bank_ptr->size;
		uintptr_t end;

		/* Base address, size of bank and alignments */
		if ((start == 0UL) || (size == 0UL) ||
		    (((start | size) & PAGE_SIZE_MASK) != 0UL)) {
			report_fail_to_el3(E_RMM_BOOT_MANIFEST_DATA_ERROR);
		}

		end = start + size - 1UL;

		/* Update check sum */
		check_sum += start + size;

		if (i == 1UL) {
			/* Check for overlapping */
			if (!((start > fvp_dram->fvp_bank[0].end_addr) ||
				(end < fvp_dram->fvp_bank[0].start_addr))) {
				report_fail_to_el3(E_RMM_BOOT_MANIFEST_DATA_ERROR);
			}

			/* Start granule index in bank 1 */
			fvp_dram->idx_bank_1 = dram_size / GRANULE_SIZE;
		}

		/* Total size of DRAM */
		dram_size += size;

		fvp_dram->fvp_bank[i].start_addr = start;
		fvp_dram->fvp_bank[i].end_addr = end;

		VERBOSE("DRAM%lu: 0x%lx-0x%lx\n", i,
			fvp_dram->fvp_bank[i].start_addr,
			fvp_dram->fvp_bank[i].end_addr);

		bank_ptr++;
	}

	/* Check sum must be 0 */
	if (check_sum != 0UL) {
		report_fail_to_el3(E_RMM_BOOT_MANIFEST_DATA_ERROR);
	}

	/* Check for the maximum number of granules supported */
	fvp_dram->num_granules = dram_size / GRANULE_SIZE;
	if (fvp_dram->num_granules > RMM_MAX_GRANULES) {
		report_fail_to_el3(E_RMM_BOOT_MANIFEST_DATA_ERROR);
	}

	flush_dcache_range((uintptr_t)fvp_dram, sizeof(fvp_dram));
}
