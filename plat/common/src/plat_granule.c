/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <plat_common.h>

unsigned long plat_granule_addr_to_idx(unsigned long addr)
{
	struct plat_dram_layout *dram = plat_get_dram_layout();
	unsigned long idx = UINT64_MAX, prev_idx = 0;
	unsigned long num;

	if ((NULL == dram) ||
	    (0 == dram->num_granules) ||
	    !GRANULE_ALIGNED(addr)) {
		return idx;
	}

	for (num = 0; num < dram->num_banks; num++) {

		/* Check if addr falls in [start - end] of thsi bank */
		if ((addr >= dram->bank[num].start_addr) &&
		    (addr <= dram->bank[num].end_addr)) {
			idx = prev_idx + ((addr - dram->bank[num].start_addr) /
					GRANULE_SIZE);
			break;
		}

		prev_idx += ((dram->bank[num].end_addr -
			       dram->bank[num].start_addr + 1) / GRANULE_SIZE);
	}

	return idx;
}

unsigned long plat_granule_idx_to_addr(unsigned long idx)
{
	struct plat_dram_layout *dram = plat_get_dram_layout();
	unsigned long idx_start = 0, idx_end;
	unsigned long num, addr = 0;

	assert((dram != NULL) && (idx < dram->num_granules));

	for (num = 0; num < dram->num_banks; num++) {

		idx_end = idx_start + ((dram->bank[num].end_addr -
			       dram->bank[num].start_addr + 1) / GRANULE_SIZE);

		/* Check if index falls in [start - end] of this bank */
		if ((idx >= idx_start) && (idx < idx_end)) {
			addr = dram->bank[num].start_addr + ((idx - idx_start) *
					GRANULE_SIZE);
			break;
		}
		idx_start = idx_end;
	}

	return addr;
}