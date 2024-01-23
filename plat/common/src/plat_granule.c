/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors
 */

#include <assert.h>
#include <plat_common.h>

unsigned long plat_granule_addr_to_idx(unsigned long addr)
{
	struct plat_dram_layout *dram = plat_get_dram_layout();
	unsigned long idx = UINT64_MAX, prev_idx = 0;

	if ((dram == NULL) || (dram->num_granules == 0) ||
		(!GRANULE_ALIGNED(addr))) {
		return idx;
	}

	for (unsigned int i = 0; i < dram->num_banks; i++) {
		/* Check if addr falls in [start - end] of this bank */
		if ((addr >= dram->bank[i].start_addr) &&
			(addr <= dram->bank[i].end_addr)) {
			idx = prev_idx + ((addr - dram->bank[i].start_addr) /
				GRANULE_SIZE);
			break;
		}
		prev_idx += ((dram->bank[i].end_addr -
			dram->bank[i].start_addr + 1) / GRANULE_SIZE);
	}

	return idx;
}

unsigned long plat_granule_idx_to_addr(unsigned long idx)
{
	struct plat_dram_layout *dram = plat_get_dram_layout();
	unsigned long addr = 0, idx_start = 0, idx_end;

	assert((dram != NULL) && (idx < dram->num_granules));

	for (unsigned int i = 0; i < dram->num_banks; i++) {
		idx_end = idx_start + ((dram->bank[i].end_addr -
                                      dram->bank[i].start_addr + 1) / GRANULE_SIZE);

		/* Check if index falls in [start - end] of this bank */
		if ((idx >= idx_start) && (idx < idx_end)) {
			addr = dram->bank[i].start_addr +
				((idx - idx_start) * GRANULE_SIZE);
		}
		idx_start = idx_end;
	}

	return addr;
}
