/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <plat_common.h>

unsigned long plat_granule_addr_to_idx(unsigned long addr)
{
    struct plat_dram_layout *dram = plat_get_dram_layout();

    if (!GRANULE_ALIGNED(addr)) {
        return UINT64_MAX;
    }

    if ((addr >= dram->bank[0].start_addr) &&
	    (addr <= dram->bank[0].end_addr)) {
		return (addr - dram->bank[0].start_addr) / GRANULE_SIZE;
	}

	if ((dram->bank[1].start_addr != 0UL) &&
	    (addr >= dram->bank[1].start_addr) &&
	    (addr <= dram->bank[1].end_addr)) {
		return ((addr - dram->bank[1].start_addr) /
			GRANULE_SIZE) + dram->idx_bank_1;
	}

	return UINT64_MAX;
}

unsigned long plat_granule_idx_to_addr(unsigned long idx)
{
	struct plat_dram_layout *dram = plat_get_dram_layout();

	assert(idx < dram->num_granules);

	if (idx < dram->idx_bank_1) {
		return dram->bank[0].start_addr + (idx * GRANULE_SIZE);
	}

	return dram->bank[1].start_addr +
			((idx - dram->idx_bank_1) * GRANULE_SIZE);
}