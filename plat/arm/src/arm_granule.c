/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arm_dram.h>
#include <assert.h>
#include <platform_api.h>
#include <utils_def.h>

static struct arm_dram_layout arm_dram;

struct arm_dram_layout *arm_get_dram_layout(void)
{
	return &arm_dram;
}

unsigned long plat_granule_addr_to_idx(unsigned long addr)
{
	struct arm_dram_layout *dram = &arm_dram;
	struct arm_dram_bank *bank;
	unsigned long i, r, l = 0UL, idx = UINT64_MAX;

	if (!GRANULE_ALIGNED(addr)) {
		return idx;
	}

	r = dram->num_banks - 1UL;

	/**
	 * Use a binary search, rather than a linear one, to locate the bank
	 * which the given address falls within, then use the bank size cache
	 * to calculate the granule index. On system with a large number of
	 * non-contiguous DRAM banks this is a more efficient way of calculating
	 * the index.
	 */
	while (l <= r) {
		i = l + (r / 2UL);
		bank = &dram->bank[i];

		if (addr < bank->base) {
			r = i - 1UL;
		} else if (addr > (bank->base + bank->size)) {
			l = i + 1UL;
		} else {
			idx = (bank->cumulative_size / GRANULE_SIZE) + ((addr - bank->base) / GRANULE_SIZE);
			break;
		}
	}
	return idx;
}

unsigned long plat_granule_idx_to_addr(unsigned long idx)
{
	struct arm_dram_layout *dram = &arm_dram;
	struct arm_dram_bank *bank;
	unsigned long i, r, l = 0UL, addr = 0UL, idx_start = 0UL, idx_end;

	assert(idx < dram->num_granules);
	r = dram->num_banks - 1UL;

	/**
	 * Calculate the start and end granule index of each bank, and then
	 * check whether the given index falls within it. Again, the bank size
	 * cache, paired with a binary instead of linear search, allowing this
	 * process to be more efficient. Particularly on platforms with a large
	 * number of DRAM banks.
	 */
	while (l <= r) {
		i = l + (r / 2UL);
		bank = &dram->bank[i];

		idx_start = (bank->cumulative_size / GRANULE_SIZE);
		idx_end = idx_start + ((bank->size + 1UL) / GRANULE_SIZE);

		if (idx < idx_start) {
			r = i - 1UL;
		} else if (idx > idx_end) {
			l = i + 1UL;
		} else {
			addr = bank->base + ((idx - idx_start) * GRANULE_SIZE);
			break;
		}
	}
	return addr;
}
