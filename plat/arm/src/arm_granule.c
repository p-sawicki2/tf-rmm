/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <arm_dram.h>
#include <platform_api.h>
#include <utils_def.h>

static uint64_t prev_banks_size[RMM_MAX_NUM_DRAM_BANKS];
static struct arm_dram_layout arm_dram;

struct arm_dram_layout *arm_get_dram_layout(void)
{
	return &arm_dram;
}

/**
 * When translating an address to granule index, or vice-versa, we need to know
 * the total size of the previous DRAM banks combined. This function is called
 * once during RMM setup to cache the size of all the previous dram banks for
 * each bank index. i.e: prev_banks_size[n] = bank_0 + ... bank_{n-1}
 */
void plat_granule_cache_size (void)
{
	struct arm_dram_layout *dram = arm_get_dram_layout ();

	prev_banks_size[0] = 0UL;
	for (unsigned int i = 1U; i < RMM_MAX_NUM_DRAM_BANKS; i++) {
		prev_banks_size[i] = prev_banks_size[i-1U] + (dram->bank[i-1U].end_addr -
			dram->bank[i-1U].start_addr + 1UL);
	}
}

unsigned long plat_granule_addr_to_idx(unsigned long addr)
{
	struct arm_dram_layout *dram = arm_get_dram_layout ();
	unsigned long i, r, l = 0UL, idx = UINT64_MAX;

	if ((dram == NULL) || (dram->num_granules == 0UL) ||
		(!GRANULE_ALIGNED(addr))) {
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
		i = (l + r) / 2UL;
		if (addr < dram->bank[i].start_addr) {
			r = i - 1UL;
		} else if (addr > dram->bank[i].end_addr) {
			l = i + 1UL;
		} else {
			idx = (prev_banks_size[i] / GRANULE_SIZE) +
				((addr - dram->bank[i].start_addr) / GRANULE_SIZE);
			break;
		}
	}
	return idx;
}

unsigned long plat_granule_idx_to_addr(unsigned long idx)
{
	struct arm_dram_layout *dram = arm_get_dram_layout ();
	unsigned long i, r, l = 0UL, addr = 0UL, idx_start = 0UL, idx_end;

	assert((dram != NULL) && (idx < dram->num_granules));
	r = dram->num_banks - 1UL;

	/**
	 * Calculate the start and end granule index of each bank, and then
	 * check whether the given index falls within it. Again, the bank size
	 * cache, paired with a binary instead of linear search, allowing this
	 * process to be more efficient. Particularly on platforms with a large
	 * number of DRAM banks.
	 */
	while (l <= r) {
		i = (l + r) / 2UL;
		idx_start = (prev_banks_size[i] / GRANULE_SIZE);
		idx_end = idx_start + ((dram->bank[i].end_addr -
			dram->bank[i].start_addr + 1UL) / GRANULE_SIZE);

		if (idx < idx_start) {
			r = i - 1UL;
		} else if (idx > idx_end) {
			l = i + 1UL;
		} else {
			addr = dram->bank[i].start_addr + ((idx - idx_start) *
				GRANULE_SIZE);
			break;
		}
	}
	return addr;
}
