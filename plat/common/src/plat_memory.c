/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors
 */

#include <arch_helpers.h>
#include <assert.h>
#include <plat_common.h>

COMPILER_ASSERT(MAX_DRAM_NUM_BANKS == 2UL);

static struct plat_dram_layout dram;

void plat_set_dram_layout(struct ns_dram_info *plat_dram)
{
    uint64_t num_banks, num_granules = 0UL;
    struct ns_dram_bank *bank_ptr;

    /* Number of banks */
    num_banks = plat_dram->num_banks;
    assert(num_banks <= MAX_DRAM_NUM_BANKS);

    /* Pointer to dram_bank[] array */
    bank_ptr = plat_dram->banks;

    for (unsigned long i = 0UL; i < num_banks; i++) {
        uintptr_t start = bank_ptr->base;
        uint64_t size = bank_ptr->size;
        uintptr_t end = start + size - 1UL;

        if (i == 1UL) {
            /* Start granule index in bank 1 */
            dram.idx_bank_1 = num_granules;
        }

        /* Total number of granules */
        num_granules += (size / GRANULE_SIZE);

        dram.bank[i].start_addr = start;
        dram.bank[i].end_addr = end;

        bank_ptr++;
    }

    dram.num_granules = num_granules;
    flush_dcache_range((uintptr_t)&dram, sizeof(&dram));
}

struct plat_dram_layout *plat_get_dram_layout(void)
{
    return &dram;
}