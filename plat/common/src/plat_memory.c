/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors
 */

#include <arch_helpers.h>
#include <assert.h>
#include <plat_common.h>

static struct plat_dram_layout dram;

void plat_set_dram_layout(struct ns_dram_info *plat_dram)
{
    struct ns_dram_bank *bank_ptr;

    /* Number of banks */
    dram.num_banks = plat_dram->num_banks;
    assert(dram.num_banks <= RMM_MAX_DRAM_NUM_BANKS);

    /* Pointer to dram_bank[] array */
    bank_ptr = plat_dram->banks;

    dram.num_granules = 0;

    for (unsigned long i = 0UL; i < dram.num_banks; i++) {
        uintptr_t start = bank_ptr->base;
        uint64_t size = bank_ptr->size;
        uintptr_t end = start + size - 1UL;

        /* Total number of granules */
        dram.num_granules += (size / GRANULE_SIZE);

        dram.bank[i].start_addr = start;
        dram.bank[i].end_addr = end;

        bank_ptr++;
    }

    flush_dcache_range((uintptr_t)&dram, sizeof(&dram));
}

struct plat_dram_layout *plat_get_dram_layout(void)
{
    return &dram;
}