/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <buffer.h>
#include <xlat_tables.h>

#define RMM_SLOT_BUF_SIZE	((NR_CPU_SLOTS) * (GRANULE_SIZE))

/*
 * All the slot buffers for a given PE must be mapped by a single translation
 * table. To maximize the chance of this, make the slot buffers to the top of
 * the VA range.
 */
#define SLOT_VIRT		((ULL(0xffffffffffffffff) - \
				 RMM_SLOT_BUF_SIZE + ULL(1)))

/* Leave some pages of gap between the slot buf and the stack */
#define CPU_STACK_GAP		(16ULL * 0x1000ULL)

#define CPU_STACK_SIZE		(RMM_NUM_PAGES_PER_STACK * GRANULE_SIZE)

#define STACK_VIRT		(SLOT_VIRT - CPU_STACK_GAP - CPU_STACK_SIZE)

/*
 * The VA space size for the high region needs to be a power of two, so round
 * STACK_VIRT up to the closest power of two.
 */
#define ROUNDED_VA_SIZE (1ULL << (64ULL - \
	__builtin_clzll((ULL(0xffffffffffffffff) - STACK_VIRT + 1) - 1)))


struct xlat_llt_info *get_cached_llt_info(void);
uintptr_t slot_to_va(enum buffer_slot slot);
