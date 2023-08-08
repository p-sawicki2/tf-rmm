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

struct xlat_llt_info *get_cached_llt_info(void);
uintptr_t slot_to_va(enum buffer_slot slot);
