/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <buffer.h>
#include <buffer_private.h>
#include <xlat_tables.h>

/*
 * Return the PA mapped to a given slot.
 *
 * NOTE:	This API assumes a 4KB granularity and that the architecture
 *		has a VA space of 48 bits.
 */
static uintptr_t slot_to_pa(enum buffer_slot slot)
{
	struct xlat_table_entry *entry = get_cache_entry();
	uintptr_t va = slot_to_va(slot);
	uint64_t *desc_ptr = xlat_get_pte_from_table(entry, va);
	uint64_t descriptor = xlat_read_descriptor(desc_ptr);

	return (uintptr_t)(descriptor & XLAT_TTE_L3_PA_MASK);
}

/*
 * Helper function to find the slot VA to which a PA is mapped to.
 * This function is used to validate that the slot buffer library
 * mapped the given PA to the VA that would be expected by the
 * aarch64 VMSA.
 */
uintptr_t realm_test_util_get_slot_va(uintptr_t pa)
{
	for (unsigned int i = 0U; i < NR_CPU_SLOTS; i++) {
		if (pa == slot_to_pa((enum buffer_slot)i)) {
			/*
			 * Found a slot returning the same address, get
			 * the VA for that slot (the one that would be
			 * used by the aarch64 VMSA).
			 */
			return slot_to_va((enum buffer_slot)i);
		}
	}

	/* No buffer slot found */
	return (uintptr_t)NULL;
}
