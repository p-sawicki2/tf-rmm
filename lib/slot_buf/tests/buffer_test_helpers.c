/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <buffer.h>
#include <buffer_private.h>
#include <stddef.h>
#include <test_helpers.h>
#include <xlat_tables.h>

uintptr_t buffer_test_helpers_slot_to_pa(enum buffer_slot slot)
{
	struct xlat_llt_info *entry = get_cached_llt_info();
	uintptr_t va = slot_to_va(slot);
	uint64_t *desc_ptr = xlat_get_tte_ptr(entry, va);
	uint64_t descriptor = xlat_read_tte(desc_ptr);

	return (uintptr_t)xlat_get_oa_from_tte(descriptor);
}

/*
 * Helper function to find the slot VA to which a PA is mapped to.
 * This function is used to validate that the slot buffer library
 * mapped the given PA to the VA that would be expected by the
 * aarch64 VMSA.
 */
uintptr_t buffer_test_helpers_slot_va_from_pa(uintptr_t pa)
{
	for (unsigned int i = 0U; i < (unsigned int)NR_CPU_SLOTS; i++) {
		if (pa == buffer_test_helpers_slot_to_pa((enum buffer_slot)i)) {
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

/*
 * Maps addr to the requested slot buffer and returns a pointer which can be
 * accessed for read or write by the tests. The callback maps the `addr` as
 * per aarch64 VMSA and walks the xlat tables to retrieve the original
 * `addr` thus verifying that the `addr` was mapped correctly in the tables.
 */
void *buffer_test_cb_map_access(unsigned int slot, unsigned long addr)
{
	void *va = buffer_map_internal((enum buffer_slot)slot, addr);

	if (va == NULL) {
		return NULL;
	}

	/*
	 * Perform a table walk to get the PA mapped to `slot`.
	 * If everything went well it should return the same address as `addr`.
	 */
	return (void *)buffer_test_helpers_slot_to_pa((enum buffer_slot)slot);
}

/*
 * Receives an accessible `buf` address corresponding to a mapped
 * slot buffer and unmaps the granule mapped to it.
 */
void buffer_test_cb_unmap_access(void *buf)
{
	void *slot_va =
		(void *)buffer_test_helpers_slot_va_from_pa((uintptr_t)buf);

	assert(slot_va != NULL);

	buffer_unmap_internal(slot_va);
}

/*
 * Maps addr to the requested slot buffer and returns a mapped VA
 * corresponding to the slot buffer as per aarch64 VMSA.
 */
void *buffer_test_cb_map_aarch64_vmsa(unsigned int slot, unsigned long addr)
{
	return buffer_map_internal((enum buffer_slot)slot, addr);
}

/*
 * Receives an aarch64 VMSA `buf` address corresponding to a mapped
 * slot buffer and unmaps the granule mapped to it.
 */
void buffer_test_cb_unmap_aarch64_vmsa(void *buf)
{
	buffer_unmap_internal(buf);
}
