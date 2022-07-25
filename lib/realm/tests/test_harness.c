/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <realm_test_utils.h>

/*
 * Maps addr to the requested slot buffer and returns a pointer which can be
 * accessed for read or write by the tests. The callback maps the `addr` as
 * per aarch64 VMSA and waslk of the xlat tables to retriveve the original
 * `addr` thus verifying that the `addr` was mapped correctly in the tables.
 */
void *test_buffer_map_access(enum buffer_slot slot, unsigned long addr)
{
	uintptr_t va = (uintptr_t)buffer_map_internal(slot, addr);

	if ((void *)va == NULL) {
		return NULL;
	}

	/*
	 * Perform a table walk to get the PA mapped to `slot`.
	 * If everything went well it should return the same address as `addr`.
	 */
	return(void *)realm_test_util_slot_to_pa(slot);
}

/*
 * Receives a VA as per the fake_host architecture corresponding
 * to a slot buffer and unmap the granule mapped to it.
 */
void test_buffer_unmap_access(void *buf)
{
	void *slot_va =
		(void *)realm_test_util_slot_va_from_pa((uintptr_t)buf);

	assert(slot_va != NULL);

	buffer_unmap_internal(slot_va);
}

/*
 * Maps addr to the request slot buffer and returns the expected VA
 * of the slot buffer as per aarch64 VMSA.
 */
void *test_buffer_map_aarch64_vmsa(enum buffer_slot slot, unsigned long addr)
{
	return buffer_map_internal(slot, addr);
}

/*
 * Unmap a buffer addr which was previously mapped using
 * test_buffer_map_access(). The addr needs to correspond to VA as per aarch64
 * VMSA, hence use the test helper to retrieve the same.
 */
void test_buffer_unmap_aarch64_vmsa(void *buf)
{
	buffer_unmap_internal(buf);
}
