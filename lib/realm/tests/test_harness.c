/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <realm_test_utils.h>

/*
 * Maps addr to the requested slot buffer and returns a pointer to the
 * VA as seen by the fake_host architecture, which in this case corresponds
 * to the same 'addr' passed as granule PA.
 *
 * This callback is needed in order to test APIs such as ns_buffer_read() and
 * ns_buffer_write(), as these APIs use the VA returned by granule_map() to
 * perform read/write operations and for the fake_host architecture this VA
 * corresponds to the same PA used for the granule (there is no concept of
 * VA for fake_host)
 */
void *test_buffer_map_host_va(enum buffer_slot slot, unsigned long addr)
{
	uintptr_t va = (uintptr_t)buffer_map_internal(slot, addr);

	if ((void *)va == NULL) {
		return NULL;
	}

	/*
	 * We could have just returned 'addr' here, but instead, perform a
	 * table walk to get the PA mapped to 'slot'. If everything went
	 * well, it should return the same address as 'addr'. This will
	 * help validate that the translation context was properly managed
	 * for those slot types that cannot be mapped directly through
	 * granule_map() (e.g SLOT_NS)
	 */
	return(void *)realm_test_util_slot_to_pa(slot);
}

/*
 * Receives a VA as per the fake_host architecture corresponding
 * to a slot buffer and unmap the granule mapped to it.
 */
void test_buffer_unmap_host_va(void *buf)
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
 * Receives a VA as per aarch64 VMSA corresponding to a slot buffer
 * and unmap the granule mapped to it.
 */
void test_buffer_unmap_aarch64_vmsa(void *buf)
{
	buffer_unmap_internal(buf);
}
