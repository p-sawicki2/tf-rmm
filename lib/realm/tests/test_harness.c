/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <realm_test_utils.h>

/*
 * Maps addr to the requested slot buffer and returns a pointer to the
 * fake VA for the slot (the current addr), so the host can perform R/W
 * operations on the mapped granule.
 */
void *test_buffer_map_ret_pa(enum buffer_slot slot, unsigned long addr)
{
	uintptr_t va = (uintptr_t)buffer_map_internal(slot, addr);

	if ((void *)va == NULL) {
		return NULL;
	}

	return(void *)addr;
}

void test_buffer_unmap_from_pa(void *buf)
{
	void *slot_va = (void *)realm_test_util_slot_va_from_pa((uintptr_t)buf);

	assert(slot_va != NULL);

	buffer_unmap_internal(slot_va);
}

/*
 * Maps addr to the request slot buffer and returns the expected VA
 * of the slot buffer as per the aarch64 architecture.
 */
void *test_buffer_map_ret_va(enum buffer_slot slot, unsigned long addr)
{
	return buffer_map_internal(slot, addr);
}

void test_buffer_unmap_from_va(void *buf)
{
	buffer_unmap_internal(buf);
}
