/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <buffer.h>
#include <buffer_private.h>
#include <realm_test_utils.h>
#include <test_harness.h>

/*
 * Maps addr to the requested slot buffer and returns a pointer to the
 * fake VA for the slot (the current addr), so the host can perform R/W
 * operations on the mapped granule.
 */
void *test_buffer_map(enum buffer_slot slot,
		      unsigned long addr, bool ns)
{
	uintptr_t va = (uintptr_t)buffer_map_internal(slot, addr, ns);

	if ((void *)va == NULL) {
		return NULL;
	}

	return(void *)addr;
}

void test_buffer_unmap(void *buf)
{
	void *slot_va = (void *)host_pa_to_slot_va((uintptr_t)buf, NULL);

	assert(slot_va != NULL);

	buffer_unmap_internal(slot_va);
}
