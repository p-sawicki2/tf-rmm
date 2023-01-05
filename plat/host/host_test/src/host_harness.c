/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */


#include <buffer.h>
#include <host_harness.h>
#include <test_helpers.h>
#include <test_private.h>

/*
 * Below are the definitions for callbacks for functions to be defined
 * by the tests which allow them to implement specific host harness APIs.
 * Each callback is identified by an unique ID, defined in test_helpers.h
 *
 * test_helpers.h defines the API to register such callbacks at run time.
 */

/*
 * Callback ID: CB_BUFFER_MAP
 *
 * Map a given granule address to a specific slot buffer
 * Args
 *	slot - Slot buffer type where to map to
 *	addr - Granule address to map
 * Return
 *	The VA (or platform equivalent) where the granule was mapped to
 */

typedef void*(*cb_buffer_map)(enum buffer_slot slot, unsigned long addr);

/*
 * Callback ID: CB_BUFFER_UNMAP
 *
 * Unmap a given granule from its corresponding slot buffer given the
 * mapped granule address.
 */
typedef void(*cb_buffer_unmap)(void *buf);

/*
 * Harness corresponding to CB_BUFFER_MAP.
 * This harness searches for a valid pointer to CB_BUFFER_MAP and calls it.
 * If there is no valid pointer, the default behavior is to return addr
 */
void *host_buffer_arch_map(enum buffer_slot slot, unsigned long addr)
{
	cb_buffer_map cb = (cb_buffer_map)get_cb(CB_BUFFER_MAP);

	return (cb == NULL) ? (void *)addr : cb(slot, addr);
}

/*
 * Harness corresponding to CB_BUFFER_UNMAP.
 * This harness searches for a valid pointer to CB_BUFFER_UNMAP and calls it.
 * If there is no valid pointer, the default behavior is to do nothing.
 */
void host_buffer_arch_unmap(void *buf)
{
	cb_buffer_unmap cb = (cb_buffer_unmap)get_cb(CB_BUFFER_UNMAP);

	if (cb != NULL) {
		cb(buf);
	}
}
