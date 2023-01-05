/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef TEST_HELPERS_H
#define TEST_HELPERS_H

#include <buffer.h>

/*
 * Callback identifiers for all the possible system callbacks that can be
 * installed by the unit tests.
 */
enum cb_ids {
	CB_ID0 = 0,
	CB_BUFFER_MAP = CB_ID0,
	CB_BUFFER_UNMAP,
	CB_IDS
};

/*
 * Register a system callback to be used for testing, overwriting any existing
 * one.
 *
 * Args:
 *	- cb: Generic pointer to the callback to use
 *	- id: Unique ID for the callback
 * Return:
 *	- 0 If the callback is successfully registered
 *	- -EINVAL on an argument error
 */
int test_helpers_register_cb(uintptr_t cb, enum cb_ids id);

/*
 * Unregister a system callback for testing.
 *
 * Args:
 * 	- id: Unique ID for the callback
 * Return:
 *	- 0 If the callback is successfuly registered
 * 	- -EINVAL on an argument error
 */
int test_helpers_unregister_cb(enum cb_ids id);

/*
 * Return a random value within [min, max] range.
 */
int test_helpers_get_rand_in_range(int min, int max);

/*
 * Helper function to fully initialize RMM.
 *
 * Args
 *	secondaries - If true, support for secondary PEs is enabled.
 */
void test_helpers_rmm_start(bool secondaries);

/*
 * Helper function to get the total number of memory granules available
 * to the system.
 */
unsigned int test_helpers_get_nr_granules(void);

#endif
