/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef TEST_PRIVATE_H
#define TEST_PRIVATE_H

#include <test_helpers.h>

/*
 * Return a callback for a give callback ID
 */
uintptr_t get_cb(enum cb_ids id);

/*
 * Save the sysreg state across all PEs in the system along with registered
 * callbacks. This function must only be used during RMM runtime bring-up,
 * at a point wherein the system is initialized properly and can restored
 * for later test iterations.
 */
void host_util_take_sysreg_snapshot(void);

/*
 * Restore a saved sysreg state and associated callbacks. The state is already
 * assumed to be saved prior to calling this API.
 */
void host_util_restore_sysreg_snapshot(void);

#endif /* TEST_PRIVATE_H */
