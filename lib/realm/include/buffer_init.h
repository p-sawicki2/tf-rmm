/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef BUFFER_INIT_H
#define BUFFER_INIT_H

/*
 * Initializes and enables the VMSA for the slot buffer mechanism.
 *
 * Create an empty translation context for the current PE.
 * If the context already exists (e.g. current PE was previously
 * turned on and therefore the context is already in memory),
 * nothing happens.
 */
void slot_buf_setup_xlat(void);

/*
 * Initializes the slot buffer components common to all PEs. This function
 * must only be called once during cold boot initialization.
 *
 * Returns 0 on success and a negative POSIX error code otherwise.
 */
int slot_buf_coldboot_init(void);

/*
 * Finishes initializing the slot buffer mechanism.
 * This function should be called after the MMU is enabled, during the
 * warmboot path.
 */
void slot_buf_finish_warmboot_init(void);

#endif /* BUFFER_INIT_H */
