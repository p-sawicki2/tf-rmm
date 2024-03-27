/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef SIMD_TEST_PRIVATE_H
#define SIMD_TEST_PRIVATE_H

/*
 * Resets the values of the static global variables g_simd_cfg, g_simd_init_done
 * and g_simd_state_saved[].
 *
 * This should only be called during unit tests, to provide a clean state for
 * each test.
 */
void simd_reset(void);

#endif
