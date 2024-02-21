/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef SIMD_TEST_PRIVATE_H
#define SIMD_TEST_PRIVATE_H

/*
 * Sets the static global variable g_simd_init_done in simd.c to a specified
 * value. This should only be called during unit tests.
 */
void set_g_simd_init_done(bool val);

/*
 * Sets all fields in the static global variable g_simd_cfg in simd.c to zero.
 * This should only be called during unit tests.
 */
void reset_g_simd_cfg(void);

#endif
