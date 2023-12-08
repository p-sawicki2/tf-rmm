/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef SIMD_TEST_HELPERS_H
#define SIMD_TEST_HELPERS_H

#include <host_utils.h>
#include <simd.h>
#include <stdlib.h>
#include <test_helpers.h>

/*
 * Generate a random vector for a SIMD vreg.
 */
simd_vreg simd_test_helpers_get_rand_vector(void);

/*
 * Force g_simd_state_saved[my_cpuid()] to be set to a specified value. If it is
 * not already set to this value, simd_context_switch() will be called with the
 * correct parameters to set it to this value.
 *
 * This helper should be called at the start of a test, prior to the setting of
 * any SIMD registers, to avoid these registers being saved or restored before
 * the testing occurs.
 *
 * Arguments:
 *      - state: The value that g_simd_state_saved[my_cpuid()] should be set to.
 */
void simd_test_helpers_set_state_saved(bool state);

#endif
