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

#endif
