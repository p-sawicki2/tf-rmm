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
 * Should be called before each unit test to set up the testing environment,
 * e.g. resetting all sysregs to default values.
 */
void simd_test_helpers_init(void);

#endif
