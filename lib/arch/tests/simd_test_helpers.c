/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <simd_test_helpers.h>
#include <test_helpers.h>

void simd_test_helpers_init(void)
{
	test_helpers_init();
	test_helpers_rmm_start(true);
	host_util_set_cpuid(0U);
	test_helpers_expect_assert_fail(false);
}
