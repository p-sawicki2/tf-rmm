/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <simd_test_helpers.h>

simd_vreg simd_test_helpers_get_rand_vector(void)
{
	simd_vreg rand_reg;

	for (int i = 0; i < FPU_VEC_REG_SIZE; i++) {
		rand_reg.q[i] = rand() % (UINT8_MAX + 1);
	}

	return rand_reg;
}
