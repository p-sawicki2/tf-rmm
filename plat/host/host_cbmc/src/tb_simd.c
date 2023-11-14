/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <simd.h>
#include <tb_common.h>

int simd_get_cpu_config(struct simd_config *simd_cfg)
{
	*simd_cfg = nondet_simd_config();
	return (int)nondet_bool();
}
