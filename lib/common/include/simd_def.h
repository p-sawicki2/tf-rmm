/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef SIMD_DEF_H
#define SIMD_DEF_H

#include <stdint.h>

#define FPU_Q_REG_SIZE (16U)

#define NUM_Q_REGS (32U)

/*
 * Prepare for adding SVE register emulation later
 */
enum simd_variant {
	FPU
};

/*
 * Using a union to prepare for adding SVE Z registers later
 */
typedef union {
	uint8_t q[FPU_Q_REG_SIZE];
} simd_vreg;

#endif
