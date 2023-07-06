/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef SIMD_DEFS_H
#define SIMD_DEFS_H

#include <utils_def.h>

/* Size of one FPU vector register in bytes */
#define FPU_VEC_REG_SIZE	16U
#define FPU_VEC_REG_NUM		32U
#define FPU_REGS_SIZE		(FPU_VEC_REG_SIZE * FPU_VEC_REG_NUM)

/*
 * Size of SVE Z, Predicate (P), First Fault predicate Register (FFR) registers
 * in bytes for vector length 128 bits (0 vq). P and FFR registers are 1/8 of
 * Z register.
 */
#define SVE_Z_REG_MIN_SIZE	U(16)
#define SVE_P_REG_MIN_SIZE	(SVE_Z_REG_MIN_SIZE / 8)
#define SVE_FFR_REG_MIN_SIZE	(SVE_Z_REG_MIN_SIZE / 8)

/* Number of Z, P, FFR registers */
#define SVE_Z_REG_NUM		U(32)
#define SVE_P_REG_NUM		U(16)
#define SVE_FFR_REG_NUM		U(1)

#define SVE_Z_REGS_SIZE(vq)	((vq + 1) * (SVE_Z_REG_MIN_SIZE * SVE_Z_REG_NUM))
#define SVE_P_REGS_SIZE(vq)	((vq + 1) * (SVE_P_REG_MIN_SIZE * SVE_P_REG_NUM))
#define SVE_FFR_REGS_SIZE(vq)	((vq + 1) * (SVE_FFR_REG_MIN_SIZE * \
					     SVE_FFR_REG_NUM))

#endif /* SIMD_DEFS_H */
