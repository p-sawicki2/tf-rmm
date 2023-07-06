/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

/*
 *****************************************
 * This header is only for CBMC analysis *
 *****************************************
 */

#ifndef SIMD_DEFS_H
#define SIMD_DEFS_H

#include <utils_def.h>

/* Size of one FPU vector register in bytes */
#define FPU_VEC_REG_SIZE	8
#define FPU_VEC_REG_NUM		1
#define FPU_REGS_SIZE		(FPU_VEC_REG_SIZE * FPU_VEC_REG_NUM)

#define SVE_Z_REGS_SIZE(vq)	U(8)
#define SVE_P_REGS_SIZE(vq)	U(8)
#define SVE_FFR_REGS_SIZE(vq)	U(8)

#endif /* SIMD_DEFS_H */
