/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef SIMD_PRIVATE_H
#define SIMD_PRIVATE_H

#include <stdbool.h>
#include <stdint.h>

/* Convert SVE VL in bytes to VQ */
#define SVE_VL_TO_VQ(vl_bytes)	((((vl_bytes) << 3) / 128) - 1)

/*
 * Save current FPU registers to memory pointed by `fpu_state`. FPU trap needs
 * to be disabled before calling this function.
 */
void fpu_save_state(uint64_t fpu_state);

/*
 * Restore FPU context from memory pointed by `fpu_state` to FPU registers. FPU
 * trap needs to be disabled before calling this function.
 */
void fpu_restore_state(uint64_t fpu_state);

/*
 * Return the length of one vector register in bytes. SVE trap needs to be
 * disabled before calling this function.
 */
uint64_t sve_rdvl(void);

/*
 * Save SVE state from Z/P/FFR, ZCR_EL12, FPSR/FPCR registers to memory pointed
 * by `sve_state`. SVE trap needs to be disabled before calling this function.
 */
void sve_save_state(uint64_t sve_state, bool save_ffr);

/*
 * Restore SVE state from memory pointed by 'sve_state' to Z/P/FFR, ZCR_EL12,
 * FPSR/FPCR registers. SVE trap needs to be disabled before calling this
 * function.
 */
void sve_restore_state(uint64_t sve_state, bool restore_ffr);

#endif /* SIMD_PRIVATE_H */
