/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef SIMD_PRIVATE_H
#define SIMD_PRIVATE_H

#include <stdbool.h>
#include <stdint.h>

#define _VL_TO_VQ(bytes)		((((bytes) << 3) / 128) - 1)

/* Convert SVE VL in bytes to VQ */
#define SVE_VL_TO_VQ(vl_bytes)		(_VL_TO_VQ(vl_bytes))

/* Convert SME SVL in bytes to SVQ */
#define SME_SVL_TO_SVQ(svl_bytes)	(_VL_TO_VQ(svl_bytes))

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

/* Returns 'true' when CPU in Streaming SVE mode, else 'false' */
static inline bool is_sme_sm(void)
{
	return ((read_svcr() & SVCR_SM_BIT) != 0U);
}

/* Enter Streaming SVE mode */
static inline void sme_smstart(void)
{
	write_svcr(read_svcr() | SVCR_SM_BIT);
	isb();
}

/* Exit Streaming SVE mode */
static inline void sme_smstop(void)
{
	write_svcr(read_svcr() & ~SVCR_SM_BIT);
	isb();
}

/* Returns 'true' when FEAT_SME_FA64 is enabled at the current exception level */
static inline bool sme_feat_fa64_enabled(void)
{
	return ((read_smcr_el2() & SMCR_EL2_FA64_BIT) != 0U);
}

#endif /* SIMD_PRIVATE_H */
