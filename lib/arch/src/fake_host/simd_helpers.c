/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <host_utils.h>
#include <simd.h>
#include <stdlib.h>
#include <string.h>

/*
 * Save current FPU Q registers to memory pointed by `regs`.
 */
void fpu_save_registers(struct fpu_regs *regs)
{
	for (unsigned int i = 0U; i < FPU_VEC_REG_NUM; i++) {
		simd_vreg val = host_read_simd_vreg(FPU, i);

		(void)memcpy(&regs->q[(size_t)i * FPU_VEC_REG_SIZE],
			     &val.q,
			     FPU_VEC_REG_SIZE);
	}
}

/*
 * Restore FPU context from memory pointed by `regs` to FPU Q registers.
 */
void fpu_restore_registers(struct fpu_regs *regs)
{
	for (unsigned int i = 0U; i < FPU_VEC_REG_NUM; i++) {
		simd_vreg val;

		(void)memcpy(&val.q,
			     &regs->q[(size_t)i * FPU_VEC_REG_SIZE],
			     FPU_VEC_REG_SIZE);

		host_write_simd_vreg(FPU, i, val);
	}
}

uint32_t sve_rdvl(void)
{
	return 0U;
}

void sve_save_vector_registers(struct sve_regs *regs, bool save_ffr)
{
	(void)regs;
	(void)save_ffr;
}

void sve_restore_vector_registers(struct sve_regs *regs, bool restore_ffr)
{
	(void)regs;
	(void)restore_ffr;
}

void sve_clear_p_ffr_registers(void)
{
}
