/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <simd.h>
#include <simd_callbacks.h>
#include <string.h>

uintptr_t callbacks[SIMD_CB_IDS];

static uintptr_t get_callback(enum simd_cb_ids id)
{
	return callbacks[id];
}

void fpu_save_registers(struct fpu_regs *regs)
{
	cb_fpu_save_restore cb =
			       (cb_fpu_save_restore)get_callback(FPU_SAVE_REGS);

	if (cb != NULL) {
		cb(regs);
	}
}

void fpu_restore_registers(struct fpu_regs *regs)
{
	cb_fpu_save_restore cb =
			    (cb_fpu_save_restore)get_callback(FPU_RESTORE_REGS);

	if (cb != NULL) {
		cb(regs);
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

/******************************************************************
 * APIs for test callbacks
 *****************************************************************/

void simd_test_register_callback(enum simd_cb_ids id, union simd_cbs cb)
{
	assert(id <= FPU_RESTORE_REGS);
	callbacks[id] = (uintptr_t)cb.fpu_save_restore_regs;
}

void simd_test_unregister_callback(enum simd_cb_ids id)
{
	callbacks[id] = (uintptr_t)NULL;
}
