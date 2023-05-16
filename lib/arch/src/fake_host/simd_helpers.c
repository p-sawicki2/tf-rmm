/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch_helpers.h>
#include <simd_private.h>

void fpu_save_state(uint64_t fpu_state)
{
	(void)fpu_state;
}

void fpu_restore_state(uint64_t fpu_state)
{
	(void)fpu_state;
}

uint64_t sve_rdvl(void)
{
	return 0;
}

void sve_save_state(uint64_t sve_state, bool save_ffr)
{
	(void)sve_state;
	(void)save_ffr;
}

void sve_restore_state(uint64_t sve_state, bool restore_ffr)
{
	(void)sve_state;
	(void)restore_ffr;
}
