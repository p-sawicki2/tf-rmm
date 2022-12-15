/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors
 */

#include <arch.h>
#include <asm_macros.S>
#include <pauth.h>

.globl pauth_enable_el2
.globl restore_rmm_pauth_regs
.globl save_rmm_pauth_regs
/*
 * These functions are implemented in assembly because enabling
 * pauth in C function after changing keys leads to exception which
 * is mostly the case when we enable pauth
 */

/*
 * Enable pointer authentication in EL2
 */
func pauth_enable_el2
	mrs	x0, sctlr_el2
	orr	x0, x0, #SCTLR_ELx_EnIA_BIT
	msr	sctlr_el2, x0
	isb
	ret
endfunc pauth_enable_el2

/*
 * Restore Pointer authentication keys after returning to
 * Non secure world from Realm world
 * Clobbers x1, x2, x3
 */
func restore_rmm_pauth_regs
	mrs	x3, tpidr_el2
	adrp	x1, g_rmm_pauth_apia
	lsl	x3, x3, #PAUTH_KEY_SHIFT
	add	x1, x1, :lo12:g_rmm_pauth_apia
	add	x3, x3, x1
	ldp	x1, x2, [x3]
	msr	APIAKeyLo_EL1, x1
	msr	APIAKeyHi_EL1, x2
	ret
endfunc restore_rmm_pauth_regs
