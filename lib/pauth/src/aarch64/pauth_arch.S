/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors
 */

#include <arch.h>
#include <asm_macros.S>

.globl pauth_enable_el2
.globl pauth_init_key

/* These functions are implemented in assembly because enabling
 * pauth in C function after changing keys leads to exception which
 * is mostly the case when we enable pauth
 */

/*
 * Program APIAKey_EL1 and enable Pointer Authentication
 * for Instruction Addresses in EL2
 */
func pauth_init_key

	stp     x29, x30, [sp, #-16]!

	/* Initialize platform key */
	bl	plat_init_apkey

	/* Enable pointer authentication */
	mrs	x0, sctlr_el2
	orr	x0, x0, #SCTLR_ELx_EnIA
	msr	sctlr_el2, x0
	isb

	ldp	x29, x30, [sp], #16
	ret
endfunc pauth_init_key

/*
 * Enable pointer authentication in EL2
 */
func pauth_enable_el2
	mrs	x0, sctlr_el2
	orr	x0, x0, #SCTLR_ELx_EnIA
	msr	sctlr_el2, x0
	isb
	ret
endfunc pauth_enable_el2

