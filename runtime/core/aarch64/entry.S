/*
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <asm_macros.S>
#include <smc.h>

.globl rmm_handler

func rmm_handler
	/*
	 * Save Link Register and X4, as per SMCCC v1.2 its value
	 * must be preserved unless it contains result, as specified
	 * in the function definition.
	 */
	stp	x4, lr, [sp, #-16]!

	/*
	 * Save the value of SP_EL0 as it is going to contain the exception
	 * handler stack address while RMM is running
	 */
	mrs	x4, sp_el0
	stp 	x4, xzr, [sp, #-16]!

	/* Load the handler stack bottom to SP_EL0 */
	adrp	x4, cpu_handler_stack_bottom_va
	ldr	x4, [x4, :lo12:cpu_handler_stack_bottom_va]
	msr	sp_el0, x4

	/* restore x4 */
	ldr	x4, [sp, #16]

	/*
	 * Zero the space for X0-X3 in the smc_result structure
	 * and pass its address as the last argument.
	 */
	stp	xzr, xzr, [sp, #-16]!
	stp	xzr, xzr, [sp, #-16]!
	mov	x7, sp

	bl	handle_ns_smc

	/*
	 * Copy command output values back to caller. Since this is
	 * done through SMC, X0 is used as the FID, and X1-X5 contain
	 * the values of X0-X4 copied from the smc_result structure.
	 */
	ldr	x0, =SMC_RMM_REQ_COMPLETE
	ldp	x1, x2, [sp], #16
	ldp	x3, x4, [sp], #16

	/*
	 * restore the value of SP_EL0
	 */

	ldr 	x5, [sp]
	msr	sp_el0, x5
	add	sp, sp, #16

	ldp	x5, lr, [sp], #16

	smc	#0

	/* Continue the rmm handling loop */
	b	rmm_handler
endfunc rmm_handler
