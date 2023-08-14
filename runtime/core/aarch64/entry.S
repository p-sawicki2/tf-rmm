/*
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <asm_macros.S>
#include <smc.h>
#include <xlat_high_va.h>

.globl rmm_handler

func rmm_handler
	/*
	 * This is the entry point to the RMM, so currently SP points to the
	 * stack bottom. We allocate space for the `res` parameter of
	 * handle_ns_smc on the stack, and also save SP_EL0 and the link
	 * register.
	 * So the stack should look like this before calling handle_ns_smc:
	 * stack bottom ->
	 *                 Unused   <- To preserve stack alignment
	 *                 SP_EL0   <- The saved SP for EL0
	 *                 LR       <- The saved link register
	 *                 X4       <- the saved X4 register  \
	 *                 0x0                                 |
	 *                 0x0                                 +- struct smc_result res
	 *                 0x0                                 |
	 * SP           -> 0x0                                /
	 */

	/*
	 * Save Link Register and X4, as per SMCCC v1.2 its value
	 * must be preserved unless it contains result, as specified
	 * in the function definition.
	 * The same time allocate the space for SP_EL0 preserving the stack
	 * alignment.
	 */
	stp	x4, lr, [sp, #-32]!

	/*
	 * Save the value of SP_EL0 as it is going to contain the exception
	 * handler stack address while RMM is running
	 */
	mrs	x4, sp_el0
	str	x4, [sp, #16]

	/* Load the exception handler stack bottom to SP_EL0 */
	mov_imm	x4, RMM_CPU_EH_STACK_END_VA
	msr	sp_el0, x4

	/* Restore x4 */
	ldr	x4, [sp]

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
	 * Restore the value of SP_EL0
	 */
	ldr 	x5, [sp, #16]
	msr	sp_el0, x5

	/*
	 * Copy the field X4 from the result structure to X5 and restore SP to
	 * the stack bottom
	 */
	ldp	x5, lr, [sp], #32

	smc	#0

	/* Continue the rmm handling loop */
	b	rmm_handler
endfunc rmm_handler
