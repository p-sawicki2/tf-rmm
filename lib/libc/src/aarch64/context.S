/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <asm_macros.S>
#include <context.h>

	.global swapcontext
	.global startlinkcontext

/* Load the context and jump to the PC */
func setcontext
	ldp	x19, x20, [x0, #CTX_OFFSET_X19]
	ldp	x21, x22, [x0, #CTX_OFFSET_X21]
	ldp	x23, x24, [x0, #CTX_OFFSET_X23]
	ldp	x25, x26, [x0, #CTX_OFFSET_X25]
	ldp	x27, x28, [x0, #CTX_OFFSET_X27]
	ldp	x29, x30, [x0, #CTX_OFFSET_X29]

	/* Load SP and PC. Load PC in x16 to avoid Branch Target exception */
	ldp	x1, x16, [x0, #CTX_OFFSET_SP]
	mov	sp, x1

	/* Load the arg0 in x0 and x1 holds the LR */
	ldp	x0, x1, [x0, #CTX_OFFSET_X0]

	/* Switch to new PC */
	br	x16

	/* todo: call assert */
endfunc setcontext

/*
 * int swapcontext(context_t *save, const context_t *restore)
 */
func swapcontext
	str	x30, [x0, #CTX_OFFSET_X1]
	adr	x30, 1f

	/* Save the current C context to the context pointed by 'save' */
	stp	x19, x20, [x0, #CTX_OFFSET_X19]
	stp	x21, x22, [x0, #CTX_OFFSET_X21]
	stp	x23, x24, [x0, #CTX_OFFSET_X23]
	stp	x25, x26, [x0, #CTX_OFFSET_X25]
	stp	x27, x28, [x0, #CTX_OFFSET_X27]
	stp	x29, x30, [x0, #CTX_OFFSET_X29]

	/* Save SP and PC */
	mov	x2, sp
	stp	x2, x30, [x0, #CTX_OFFSET_SP]

	/* Set return value of swapcontext */
	mov	x2, 0
	str	x2, [x0, #CTX_OFFSET_X0]

	/* Restore the context pointer by 'restore' */
	mov	x0, x1
	bl	setcontext
1:
	/* BTI_J 'hint #36' */
	bti	j
	mov	x30, x1
	ret
endfunc swapcontext

/*
 * Called when context passed to makecontext returns. Switches to the linked
 * context.
 */
func startlinkcontext
	mov	x0, x19
	b	setcontext

	/* todo: call assert */
endfunc startlinkcontext
