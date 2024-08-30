/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef CONTEXT_H
#define CONTEXT_H

#define CTX_OFFSET_X0		0x0
#define CTX_OFFSET_X1		0x8
#define CTX_OFFSET_X19		0x10
#define CTX_OFFSET_X20		0x18
#define CTX_OFFSET_X21		0x20
#define CTX_OFFSET_X22		0x28
#define CTX_OFFSET_X23		0x30
#define CTX_OFFSET_X24		0x38
#define CTX_OFFSET_X25		0x40
#define CTX_OFFSET_X26		0x48
#define CTX_OFFSET_X27		0x50
#define CTX_OFFSET_X28		0x58
#define CTX_OFFSET_X29		0x60
#define CTX_OFFSET_X30		0x68
#define CTX_OFFSET_SP		0x70
#define CTX_OFFSET_PC		0x78

#ifndef __ASSEMBLER__

#include <stddef.h>

/* Minimal C context required to save and restore across switching context */
typedef struct context {
	uint64_t x0;
	uint64_t x1;

	uint64_t x19;
	uint64_t x20;
	uint64_t x21;
	uint64_t x22;
	uint64_t x23;
	uint64_t x24;
	uint64_t x25;
	uint64_t x26;
	uint64_t x27;
	uint64_t x28;
	uint64_t x29;
	uint64_t x30;

	uint64_t sp;
	uint64_t pc;

	struct context *link;
	void *stack;
	size_t stack_size;
} context_t;

int getcontext(context_t *ctx);

void makecontext_setup(context_t *ctx, void *stack, size_t stack_size,
		       context_t *next);

void makecontext(context_t *ctx, void (*func)(), int argc, void *arg);

int swapcontext(context_t *save, const context_t *restore);

#endif /* __ASSEMBLER__ */

#endif /* CONTEXT_H */
