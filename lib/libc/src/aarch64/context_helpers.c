/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch.h>
#include <assert.h>
#include <context.h>
#include <stddef.h>
#include <stdbool.h>

void startlinkcontext(context_t *ctx);

int getcontext(context_t *ctx)
{
	return 0;
}

void makecontext_setup(context_t *ctx, void *stack, size_t stack_size,
		       context_t *link)
{
	assert(stack_size >= 4096);

	ctx->stack = stack;
	ctx->stack_size = stack_size;
	ctx->link = link;
}

void makecontext(context_t *ctx, void (*func)(), int argc, void *arg)
{
	assert(argc == 1);

	ctx->x0 = (uint64_t)arg;
	ctx->x19 = (uint64_t)ctx->link;
	ctx->x29 = 0;
	ctx->x30 = (uint64_t)startlinkcontext;

	ctx->sp = (uint64_t)(ctx->stack + ctx->stack_size);
	ctx->pc = (uint64_t)func;
}
