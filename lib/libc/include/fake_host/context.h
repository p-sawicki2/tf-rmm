/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef CONTEXT_H
#define CONTEXT_H

#include <ucontext.h>

typedef ucontext_t context_t;

static inline void makecontext_setup(context_t *ctx, void *stack,
				     size_t stack_size, context_t *link)
{
	ctx->uc_stack.ss_sp = stack;
	ctx->uc_stack.ss_size = stack_size;
	ctx->uc_link = link;
}

#endif /* CONTEXT_H */
