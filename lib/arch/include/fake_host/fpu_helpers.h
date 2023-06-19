/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef FPU_HELPERS_H
#define FPU_HELPERS_H

#include <arch.h>
#include <assert.h>
#include <stddef.h>

struct fpu_state {
	uint64_t unused;
};

void fpu_save_state(struct fpu_state *fpu);
void fpu_restore_state(const struct fpu_state *fpu);

#endif /* FPU_HELPERS_H */
