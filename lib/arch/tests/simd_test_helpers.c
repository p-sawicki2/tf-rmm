/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <simd_test_helpers.h>

simd_vreg simd_test_helpers_get_rand_vector(void) {
	simd_vreg rand_reg;

	for (int i = 0; i < FPU_VEC_REG_SIZE; i++) {
		rand_reg.q[i] = rand() % (UINT8_MAX + 1);
	}

	return rand_reg;
}

void simd_test_helpers_set_state_saved_true(void)
{
	if (simd_is_state_saved()) {
		return;
	}

	struct simd_context save_simd_ctx =
	{
		.sflags = 0,
	};

	save_simd_ctx.sflags |= SIMD_SFLAG_INIT_DONE;
	save_simd_ctx.sflags &= ~SIMD_SFLAG_SAVED;
	save_simd_ctx.tflags &= ~SIMD_TFLAG_SVE;
	save_simd_ctx.tflags &= ~SIMD_TFLAG_SME;
	save_simd_ctx.owner = SIMD_OWNER_REL1;

	simd_context_switch(&save_simd_ctx, NULL);

	assert(simd_is_state_saved());
}

void simd_test_helpers_set_state_saved_false(void)
{
	if (!simd_is_state_saved()) {
		return;
	}

	struct simd_context restore_simd_ctx =
	{
		.sflags = 0,
	};

	restore_simd_ctx.sflags |= SIMD_SFLAG_INIT_DONE;
	restore_simd_ctx.sflags |= SIMD_SFLAG_SAVED;
	restore_simd_ctx.tflags &= ~SIMD_TFLAG_SVE;
	restore_simd_ctx.tflags &= ~SIMD_TFLAG_SME;
	restore_simd_ctx.owner = SIMD_OWNER_REL1;

	simd_context_switch(NULL, &restore_simd_ctx);

	assert(!simd_is_state_saved());
}
