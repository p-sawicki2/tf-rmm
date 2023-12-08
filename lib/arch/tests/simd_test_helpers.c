/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <simd_test_helpers.h>

simd_vreg simd_test_helpers_get_rand_vector(void)
{
	simd_vreg rand_reg;

	for (int i = 0; i < FPU_VEC_REG_SIZE; i++) {
		rand_reg.q[i] = rand() % (UINT8_MAX + 1);
	}

	return rand_reg;
}

void simd_test_helpers_set_state_saved(bool state)
{
	if (simd_is_state_saved() == state) {
		return;
	}

	struct simd_context simd_ctx = { .sflags = 0 };

	simd_ctx.sflags |= SIMD_SFLAG_INIT_DONE;
	simd_ctx.tflags &= ~SIMD_TFLAG_SVE;
	simd_ctx.tflags &= ~SIMD_TFLAG_SME;
	simd_ctx.owner = SIMD_OWNER_REL1;

	if (state) {
		simd_ctx.sflags &= ~SIMD_SFLAG_SAVED;
		simd_context_switch(&simd_ctx, NULL);
	} else {
		simd_ctx.sflags |= SIMD_SFLAG_SAVED;
		simd_context_switch(NULL, &simd_ctx);
	}

	assert(simd_is_state_saved() == state);
}
