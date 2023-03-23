/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef SIMD_H
#define SIMD_H

#include <arch.h>
#include <arch_features.h>
#include <assert.h>
#include <fpu_helpers.h>
#include <stddef.h>
#include <sve_helpers.h>

typedef enum {
	SIMD_NONE,
	SIMD_FPU,
	SIMD_SVE
} simd_t;

struct simd_state {
	union {
		struct fpu_state fpu;
		struct sve_state sve;
	} t;
	simd_t saved_state;
};

void simd_init(void);
void simd_save_state(simd_t type, struct simd_state *simd);
void simd_restore_state(simd_t type, struct simd_state *simd);
void simd_sve_state_init(struct simd_state *simd, uint8_t vq);
void simd_save_ns_state(void);
void simd_restore_ns_state(void);

static inline simd_t cpu_simd_type(void)
{
	return is_feat_sve_present() ? SIMD_SVE : SIMD_FPU;
}

/* Allow FPU and/or SVE access */
static inline void simd_traps_disable(simd_t type)
{
	unsigned long cptr;

	cptr = read_cptr_el2();
	cptr &= ~(MASK(CPTR_EL2_FPEN) | MASK(CPTR_EL2_ZEN));

	switch (type) {
	case SIMD_SVE:
		assert(is_feat_sve_present());

		cptr |= INPLACE(CPTR_EL2_ZEN, CPTR_EL2_ZEN_NO_TRAP_11);
		cptr |= INPLACE(CPTR_EL2_FPEN, CPTR_EL2_FPEN_NO_TRAP_11);
		break;
	case SIMD_FPU:
		if (is_feat_sve_present()) {
			cptr |= INPLACE(CPTR_EL2_ZEN, CPTR_EL2_ZEN_TRAP_ALL_00);
		}
		cptr |= INPLACE(CPTR_EL2_FPEN, CPTR_EL2_FPEN_NO_TRAP_11);
		break;
	default:
		assert(false);
	}

	write_cptr_el2(cptr);
	isb();
}

/* Deny FPU and SVE access */
static inline void simd_traps_enable(void)
{
	unsigned long cptr;

	cptr = read_cptr_el2();
	cptr &= ~(MASK(CPTR_EL2_FPEN) | MASK(CPTR_EL2_ZEN));

	if (is_feat_sve_present()) {
		cptr |= INPLACE(CPTR_EL2_ZEN, CPTR_EL2_ZEN_TRAP_ALL_00);
	}
	cptr |= INPLACE(CPTR_EL2_FPEN, CPTR_EL2_FPEN_TRAP_ALL_00);

	write_cptr_el2(cptr);
	isb();
}

static inline void simd_set_saved_state(simd_t type, struct simd_state *simd)
{
	assert(simd != NULL);
	assert(simd->saved_state == SIMD_NONE);
	simd->saved_state = type;
}

/*
 * RMM support to use SIMD (FPU) at REL2
 */
#ifdef RMM_FPU_USE_AT_REL2
#define SIMD_FPU_ALLOW(expression)				\
	do {							\
		assert(simd_is_fpu_available_for_rmm());	\
		simd_traps_disable(SIMD_FPU);			\
		expression;					\
		simd_traps_enable();				\
	} while (false)

#define SIMD_IS_FPU_ALLOWED()					\
	(simd_is_fpu_available_for_rmm() && is_fpen_enabled())

bool simd_is_fpu_available_for_rmm(void);

#else /* !RMM_FPU_USE_AT_REL2 */
#define SIMD_FPU_ALLOW(expression)				\
	do {							\
		expression;					\
	} while (false)

#define SIMD_IS_FPU_ALLOWED() (true)

#endif /* RMM_FPU_USE_AT_REL2 */

#endif /* SIMD_H */
