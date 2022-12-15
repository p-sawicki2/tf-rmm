/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors
 */

#ifndef PAUTH_H
#define PAUTH_H

#ifndef __ASSEMBLER__
#include <assert.h>

struct pauth_state {
	__uint128_t apiakey;
};
COMPILER_ASSERT(sizeof(struct pauth_state) == 16U);
#endif

/***********************************************************************
 * Pauth control helper functions
 **********************************************************************/
void pauth_init(void);

void pauth_enable_el2(void);

void pauth_enable_access(void);
void save_rmm_pauth_regs(void);
void restore_rmm_pauth_regs(void);

#endif /* PAUTH_H */
