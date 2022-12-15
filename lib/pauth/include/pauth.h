/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors
 */

#ifndef PAUTH_H
#define PAUTH_H
#include <stdint.h>

#ifndef __ASSEMBLER__

struct pauth_state {
	__uint128_t apiakey;
};
#endif

/***********************************************************************
 * Pauth control helper functions
 **********************************************************************/
void pauth_init(void);
void pauth_enable_el2(void);

#endif /* PAUTH_H */
