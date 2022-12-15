/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors
 */

#ifndef PAUTH_H
#define PAUTH_H

struct pauth_state {
	__uint128_t apiakey;
};

/***********************************************************************
 * Pauth control helper functions
 **********************************************************************/
void pauth_init_key(void);

void pauth_disable_el1(void);
void pauth_enable_el1(void);

void pauth_disable_el2(void);
void pauth_enable_el2(void);

void pauth_enable_access(void);
void save_pauth_regs(struct pauth_state *pauth);
void restore_pauth_regs(struct pauth_state *pauth);
void plat_init_apkey(void);

#endif /* PAUTH_H */
