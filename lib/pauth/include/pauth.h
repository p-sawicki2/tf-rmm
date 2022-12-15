/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors
 */

#ifndef PAUTH_H
#define PAUTH_H

#define SIZEOF_PAUTH_KEY	16U
#define PAUTH_KEY_SHIFT		4U

#ifndef __ASSEMBLER__
struct pauth_state {
	uint64_t apiakeylo_el1;
	uint64_t apiakeyhi_el1;
	uint64_t apibkeylo_el1;
	uint64_t apibkeyhi_el1;
	uint64_t apdakeylo_el1;
	uint64_t apdakeyhi_el1;
	uint64_t apdbkeylo_el1;
	uint64_t apdbkeyhi_el1;
	uint64_t apgakeylo_el1;
	uint64_t apgakeyhi_el1;
};

/***********************************************************************
 * Pauth control helper functions
 **********************************************************************/
void pauth_init(void);
void pauth_enable_el2(void);

#endif /* __ASSEMBLER__ */
#endif /* PAUTH_H */
