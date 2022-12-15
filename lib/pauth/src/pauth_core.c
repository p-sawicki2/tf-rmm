/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors
 */

#include <arch.h>
#include <arch_helpers.h>
#include <assert.h>
#include <cpuid.h>
#include <pauth.h>

struct pauth_state rmm_pauth_state;

/*
 * Program APIAKey_EL1 with random key generated from
 * a TRNG entropy source
 */
void plat_init_apkey(void)
{
	unsigned long low = read_rndr();
	unsigned long high = read_rndr();

	rmm_pauth_state.regs = ((__uint128_t)high << 64) | low;

	write_apiakeylo_el1(low);
	write_apiakeyhi_el1(high);
	isb();
}

/*
 * Restore Pointer authentication keys after returning to
 * Non secure world from Realm world
 */
void restore_pauth_regs(struct pauth_state *state)
{
	assert(state != NULL);

	write_apiakeylo_el1((unsigned long)state->regs);
	write_apiakeyhi_el1((unsigned long)(state->regs >> 64));
	isb();
}

/*
 * Saving Pointer authentication keys before entering
 * Realm world
 */
void save_pauth_regs(struct pauth_state *state)
{
	assert(state != NULL);

	state->regs = ((__uint128_t)read_apiakeyhi_el1() << 64) |
					  read_apiakeylo_el1();
}

/* Disable Pointer Authentication for R-EL2 */
void pauth_disable_el2(void)
{
	write_sctlr_el2(read_sctlr_el2() & ~SCTLR_ELx_EnIA);
	isb();
}

/*
 * Enable Pointer authentication Instruction access
 * and register access to EL0/1 without trapping to EL2
 */
void pauth_enable_access(void)
{
	write_hcr_el2(read_hcr_el2() | HCR_API | HCR_APK);
	isb();
}
