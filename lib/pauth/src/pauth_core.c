/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors
 */

#include <arch.h>
#include <arch_helpers.h>
#include <assert.h>
#include <cpuid.h>
#include <pauth.h>

struct pauth_state g_rmm_pauth_data[MAX_CPUS];

/*
 * Allow Pointer authentication Instruction access
 * and register access to EL0/1 without trapping to EL2
 */
static void pauth_disable_trap(void)
{
	write_hcr_el2(read_hcr_el2() | HCR_API | HCR_APK);
}

/*
 * Program APIAKey_EL1 with random key generated from
 * a TRNG entropy source
 */
void pauth_init(void)
{
	unsigned long low = read_rndr();
	unsigned long high = read_rndr();

	pauth_disable_trap();
	write_apiakeylo_el1(low);
	write_apiakeyhi_el1(high);
	isb();
}
