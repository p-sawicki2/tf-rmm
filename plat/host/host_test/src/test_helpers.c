/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch.h>
#include <cpuid.h>
#include <gic.h>
#include <granule.h>
#include <host_defs.h>
#include <host_utils.h>
#include <platform_api.h>
#include <rmm_el3_ifc.h>
#include <xlat_tables.h>

/* Implemented in init.c and needed here */
void rmm_warmboot_main(void);
void rmm_main(void);

/*
 * Define and set the Boot Interface arguments.
 */
#define RMM_EL3_IFC_ABI_VERSION		(RMM_EL3_IFC_SUPPORTED_VERSION)
#define RMM_EL3_MAX_CPUS		(MAX_CPUS)

static unsigned char el3_rmm_shared_buffer[PAGE_SIZE] __aligned(PAGE_SIZE);

/*
 * Create a basic boot manifest.
 */
static struct rmm_core_manifest *boot_manifest =
			(struct rmm_core_manifest *)el3_rmm_shared_buffer;

/*
 * Each available PE in the system needs to have its own sctlr_el2 register
 * amongst other, to control the MMU independenly for each CPU (warmboot might
 * fail if the MMU is enabled). So allocate an sctlr_el2 register for each CPU.
 */
static u_register_t emulated_sctlr_el2[MAX_CPUS];

/*
 * Callbacks to access sctlr_el2
 */
static u_register_t sctlr_el2_rd_cb(u_register_t *regval)
{
	(void)regval;

	return emulated_sctlr_el2[my_cpuid()];
}

static void sctlr_el2_wr_cb(u_register_t val, u_register_t *reg)
{
	(void)reg;

	emulated_sctlr_el2[my_cpuid()] = val;
}

/*
 * Performs some initialization needed before RMM can be run, such as
 * setting up callbacks for sysreg access.
 */
static void setup_host_harness(void)
{
	/*
	 * Initialize ID_AA64MMFR0_EL1 with a physical address
	 * range of 18 bits
	 */
	(void)host_util_set_default_sysreg_cb("id_aa64mmfr0_el1",
			INPLACE(ID_AA64MMFR0_EL1_PARANGE, 5UL));

	/*
	 * Initialize ICH_VTR_EL2 with 6 preemption bits.
	 * (PREbits is equal number of preemption bits minus one)
	 */
	(void)host_util_set_default_sysreg_cb("ich_vtr_el2",
			INPLACE(ICH_VTR_EL2_PRE_BITS, 5UL));

	/* Used to hold CPU Id. Reset to CPUid 0. */
	(void)host_util_set_default_sysreg_cb("tpidr_el2", 0UL);

	/*
	 * Need a different sctlr_el2 per CPU.
	 * The initialization value is ignored here.
	 */
	(void)host_util_set_sysreg_cb("sctlr_el2",
				    sctlr_el2_rd_cb,
				    sctlr_el2_wr_cb,
				    0UL);

	/* Initialize sctlr_el2 for all CPUs to 0. */
	for (unsigned int i = 0U; i < MAX_CPUS; i++) {
		emulated_sctlr_el2[i] = (u_register_t)0UL;
	}

	/* Initialize the boot manifest */
	boot_manifest->version = RMM_EL3_IFC_SUPPORTED_VERSION;
	boot_manifest->plat_data = (uintptr_t)NULL;
}

/*
 * Function to emulate the turn on of the MMU for the fake_host architecture.
 */
static void enable_fake_mmu(void)
{
	write_sctlr_el2(SCTLR_EL2_WXN | SCTLR_EL2_M);
}

static void start_primary_pe(void)
{
	host_set_cpuid(0U);
	plat_setup(0UL,
		   RMM_EL3_IFC_ABI_VERSION,
		   RMM_EL3_MAX_CPUS,
		   (uintptr_t)&el3_rmm_shared_buffer);

	/*
	 * Enable the MMU. This is needed as some initialization code
	 * called by rmm_main() asserts that the mmu is enabled.
	 */
	enable_fake_mmu();

	/*
	 * rmm_main() finishhes the warmboot path.
	 *
	 * Note: It is expected that the attestation init will fail.
	 */
	rmm_main();
}

static void start_secondary_pe(unsigned int cpuid)
{
	host_set_cpuid(cpuid);

	plat_warmboot_setup(0UL,
			    RMM_EL3_IFC_ABI_VERSION,
			    RMM_EL3_MAX_CPUS,
			    (uintptr_t)&el3_rmm_shared_buffer);

	/*
	 * Enable the MMU. This is needed to avoid assertions during boot up
	 * that would otherwise occur if the MMU is disabled.
	 */
	enable_fake_mmu();

	/*
	 * Finalize the warmboot path.
	 * This enables the slot buffer mechanism.
	 */
	rmm_warmboot_main();
}

void test_platform_setup(bool secondaries)
{
	/* Enable RMM and setup basic structures for each test. */
	setup_host_harness();

	/* bringup primary CPU */
	start_primary_pe();

	if (secondaries) {
		for (unsigned int i = 1U; i < RMM_EL3_MAX_CPUS; i++) {
			start_secondary_pe(i);
		}
		host_set_cpuid(0U);
	}
}

unsigned int test_get_platform_nr_granules(void)
{
	return HOST_NR_GRANULES;
}
