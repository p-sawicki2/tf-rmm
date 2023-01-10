/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <buffer.h>
#include <cpputest_ifc.h>
#include <debug.h>
#include <errno.h>
#include <gic.h>
#include <host_defs.h>
#include <host_utils.h>
#include <platform_api.h>
#include <rmm_el3_ifc.h>
#include <stdlib.h>
#include <string.h>
#include <test_private.h>
#include <utils_def.h>
#include <xlat_tables.h>

/* Implemented in init.c and needed here */
void rmm_warmboot_main(void);
void rmm_main(void);

/*
 * Define and set the Boot Interface arguments.
 */
#define RMM_EL3_IFC_ABI_VERSION		(RMM_EL3_IFC_SUPPORTED_VERSION)
#define RMM_EL3_MAX_CPUS		(MAX_CPUS)

/* Maximum size of the assertion check string */
#define CHECK_SIZE			U(80)

/* Assertion control variables */
static char assert_check[CHECK_SIZE + 1U];
static bool assert_expected;
static bool asserted;

/* Panic control variables */
static bool panic_expected;
static bool panicked;

static unsigned char el3_rmm_shared_buffer[PAGE_SIZE] __aligned(PAGE_SIZE);

static uintptr_t callbacks[CB_IDS];

/*
 * Create a basic boot manifest.
 */
static struct rmm_core_manifest *boot_manifest =
			(struct rmm_core_manifest *)el3_rmm_shared_buffer;

/*
 * Performs some initialization needed before RMM can be run, such as
 * setting up callbacks for sysreg access.
 */
static void setup_sysreg_and_boot_manifest(void)
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

	(void)host_util_set_default_sysreg_cb("sctlr_el2", 0UL);

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
	host_util_set_cpuid(0U);

	/* Early setup the CpuId into tpidr_el2 */
	write_tpidr_el2(0U);

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
	host_util_set_cpuid(cpuid);

	/*
	 * Early setup the CpuId into tpidr_el2 for each secondary.
	 */
	write_tpidr_el2(cpuid);

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

void test_helpers_rmm_start(bool secondaries)
{
	static bool initialized;

	if (initialized == false) {
		/* Enable RMM and setup basic structures for each test. */
		setup_sysreg_and_boot_manifest();

		/* bringup primary CPU */
		start_primary_pe();

		if (secondaries) {
			for (unsigned int i = 1U; i < RMM_EL3_MAX_CPUS; i++) {
				start_secondary_pe(i);
			}
			host_util_set_cpuid(0U);
		}
		initialized = true;
	}
}

unsigned int test_helpers_get_nr_granules(void)
{
	return HOST_NR_GRANULES;
}

int test_helpers_get_rand_in_range(int min, int max)
{
	return (rand() % (max - min + 1)) + min;
}

int test_helpers_register_cb(union test_harness_cbs cb, enum cb_ids id)
{
	if (id >= CB_IDS) {
		return -EINVAL;
	}

	/*
	 * Covert the pointer stored in cb into a generic one
	 * and store it.
	 * We ignore the exact the cb corresponding to the cbs_id
	 * and just use the first one.
	 */
	callbacks[id] = (uintptr_t)cb.buffer_map;

	return 0;
}

int test_helpers_unregister_cb(enum cb_ids id)
{
	union test_harness_cbs cb;

	/*
	 * Set the callback to NULL.
	 * We ignore the exact the cb corresponding to the cbs_id
	 * and just use the first one.
	 */
	cb.buffer_map = NULL;
	return test_helpers_register_cb(cb, id);
}

/* Assertion control */
void __assert_fail(const char *assertion, const char *file,
		   unsigned int line, const char *function)
{
	asserted = true;

	if (assert_expected == true) {
		if (strlen(assert_check) > 0U) {
			if (strncmp(assert_check, assertion,
				    strlen(assertion)) != 0) {
				VERBOSE("Assertion mismatch on %s at line %u\n",
					file, line);
				VERBOSE("Expected assertion \"%s\"\n",
					assert_check);
				VERBOSE("Received assertion \"%s\"\n",
					assertion);
				cpputest_ifc_fail_test("Assertion mismatch\n");
			}
		}
	} else {
		VERBOSE("Unexpected assertion \"%s\" on file %s at line %u\n",
			assertion, file, line);
		cpputest_ifc_fail_test("Unexpected assertion\n");
	}

	assert_check[0] = '\0';
	assert_expected = false;

	VERBOSE("Expected assertion \"%s\" on file %s at line %u\n",
			assertion, file, line);

	cpputest_ifc_pass_test();
}

void test_helpers_expect_assert_fail_with_check(bool expected, char *check)
{
	if (check == NULL) {
		assert_check[0] = '\0';
	} else {
		if (strlen(check) > CHECK_SIZE) {
			cpputest_ifc_fail_test("Assert check string too large");
		}
		strncpy(assert_check, check, CHECK_SIZE);
		assert_check[CHECK_SIZE] = '\0';
	}
	asserted = false;
	assert_expected = expected;
}

void test_helpers_expect_assert_fail(bool expected)
{
	test_helpers_expect_assert_fail_with_check(expected, NULL);
}

void test_helpers_fail_if_no_assert_failed(void)
{
	if (asserted == false) {
		cpputest_ifc_fail_test("Expected assertion did not happen");
	} else {
		asserted = false;
		assert_check[0] = '\0';
		assert_expected = false;
	}

}

/******************************************************************
 * Private APIs shared with other host_test files.
 *****************************************************************/
uintptr_t get_cb(enum cb_ids id)
{
	assert(id < CB_IDS);

	return callbacks[id];

}

void test_helpers_expect_panic(bool expected)
{
	panicked = false;
	panic_expected = expected;
}

void test_helper_fail_if_no_panic(void)
{
	if (panicked == false) {
		cpputest_ifc_fail_test("Expected panic() did not happen");
	} else {
		panicked = false;
		panic_expected = false;
	}
}

/***************************************************************************
 * Private helpers used internally by the platform layer.
 **************************************************************************/

__dead2 void test_private_panic(void)
{
	if (panic_expected == true) {
		panic_expected = false;
		VERBOSE("Excpected call to panic()\n");
		cpputest_ifc_pass_test();
	}

	cpputest_ifc_fail_test("Unexpected call to panic()\n");
}
