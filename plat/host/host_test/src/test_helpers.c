/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <debug.h>
#include <gic.h>
#include <host_defs.h>
#include <host_utils.h>
#include <platform_api.h>
#include <rmm_el3_ifc.h>
#include <xlat_tables.h>
#include <setjmp.h>
#include <string.h>
#include <test_helpers_private.h>

/* Possible return codes for setjmp on an assert context */
enum assert_ret_codes {
	ASSERT_CONTINUE = 0,
	ASSERT_FAIL,
	ASSERT_PASS
};

/* Implemented in init.c and needed here */
void rmm_warmboot_main(void);
void rmm_main(void);

/*
 * Define and set the Boot Interface arguments.
 */
#define RMM_EL3_IFC_ABI_VERSION		(RMM_EL3_IFC_SUPPORTED_VERSION)
#define RMM_EL3_MAX_CPUS		(MAX_CPUS)

/* Assertion control variables */
static jmp_buf assert_buf;
static char *assert_check;
static bool assert_expected;
static bool asserted;

static unsigned char el3_rmm_shared_buffer[PAGE_SIZE] __aligned(PAGE_SIZE);

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

void test_helper_rmm_start(bool secondaries)
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

unsigned int test_helper_get_nr_granules(void)
{
	return HOST_NR_GRANULES;
}

/* Assertion control */
void __assert_fail(const char *assertion, const char *file,
		   unsigned int line, const char *function)
{
	int retval;

	asserted = true;

	if (assert_expected == true) {
		if (assert_check == NULL) {
			retval = ASSERT_PASS;
		} else {
			if (strncmp(assert_check, assertion,
				    strlen(assertion)) == 0) {
				retval = ASSERT_PASS;
			} else {
				VERBOSE("Assertion mismatch on %s at line %u\n",
					file, line);
				VERBOSE("Expected assertion \"%s\"\n",
					assert_check);
				VERBOSE("Received assertion \"%s\"\n",
					assertion);
				retval = ASSERT_FAIL;
			}
		}
	} else {
		VERBOSE("Unexpected assertion \"%s\" on file %s at line %u\n",
			assertion, file, line);
		retval = ASSERT_FAIL;
	}

	if (retval == ASSERT_PASS) {
		VERBOSE("Expected assertion \"%s\" on file %s at line %u\n",
			assertion, file, line);

	}

	assert_check = NULL;
	assert_expected = false;
	longjmp(assert_buf, retval);
}

void test_helper_expect_assert_with_check(bool expected, char *check)
{
	int assert_ret;

	asserted = false;
	assert_expected = expected;
	assert_check = check;

	assert_ret = setjmp(assert_buf);

	switch (assert_ret) {
	case ASSERT_FAIL:
		test_helpers_private_fail_test("Unexpected assertion\n");
		break;
	case ASSERT_PASS:
		test_helpers_private_pass_test();
		break;
	case ASSERT_CONTINUE:
		/* Nothing to do in this case */
	break;
	default:
		test_helpers_private_fail_test("Unexpected assert return code\n");
	}
}

void test_helper_expect_assert(bool expected)
{
	int assert_ret;

	asserted = false;
	assert_expected = expected;
	assert_check = NULL;

	assert_ret = setjmp(assert_buf);

	switch (assert_ret) {
	case ASSERT_FAIL:
		test_helpers_private_fail_test("Unexpected assertion\n");
		break;
	case ASSERT_PASS:
		test_helpers_private_pass_test();
		break;
	case ASSERT_CONTINUE:
		/* Nothing to do in this case */
	break;
	default:
		test_helpers_private_fail_test("Unexpected assert return code\n");
	}
}

void test_helper_fail_if_no_assertion(void)
{
	if (asserted == false) {
		test_helpers_private_fail_test("Expected assertion did not happen");
	}
}
