/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch.h>
#include <arch_helpers.h>
#include <debug.h>
#include <gic.h>
#include <host_defs.h>
#include <host_rmi_wrappers_private.h>
#include <host_utils.h>
#include <platform_api.h>
#include <rmm_el3_ifc.h>
#include <smc-rmi.h>
#include <stdint.h>
#include <string.h>
#include <table.h>
#include <xlat_tables.h>

#define RMM_EL3_IFC_ABI_VERSION		(RMM_EL3_IFC_SUPPORTED_VERSION)
#define RMM_EL3_MAX_CPUS		(1U)

#define CHECK_RMI_RESULT() \
	do {if (result.x[0] != 0) { \
		ERROR("RMI call failed at %s:%d. status=%lu.\n", __FILE__, __LINE__, result.x[0]); \
		return -1; \
	}} while (0)

/*
 * Define and set the Boot Interface arguments.
 */
static unsigned char el3_rmm_shared_buffer[PAGE_SIZE] __aligned(PAGE_SIZE);

/*
 * Create a basic boot manifest.
 */
static struct rmm_core_manifest *boot_manifest =
			(struct rmm_core_manifest *)el3_rmm_shared_buffer;

/*
 * Performs some initialization needed before RMM can be ran, such as
 * setting up callbacks for sysreg access.
 */
static void setup_sysreg_and_boot_manifest(void)
{
	int ret;

	/*
	 * By default, set current CPU to be CPU0.
	 * Fake host doesn't support using more than one CPU.
	 */
	host_util_set_cpuid(0U);

	/*
	 * Initialize ID_AA64MMFR0_EL1 with a physical address
	 * range of 48 bits (PARange bits set to 0b0101)
	 */
	ret = host_util_set_default_sysreg_cb("id_aa64mmfr0_el1",
				INPLACE(ID_AA64MMFR0_EL1_PARANGE, 5UL),
				false);

	/*
	 * Initialize ICH_VTR_EL2 with 6 preemption bits.
	 * (PREbits is equal number of preemption bits minus one)
	 */
	ret = host_util_set_default_sysreg_cb("ich_vtr_el2",
				INPLACE(ICH_VTR_EL2_PRE_BITS, 5UL),
				false);

	/* SCTLR_EL2 is reset to zero */
	ret = host_util_set_default_sysreg_cb("sctlr_el2", 0UL, false);

	/* TPIDR_EL2 is reset to zero */
	ret = host_util_set_default_sysreg_cb("tpidr_el2", 0UL, false);

	/* ID_AA64ISAR0.RNDR is reset to 1 */
	ret = host_util_set_default_sysreg_cb("id_aa64isar0_el1",
				INPLACE(ID_AA64ISAR0_EL1_RNDR, 1UL),
				true);

	/*
	 * Add callback to elr_el2 so that the realm entry point can be accessed
	 * by host_run_realm
	 */
	ret = host_util_set_default_sysreg_cb("elr_el2", 0UL, false);

	/*
	 * Only check the return value of the last callback setup, to detect
	 * if we are out of callback slots.
	 */
	if (ret != 0) {
		panic();
	}

	/* Initialize the boot manifest */
	boot_manifest->version = RMM_EL3_IFC_SUPPORTED_VERSION;
	boot_manifest->plat_data = (uintptr_t)NULL;

	/* Store current CPU ID into tpidr_el2 */
	write_tpidr_el2(0);
}

/*
 * Function to emulate the MMU enablement for the fake_host architecture.
 */
static void enable_fake_host_mmu(void)
{
	write_sctlr_el2(SCTLR_EL2_WXN | SCTLR_EL2_M);
}

static void *allocate_granule(void)
{
	static unsigned int next_granule_index;
	unsigned long granule;

	granule = host_util_get_granule_base() +
		  next_granule_index * GRANULE_SIZE;
	++next_granule_index;

	return (void *)granule;
}

void realm_entry_point(void)
{
	INFO("###########################\n");
	INFO("# Hello World from a Realm!\n");
	INFO("###########################\n");
}

static int create_realm(void)
{
	struct smc_result result;
	unsigned long rec_aux_count;
	unsigned int i;
	void *rtts[4];
	void *rec_aux_granules[MAX_REC_AUX_GRANULES];
	void *rd = allocate_granule();
	void *rec = allocate_granule();
	struct rmi_realm_params *realm_params = allocate_granule();
	struct rmi_rec_params *rec_params = allocate_granule();
	struct rmi_rec_run *rec_run = allocate_granule();

	rmi_granule_delegate(rd, &result);
	CHECK_RMI_RESULT();
	rmi_granule_delegate(rec, &result);
	CHECK_RMI_RESULT();
	for (i = 0; i < 4; ++i) {
		rtts[i] = allocate_granule();
		rmi_granule_delegate(rtts[i], &result);
		CHECK_RMI_RESULT();
	}

	memset(realm_params, 0, sizeof(*realm_params));
	realm_params->features_0 |= INPLACE(RMM_FEATURE_REGISTER_0_S2SZ, arch_feat_get_pa_width());
	realm_params->rtt_num_start = 1;
	realm_params->rtt_base = (uintptr_t)rtts[0];

	rmi_realm_create(rd, realm_params, &result);
	CHECK_RMI_RESULT();

	for (i = 1; i < 4; ++i) {
		rmi_rtt_create(rtts[i], rd, 0, i, &result);
		CHECK_RMI_RESULT();
	}

	rmi_rec_aux_count(rd, &result);
	CHECK_RMI_RESULT();
	rec_aux_count = result.x[1];

	assert(rec_aux_count == MAX_REC_AUX_GRANULES);
	INFO("A rec requires %lu rec aux pages\n", rec_aux_count);

	memset(rec_params, 0, sizeof(*rec_params));
	for (i = 0; i < rec_aux_count; ++i) {
		rec_aux_granules[i] = allocate_granule();
		rec_params->aux[i] = (uintptr_t)rec_aux_granules[i];
		rmi_granule_delegate(rec_aux_granules[i], &result);
		CHECK_RMI_RESULT();
	}
	rec_params->num_aux = rec_aux_count;
	rec_params->flags |= REC_PARAMS_FLAG_RUNNABLE;
	rec_params->pc = (uintptr_t)realm_entry_point;

	rmi_rec_create(rec, rd, rec_params, &result);
	CHECK_RMI_RESULT();
	rmi_realm_activate(rd, &result);
	CHECK_RMI_RESULT();

	memset(rec_run, 0, sizeof(*rec_run));
	rmi_rec_enter(rec, rec_run, &result);
	CHECK_RMI_RESULT();

	rmi_rec_destroy(rec, &result);
	CHECK_RMI_RESULT();

	for (i = 0; i < rec_aux_count; ++i) {
		rmi_granule_undelegate(rec_aux_granules[i], &result);
		CHECK_RMI_RESULT();
	}

	for (i = 3; i >= 1; --i) {
		rmi_rtt_destroy(rtts[i], rd, 0, i, &result);
		CHECK_RMI_RESULT();
		rmi_granule_undelegate(rtts[i], &result);
		CHECK_RMI_RESULT();
	}

	rmi_realm_destroy(rd, &result);
	CHECK_RMI_RESULT();
	rmi_granule_undelegate(rd, &result);
	CHECK_RMI_RESULT();
	rmi_granule_undelegate(rec, &result);
	CHECK_RMI_RESULT();
	return 0;
}

void rmm_main(void);

int main(int argc, char *argv[])
{
	(void)argc;
	(void)argv;

	VERBOSE("RMM: Beginning of Fake Host execution\n");

	setup_sysreg_and_boot_manifest();

	plat_setup(0UL,
		   RMM_EL3_IFC_ABI_VERSION,
		   RMM_EL3_MAX_CPUS,
		   (uintptr_t)&el3_rmm_shared_buffer);

	/*
	 * Enable the MMU. This is needed as some initialization code
	 * called by rmm_main() asserts that the mmu is enabled.
	 */
	enable_fake_host_mmu();

	/* Start RMM */
	rmm_main();

	/* Create a realm */
	if (create_realm() != 0) {
		ERROR("ERROR: FAILED TO CREATE REALM");
		return -1;
	}

	VERBOSE("RMM: Fake Host execution completed\n");

	return 0;
}
