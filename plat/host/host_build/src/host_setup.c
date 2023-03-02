/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <arch_helpers.h>
#include <debug.h>
#include <host_defs.h>
#include <host_rmi_wrappers.h>
#include <host_utils.h>
#include <platform_api.h>
#include <rmm_el3_ifc.h>
#include <smc-rmi.h>
#include <string.h>
#include <table.h>

#define RTT_COUNT 4

#define RMM_EL3_IFC_ABI_VERSION		(RMM_EL3_IFC_SUPPORTED_VERSION)
#define RMM_EL3_MAX_CPUS		(1U)

#define CHECK_RMI_RESULT() \
	do {if (result.x[0] != 0) { \
		ERROR("RMI call failed at %s:%d. status=%lu.\n", __FILE__, __LINE__, result.x[0]); \
		return -1; \
	}} while (0)

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
	void *rtts[RTT_COUNT];
	void *rec_aux_granules[MAX_REC_AUX_GRANULES];
	void *rd = allocate_granule();
	void *rec = allocate_granule();
	struct rmi_realm_params *realm_params = allocate_granule();
	struct rmi_rec_params *rec_params = allocate_granule();
	struct rmi_rec_run *rec_run = allocate_granule();

	host_rmi_granule_delegate(rd, &result);
	CHECK_RMI_RESULT();
	host_rmi_granule_delegate(rec, &result);
	CHECK_RMI_RESULT();
	for (i = 0; i < RTT_COUNT; ++i) {
		rtts[i] = allocate_granule();
		host_rmi_granule_delegate(rtts[i], &result);
		CHECK_RMI_RESULT();
	}

	memset(realm_params, 0, sizeof(*realm_params));
	realm_params->features_0 |= INPLACE(RMM_FEATURE_REGISTER_0_S2SZ, arch_feat_get_pa_width());
	realm_params->rtt_num_start = 1;
	realm_params->rtt_base = (uintptr_t)rtts[0];

	host_rmi_realm_create(rd, realm_params, &result);
	CHECK_RMI_RESULT();

	for (i = 1; i < RTT_COUNT; ++i) {
		host_rmi_rtt_create(rtts[i], rd, 0, i, &result);
		CHECK_RMI_RESULT();
	}

	host_rmi_rec_aux_count(rd, &result);
	CHECK_RMI_RESULT();
	rec_aux_count = result.x[1];

	assert(rec_aux_count == MAX_REC_AUX_GRANULES);
	INFO("A rec requires %lu rec aux pages\n", rec_aux_count);

	memset(rec_params, 0, sizeof(*rec_params));
	for (i = 0; i < rec_aux_count; ++i) {
		rec_aux_granules[i] = allocate_granule();
		rec_params->aux[i] = (uintptr_t)rec_aux_granules[i];
		host_rmi_granule_delegate(rec_aux_granules[i], &result);
		CHECK_RMI_RESULT();
	}
	rec_params->num_aux = rec_aux_count;
	rec_params->flags |= REC_PARAMS_FLAG_RUNNABLE;
	rec_params->pc = (uintptr_t)realm_entry_point;

	host_rmi_rec_create(rec, rd, rec_params, &result);
	CHECK_RMI_RESULT();
	host_rmi_realm_activate(rd, &result);
	CHECK_RMI_RESULT();

	memset(rec_run, 0, sizeof(*rec_run));
	host_rmi_rec_enter(rec, rec_run, &result);
	CHECK_RMI_RESULT();

	host_rmi_rec_destroy(rec, &result);
	CHECK_RMI_RESULT();

	for (i = 0; i < rec_aux_count; ++i) {
		host_rmi_granule_undelegate(rec_aux_granules[i], &result);
		CHECK_RMI_RESULT();
	}

	for (i = RTT_COUNT-1; i >= 1; --i) {
		host_rmi_rtt_destroy(rtts[i], rd, 0, i, &result);
		CHECK_RMI_RESULT();
		host_rmi_granule_undelegate(rtts[i], &result);
		CHECK_RMI_RESULT();
	}

	host_rmi_realm_destroy(rd, &result);
	CHECK_RMI_RESULT();
	host_rmi_granule_undelegate(rd, &result);
	CHECK_RMI_RESULT();
	host_rmi_granule_undelegate(rec, &result);
	CHECK_RMI_RESULT();
	return 0;
}

void rmm_main(void);

int main(int argc, char *argv[])
{
	(void)argc;
	(void)argv;

	VERBOSE("RMM: Beginning of Fake Host execution\n");

	host_util_set_cpuid(0U);

	host_util_setup_sysreg_and_boot_manifest();

	plat_setup(0UL,
		   RMM_EL3_IFC_ABI_VERSION,
		   RMM_EL3_MAX_CPUS,
		   (uintptr_t)host_util_get_el3_rmm_shared_buffer());

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
