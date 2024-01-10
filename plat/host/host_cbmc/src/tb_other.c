/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <rec.h>
#include <rsi-handler.h>
#include <simd.h>
#include <smc-rmi.h>
#include <tb_common.h>
#include <xlat_tables.h>

void handle_psci(struct rec *rec,
		 struct rmi_rec_exit *rec_exit,
		 struct rsi_result *res)
{
	ASSERT(false, "handle_psci");
}

void inject_serror(struct rec *rec, unsigned long vsesr)
{
	ASSERT(false, "inject_serror");
}

struct simd_context *get_cpu_ns_simd_context(void)
{
	ASSERT(false, "get_cpu_ns_simd_context");
	return NULL;
}

void simd_update_smc_sve_hint(struct simd_context *ctx, bool sve_hint)
{
	ASSERT(false, "simd_update_smc_sve_hint");
}

bool simd_is_state_saved(void)
{
	ASSERT(false, "simd_is_state_saved");
	return false;
}

unsigned int rmm_el3_ifc_get_version(void)
{
	ASSERT(false, "rmm_el3_ifc_get_version");
	return 0;
}

unsigned int rmm_el3_ifc_get_manifest_version(void)
{
	ASSERT(false, "rmm_el3_ifc_get_manifest_version");
	return 0U;
}

void simd_init(void)
{
	ASSERT(false, "simd_init");
}

void init_all_cpus_ns_simd_context(void)
{
	ASSERT(false, "init_all_cpus_ns_simd_context");
}

int simd_context_init(simd_owner_t owner, struct simd_context *simd_ctx,
		      const struct simd_config *simd_cfg)
{
	ASSERT(false, "simd_context_init");
	return 0;
}

unsigned long psci_complete_request(struct rec *calling_rec,
				    struct rec *target_rec, unsigned long status)
{
	ASSERT(false, "psci_complete_request");
	return 0UL;
}

struct rsi_walk_result complete_rsi_host_call(struct rec *rec,
					      struct rmi_rec_enter *rec_enter)
{
	struct rsi_walk_result r = {0};

	ASSERT(false, "complete_rsi_host_call");
	return r;
}

void rec_run_loop(struct rec *rec, struct rmi_rec_exit *rec_exit)
{
	ASSERT(false, "rec_run_loop");
}

int plat_cmn_warmboot_setup(void)
{
	ASSERT(false, "plat_cmn_warmboot_setup");
	return 0;
}

int plat_cmn_setup(unsigned long x0, unsigned long x1,
		   unsigned long x2, unsigned long x3,
		   struct xlat_mmap_region *plat_regions,
		   unsigned int nregions)
{
	ASSERT(false, "plat_cmn_setup");
	return 0;
}

