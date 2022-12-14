/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch_helpers.h>
#include <assert.h>
#include <debug.h>
#include <rmm_el3_ifc.h>
#include <smc.h>
#include <stdint.h>
#include <string.h>
#include <utils_def.h>

/*
 * Local copy of the core boot manifest to be used during runtime
 */
static struct rmm_core_manifest local_core_manifest;

/*
 * Manifest status
 */
static bool manifest_processed;

void rmm_el3_ifc_process_boot_manifest(void)
{
	assert((manifest_processed == false) &&
		(is_mmu_enabled() == false));

	/*
	 * The boot manifest is expected to be on the shared area.
	 * Make a local copy of it.
	 */
	(void)memcpy((void *)&local_core_manifest,
		     (void *)rmm_el3_ifc_get_shared_buf_pa(),
		     sizeof(struct rmm_core_manifest));

	flush_dcache_range((uintptr_t)&local_core_manifest,
				sizeof(local_core_manifest));

	/*
	 * Validate the Boot Manifest Version.
	 * Only the version major is taken into account on the verification.
	 */
	if ((RMM_EL3_MANIFEST_GET_VERS_MAJOR(local_core_manifest.version)) >
					RMM_EL3_MANIFEST_VERS_MAJOR) {
		report_fail_to_el3(E_RMM_BOOT_MANIFEST_VERSION_NOT_SUPPORTED);
	}

	manifest_processed = true;
	flush_dcache_range((uintptr_t)&manifest_processed, sizeof(bool));
}

/* Return the raw value of the received boot manifest */
unsigned int rmm_el3_ifc_get_manifest_version(void)
{
	assert(manifest_processed == true);

	return local_core_manifest.version;
}

/* Return a pointer to the platform manifest */
uintptr_t rmm_el3_ifc_get_plat_manifest_pa(void)
{
	assert((manifest_processed == true) &&
		(is_mmu_enabled() == false));

	return local_core_manifest.plat_data;
}

/* Return a pointer to the platform DRAM info setup by EL3 Firmware */
struct dram_info *rmm_el3_ifc_get_dram_data_manifest_pa(void)
{
	assert((manifest_processed == true) &&
		(is_mmu_enabled() == false));

	return &local_core_manifest.plat_dram;
}
