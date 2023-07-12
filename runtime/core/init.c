/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch_features.h>
#include <attestation.h>
#include <buffer.h>
#include <buffer_init.h>
#include <debug.h>
#include <rmm_el3_ifc.h>
#include <simd.h>
#include <smc-rmi.h>
#include <smc-rsi.h>


#ifdef NDEBUG
#define RMM_BUILD_TYPE	"release"
#else
#define RMM_BUILD_TYPE	"debug"
#endif

#define VER_STRING(toolchain, major, minor, patch) \
		toolchain __STRING(major) "." \
		__STRING(minor) "." __STRING(patch)

static void rmm_arch_init(void)
{
	MPAM(write_mpam2_el2(MPAM2_EL2_INIT));
	MPAM(write_mpamhcr_el2(MPAMHCR_EL2_INIT));
	SPE(write_pmscr_el2(PMSCR_EL2_INIT));

	write_cnthctl_el2(CNTHCTL_EL2_INIT);
	write_vpidr_el2(read_midr_el1());
	write_mdcr_el2(MDCR_EL2_INIT |
			INPLACE(MDCR_EL2_HPMN,
			EXTRACT(PMCR_EL0_N, read_pmcr_el0())));

	simd_init();
}

void rmm_warmboot_main(void)
{
	/*
	 * Do the rest of RMM architecture init
	 */
	rmm_arch_init();

	/*
	 * Finish initializing the slot buffer mechanism
	 */
	slot_buf_finish_warmboot_init();
}

void rmm_main(void)
{
	unsigned int rmm_el3_ifc_version = rmm_el3_ifc_get_version();
	unsigned int manifest_version = rmm_el3_ifc_get_manifest_version();

	/*
	 * Report project name, version, build type and
	 * commit information if it is present
	 */
	NOTICE("Booting %s v.%s(%s) %s Built with %s\n",
		NAME, VERSION, RMM_BUILD_TYPE, COMMIT_INFO,
#ifdef __clang__
	VER_STRING("Clang ", __clang_major__, __clang_minor__,
		__clang_patchlevel__)
#else
	VER_STRING("GCC ", __GNUC__, __GNUC_MINOR__,
		__GNUC_PATCHLEVEL__)
#endif
		);

	/* Report Boot Interface version */
	NOTICE("RMM-EL3 Interface v.%u.%u\n",
		RMM_EL3_IFC_GET_VERS_MAJOR(rmm_el3_ifc_version),
		RMM_EL3_IFC_GET_VERS_MINOR(rmm_el3_ifc_version));

	/* Report Boot Manifest version */
	NOTICE("Boot Manifest Interface v.%u.%u\n",
		RMM_EL3_MANIFEST_GET_VERS_MAJOR(manifest_version),
		RMM_EL3_MANIFEST_GET_VERS_MINOR(manifest_version));

	/* Report RMI/RSI ABI versions and build timestamp */
	NOTICE("RMI/RSI ABI v.%u.%u/%u.%u built: %s %s\n",
		RMI_ABI_VERSION_MAJOR, RMI_ABI_VERSION_MINOR,
		RSI_ABI_VERSION_MAJOR, RSI_ABI_VERSION_MINOR,
		__DATE__, __TIME__);

	rmm_warmboot_main();

#ifdef RMM_FPU_USE_AT_REL2
	simd_save_ns_state();
#endif
	if (attestation_init() != 0) {
		WARN("Attestation init failed.\n");
	}
#ifdef RMM_FPU_USE_AT_REL2
	/*
	 * TODO: Do not save and restore NS state. Instead after
	 * attestation_init clear FPU state.
	 */
	simd_restore_ns_state();
#endif
}
