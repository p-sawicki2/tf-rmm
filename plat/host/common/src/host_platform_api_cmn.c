/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <debug.h>
#include <gic.h>
#include <host_defs.h>
#include <host_platform_api.h>
#include <host_utils.h>
#include <plat_common.h>
#include <rmm_el3_ifc.h>
#include <stdint.h>
#include <xlat_tables.h>

COMPILER_ASSERT(RMM_MAX_GRANULES >= HOST_NR_GRANULES);

/* No regions to add for host */
struct xlat_mmap_region plat_regions[] = {
	{0}
};

/*
 * Define and set the Boot Interface arguments.
 */
unsigned char el3_rmm_shared_buffer[PAGE_SIZE] __aligned(PAGE_SIZE);

/*
 * Create a basic boot manifest.
 */
static struct rmm_core_manifest *boot_manifest =
			(struct rmm_core_manifest *)el3_rmm_shared_buffer;

/*
 * Local platform setup for RMM.
 *
 * This function will only be invoked during
 * warm boot and is expected to setup architecture and platform
 * components local to a PE executing RMM.
 */
void plat_warmboot_setup(uint64_t x0, uint64_t x1,
			 uint64_t x2, uint64_t x3)
{
	/* Avoid MISRA C:2102-2.7 warnings */
	(void)x0;
	(void)x1;
	(void)x2;
	(void)x3;

	if (plat_cmn_warmboot_setup() != 0) {
		panic();
	}
}

/*
 * Global platform setup for RMM.
 *
 * This function will only be invoked once during cold boot
 * and is expected to setup architecture and platform components
 * common for all PEs executing RMM. The translation tables should
 * be initialized by this function.
 */
void plat_setup(uint64_t x0, uint64_t x1,
		uint64_t x2, uint64_t x3)
{
	/* Initialize the RMM <-> EL3 interface.
	 * Since host platform does not have VA address translation, we pass the
	 * same shared buf address as the VA to be used for access by users of
	 * rmm-el3-ifc.
	 */
	if (rmm_el3_ifc_init(x0, x1, x2, x3, x3) != 0) {
		panic();
	}

	/* Carry on with the rest of the system setup */
	if (plat_cmn_setup(x0, x1, x2, x3, plat_regions) != 0) {
		panic();
	}

	plat_warmboot_setup(x0, x1, x2, x3);
}

unsigned long plat_granule_addr_to_idx(unsigned long addr)
{
	if (!(GRANULE_ALIGNED(addr) &&
		(addr < (host_util_get_granule_base() + HOST_MEM_SIZE)) &&
		(addr >= host_util_get_granule_base()))) {
		return UINT64_MAX;
	}

	return (addr - host_util_get_granule_base()) / GRANULE_SIZE;
}

unsigned long plat_granule_idx_to_addr(unsigned long idx)
{
	assert(idx < HOST_NR_GRANULES);
	return host_util_get_granule_base() + (idx * GRANULE_SIZE);
}

unsigned char *plat_get_el3_rmm_shared_buffer(void)
{
	return el3_rmm_shared_buffer;
}

void plat_setup_sysreg_and_boot_manifest(void)
{
	/*
	 * Initialize ID_AA64MMFR0_EL1 with a physical address
	 * range of 48 bits (PARange bits set to 0b0101)
	 */
	(void)host_util_set_default_sysreg_cb("id_aa64mmfr0_el1",
			INPLACE(ID_AA64MMFR0_EL1_PARANGE, 5UL));

	/*
	 * Initialize ICH_VTR_EL2 with 6 preemption bits.
	 * (PREbits is equal number of preemption bits minus one)
	 */
	(void)host_util_set_default_sysreg_cb("ich_vtr_el2",
			INPLACE(ICH_VTR_EL2_PRE_BITS, 5UL));

	/* SCTLR_EL2 is reset to zero */
	(void)host_util_set_default_sysreg_cb("sctlr_el2", 0UL);

	/* TPIDR_EL2 is reset to zero */
	(void)host_util_set_default_sysreg_cb("tpidr_el2", 0UL);

	/* Initialize the boot manifest */
	boot_manifest->version = RMM_EL3_IFC_SUPPORTED_VERSION;
	boot_manifest->plat_data = (uintptr_t)NULL;
}
