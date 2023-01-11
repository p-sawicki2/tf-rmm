/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <debug.h>
#include <fvp_dram.h>
#include <fvp_private.h>
#include <pl011.h>
#include <plat_common.h>
#include <rmm_el3_ifc.h>
#include <sizes.h>
#include <xlat_tables.h>

#define FVP_RMM_UART		MAP_REGION_FLAT(			\
					RMM_UART_ADDR,			\
					SZ_4K,				\
					MT_DEVICE | MT_RW | MT_REALM)

/* TBD Initialize UART for early log */
struct xlat_mmap_region plat_regions[] = {
	FVP_RMM_UART,
	{0}
};

/*
 * Local platform setup for RMM.
 *
 * This function will only be invoked during
 * warm boot and is expected to setup architecture and platform
 * components local to a PE executing RMM.
 */
void plat_warmboot_setup(uint64_t x0, uint64_t x1, uint64_t x2, uint64_t x3)
{
	/* Avoid MISRA C:2012-2.7 warnings */
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
void plat_setup(uint64_t x0, uint64_t x1, uint64_t x2, uint64_t x3)
{
	struct dram_info *plat_dram;

	uart_init(RMM_UART_ADDR, FVP_UART_CLK_IN_HZ, FVP_UART_BAUDRATE);

	/* Initialize the RMM <-> EL3 interface and xlat table */
	if (plat_cmn_setup(x0, x1, x2, x3, plat_regions) != 0) {
		panic();
	}

	/*
	 * Validate DRAM data and get pointer
	 * to the platform DRAM info structure
	 */
	plat_dram = rmm_el3_ifc_get_dram_data_validated_pa(MAX_DRAM_NUM_BANKS);

	/* Validate DRAM info pointer */
	if (plat_dram == NULL) {
		ERROR("DRAM data error\n");
		rmm_el3_ifc_report_fail_to_el3(E_RMM_BOOT_MANIFEST_DATA_ERROR);
	}

	/* Set up FVP DRAM layout */
	fvp_set_dram_layout(plat_dram);

	plat_warmboot_setup(x0, x1, x2, x3);
}
