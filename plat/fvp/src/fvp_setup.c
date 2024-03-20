/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch_features.h>
#include <debug.h>
#include <fvp_dram.h>
#include <fvp_private.h>
#include <pl011.h>
#include <plat_common.h>
#include <platform_api.h>
#include <rmm_el3_ifc.h>
#include <sizes.h>
#include <string.h>
#include <xlat_tables.h>

/* FVP UART Base address. */
#define FVP_UART_ADDR	UL(0x1c0c0000)

#define FVP_RMM_UART	MAP_REGION_FLAT(			\
				0,			\
				SZ_4K,				\
				(MT_DEVICE | MT_RW | MT_REALM))

/*
 * Local platform setup for RMM.
 *
 * This function will only be invoked during
 * warm boot and is expected to setup architecture and platform
 * components local to a PE executing RMM.
 */
/* coverity[misra_c_2012_rule_8_7_violation:SUPPRESS] */
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
/* coverity[misra_c_2012_rule_8_7_violation:SUPPRESS] */
void plat_setup(uint64_t x0, uint64_t x1, uint64_t x2, uint64_t x3)
{
	int ret;
	struct ns_dram_info *plat_dram;
	struct console_list *csl_list;

	/* TBD Initialize UART for early log */
	struct xlat_mmap_region plat_regions[] = {
		FVP_RMM_UART,
		{0}
	};

	/* Initialize the RMM-EL3 interface*/
	ret = plat_cmn_init_el3_ifc(x0, x1, x2, x3);
	if (ret != E_RMM_BOOT_SUCCESS) {
		rmm_el3_ifc_report_fail_to_el3(ret);
	}

	/* Initialize console first */
	ret = rmm_el3_ifc_get_console_list_pa(&csl_list);
	if (ret != 0) {
		rmm_el3_ifc_report_fail_to_el3(ret);
	}

	/* We need atleast one console and it needs to be PL011 */
	if (csl_list->num_consoles == 0) {
		rmm_el3_ifc_report_fail_to_el3(E_RMM_BOOT_UNKNOWN_ERROR);
	}

	if(strncmp(csl_list->consoles[0].name, "pl011", 6) != 0) {
		rmm_el3_ifc_report_fail_to_el3(E_RMM_BOOT_UNKNOWN_ERROR);
	}

	uintptr_t uart_base = csl_list->consoles[0].base;

	/* RMM supports only one console atm */
	ret = pl011_init(uart_base, csl_list->consoles[0].clk_in_hz, csl_list->consoles[0].baud_rate);
	if (ret != 0) {
		rmm_el3_ifc_report_fail_to_el3(E_RMM_BOOT_UNKNOWN_ERROR);
	}

	plat_regions[0].base_pa = uart_base;
	plat_regions[0].base_va = uart_base;

	/* Carry on with the rest of the system setup */
	ret = plat_cmn_setup(plat_regions, 1U);
	if (ret != 0) {
		ERROR("%s (%u): Failed to setup the platform (%i)\n",
			__func__, __LINE__, ret);
		rmm_el3_ifc_report_fail_to_el3(E_RMM_BOOT_UNKNOWN_ERROR);
	}

	/*
	 * Validate DRAM data and get pointer
	 * to the platform DRAM info structure
	 */
	ret = rmm_el3_ifc_get_dram_data_validated_pa(
					MAX_DRAM_NUM_BANKS,
					&plat_dram);
	if (ret != E_RMM_BOOT_SUCCESS) {
		ERROR("DRAM data error\n");
		rmm_el3_ifc_report_fail_to_el3(ret);
	}

	/* Set up FVP DRAM layout */
	fvp_set_dram_layout(plat_dram);

	plat_warmboot_setup(x0, x1, x2, x3);
}
