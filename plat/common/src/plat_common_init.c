/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch_helpers.h>
#include <assert.h>
#include <buffer.h>
#include <cpuid.h>
#include <debug.h>
#include <errno.h>
#include <gic.h>
#include <import_sym.h>
#include <rmm_el3_ifc.h>
#include <sizes.h>
#include <stdint.h>
#include <string.h>
#include <xlat_contexts.h>
#include <xlat_tables.h>

IMPORT_SYM(uintptr_t, rmm_text_start,		RMM_CODE_START);
IMPORT_SYM(uintptr_t, rmm_text_end,		RMM_CODE_END);
IMPORT_SYM(uintptr_t, rmm_ro_start,		RMM_RO_START);
IMPORT_SYM(uintptr_t, rmm_ro_end,		RMM_RO_END);
IMPORT_SYM(uintptr_t, rmm_rw_start,		RMM_RW_START);
IMPORT_SYM(uintptr_t, rmm_rw_end,		RMM_RW_END);

/*
 * Leave an invalid page between the end of RMM memory and the beginning
 * of the shared buffer VA. This will help to detect any memory access
 * underflow by RMM.
 */
#define RMM_SHARED_BUFFER_START	(RMM_RW_END + SZ_4K)
/*
 * Memory map REGIONS used for the RMM runtime (static mappings)
 */
#define RMM_CODE_SIZE		(RMM_CODE_END - RMM_CODE_START)
#define RMM_RO_SIZE		(RMM_RO_END - RMM_RO_START)
#define RMM_RW_SIZE		(RMM_RW_END - RMM_RW_START)

#define RMM_CODE		MAP_REGION_FLAT(			\
					RMM_CODE_START,			\
					RMM_CODE_SIZE,			\
					MT_CODE | MT_REALM)

#define RMM_RO			MAP_REGION_FLAT(			\
					RMM_RO_START,			\
					RMM_RO_SIZE,			\
					MT_RO_DATA | MT_REALM)

#define RMM_RW			MAP_REGION_FLAT(			\
					RMM_RW_START,			\
					RMM_RW_SIZE,			\
					MT_RW_DATA | MT_REALM)

/*
 * Some of the fields for the RMM_SHARED region will be populated
 * at runtime.
 */
#define RMM_SHARED		MAP_REGION(				\
					0U,				\
					RMM_SHARED_BUFFER_START,	\
					0U,				\
					MT_RW_DATA | MT_REALM)

/* Number of currently existing regions */
#define CURRENT_REGIONS		(4U)

/* Allocate the runtime translation tables */
static uint64_t runtime_s1tt[XLAT_TABLE_ENTRIES * PLAT_CMN_CTX_MAX_XLAT_TABLES]
					__aligned(XLAT_TABLES_ALIGNMENT)
					__section("xlat_static_tables");

/* Structures to hold the runtime translation context information  */
static struct xlat_ctx_tbls runtime_tbls;
static struct xlat_ctx_cfg runtime_xlat_ctx_cfg;
static struct xlat_ctx runtime_xlat_ctx;

/*
 * Platform common cold boot setup for RMM.
 *
 * This function should only be invoked once during cold boot
 * and is expected to setup architecture and platform components
 * common for all PEs executing RMM.
 * The xlat tables and GIC driver are initialized by this function.
 */
int plat_cmn_setup(unsigned long x0, unsigned long x1,
		   unsigned long x2, unsigned long x3,
		   struct xlat_mmap_region *plat_regions)
{
	int ret;
	struct xlat_mmap_region empty_mmap_region = {0};
	struct xlat_mmap_region *mmap_ptr;
	unsigned int region;

	/*
	 * xlat library might modify the memory mappings
	 * to optimize it, so don't make this constant.
	 */
	struct xlat_mmap_region runtime_regions[
					PLAT_CMN_MAX_MMAP_REGIONS + 1U] = {
		RMM_CODE,
		RMM_RO,
		RMM_RW,
		RMM_SHARED,
		{0}
	};

	assert(plat_regions != NULL);

	/* Initialize the RMM <-> EL3 interface */
	ret = rmm_el3_ifc_init(x0, x1, x2, x3, RMM_SHARED_BUFFER_START);
	if (ret != 0) {
		ERROR("%s (%u): Failed to initialize the RMM EL3 Interface\n",
		      __func__, __LINE__);
		return ret;
	}

	/* Setup the parameters of the shared area */
	runtime_regions[3].base_pa = rmm_el3_ifc_get_shared_buf_pa();
	runtime_regions[3].size = rmm_el3_ifc_get_shared_buf_size();

	/* Append the platform mmap regions to the list of runtime ones */
	region = CURRENT_REGIONS;
	mmap_ptr = &runtime_regions[region];
	while (memcmp((void *)plat_regions, (void *)&empty_mmap_region,
				sizeof (struct xlat_mmap_region)) != 0) {
		if (region >= PLAT_CMN_MAX_MMAP_REGIONS) {
			ERROR("%s (%u): Insufficient space for mmap regions\n",
				__func__, __LINE__);
			return -ENOMEM;
		}
		memcpy((void *)mmap_ptr, (void *)plat_regions,
				sizeof(struct xlat_mmap_region));
		plat_regions++;
		mmap_ptr++;
		region++;
	}

	ret = xlat_ctx_cfg_init(&runtime_xlat_ctx_cfg, VA_LOW_REGION,
				&runtime_regions[0], VIRT_ADDR_SPACE_SIZE);

	if (ret != 0) {
		ERROR("%s (%u): %s (%i)\n",
			__func__, __LINE__,
			"Failed to initialize the xlat ctx within the xlat library\n",
			ret);
		return ret;
	}

	ret = xlat_ctx_init(&runtime_xlat_ctx, &runtime_xlat_ctx_cfg,
			    &runtime_tbls,
			    &runtime_s1tt[0],
			    PLAT_CMN_CTX_MAX_XLAT_TABLES);

	if (ret != 0) {
		ERROR("%s (%u): %s (%i)\n",
			__func__, __LINE__,
			"Failed to create the xlat ctx within the xlat library\n",
			ret);
		return ret;
	}

	/* Read supported GIC virtualization features and init GIC variables */
	gic_get_virt_features();

	/* Perform coold boot initialization of the slot buffer mechanism */
	return slot_buf_coldboot_init();
}

/*
 * Local PE common platform setup for RMM.
 *
 * This function will only be invoked during
 * warm boot and is expected to setup architecture and platform
 * components local to a PE executing RMM.
 */
int plat_cmn_warmboot_setup(void)
{
	int ret;

	/* Setup the MMU cfg for the low region (runtime context) */
	ret = xlat_arch_setup_mmu_cfg(&runtime_xlat_ctx);
	if (ret != 0) {
		ERROR("%s (%u): Failed to setup xlat tables for CPU[%u]\n",
			__func__, __LINE__, my_cpuid());
		return ret;
	}

	/* Setup the MMU cfg for the slot buffer context (high region) */
	slot_buf_setup_xlat();

	VERBOSE("xlat tables configured for CPU[%u]\n", my_cpuid());
	return 0;
}
