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
#include <plat_cmn_arch.h>
#include <plat_common.h>
#include <rmm_el3_ifc.h>
#include <sizes.h>
#include <stdint.h>
#include <string.h>
#include <utils_def.h>
#include <xlat_contexts.h>
#include <xlat_tables.h>


IMPORT_SYM(uintptr_t, rmm_text_start, RMM_CODE_START);
IMPORT_SYM(uintptr_t, rmm_text_end, RMM_CODE_END);
IMPORT_SYM(uintptr_t, rmm_ro_start, RMM_RO_START);
IMPORT_SYM(uintptr_t, rmm_ro_end, RMM_RO_END);
IMPORT_SYM(uintptr_t, rmm_rw_start, RMM_RW_START);
IMPORT_SYM(uintptr_t, rmm_rw_flat_end, RMM_RW_FLAT_END);
IMPORT_SYM(uintptr_t, rmm_stack_end, RMM_STACK_END);
IMPORT_SYM(uintptr_t, rmm_handler_stack_end, RMM_HANDLER_STACK_END);

/*
 * Memory map REGIONS used for the RMM runtime (static mappings)
 */
#define RMM_CODE_SIZE		(RMM_CODE_END - RMM_CODE_START)
#define RMM_RO_SIZE		(RMM_RO_END - RMM_RO_START)
#define RMM_RW_FLAT_SIZE	(RMM_RW_FLAT_END - RMM_RW_START)

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
					RMM_RW_FLAT_SIZE,		\
					MT_RW_DATA | MT_REALM)

/*
 * Leave an invalid page between the end of RMM memory and the beginning
 * of the shared buffer VA. This will help to detect any memory access
 * underflow by RMM.
 */
#define RMM_SHARED_BUFFER_START	(RMM_RW_FLAT_END + SZ_4K)

/*
 * Some of the fields for the RMM_SHARED region will be populated
 * at runtime.
 */
#define RMM_SHARED		MAP_REGION(				\
					0U,				\
					RMM_SHARED_BUFFER_START,	\
					0U,				\
					MT_RW_DATA | MT_REALM)

/* Number of common memory mapping regions */
#define COMMON_REGIONS		(4U)

/* Total number of memory mapping regions */
#define TOTAL_MMAP_REGIONS	(COMMON_REGIONS + PLAT_CMN_EXTRA_MMAP_REGIONS)

#define STACK_ATTR		(MT_RW_DATA | MT_NG)

/* Leave some pages of gap above the stack top */
#define GAP_PAGE_COUNT		1U
#define CPU_STACK_GAP		(GAP_PAGE_COUNT * PAGE_SIZE)

#define RMM_STACK_MMAP		MAP_REGION_FULL_SPEC(			\
				0, /* PA is different for each CPU */	\
				0, /* VA is calculated based on slot buf VA */ \
				CPU_STACK_SIZE,				\
				STACK_ATTR,				\
				PAGE_SIZE)

/*
 * This mapping is used for the stack that is used by the exception handler when
 * a synchronous exception is taken.
 */
#define RMM_HANDLER_STACK_MMAP	MAP_REGION_FULL_SPEC(			\
				0, /* PA is different for each CPU */	\
				0, /* VA is calculated based on slot buf VA */ \
				GRANULE_SIZE,				\
				STACK_ATTR,				\
				PAGE_SIZE)

#define MMAP_REGION_COUNT	3U

/* Memory mapping regions for the system runtime */
static struct xlat_mmap_region static_regions[TOTAL_MMAP_REGIONS];

/*
 * Allocate the runtime translation tables.
 * Although a base table at level -1 when FEAT_LPA2 is enabled only has
 * 16 entries, all tables are allocated a page for simplicity.
 */
static uint64_t static_s1tt[XLAT_TABLE_ENTRIES * PLAT_CMN_CTX_MAX_XLAT_TABLES]
					__aligned(XLAT_TABLES_ALIGNMENT)
					__section("xlat_static_tables");

/* Structures to hold the runtime translation context information  */
static struct xlat_ctx_tbls runtime_tbls;
static struct xlat_ctx_cfg runtime_xlat_ctx_cfg;
static struct xlat_ctx runtime_xlat_ctx;

/*
 * The base tables for all the contexts are manually allocated as a continuous
 * block of memory (one L3 table per PE).
 */
static uint64_t high_va_tts[XLAT_TABLE_ENTRIES * MAX_CPUS]
				__aligned(XLAT_TABLES_ALIGNMENT);

/* Allocate per-cpu xlat_ctx_tbls */
static struct xlat_ctx_tbls high_va_tbls[MAX_CPUS];

/* Allocate xlat_ctx_cfg for high VA which will be specific to PEs */
static struct xlat_ctx_cfg high_va_xlat_ctx_cfgs[MAX_CPUS];

/* context definition */
static struct xlat_ctx high_va_xlat_ctx[MAX_CPUS];

/*
 * Global symbol set by the C code
 * The stack bottom VA is calculated using CLZ operation which is not supported
 * by the preprocessor. So the C code sets the address in this variable, and
 * the assembly init function loads it from here when setting SP to the stack
 * VA.
 */
uintptr_t cpu_stack_bottom_va;
/*
 * The bottom of the stack that is used by the exception handler when a
 * synchronous exception is taken.
 */
uintptr_t cpu_handler_stack_bottom_va;

/*
 * Platform common cold boot setup for RMM.
 *
 * This function should only be invoked once during cold boot
 * and is expected to setup architecture and platform components
 * common for all PEs executing RMM. The rmm_el3_ifc, the xlat tables
 * and GIC driver are initialized by this function.
 */
int plat_cmn_setup(unsigned long x0, unsigned long x1,
		   unsigned long x2, unsigned long x3,
		   struct xlat_mmap_region *plat_regions,
		   unsigned int nregions)
{
	int ret;
	unsigned int plat_offset, cmn_offset;

	/* Common regions sorted by ascending VA */
	struct xlat_mmap_region regions[COMMON_REGIONS] = {
		RMM_CODE,
		RMM_RO,
		RMM_RW,
		RMM_SHARED
	};

	if (nregions > PLAT_CMN_EXTRA_MMAP_REGIONS) {
		return -ERANGE;
	}

	if (nregions > 0U && plat_regions == NULL) {
		return -EINVAL;
	}

	/* Initialize the RMM <-> EL3 interface */
	ret = rmm_el3_ifc_init(x0, x1, x2, x3, get_shared_buf_va(x3));
	if (ret != 0) {
		ERROR("%s (%u): Failed to initialize the RMM EL3 Interface\n",
		      __func__, __LINE__);
		return ret;
	}

	/* Setup the parameters of the shared area */
	regions[3].base_pa = get_shared_buf_pa();
	regions[3].size = rmm_el3_ifc_get_shared_buf_size();

	plat_offset = COMMON_REGIONS;
	cmn_offset = 0U;
	if (nregions > 0U) {
		/*
		 * Combine the common memory regions with the platform ones
		 * in an array where they are sorted as per VA.
		 */
		if (plat_regions[0].base_va < RMM_CODE_START) {
			plat_offset = 0U;
			cmn_offset = nregions;
		}
		(void)memcpy((void *)&static_regions[plat_offset],
			     (void *)&plat_regions[0U],
			     sizeof(struct xlat_mmap_region) * nregions);
	}

	(void)memcpy((void *)&static_regions[cmn_offset], (void *)&regions[0U],
		     sizeof(struct xlat_mmap_region) * COMMON_REGIONS);

	ret = xlat_ctx_cfg_init(&runtime_xlat_ctx_cfg, VA_LOW_REGION,
				&static_regions[0], nregions + COMMON_REGIONS,
				VIRT_ADDR_SPACE_SIZE);

	if (ret != 0) {
		ERROR("%s (%u): %s (%i)\n",
			__func__, __LINE__,
			"Failed to initialize the xlat ctx within the xlat library ",
			ret);
		return ret;
	}

	ret = xlat_ctx_init(&runtime_xlat_ctx, &runtime_xlat_ctx_cfg,
			    &runtime_tbls,
			    &static_s1tt[0],
			    PLAT_CMN_CTX_MAX_XLAT_TABLES);

	if (ret != 0) {
		ERROR("%s (%u): %s (%i)\n",
			__func__, __LINE__,
			"Failed to create the xlat ctx within the xlat library ",
			ret);
		return ret;
	}

	/* Read supported GIC virtualization features and init GIC variables */
	gic_get_virt_features();

	return 0;
}

static void copy_to_region(
	struct xlat_mmap_region dest_array[MMAP_REGION_COUNT],
	unsigned int index,
	struct xlat_mmap_region *src)
{
	assert(index < MMAP_REGION_COUNT);
	memcpy(&(dest_array[index]),
	       src,
	       sizeof(struct xlat_mmap_region));
}

/* inline */ struct xlat_ctx *get_high_va_xlat_ctx(void)
{
	return &high_va_xlat_ctx[my_cpuid()];
}

static int high_va_warmboot_init(void)
{
	static struct xlat_mmap_region
		mm_regions_array[MAX_CPUS][MMAP_REGION_COUNT];
	struct xlat_mmap_region rmm_slot_buf_mmap;
	struct xlat_mmap_region rmm_stack_mmap = RMM_STACK_MMAP;
	struct xlat_mmap_region rmm_handler_stack_mmap = RMM_HANDLER_STACK_MMAP;
	unsigned int cpuid = my_cpuid();
	uintptr_t slot_buffer_va;
	uintptr_t stack_va;
	uintptr_t handler_stack_va;
	size_t index = 0;

	slot_buf_get_mmap(&rmm_slot_buf_mmap);

	slot_buffer_va = rmm_slot_buf_mmap.base_va;
	stack_va = slot_buffer_va - CPU_STACK_GAP - CPU_STACK_SIZE;
	handler_stack_va = stack_va - CPU_STACK_GAP - GRANULE_SIZE;

	cpu_stack_bottom_va =
		stack_va + CPU_STACK_SIZE;
	cpu_handler_stack_bottom_va =
		handler_stack_va + GRANULE_SIZE;

	/* Set stack VA for this CPU */
	rmm_stack_mmap.base_pa = RMM_STACK_END - (cpuid + 1U) * CPU_STACK_SIZE;
	rmm_stack_mmap.base_va = stack_va;
	rmm_handler_stack_mmap.base_pa = RMM_HANDLER_STACK_END - (cpuid + 1U) * GRANULE_SIZE;
	rmm_handler_stack_mmap.base_va = handler_stack_va;

	copy_to_region(mm_regions_array[cpuid], index++, &rmm_handler_stack_mmap);
	copy_to_region(mm_regions_array[cpuid], index++, &rmm_stack_mmap);
	copy_to_region(mm_regions_array[cpuid], index++, &rmm_slot_buf_mmap);

	/*
	 * A single L3 page is used to map the slot buffers as well as the stacks, so
	 * enforce here that they fit within that L3 page.
	 */
	assert((~0LU - mm_regions_array[cpuid][0U].base_va + 1) / PAGE_SIZE <= XLAT_TABLE_ENTRIES);

	/* Initialize the context configuration for this CPU */
	return xlat_ctx_cfg_init(&high_va_xlat_ctx_cfgs[cpuid], VA_HIGH_REGION,
				 &mm_regions_array[cpuid][0U],
				 index,
				 XLAT_TABLE_ENTRIES * PAGE_SIZE);
}

/*
 * Setup xlat table for the high VA region for each PE.
 * Must be called for every PE in the system
 */
void high_va_setup_xlat(void)
{
	unsigned int cpuid = my_cpuid();
	struct xlat_ctx *high_va_ctx = get_high_va_xlat_ctx();

	/*
	 * Initialize the translation tables for the current context.
	 * This is done on the first boot of each PE.
	 */
	int ret = xlat_ctx_init(high_va_ctx,
				&high_va_xlat_ctx_cfgs[cpuid],
				&high_va_tbls[cpuid],
				&high_va_tts[XLAT_TABLE_ENTRIES * cpuid], 1U);

	if (!((ret == 0) || (ret == -EALREADY))) {
		/*
		 * If the context was already created, carry on with the
		 * initialization. If it cannot be created, panic.
		 */
		ERROR("%s (%u): Failed to initialize xlat context for the high VA region (-%i)\n",
					__func__, __LINE__, ret);
		panic();
	}

	/* Configure MMU registers */
	if (xlat_arch_setup_mmu_cfg(get_high_va_xlat_ctx())) {
		ERROR("%s (%u): MMU registers failed to initialize\n",
					__func__, __LINE__);
		panic();
	}
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

	/* Perform warm boot initialization of the high VA region */
	ret = high_va_warmboot_init();
	if (!((ret == 0) || (ret == -EALREADY))) {
		ERROR("%s (%u): Failed to setup high va xlat tables for CPU[%u]. ret=%d\n",
			__func__, __LINE__, my_cpuid(), ret);
		return ret;
	}

	/* Setup the MMU cfg for the high region */
	high_va_setup_xlat();

	VERBOSE("xlat tables configured for CPU[%u]\n", my_cpuid());
	return 0;
}
