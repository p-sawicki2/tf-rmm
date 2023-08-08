/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <cpuid.h>
#include <debug.h>
#include <errno.h>
#include <import_sym.h>
#include <sizes.h>
#include <stdint.h>
#include <string.h>
#include <utils_def.h>
#include <xlat_contexts.h>
#include <xlat_high_va.h>
#include <xlat_tables.h>

#define RMM_SLOT_BUF_SIZE	((XLAT_HIGH_VA_SLOT_NUM) * (GRANULE_SIZE))

#define RMM_SLOT_BUF_MMAP	MAP_REGION_TRANSIENT(		\
					SLOT_VIRT,		\
					RMM_SLOT_BUF_SIZE,	\
					PAGE_SIZE)

#define STACK_ATTR		(MT_RW_DATA | MT_NG)

#define RMM_STACK_MMAP		MAP_REGION_FULL_SPEC(			\
				0, /* PA is different for each CPU */	\
				0, /* VA is calculated based on slot buf VA */ \
				RMM_CPU_STACK_SIZE,				\
				STACK_ATTR,				\
				PAGE_SIZE)

#define MMAP_REGION_COUNT	2U

/*
 * All the slot buffers for a given PE must be mapped by a single translation
 * table, which means the max VA size should be <= 4KB * 512
 */
COMPILER_ASSERT(XLAT_HIGH_VA_SLOT_NUM <= XLAT_TABLE_ENTRIES);

/*
 * A single L3 page is used to map the slot buffers as well as the stack, so
 * enforce here that they fit within that L3 page.
 */
COMPILER_ASSERT((RMM_NUM_PAGES_PER_STACK + GAP_PAGE_COUNT + XLAT_HIGH_VA_SLOT_NUM) <=
	XLAT_TABLE_ENTRIES);

/* context definition */
static struct xlat_ctx high_va_xlat_ctx[MAX_CPUS];

struct xlat_ctx *xlat_get_high_va_xlat_ctx(void)
{
	return &high_va_xlat_ctx[my_cpuid()];
}

static void copy_to_region(
	struct xlat_mmap_region dest_array[MMAP_REGION_COUNT],
	unsigned int index,
	struct xlat_mmap_region *src)
{
	assert(index < MMAP_REGION_COUNT);
	(void)memcpy(&(dest_array[index]), src, sizeof(struct xlat_mmap_region));
}

/*
 * Setup xlat table for the high VA region for each PE.
 * Must be called for every PE in the system.
 * The layout of the High VA space:
 *
 * +-----------------+  0xFFFFFFFFFFFFFFFF (VA max)
 * |                 |
 * |   Slot buffer   |  XLAT_HIGH_VA_SLOT_NUM * GRANULE_SIZE bytes
 * |                 |
 * +-----------------+
 * |                 |
 * |   Stack guard   |  CPU_STACK_GAP bytes, Unmapped
 * |                 |
 * +-----------------+
 * |                 |
 * |    RMM stack    |  RMM_CPU_STACK_SIZE bytes,
 * |                 |
 * +-----------------+
 * |                 |
 * |     Unmapped    |
 * |                 |
 * +-----------------+  0x0FFFFFFFFFFFFFFF
 */
void xlat_high_va_setup(void)
{
	/* Allocate xlat_ctx_cfg for high VA which will be specific to PEs */
	static struct xlat_ctx_cfg high_va_xlat_ctx_cfgs[MAX_CPUS];
	/* Allocate per-cpu xlat_ctx_tbls */
	static struct xlat_ctx_tbls high_va_tbls[MAX_CPUS];
	/* Allocate xlat_mmap_region for high VA mappings which will be specific to PEs */
	static struct xlat_mmap_region mm_regions_array[MAX_CPUS][MMAP_REGION_COUNT];
	/*
	 * The base tables for all the contexts are manually allocated as a continuous
	 * block of memory (one L3 table per PE).
	 */
	static uint64_t high_va_tts[XLAT_TABLE_ENTRIES * MAX_CPUS] __aligned(XLAT_TABLES_ALIGNMENT);

	struct xlat_mmap_region rmm_slot_buf_mmap = RMM_SLOT_BUF_MMAP;
	struct xlat_mmap_region rmm_stack_mmap = RMM_STACK_MMAP;
	unsigned int cpuid = my_cpuid();
	unsigned int index = 0;
	int ret;

	/* Set stack PA and VA for this CPU */
	rmm_stack_mmap.base_pa = rmm_get_my_stack(cpuid) - RMM_CPU_STACK_SIZE;
	rmm_stack_mmap.base_va = CPU_STACK_VIRT;

	copy_to_region(mm_regions_array[cpuid], index++, &rmm_stack_mmap);
	copy_to_region(mm_regions_array[cpuid], index++, &rmm_slot_buf_mmap);

	/* Initialize the context configuration for this CPU */
	ret = xlat_ctx_cfg_init(&high_va_xlat_ctx_cfgs[cpuid], VA_HIGH_REGION,
				 &mm_regions_array[cpuid][0U],
				 index,
				 XLAT_TABLE_ENTRIES * PAGE_SIZE);
	if (!((ret == 0) || (ret == -EALREADY))) {
		ERROR("%s (%u): Failed to setup high va xlat tables for CPU[%u]. ret=%d\n",
			__func__, __LINE__, cpuid, ret);
		panic();
	}

	/*
	 * Initialize the translation tables for the current context.
	 * This is done on the first boot of each PE.
	 */
	ret = xlat_ctx_init(&high_va_xlat_ctx[cpuid],
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
	if (xlat_arch_setup_mmu_cfg(&high_va_xlat_ctx[cpuid]) != 0) {
		ERROR("%s (%u): MMU registers failed to initialize\n",
					__func__, __LINE__);
		panic();
	}
}
