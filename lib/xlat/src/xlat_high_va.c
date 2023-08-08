/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <cpuid.h>
#include <debug.h>
#include <errno.h>
#include <import_sym.h>
#include <plat_common.h>
#include <sizes.h>
#include <stdint.h>
#include <string.h>
#include <utils_def.h>
#include <xlat_contexts.h>
#include <xlat_tables.h>

#define RMM_SLOT_BUF_SIZE	((NUM_OF_SLOT) * (GRANULE_SIZE))

#define RMM_SLOT_BUF_MMAP	MAP_REGION_TRANSIENT(		\
					SLOT_VIRT,		\
					RMM_SLOT_BUF_SIZE,	\
					PAGE_SIZE)

#define STACK_ATTR		(MT_RW_DATA | MT_NG)

/* Leave some pages of gap above the stack top */
#define GAP_PAGE_COUNT		1U
#define CPU_STACK_GAP		(GAP_PAGE_COUNT * PAGE_SIZE)

#define CPU_STACK_SIZE		(RMM_NUM_PAGES_PER_STACK * PAGE_SIZE)

#define RMM_STACK_MMAP		MAP_REGION_FULL_SPEC(			\
				0, /* PA is different for each CPU */	\
				0, /* VA is calculated based on slot buf VA */ \
				CPU_STACK_SIZE,				\
				STACK_ATTR,				\
				PAGE_SIZE)

#define MMAP_REGION_COUNT	2U

/*
 * A single L3 page is used to map the slot buffers as well as the stack, so
 * enforce here that they fit within that L3 page.
 */
COMPILER_ASSERT(RMM_NUM_PAGES_PER_STACK + GAP_PAGE_COUNT + NUM_OF_SLOT <= XLAT_TABLE_ENTRIES);

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
	memcpy(&(dest_array[index]),
	       src,
	       sizeof(struct xlat_mmap_region));
}

/*
 * The layout of the High VA space:
 *
 * +-----------------+  0xFFFFFFFFFFFFFFFF (VA max)
 * |                 |
 * |   Slot buffer   |  NUM_OF_SLOT * GRANULE_SIZE bytes
 * |                 |
 * +-----------------+
 * |                 |
 * |   Stack guard   |  CPU_STACK_GAP bytes, Unmapped
 * |                 |
 * +-----------------+
 * |                 |
 * |    RMM stack    |  CPU_STACK_SIZE bytes,
 * |                 |
 * +-----------------+
 * |                 |
 * |     Unmapped    |
 * |                 |
 * +-----------------+  0x0FFFFFFFFFFFFFFF
*/

int xlat_high_va_context_init(void)
{
	static struct xlat_mmap_region
		mm_regions_array[MAX_CPUS][MMAP_REGION_COUNT];
	struct xlat_mmap_region rmm_slot_buf_mmap = RMM_SLOT_BUF_MMAP;
	struct xlat_mmap_region rmm_stack_mmap = RMM_STACK_MMAP;
	unsigned int cpuid = my_cpuid();
	uintptr_t slot_buffer_va;
	uintptr_t stack_va;
	size_t index = 0;

	slot_buffer_va = rmm_slot_buf_mmap.base_va;
	stack_va = slot_buffer_va - CPU_STACK_GAP - CPU_STACK_SIZE;

	cpu_stack_bottom_va =
		stack_va + (RMM_NUM_PAGES_PER_STACK * GRANULE_SIZE);

	/* Set stack VA for this CPU */
	rmm_stack_mmap.base_pa = plat_get_rmm_stack_end() - (cpuid + 1U) * CPU_STACK_SIZE;
	rmm_stack_mmap.base_va = stack_va;

	copy_to_region(mm_regions_array[cpuid], index++, &rmm_stack_mmap);
	copy_to_region(mm_regions_array[cpuid], index++, &rmm_slot_buf_mmap);

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
void xlat_high_va_setup(void)
{
	unsigned int cpuid = my_cpuid();

	/*
	 * Initialize the translation tables for the current context.
	 * This is done on the first boot of each PE.
	 */
	int ret = xlat_ctx_init(&high_va_xlat_ctx[cpuid],
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
	if (xlat_arch_setup_mmu_cfg(&high_va_xlat_ctx[cpuid])) {
		ERROR("%s (%u): MMU registers failed to initialize\n",
					__func__, __LINE__);
		panic();
	}
}