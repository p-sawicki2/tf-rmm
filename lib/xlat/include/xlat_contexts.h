/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 * SPDX-FileCopyrightText: Copyright Arm Limited and Contributors.
 */

/* This file is derived from xlat_table_v2 library in TF-A project */

#ifndef XLAT_CONTEXTS_H
#define XLAT_CONTEXTS_H

#ifndef __ASSEMBLER__

#include <assert.h>
#include <stdbool.h>
#include <stddef.h>
#include <utils_def.h>
#include <xlat_defs.h>

/* Forward declaration */
struct xlat_mmap_region;

/* Enumerator to identify the right address space within a context */
typedef enum xlat_addr_region_id {
	VA_LOW_REGION = 0,
	VA_HIGH_REGION,
	VA_REGIONS
} xlat_addr_region_id_t;

/*
 * Structure to hold all the xlat tables and related information within a
 * context. This allows to reuse the same xlat_ctx_cfg part of the context
 * on several PEs that share the same memory map region whilst keeping
 * private tables for each PE.
 */
struct xlat_ctx_tbls {
	/*
	 * Array of finer-grain translation tables.
	 * For example, if the initial lookup level is 1 then this array would
	 * contain both level-2 and level-3 entries.
	 */
	uint64_t (*tables)[XLAT_TABLE_ENTRIES];
	unsigned int tables_num;
	unsigned int next_table;

	/*
	 * Base translation table.
	 * It has the same number of entries as the ones used for other levels
	 * although it is possible that not all the entries are used.
	 *
	 * If, as an example, the translation tables for the current context
	 * start at L1, then the *tables field will contain the L2 and L3
	 * tables.
	 */
	uint64_t *base_table;
	unsigned int max_base_table_entries;

	/* Set to true when the translation tables are initialized. */
	bool initialized;
};

/* Struct that holds the context configuration */
struct xlat_ctx_cfg {
	/*
	 * Maximum size allowed for the VA space handled by the context.
	 */
	uintptr_t max_va_size;

	/*
	 * Array of all memory regions stored in order of ascending base_va.
	 * The list is terminated by the first entry with
	 * size == 0 or when all entries are used (as specified by mmap_num).
	 */
	struct xlat_mmap_region *mmap;
	unsigned int mmap_num;

	/*
	 * Base address for the virtual space on this context.
	 */
	uintptr_t base_va;

	/*
	 * Max Physical and Virtual addresses currently in use by the
	 * current context. These will get updated as we map memory
	 * regions but it will never go beyond the maximum physical address
	 * or max_va_size respectively.
	 *
	 * max_mapped_pa is an absolute Physical Address.
	 */
	uintptr_t max_mapped_pa;
	uintptr_t max_mapped_va_offset;

	/* Level of the base translation table. */
	unsigned int base_level;

	/*
	 * Virtual address region handled by this context.
	 */
	xlat_addr_region_id_t region;

	bool initialized;
};

/*
 * Struct that holds the context itself, composed of
 * a pointer to the context config and a pointer to the
 * translation tables associated to it.
 */
struct xlat_ctx {
	struct xlat_ctx_cfg *cfg;
	struct xlat_ctx_tbls *tbls;
};

/*
 * The translation tables are aligned to their size. For 4KB graularity, this
 * is aligned to 4KB as well.
 */
#define XLAT_TABLES_ALIGNMENT		XLAT_TABLE_SIZE

/*
 * Compute the number of entries required at the initial lookup level to
 * address the whole virtual address space.
 */
#define GET_NUM_BASE_LEVEL_ENTRIES(addr_space_size)			\
	((addr_space_size) >>						\
		XLAT_ADDR_SHIFT(GET_XLAT_TABLE_LEVEL_BASE(addr_space_size)))

/*
 * Macro to check if the xlat_ctx_cfg part of a context is valid.
 */
#define XLAT_TABLES_CTX_CFG_VALID(_ctx)	((_ctx)->cfg != NULL)

/*
 * Macro to check if the xlat_ctx_tbls part of a context is valid.
 */
#define XLAT_TABLES_CTX_TBL_VALID(_ctx)		((_ctx)->tbls != NULL)

/*
 * Macro to calculate the size of a memory buffer able to contain all the
 * translation tables for a context.
 */
#define XLAT_TABLES_CTX_BUF_SIZE(_tables)				\
		((size_t)(XLAT_TABLE_SIZE * ((_tables) + 1U)))

/*
 * Function to generate a set of empty translation tables and initialize
 * a translation context with them.
 *
 * Arguments:
 *	- buf:	Memory area where the tables will be initialized.
 *	- buf_size: Size of the `buf` memory area.
 *	- t_count: Number of tables to initialize. This does not take
 *		   into account the base table.
 *	- tbls_ctx: Pointer to a xlat_ctx_tbls structure with the tables
 *	       context to be initialized.
 *
 * Return:
 *	- 0 on success or a negative POSIX error otherwise.
 *
 * NOTE: This function does not perform any zeroing or cleaning of the
 *	 allocated translation tables.
 */
int xlat_ctx_allocate_tables(uintptr_t buf, size_t buf_size,
			     unsigned int t_count,
			     struct xlat_ctx_tbls *tbls_ctx);

/*
 * Function to initialize the configuration structure for a
 * translation context.
 *
 * Arguments:
 *	- cfg: Pointer to a xlat_ctx_cfg structure to initialize.
 *	- region: xlat_addr_region_id_t descriptor indicating the memory
 *		  region for the configured context.
 *	- mmap: Pointer to an array of xlat_mmap_region structures.
 *	- mmap_count: Number of mmap regions to be stored on the current
 *		      context.
 *	- va_size: Size of the VA space for the current context.
 *
 * Return:
 *	- 0 on success or a negative POSIX error otherwise.
 */
int xlat_ctx_init_config(struct xlat_ctx_cfg *cfg,
			 xlat_addr_region_id_t region,
			 struct xlat_mmap_region *mmap,
			 unsigned int mmap_count,
			 size_t va_size);

/*
 * Function to initialize a context along with its configuration and
 * associate the translation table set passed to it.
 *
 * Arguments:
 *	- ctx: Pointer to the empty translation context to generate.
 *	- cfg: Pointer to the translation context configuration structure.
 *	- tbls_ctx: Pointer to a xlat_ctx_tbls structure with the tables
 *	       context already setup.
 *	- region: xlat_addr_region_id_t descriptor indicating the memory
 *		  region for the configured context.
 *	- mmap: Pointer to an array of xlat_mmap_region structures.
 *	- mmap_count: Number of mmap regions to be stored on the current
 *		      context.
 *	- va_size: Size of the VA space for the current context.
 *
 * Return:
 *	- 0 on success or a negative POSIX error otherwise.
 */
int xlat_ctx_register_context(struct xlat_ctx *ctx,
			      struct xlat_ctx_cfg *cfg,
			      struct xlat_ctx_tbls *tbls_ctx,
			      xlat_addr_region_id_t region,
			      struct xlat_mmap_region *mmap,
			      unsigned int mmap_count,
			      size_t va_size);

/*
 * Setup a given translation context with a given configuration and
 * set of translation tables
 *
 * Arguments:
 *	- ctx: Pointer to the translation context to generate.
 *	- cfg: Pointer to the structure containing the context configuration.
 *	- tbls_ctx: Pointer to a tables structure to configure the associated
 *		    table data for the translation context.
 *	- base_table: Pointer to the base table for the given context.
 *	- base_level_entries: Maximum number of entries on the base table.
 *	- tables_ptr: Pointer to the intermediate translation tables for the
 *		      given context.
 *	-ntables: Number of intermediate tables.
 */
int xlat_ctx_setup_context(struct xlat_ctx *ctx,
			   struct xlat_ctx_cfg *cfg,
			   struct xlat_ctx_tbls *tbls_ctx,
			   uint64_t *base_table,
			   unsigned int base_level_entries,
			   uint64_t *tables_ptr,
			   unsigned int ntables);

/*
 * Return true if the xlat_ctx_cfg field in the xlat_ctx is initialized.
 */
bool xlat_ctx_cfg_initialized(const struct xlat_ctx * const ctx);

/*
 * Return true if the translation tables on the current context are already
 * initialized or false otherwise.
 */
bool xlat_ctx_tbls_initialized(const struct xlat_ctx * const ctx);

#endif /*__ASSEMBLER__*/
#endif /* XLAT_CONTEXTS_H */
