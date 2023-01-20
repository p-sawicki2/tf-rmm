/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef ST1_XLAT_TEST_HELPERS_H
#define ST1_XLAT_TEST_HELPERS_H

#include <arch_helpers.h>
#include <xlat_contexts.h>
#include <xlat_defs.h>

/* Needed to configure different supported PA ranges */
DEFINE_SYSREG_WRITE_FUNC(id_aa64mmfr0_el1);

/*
 * Helper function to initialize a xlat_ctx_tbls structure with
 * a given set of parameters.
 *
 * Note that this function expects valid ranges, so no checks
 * are done on any of the arguments.
 */
void st1_xlat_test_helpers_init_ctx_tbls(struct xlat_ctx_tbls *ctx_tbls,
					 uint64_t *tbls,
					 unsigned int tables_num,
					 unsigned int next_table,
					 bool initialized);

/*
 * Helper function to initialize a xlat_ctx_cfg structure with
 * a given set of parameters.
 *
 * Note that this function expects valid ranges, so no checks
 * are done on any of the arguments.
 */
void st1_xlat_test_helpers_init_ctx_cfg(struct xlat_ctx_cfg *ctx_cfg,
					uintptr_t max_va_size,
					uintptr_t base_va,
					uintptr_t max_mapped_pa,
					uintptr_t max_mapped_va_offset,
					unsigned int base_level,
					xlat_addr_region_id_t region,
					struct xlat_mmap_region *mm,
					unsigned int mmaps,
					bool initialized);

/*
 * Helper function to initialize a xlat_ctx structure with
 * a given set of parameters.
 *
 * Note that this function expects valid ranges, so no checks
 * are done on any of the arguments.
 */
void st1_xlat_test_helpers_init_ctx(struct xlat_ctx *ctx,
				    struct xlat_ctx_cfg *cfg,
				    struct xlat_ctx_tbls *tbls);

/*
 * Helper function to perform any system register initialization
 * needed for the tests.
 */
void st1_xlat_test_helpers_init_registers(void);

/*
 * Helper function to perform a table walk given a VA.
 * This function returns the tte for the VA, as well as the
 * look-up level and the index of the tte within the block/page.
 */
int st1_xlat_test_helpers_table_walk(struct xlat_ctx *ctx,
				     unsigned long long va,
				     uint64_t *tte,
				     unsigned int *level,
				     unsigned int *index);

/*
 * Helper function to generate the lower and upper attributes as expected
 * to be in a block/page tte given a VA and a translation context.
 *
 * This function returns 0 if the attributes can be generated and a negative
 * error code otherwise.
 *
 * This function assumes that the context is valid and properly initialized.
 */
int st1_xlat_test_helpers_gen_attrs(struct xlat_ctx *ctx,
				    unsigned long long va,
				    uint64_t *attrs);

#endif /* ST1_XLAT_TEST_HELPERS_H */
