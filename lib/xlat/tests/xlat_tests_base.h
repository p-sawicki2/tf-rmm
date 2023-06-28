/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <CppUTest/CommandLineTestRunner.h>
#include <CppUTest/TestHarness.h>

extern "C" {
#include <xlat_contexts.h>	/* API to test */
#include <xlat_tables.h>	/* API to test */
}

TEST_BASE(xlat_tests_base) {

	protected:

		void setup(bool lpa2);

		void map_region_full_spec_tc1(void);

		void map_region_tc1(void);

		void map_region_flat_tc1(void);

		void map_region_transient_tc1(void);

		void xlat_ctx_cfg_init_tc1(void);
		void xlat_ctx_cfg_init_tc2(void);
		void xlat_ctx_cfg_init_tc3(void);
		void xlat_ctx_cfg_init_tc4(void);
		void xlat_ctx_cfg_init_tc5(void);
		void xlat_ctx_cfg_init_tc6(void);
		void xlat_ctx_cfg_init_tc7(void);
		void xlat_ctx_cfg_init_tc8(void);
		void xlat_ctx_cfg_init_tc9(void);
		void xlat_ctx_cfg_init_tc10(void);
		void xlat_ctx_cfg_init_tc11(void);
		void xlat_ctx_cfg_init_tc12(void);

		void xlat_ctx_init_tc1(void);
		void xlat_ctx_init_tc2(void);
		void xlat_ctx_init_tc3(void);
		void xlat_ctx_init_tc4(void);
		void xlat_ctx_init_tc5(void);
		void xlat_ctx_init_tc6(void);

		void xlat_get_llt_from_va_tc1(void);
		void xlat_get_llt_from_va_tc2(void);
		void xlat_get_llt_from_va_tc3(void);
		void xlat_get_llt_from_va_tc4(void);
		void xlat_get_llt_from_va_tc5(void);
		void xlat_get_llt_from_va_tc6(void);
		void xlat_get_llt_from_va_tc7(void);
		void xlat_get_llt_from_va_tc8(void);
		void xlat_get_llt_from_va_tc9(void);

		void xlat_get_tte_ptr_tc1(void);
		void xlat_get_tte_ptr_tc2(void);
		void xlat_get_tte_ptr_tc3(void);
		void xlat_get_tte_ptr_tc4(void);

		void xlat_unmap_memory_page_tc1(void);
		void xlat_unmap_memory_page_tc2(void);
		void xlat_unmap_memory_page_tc3(void);

		void xlat_map_memory_page_with_attrs_tc1(void);
		void xlat_map_memory_page_with_attrs_tc2(void);
		void xlat_map_memory_page_with_attrs_tc3(void);

		void xlat_arch_setup_mmu_cfg_tc1(void);
		void xlat_arch_setup_mmu_cfg_tc2(void);
		void xlat_arch_setup_mmu_cfg_tc3(void);
		void xlat_arch_setup_mmu_cfg_tc4(void);
		void xlat_arch_setup_mmu_cfg_tc5(void);

		void xlat_get_oa_from_tte_tc1(void);

	private:
		void buffer_shuffle(unsigned char *buf, size_t size,
				   unsigned int stride);
		void xlat_test_cfg_init_setup(struct xlat_ctx_cfg *cfg,
					      struct xlat_mmap_region *init_mmap,
					      struct xlat_mmap_region *val_mmap,
					      unsigned int mmaps,
					      size_t va_size,
					      xlat_addr_region_id_t region);
		uint64_t gen_va_space_params_by_lvl(int level,
						    xlat_addr_region_id_t region,
						    size_t *va_size);
		int gen_mmap_array_by_level(xlat_mmap_region *mmap,
					    unsigned int *tbl_idxs,
					    unsigned int mmap_size,
					    int first_lvl,
					    int last_lvl,
					    size_t *granularity,
					    uint64_t start_va,
					    bool allow_transient);
		void validate_xlat_tables(xlat_ctx *ctx,
					  unsigned int *expected_idxs,
					  int expected_level);
		void xlat_get_llt_from_va_prepare_assertion(struct xlat_ctx *ctx,
						struct xlat_ctx_cfg *cfg,
						struct xlat_ctx_tbls *tbls,
						struct xlat_mmap_region *init_mmap);
		void validate_ttbrx_el2(struct xlat_ctx *ctx);
		void validate_tcr_el2(struct xlat_ctx *low_ctx,
				      struct xlat_ctx *high_ctx);
};