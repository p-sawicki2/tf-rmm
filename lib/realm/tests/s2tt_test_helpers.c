/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch_features.h>
#include <assert.h>
#include <errno.h>
#include <host_utils.h>
#include <limits.h>
#include <s2tt_private_defs.h>
#include <s2tt_test_helpers.h>
#include <stdlib.h>
#include <string.h>
#include <table.h>
#include <test_helpers.h>
#include <utils_def.h>

/*
 * Helper function to perform any system register initialization
 * needed for the tests.
 */
static void s2tt_test_helpers_arch_init(bool lpa2_en)
{
	unsigned int retval __unused;
	uint64_t id_aa64mmfr0_el0 = INPLACE(ID_AA64MMFR0_EL1_TGRAN4_2,
					    ID_AA64MMFR0_EL1_TGRAN4_2_TGRAN4);

	/*
	 * Enable the platform. We don't need support for several CPUs
	 * on this testsuite, so keep it disabled for simplicity.
	 */
	test_helpers_rmm_start(false);

	/*
	 * Reset the sysreg state so that we can setup
	 * custom values for the tests
	 */
	host_util_zero_sysregs_and_cbs();

	/* Setup id_aa64mmfr0_el1 */
	if (lpa2_en == true) {
		id_aa64mmfr0_el0 |= INPLACE(ID_AA64MMFR0_EL1_PARANGE, 6UL) |
				    INPLACE(ID_AA64MMFR0_EL1_TGRAN4,
					    ID_AA64MMFR0_EL1_TGRAN4_LPA2);
	} else {
		id_aa64mmfr0_el0 |= INPLACE(ID_AA64MMFR0_EL1_PARANGE, 5UL) |
				    INPLACE(ID_AA64MMFR0_EL1_TGRAN4,
					    ID_AA64MMFR0_EL1_TGRAN4_SUPPORTED);
	}

	retval = host_util_set_default_sysreg_cb("id_aa64mmfr0_el1",
						 id_aa64mmfr0_el0);

	assert(retval == 0);

	/* Make sure current cpu id is 0 (primary processor) */
	host_util_set_cpuid(0U);

	test_helpers_expect_assert_fail(false);
}

void s2tt_test_helpers_setup(bool lpa2)
{
	/* At the moment LPA2 is not supported */
	assert(lpa2 == false);

	test_helpers_init();
	s2tt_test_helpers_arch_init(lpa2);

	/*
	 * Reinitialize the s2tt component in order for the changes on
	 * FEAT_LPA2 status to be applied to the component.
	 */
	s2tt_init();
}

unsigned long s2tt_test_helpers_oa_mask(long level)
{
	assert(level >= S2TT_TEST_HELPERS_MIN_LVL);
	assert(level <= S2TT_TEST_HELPERS_MAX_LVL);

	unsigned int levels = (unsigned int)(S2TT_TEST_HELPERS_MAX_LVL - level);
	unsigned int lsb = GRANULE_SHIFT + (levels * S2TTE_STRIDE);
	unsigned int msb = max_ipa_size() - 1U;

	return BIT_MASK_ULL(msb, lsb);
}

unsigned long s2tt_test_helpers_s2tte_oa_mask(long level)
{
	return s2tt_test_helpers_oa_mask(level);
}

unsigned long s2tt_test_helpers_s2tte_to_pa(unsigned long s2tte, long level)
{
	unsigned long pa = s2tte & s2tt_test_helpers_oa_mask(level);

	return pa;
}

static unsigned long gen_pa(long level)
{
	unsigned long pa;

	do {
		pa = test_helpers_get_rand_in_range(0UL, ULONG_MAX);
		pa &= s2tt_test_helpers_oa_mask(level);
	} while (pa == 0UL);

	return pa;
}

static unsigned long gen_unaligned_pa(long level)
{
	assert(level >= S2TT_TEST_HELPERS_MIN_LVL);
	assert(level <= S2TT_TEST_HELPERS_MAX_LVL);

	unsigned int levels = S2TT_TEST_HELPERS_MAX_LVL - (unsigned int)level;
	unsigned int lsb = GRANULE_SHIFT + (levels * S2TTE_STRIDE);
	unsigned long pa;

	do {
		pa = test_helpers_get_rand_in_range((1UL << lsb), ULONG_MAX);
	} while (pa == 0UL);

	return pa;
}

unsigned long s2tt_test_helpers_gen_pa(long level, bool aligned)
{
	return ((aligned == true) ? gen_pa(level) : gen_unaligned_pa(level));
}

unsigned long s2tt_test_helpers_s2tte_to_attrs(unsigned long tte, bool ns)
{
	unsigned long attrs_mask = (ns == true) ?
				(S2TT_TEST_TTE_NS_ATTRS_MASK |
				 S2TT_TEST_TTE_HOST_NS_ATTRS_MASK):
				S2TT_TEST_TTE_ATTRS_MASK;

	return tte & attrs_mask;
}

unsigned long s2tt_test_helpers_gen_ns_attrs(bool host, bool reserved)
{
	unsigned long attrs;
	bool done;

	if (host == true) {
		/* Generate a random set of attributes comming from the host */
		do {
			bool inv_attrs;

			attrs = test_helpers_get_rand_in_range(0UL, ULONG_MAX);
			attrs &= S2TT_TEST_TTE_HOST_NS_ATTRS_MASK;

			/* Find out if we are done or not */
			inv_attrs = ((attrs & S2TTE_SH_MASK) ==
						S2TTE_SH_RESERVED);
			inv_attrs |= ((attrs & S2TTE_MEMATTR_MASK) ==
						S2TTE_MEMATTR_FWB_RESERVED);
			done = (reserved == inv_attrs);
		} while (!done);
	} else {
		/* Setup the NS TTE attributes that don't come from the host */
		attrs = S2TT_TEST_TTE_NS_ATTRS;
	}

	return attrs;
}

unsigned long s2tt_test_helpers_gen_attrs(bool invalid, long level)
{
	if (invalid == true) {
		return S2TT_TEST_TTE_ATTRS | S2TT_TEST_INVALID_DESC;
	}

	return ((level == S2TT_TEST_HELPERS_MAX_LVL) ?
			S2TT_TEST_PAGE_DESC : S2TT_TEST_BLOCK_DESC) |
							S2TT_TEST_TTE_ATTRS;
}

long s2tt_test_helpers_min_table_lvl(void)
{
	return S2TT_TEST_HELPERS_MIN_LVL;
}

long s2tt_test_helpers_min_block_lvl(void)
{
	return RTT_MIN_BLOCK_LEVEL;
}

unsigned long s2tt_test_helpers_get_entry_va_space_size(long level)
{
	assert(level >= S2TT_TEST_HELPERS_MIN_LVL);
	assert(level <= S2TT_TEST_HELPERS_MAX_LVL);

	unsigned long levels = S2TT_TEST_HELPERS_MAX_LVL - level;

	return 1UL << (GRANULE_SHIFT + (S2TTE_STRIDE * levels));
}

unsigned long s2tt_test_helpers_get_idx_from_addr(unsigned long addr,
						  long level)
{
	assert(level >= S2TT_TEST_HELPERS_MIN_LVL);
	assert(level <= S2TT_TEST_HELPERS_MAX_LVL);
	assert((addr & ~((1UL << max_ipa_size()) - 1UL)) == 0UL);

	unsigned int levels = (unsigned int)(S2TT_TEST_HELPERS_MAX_LVL - level);
	unsigned int lsb = GRANULE_SHIFT + (levels * S2TTE_STRIDE);

	return (addr >> lsb) & ((1UL << S2TTE_STRIDE) - 1UL);
}
