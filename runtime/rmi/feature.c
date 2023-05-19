/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch_features.h>
#include <assert.h>
#include <feature.h>
#include <simd.h>
#include <smc-handler.h>
#include <smc-rmi.h>
#include <status.h>
#include <utils_def.h>

unsigned long get_feature_register_0(void)
{
	/* Set S2SZ field */
	unsigned long s2sz = arch_feat_get_pa_width();
	unsigned long feat_reg0 = INPLACE(RMM_FEATURE_REGISTER_0_S2SZ, s2sz);

	/* Set LPA2 field */
	if (is_feat_lpa2_4k_present()) {
		feat_reg0 |= INPLACE(RMM_FEATURE_REGISTER_0_LPA2,
							RMI_FEATURE_TRUE);
	}

	/* Set support for SHA256 and SHA512 hash algorithms */
	feat_reg0 |= INPLACE(RMM_FEATURE_REGISTER_0_HASH_SHA_256,
						RMI_FEATURE_TRUE) |
		     INPLACE(RMM_FEATURE_REGISTER_0_HASH_SHA_512,
						RMI_FEATURE_TRUE);

	/* RMM supports PMUv3p7+ */
	assert(read_pmu_version() >= ID_AA64DFR0_EL1_PMUv3p7);

	/* Set support for PMUv3 */
	feat_reg0 |= INPLACE(RMM_FEATURE_REGISTER_0_PMU_EN,
				RMI_FEATURE_TRUE);

	/* Set number of PMU counters available */
	feat_reg0 |= INPLACE(RMM_FEATURE_REGISTER_0_PMU_NUM_CTRS,
				EXTRACT(PMCR_EL0_N, read_pmcr_el0()));

	/* Set SVE fields */
	if (is_feat_sve_present()) {
		feat_reg0 |= INPLACE(RMM_FEATURE_REGISTER_0_SVE_EN,
						RMI_FEATURE_TRUE) |
			     INPLACE(RMM_FEATURE_REGISTER_0_SVE_VL,
						simd_sve_get_max_vq());
	}

	return feat_reg0;
}

void smc_read_feature_register(unsigned long index,
				struct smc_result *ret_struct)
{
	switch (index) {
	case RMM_FEATURE_REGISTER_0_INDEX:
		ret_struct->x[0] = RMI_SUCCESS;
		ret_struct->x[1] = get_feature_register_0();
		break;
	default:
		ret_struct->x[0] = RMI_ERROR_INPUT;
		ret_struct->x[1] = 0UL;
	}
}
