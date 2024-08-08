/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch_features.h>
#include <assert.h>
#include <feature.h>
#include <gic.h>
#include <rec.h>
#include <s2tt.h>
#include <simd.h>
#include <smc-handler.h>
#include <smc-rmi.h>
#include <status.h>
#include <utils_def.h>

unsigned long get_feature_register_0(void)
{
	/* Set S2SZ field */
	unsigned long s2sz = arch_feat_get_pa_width();
	unsigned long feat_reg0 = INPLACE(RMI_FEATURE_REGISTER_0_S2SZ, s2sz);
	struct simd_config simd_cfg = { 0 };

	/* Set LPA2 field. RMM needs both Stage 1 and Stage 2 to support LPA2 */
	if ((is_feat_lpa2_4k_2_present() && is_feat_lpa2_4k_present()) == true) {
		feat_reg0 |=
			INPLACE(RMI_FEATURE_REGISTER_0_LPA2, RMI_FEATURE_TRUE);
	}

	/* Set support for SHA256 and SHA512 hash algorithms */
	feat_reg0 |= INPLACE(RMI_FEATURE_REGISTER_0_HASH_SHA_256,
						RMI_FEATURE_TRUE) |
		     INPLACE(RMI_FEATURE_REGISTER_0_HASH_SHA_512,
						RMI_FEATURE_TRUE);

	/* RMM supports PMUv3p7+ */
	assert(read_pmu_version() >= ID_AA64DFR0_EL1_PMUv3p7);

	/* Set support for PMUv3 */
	feat_reg0 |= INPLACE(RMI_FEATURE_REGISTER_0_PMU_EN,
				RMI_FEATURE_TRUE);

	/* Set number of PMU counters available */
	feat_reg0 |= INPLACE(RMI_FEATURE_REGISTER_0_PMU_NUM_CTRS,
				EXTRACT(PMCR_EL0_N, read_pmcr_el0()));

	/* The architecture requires at least two breakpoints and watchpoints */
	feat_reg0 |= INPLACE(RMI_FEATURE_REGISTER_0_NUM_BPS, 2U);
	feat_reg0 |= INPLACE(RMI_FEATURE_REGISTER_0_NUM_WPS, 2U);

	/* Get CPU simd configuration and set SVE fields if SVE is present */
	(void)simd_get_cpu_config(&simd_cfg);
	if (simd_cfg.sve_en) {
		feat_reg0 |= INPLACE(RMI_FEATURE_REGISTER_0_SVE_EN,
				     RMI_FEATURE_TRUE) |
			     INPLACE(RMI_FEATURE_REGISTER_0_SVE_VL,
				     simd_cfg.sve_vq);
	}

	/* Set number of List registers implemented, minus one */
	feat_reg0 |= INPLACE(RMI_FEATURE_REGISTER_0_GICV3_NUM_LRS,
				gic_vgic_get_num_lrs());

	/*
	 * Set the order of the maximum number of RECs which
	 * can be created per Realm.
	 */
	feat_reg0 |= INPLACE(RMI_FEATURE_REGISTER_0_MAX_RECS_ORDER,
				RMM_REC_MAX_ORDER);

	return feat_reg0;
}

void smc_read_feature_register(unsigned long index,
				struct smc_result *res)
{
	res->x[0] = RMI_SUCCESS;

	if (index == RMI_FEATURE_REGISTER_0_INDEX) {
		res->x[1] = get_feature_register_0();
	} else {
		res->x[1] = 0UL;
	}
}
