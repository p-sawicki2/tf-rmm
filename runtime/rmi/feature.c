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

#define RMM_FEATURE_MIN_IPA_SIZE		PARANGE_0000_WIDTH

static unsigned long get_feature_register_0(void)
{
	/* Set S2SZ field */
	unsigned long s2sz = arch_feat_get_pa_width();
	unsigned long feat_reg0 = INPLACE(RMM_FEATURE_REGISTER_0_S2SZ, s2sz);

	/* Set LPA2 field */
	if (is_feat_lpa2_4k_present()) {
		feat_reg0 |= INPLACE(RMM_FEATURE_REGISTER_0_LPA2, RMI_LPA2);
	}

	/* Set support for SHA256 and SHA512 hash algorithms */
	feat_reg0 |= INPLACE(RMM_FEATURE_REGISTER_0_HASH_SHA_256,
				RMI_SUPPORTED);
	feat_reg0 |= INPLACE(RMM_FEATURE_REGISTER_0_HASH_SHA_512,
				RMI_SUPPORTED);

	/* PMU is not supported */
	feat_reg0 |= INPLACE(RMM_FEATURE_REGISTER_0_PMU_EN,
				RMI_NOT_SUPPORTED);
	feat_reg0 |= INPLACE(RMM_FEATURE_REGISTER_0_PMU_NUM_CTRS, 0U);

	/* Set SVE fields */
	if (is_feat_sve_present()) {
		feat_reg0 |= INPLACE(RMM_FEATURE_REGISTER_0_SVE_EN,
				     RMI_SUPPORTED);

		simd_traps_disable(SIMD_SVE);
		feat_reg0 |= INPLACE(RMM_FEATURE_REGISTER_0_SVE_VL,
				     EXTRACT(ZCR_EL2_SVE_VL, read_zcr_el2()));
		simd_traps_enable();
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
	}
}

static bool validate_feature_register_0(unsigned long value)
{
	unsigned long feat_reg0 = get_feature_register_0();
	unsigned long s2sz = EXTRACT(RMM_FEATURE_REGISTER_0_S2SZ, value);

	/* Validate S2SZ field */
	if ((s2sz < RMM_FEATURE_MIN_IPA_SIZE) ||
	    (s2sz > EXTRACT(RMM_FEATURE_REGISTER_0_S2SZ, feat_reg0))) {
		return false;
	}

	/* Validate LPA2 flag */
	if ((EXTRACT(RMM_FEATURE_REGISTER_0_LPA2, value) == RMI_LPA2) &&
	    !is_feat_lpa2_4k_present()) {
		return false;
	}

	/* Validate PMU_EN flag */
	if ((EXTRACT(RMM_FEATURE_REGISTER_0_PMU_EN, value) == RMI_SUPPORTED) ||
	    (EXTRACT(RMM_FEATURE_REGISTER_0_PMU_NUM_CTRS, value) != 0U)) {
		return false;
	}

	/* Validate SVE flag */
	if ((EXTRACT(RMM_FEATURE_REGISTER_0_SVE_EN, value) == RMI_SUPPORTED)) {
		unsigned long zcr_val;

		if (!is_feat_sve_present()) {
			return false;
		}

		simd_traps_disable(SIMD_SVE);
		zcr_val = read_zcr_el2();
		simd_traps_enable();

		/* Validate SVE_VL value */
		if (EXTRACT(RMM_FEATURE_REGISTER_0_SVE_VL, value) >
		    EXTRACT(ZCR_EL2_SVE_VL, zcr_val)) {
			return false;
		}
	}

	return true;
}

bool validate_feature_register(unsigned long index, unsigned long value)
{
	switch (index) {
	case RMM_FEATURE_REGISTER_0_INDEX:
		return validate_feature_register_0(value);
	default:
		assert(false);
		return false;
	}
}
