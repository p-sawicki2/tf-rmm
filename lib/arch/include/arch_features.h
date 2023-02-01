/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef ARCH_FEATURES_H
#define ARCH_FEATURES_H

#include <arch_helpers.h>
#include <assert.h>
#include <stdbool.h>

static inline bool is_armv8_4_ttst_present(void)
{
	return (EXTRACT(ID_AA64MMFR2_EL1_ST,
		read_id_aa64mmfr2_el1()) == 1U);
}

/*
 * Check if SVE is enabled
 * ID_AA64PFR0_EL1.SVE, bits [35:32]:
 * 0b0000 SVE architectural state and programmers' model are not implemented.
 * 0b0001 SVE architectural state and programmers' model are implemented.
 */
static inline bool is_feat_sve_present(void)
{
	return (EXTRACT(ID_AA64PFR0_EL1_SVE,
		read_id_aa64pfr0_el1()) != 0UL);
}

/*
 * Check if RNDR is available
 */
static inline bool is_feat_rng_present(void)
{
	return (EXTRACT(ID_AA64ISAR0_EL1_RNDR,
		read_id_aa64isar0_el1()) != 0UL);
}

/*
 * Check if FEAT_VMID16 is implemented
 * ID_AA64MMFR1_EL1.VMIDBits, bits [7:4]:
 * 0b0000 8 bits.
 * 0b0010 16 bits.
 * All other values are reserved.
 */
static inline bool is_feat_vmid16_present(void)
{
	return (EXTRACT(ID_AA64MMFR1_EL1_VMIDBits,
		read_id_aa64mmfr1_el1()) == ID_AA64MMFR1_EL1_VMIDBits_16);
}

/*
 * Check if FEAT_LPA2 is implemented.
 * 4KB granule at stage 2 supports 52-bit input and output addresses:
 * ID_AA64MMFR0_EL1.TGran4_2 bits [43:40]: 0b0011
 */
static inline bool is_feat_lpa2_4k_present(void)
{
	return (EXTRACT(ID_AA64MMFR0_EL1_TGRAN4_2,
		read_id_aa64mmfr0_el1()) == ID_AA64MMFR0_EL1_TGRAN4_2_LPA2);
}

/*
 * Check if FEAT_HPMN is implemented.
 * ID_AA64DFR0_EL1.HPMN0, bits [63:60]
 * 0b0000: Setting MDCR_EL2.HPMN to zero has constrained unpredictable behavior
 * 0b0001: Setting MDCR_EL2.HPMN to zero has defined behavior
 */
static inline bool is_feat_hpmn0_present(void)
{
	return (EXTRACT(ID_AA64DFR0_EL1_HPMN0,
		read_id_aa64dfr0_el1()) != 0UL);
}

/*
 * Returns Performance Monitors Extension version.
 * ID_AA64DFR0_EL1.PMUVer, bits [11:8]:
 * 0b0000: Performance Monitors Extension not implemented
 */
static inline unsigned int read_pmu_version(void)
{
	return EXTRACT(ID_AA64DFR0_EL1_PMUVer, read_id_aa64dfr0_el1());
}

/*
 * Check if FEAT_PMUv3_SS is implemented.
 * ID_AA64DFR0_EL1.PMSS, bits [19:16]:
 * 0b0000: PMU snapshot extension not implemented
 * 0b0001: PMU snapshot extension implemented
 */
static inline bool is_feat_pmuv3_ss_present(void)
{
	return (EXTRACT(ID_AA64DFR0_EL1_PMSS,
		read_id_aa64dfr0_el1()) != 0UL);
}

/*
 * Check if FEAT_SEBEP is implemented.
 * ID_AA64DFR0_EL1.SEBEP, bits [27:24]
 * 0b0000: Synchronous-exception-based event profiling not implemented
 * 0b0001: Synchronous-exception-based event profiling implemented
 */
static inline bool is_feat_sebep_present(void)
{
	return (EXTRACT(ID_AA64DFR0_EL1_SEBEP,
		read_id_aa64dfr0_el1()) != 0UL);
}

/*
 * Check if FEAT_EBEP is implemented.
 * ID_AA64DFR1_EL1.EBEP, bits [51:48]
 * 0b0000: Exception-based event profiling not implemented
 * 0b0001: Exception-based event profiling implemented
 */
static inline bool is_feat_ebep_present(void)
{
	return (EXTRACT(ID_AA64DFR1_EL1_EBEP,
		read_id_aa64dfr1_el1()) != 0UL);
}

/*
 * Check if FEAT_PMUv3_ICNTR is implemented.
 * ID_AA64DFR1_EL1.ICNTR, bits [39:36]:
 * 0b0000: PMU fixed-function instruction counter not implemented
 * 0b0001: PMU fixed-function instruction counter not implemented implemented
 */
static inline bool is_feat_pmuv3_icntr_present(void)
{
	return (EXTRACT(ID_AA64DFR1_EL1_ICNTR,
		read_id_aa64dfr1_el1()) != 0UL);
}

/*
 * Check if FEAT_PMUv3_FGT2 is implemented.
 * ID_AA64MMFR0_EL1.FGT, bits [59:56]:
 * 0b0000: Fine-grained trap controls are not implemented
 * 0b0001: FEAT_FGT implemented
 * 0b0010: FEAT_FGT2 implemented
 */
static inline bool is_feat_fgt2_present(void)
{
	return (EXTRACT(ID_AA64MMFR0_EL1_FGT,
		read_id_aa64mmfr0_el1()) == ID_AA64MMFR0_EL1_FGT2_SUPPORTED);
}

unsigned int arch_feat_get_pa_width(void);

#endif /* ARCH_FEATURES_H */
