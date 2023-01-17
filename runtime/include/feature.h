/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef FEATURE_H
#define FEATURE_H

#include <arch.h>

/* RmiFeature enumerations */
#define RMI_NOT_SUPPORTED				UL(0)
#define RMI_SUPPORTED					UL(1)

#define RMM_FEATURE_REGISTER_0_PMU_EN_SHIFT		UL(22)
#define RMM_FEATURE_REGISTER_0_PMU_EN_WIDTH		UL(1)

#define RMM_FEATURE_REGISTER_0_PMU_NUM_CTRS_SHIFT	UL(23)
#define RMM_FEATURE_REGISTER_0_PMU_NUM_CTRS_WIDTH	UL(5)

bool validate_feature_register(unsigned long index, unsigned long value);

#endif /* FEATURE_H */
