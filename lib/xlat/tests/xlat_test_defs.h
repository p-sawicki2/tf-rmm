/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef XLAT_TEST_DEFS_H
#define XLAT_TEST_DEFS_H

#include <utils_def.h>
#include <xlat_defs_private.h>

/*
 * All the definitions on this file are as per Issue G.a of the
 * Arm Architecture Reference Manual for Armv8-A architecture profile.
 * Section D5: The AArch64 Virtual Memory System Architecture (VMSA)
 */

/*
 * Maximum PA space size supported by the architecture, in bits.
 *
 * Note that the value on this macro is regardless of the maximum
 * PA size supported by the platform, reported through
 * id_aa64mmfr0_el1 register.
 */
#define XLAT_TESTS_MAX_PA_BITS		(48U)
/* Maximum PA space size */
#define XLAT_TESTS_MAX_PA_SIZE		(1ULL << XLAT_TESTS_MAX_PA_BITS)
/* PA address mask */
#define XLAT_TESTS_PA_MASK		(XLAT_TESTS_MAX_PA_SIZE - 1ULL)

/* Bitmask for a low region VA */
#define XLAT_TESTS_LOW_REGION_MASK	(~(HIGH_REGION_MASK))

/*
 * The xlat library only supports 4KB of granularity so the lowest level
 * table descriptor that support block translation is Level 1.
 * The following macro specifies the biggest block size that can be
 * mapped by the xlat library.
 */
#define XLAT_TESTS_MAX_BLOCK_SIZE	XLAT_BLOCK_SIZE(MIN_LVL_BLOCK_DESC)

#define XLAT_TESTS_IS_DESC(tte, desc)				\
	(((tte) & (DESC_MASK)) == (desc))

#define XLAT_TESTS_TBL_ADDR_SHIFT	(12U)
#define XLAT_TESTS_TBL_ADDR_WIDTH	(48U - (XLAT_TESTS_TBL_ADDR_SHIFT))
#define XLAT_TESTS_TBL_ADDR_MASK	MASK(XLAT_TESTS_TBL_ADDR)

/*****************************************************
 * Following definitions are as per RMM xlat library
 ****************************************************/

#define XLAT_TESTS_IS_TRANSIENT_DESC(_x)			\
	((_x) & (1ULL << TRANSIENT_FLAG_SHIFT))

#endif /* XLAT_TEST_DEFS_H */
