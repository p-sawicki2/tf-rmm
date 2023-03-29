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

/*
 * Redefine all the TTE attribute masks and bits so we do not need to rely
 * on the same macros to implement and test the APIs the use them.
 *
 * Also, this will help to test not only the APIs that use the macros, but
 * the macros themselves as well.
 */

/* Table descriptor attributes */
#define XLAT_TESTS_TABLE_DESC_ATTRS_SHIFT		(51U)
#define XLAT_TESTS_TABLE_DESC_ATTRS_SIZE		(13U)
#define XLAT_TESTS_TABLE_DESC_ATTRS_MASK			\
	((1ULL << XLAT_TESTS_TABLE_DESC_ATTRS_SIZE) - 1ULL)

/* Block & Page descriptor lower attributes */
#define XLAT_TESTS_ATTR_IDX_SHIFT			(0U)
#define XLAT_TESTS_ATTR_IDX_SIZE			(3U)
#define XLAT_TESTS_ATTR_IDX_MASK				\
	((1ULL << XLAT_TESTS_ATTR_IDX_SIZE) - 1ULL)

#define XLAT_TESTS_ATTR_NS_SHIFT			(3U)
#define XLAT_TESTS_ATTR_NS_SIZE				(1U)
#define XLAT_TESTS_ATTR_NS_MASK					\
	((1ULL << XLAT_TESTS_ATTR_NS_SIZE) - 1ULL)

/* NS Bit values */
#define XLAT_TESTS_REALM				(0U)
#define XLAT_TESTS_NON_SECURE				(1U)

#define XLAT_TESTS_ATTR_AF_SHIFT			(8U)
#define XLAT_TESTS_ATTR_AF_SIZE				(1U)
#define XLAT_TESTS_ATTR_AF_MASK					\
	((1ULL << XLAT_TESTS_ATTR_AF_SIZE) - 1ULL)

#define XLAT_TESTS_ATTR_AP_SHIFT			(4U)
#define XLAT_TESTS_ATTR_AP_SIZE				(2U)
#define XLAT_TESTS_ATTR_AP_MASK					\
	((1ULL << XLAT_TESTS_ATTR_AP_SIZE) - 1ULL)

/* Access Permissions */
#define XLAT_TESTS_RW_ACCESS				(0U)
#define XLAT_TESTS_RO_ACCESS				(2U)
#define XLAT_TESTS_RW_EL0_ACCESS			(1U)
#define ST1_xLAT_RO_EL0_ACCESS				(3U)

#define XLAT_TESTS_ATTR_SH_SHIFT			(6U)
#define XLAT_TESTS_ATTR_SH_SIZE				(2U)
#define XLAT_TESTS_ATTR_SH_MASK					\
	((1ULL << XLAT_TESTS_ATTR_SH_SIZE) - 1ULL)

/* Shareability */
#define XLAT_TESTS_SHAREABILITY_NSH			(0U)
#define XLAT_TESTS_SHAREABILITY_OSH			(2U)
#define XLAT_TESTS_SHAREABILITY_ISH			(3U)

#define XLAT_TESTS_LOW_ATTR_SHIFT			(2U)
#define XLAT_TESTS_LOW_ATTR_SIZE			(10U)
#define XLAT_TESTS_LOW_ATTR_MASK				\
	((1ULL << XLAT_TESTS_LOW_ATTR_SIZE) - 1ULL)

#define XLAT_TESTS_LOWER_ATTRS(x)				\
	(((x) & XLAT_TESTS_LOW_ATTR_MASK) << XLAT_TESTS_LOW_ATTR_SHIFT)

/* Block & Page descriptor upper attributes */
#define XLAT_TESTS_ATTR_PXN_SHIFT			(3U)
#define XLAT_TESTS_ATTR_PXN_SIZE			(1U)
#define XLAT_TESTS_ATTR_PXN_MASK				\
	((1ULL << XLAT_TESTS_ATTR_PXN_SIZE) - 1ULL)

#define XLAT_TESTS_ATTR_UXN_SHIFT			(4U)
#define XLAT_TESTS_ATTR_UXN_SIZE			(1U)
#define XLAT_TESTS_ATTR_UXN_MASK				\
	((1ULL << XLAT_TESTS_ATTR_UXN_SIZE) - 1ULL)

/* Execute Never values */
#define XLAT_TESTS_EXECUTE				(0U)
#define XLAT_TESTS_EXECUTE_NEVER			(1U)

#define XLAT_TESTS_UPPER_ATTR_SHIFT			(50U)
#define XLAT_TESTS_UPPER_ATTR_SIZE			(13U)
#define XLAT_TESTS_UPPER_ATTR_MASK				\
	((1ULL << XLAT_TESTS_UPPER_ATTR_SIZE) - 1ULL)

#define XLAT_TESTS_UPPER_ATTRS(x)				\
	(((x) & XLAT_TESTS_UPPER_ATTR_MASK) << XLAT_TESTS_UPPER_ATTR_SHIFT)

#define XLAT_TESTS_TABLE_ATTRS_MASK				\
	(((XLAT_TESTS_UPPER_ATTR_MASK) << (XLAT_TESTS_UPPER_ATTR_SHIFT)) |	\
	 ((XLAT_TESTS_LOW_ATTR_MASK) << (XLAT_TESTS_LOW_ATTR_SHIFT)))

#define XLAT_TESTS_TABLE_OA_MASK				\
	(~(XLAT_TESTS_TABLE_ATTRS_MASK | DESC_MASK))

/*****************************************************
 * Following definitions are as per RMM xlat library
 ****************************************************/

/* MAIR attrs indexes */

#define XLAT_TESTS_ATTR_IWBWA_OWBWA_NTR_IDX		(0U)
#define XLAT_TESTS_ATTR_DEVICE_IDX			(1U)
#define XLAT_TESTS_ATTR_NON_CACHEABLE_IDX		(2U)

#define XLAT_TESTS_IS_TRANSIENT_DESC(_x)			\
	((_x) & (1ULL << TRANSIENT_FLAG_SHIFT))

#endif /* XLAT_TEST_DEFS_H */
