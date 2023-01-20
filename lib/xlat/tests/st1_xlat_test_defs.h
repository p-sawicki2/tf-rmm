/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef ST1_XLAT_TEST_DEFS_H
#define ST1_XLAT_TEST_DEFS_H

#include <utils_def.h>

/*
 * All the definitions on this file are as per Issue G.a of the
 * Arm Architecture Reference Manual for Armv8-A achitecture profile.
 * Section D5: The AArch64 Virtual Memory System Architecture (VMSA)
 */

/* Only 4K granularity is supported */
#define ST1_XLAT_TESTS_GRANULARITY_SHIFT (12U)
#define ST1_XLAT_TESTS_GRANULARITY_SIZE	(1U <<	\
					 (ST1_XLAT_TESTS_GRANULARITY_SHIFT))
#define ST1_XLAT_TESTS_GRANULARITY_MASK (ST1_XLAT_TESTS_GRANULARITY_SIZE - 1ULL)

/* Size of the translation table */
#define ST1_XLAT_TESTS_TBL_SIZE_SHIFT	(ST1_XLAT_TESTS_GRANULARITY_SHIFT)
#define ST1_XLAT_TESTS_TBL_SIZE		(1U << (ST1_XLAT_TESTS_TBL_SIZE_SHIFT))

/* Alignment of the translation tables */
#define ST1_XLAT_TESTS_TBL_ALIGNMENT	(ST1_XLAT_TESTS_TBL_SIZE)

/* TTE Size */
#define ST1_XLAT_TESTS_TTE_SIZE_SHIFT	(3U)
#define ST1_XLAT_TESTS_TTE_SIZE		(1U << (ST1_XLAT_TESTS_TTE_SIZE_SHIFT))

/* TTEs per translation table */
#define ST1_XLAT_TESTS_TBL_ENTRIES_SHIFT ((ST1_XLAT_TESTS_TBL_SIZE_SHIFT) - \
					  (ST1_XLAT_TESTS_TTE_SIZE_SHIFT))
#define ST1_XLAT_TESTS_TBL_ENTRIES	(1U <<	\
					 (ST1_XLAT_TESTS_TBL_ENTRIES_SHIFT))
#define ST1_XLAT_TESTS_TBL_ENTRIES_MASK	((ST1_XLAT_TESTS_TBL_ENTRIES) - 1U)

/* Maximum VA space size, in bits */
#define ST1_XLAT_TESTS_MAX_VA_BITS	(48U)
/* Maximum VA space size */
#define ST1_XLAT_TEST_MAX_VA_SIZE	(1ULL << ST1_XLAT_TESTS_MAX_VA_BITS)
/* Maximum VA space size, in pages*/
#define ST1_XLAT_TEST_MAX_VA_PAGES	(unsigned int)((ST1_XLAT_TEST_MAX_VA_SIZE \
					>> ST1_XLAT_TESTS_GRANULARITY_SHIFT) - \
					1U)

/* Maximum PA space size, in bits */
#define ST1_XLAT_TESTS_MAX_PA_BITS	(48U)
/* Maximum PA space size */
#define ST1_XLAT_TEST_MAX_PA_SIZE	(1ULL << ST1_XLAT_TESTS_MAX_PA_BITS)
/* PA address mask */
#define ST1_XLAT_TEST_PA_MASK		(ST1_XLAT_TEST_MAX_PA_SIZE - 1ULL)

/* Minimum VA space size, in bits */
#define ST1_XLAT_TESTS_MIN_VA_BITS	(16U)
/* minimum VA space size */
#define ST1_XLAT_TEST_MIN_VA_SIZE	(1ULL << ST1_XLAT_TESTS_MIN_VA_BITS)
/* Minimum VA space size, in pages*/
#define ST1_XLAT_TEST_MIN_VA_PAGES	(unsigned int)(ST1_XLAT_TEST_MIN_VA_SIZE \
					>> ST1_XLAT_TESTS_GRANULARITY_SHIFT)

/* Maximum number of table levels */
#define ST1_XLAT_TESTS_MAX_LEVEL	(3U)

/* Bitmask for a high region VA */
#define ST1_XLAT_HIGH_REGION_MASK	(ULL(0xFFFF000000000000))

/* Bitmask for a low region VA */
#define ST1_XLAT_LOW_REGION_MASK	(~(ST1_XLAT_HIGH_REGION_MASK))

/*
 * The xlat library only supports 4KB of granularity so the lower level
 * table descriptor that support block translation is Level 1.
 * The following macro specifies the biggest block size that can be
 * mapped by the xlat library.
 */
#define ST1_XLAT_MAX_BLOCK_SIZE		(1ULL << 30U)

/*
 * Calculate the shift for a given table level as per aarch64 VMSA.
 * Only 48 bits address space size is supported.
 *
 * aarch64 VMSA defines, for 4KB of granularity, the following levels with
 * their corresponding shifts:
 *
 * ----------------------------------------------------------------------
 * |   LEVEL OF TABLE	|     SIZE PER ENTRY	|   BITS USED PER IDX	|
 * ----------------------------------------------------------------------
 * |          0		|	  512 GB	|        47:39		|
 * ----------------------------------------------------------------------
 * |          1		|	   1 GB		|        38:30		|
 * ----------------------------------------------------------------------
 * |          2		|	   2 MB		|        29:21		|
 * ----------------------------------------------------------------------
 * |          3		|	   4 KB		|        20:12		|
 * ----------------------------------------------------------------------
 */
#define ST1_XLAT_TABLE_LVL_SHIFT(_x)			\
	((ST1_XLAT_TESTS_GRANULARITY_SHIFT) +		\
		(((ST1_XLAT_TESTS_MAX_LEVEL) - (_x)) *	\
		 (ST1_XLAT_TESTS_TBL_ENTRIES_SHIFT)))

/*
 * Return the bitmask for a given table level as per aarch64 VMSA.
 * Only 48 bits address space size is supported.
 */
#define ST1_XLAT_TABLE_LVL_MASK(_x)			\
	(((ST1_XLAT_TESTS_TBL_ENTRIES) - 1ULL) <<	\
	 (ST1_XLAT_TABLE_LVL_SHIFT(_x)))

/*
 * Calculate the base table level as per aarch64 VMSA specification given
 * a VA space size.
 * Only 48 bits address space size is supported.
 */
#define ST1_XLAT_GET_BASE_TABLE_LVL(_x)					\
	(((_x) >= ((1ULL) << ((ST1_XLAT_TABLE_LVL_SHIFT(0U))))) ? 0U :	\
	(((_x) >= ((1ULL) << ((ST1_XLAT_TABLE_LVL_SHIFT(1U))))) ? 1U :	\
	(((_x) >= ((1ULL) << ((ST1_XLAT_TABLE_LVL_SHIFT(2U))))) ? 2U :	\
	3U)))

/*
 * Calculate the number of entries for the base level given
 * the VA space size as per aarch64 VMSA.
 * Only 48 bits address space size is supported.
 */
#define ST1_XLAT_GET_BASE_LVL_ENTRIES(_x)			\
	((unsigned int)(((ST1_XLAT_TABLE_LVL_MASK((ST1_XLAT_GET_BASE_TABLE_LVL(_x)))) & (_x)) >> \
	 (ST1_XLAT_TABLE_LVL_SHIFT((ST1_XLAT_GET_BASE_TABLE_LVL(_x))))))

/*
 * Calculate the maximum VA for a given level as per the aarch64 VMSA.
 * Only 48 bits address space size is supported.
 */
#define ST1_XLAT_MAX_LVL_ADDR(_x)				\
	((1ULL << ((ST1_XLAT_TESTS_GRANULARITY_SHIFT) + 	\
		  ((ST1_XLAT_TESTS_TBL_ENTRIES_SHIFT) *		\
		   ((ST1_XLAT_TESTS_MAX_LEVEL) - (_x) + 1U)))) - 1ULL)

/*
 * Calculate the VA space covered by a entry of the specified level
 * as per the aarch64 VMSA.
 * Only 48 bits address space size is supported.
 */
#define ST1_XLAT_ENTRY_VA_SIZE(_x)				\
	(1ULL << (ST1_XLAT_TABLE_LVL_SHIFT(_x)))

/* Descriptor types */
#define ST1_XLAT_DESC_MASK		(U(0x03))
#define ST1_XLAT_INVALID_DESC		(U(0x00))
#define ST1_XLAT_BLOCK_DESC		(U(0x01))
#define ST1_XLAT_TABLE_DESC		(U(0x03))
#define ST1_XLAT_PAGE_DESC		(U(0x03))
#define ST1_XLAT_IS_DESC(tte, desc)				\
	(((tte) & (ST1_XLAT_DESC_MASK)) == (desc))

#define ST1_XLAT_BLOCK_OA_SHIFT(level)				\
	(((level) == 1U) ? (30U) : (21U))
#define ST1_XLAT_BLOCK_OA_LENGTH(level)				\
	(48U - (ST1_XLAT_BLOCK_OA_SHIFT(level)))
#define ST1_XLAT_BLOCK_OA_MASK(level)				\
	((1ULL < (ST1_XLAT_BLOCK_OA_LENGTH(level))) - 1ULL)

#define ST1_XLAT_NEXT_LEVEL_TA_SHIFT	(12U)
#define ST1_XLAT_NEXT_LEVEL_TA_LENGTH	(48U - (ST1_XLAT_NEXT_LEVEL_TA_SHIFT))
#define ST1_XLAT_NEXT_LEVEL_TA_MASK				\
	((1ULL << (ST1_XLAT_NEXT_LEVEL_TA_LENGTH)) - 1ULL)

#define ST1_XLAT_PAGE_OA_SHIFT		(12U)
#define ST1_XLAT_PAGE_OA_LENGTH		(48 - ST1_XLAT_PAGE_OA_SHIFT)
#define ST1_XLAT_PAGE_OA_MASK					\
	((1ULL << (ST1_XLAT_PAGE_OA_LENGTH)) - 1ULL)

/* Table descriptor attributes */
#define ST1_XLAT_TABLE_DESC_ATTRS_SHIFT		(51U)
#define ST1_XLAT_TABLE_DESC_ATTRS_SIZE		(13U)
#define ST1_XLAT_TABLE_DESC_ATTRS_MASK				\
	((1ULL << ST1_XLAT_TABLE_DESC_ATTRS_SIZE) - 1ULL)

/* Block & Page descriptor lower attributes */
#define ST1_XLAT_ATTR_IDX_SHIFT			(0U)
#define ST1_XLAT_ATTR_IDX_SIZE			(3U)
#define ST1_XLAT_ATTR_IDX_MASK					\
	((1ULL << ST1_XLAT_ATTR_IDX_SIZE) - 1ULL)

#define ST1_XLAT_ATTR_NS_SHIFT			(3U)
#define ST1_XLAT_ATTR_NS_SIZE			(1U)
#define ST1_XLAT_ATTR_NS_MASK					\
	((1ULL << ST1_XLAT_ATTR_NS_SIZE) - 1ULL)

/* NS Bit values */
#define ST1_XLAT_REALM				(0U)
#define ST1_XLAT_NON_SECURE			(1U)

#define ST1_XLAT_ATTR_AF_SHIFT			(8U)
#define ST1_XLAT_ATTR_AF_SIZE			(1U)
#define ST1_XLAT_ATTR_AF_MASK					\
	((1ULL << ST1_XLAT_ATTR_AF_SIZE) - 1ULL)

#define ST1_XLAT_ATTR_AP_SHIFT			(4U)
#define ST1_XLAT_ATTR_AP_SIZE			(2U)
#define ST1_XLAT_ATTR_AP_MASK					\
	((1ULL << ST1_XLAT_ATTR_AP_SIZE) - 1ULL)

/* Access Permissions */
#define ST1_XLAT_RW_ACCESS			(0U)
#define ST1_XLAT_RO_ACCESS			(2U)
#define ST1_XLAT_RW_EL0_ACCESS			(1U)
#define ST1_xLAT_RO_EL0_ACCESS			(3U)

#define ST1_XLAT_ATTR_SH_SHIFT			(6U)
#define ST1_XLAT_ATTR_SH_SIZE			(2U)
#define ST1_XLAT_ATTR_SH_MASK					\
	((1ULL << ST1_XLAT_ATTR_SH_SIZE) - 1ULL)

/* Shareability */
#define ST1_XLAT_SHAREABILITY_NSH		(0U)
#define ST1_XLAT_SHAREABILITY_OSH		(2U)
#define ST1_XLAT_SHAREABILITY_ISH		(3U)

#define ST1_XLAT_LOW_ATTR_SHIFT			(2U)
#define ST1_XLAT_LOW_ATTR_SIZE			(10U)
#define ST1_XLAT_LOW_ATTR_MASK					\
	((1ULL << ST1_XLAT_LOW_ATTR_SIZE) - 1ULL)

#define ST1_XLAT_LOWER_ATTRS(x)					\
	(((x) & ST1_XLAT_LOW_ATTR_MASK) << ST1_XLAT_LOW_ATTR_SHIFT)

/* Block & Page descriptor upper attributes */
#define ST1_XLAT_ATTR_PXN_SHIFT			(3U)
#define ST1_XLAT_ATTR_PXN_SIZE			(1U)
#define ST1_XLAT_ATTR_PXN_MASK					\
	((1ULL << ST1_XLAT_ATTR_PXN_SIZE) - 1ULL)

#define ST1_XLAT_ATTR_UXN_SHIFT			(4U)
#define ST1_XLAT_ATTR_UXN_SIZE			(1U)
#define ST1_XLAT_ATTR_UXN_MASK					\
	((1ULL << ST1_XLAT_ATTR_UXN_SIZE) - 1ULL)

/* Execute Never values */
#define ST1_XLAT_EXECUTE			(0U)
#define ST1_XLAT_EXECUTE_NEVER			(1U)

#define ST1_XLAT_UPPER_ATTR_SHIFT		(50U)
#define ST1_XLAT_UPPER_ATTR_SIZE		(13U)
#define ST1_XLAT_UPPER_ATTR_MASK				\
	((1ULL << ST1_XLAT_UPPER_ATTR_SIZE) - 1ULL)

#define ST1_XLAT_UPPER_ATTRS(x)					\
	(((x) & ST1_XLAT_UPPER_ATTR_MASK) << ST1_XLAT_UPPER_ATTR_SHIFT)

#define ST1_XLAT_TABLE_ATTRS_MASK				\
	(((ST1_XLAT_UPPER_ATTR_MASK) << (ST1_XLAT_UPPER_ATTR_SHIFT)) |	\
	 ((ST1_XLAT_LOW_ATTR_MASK) << (ST1_XLAT_LOW_ATTR_SHIFT)))

#define ST1_XLAT_TABLE_OA_MASK					\
	(~(ST1_XLAT_TABLE_ATTRS_MASK | ST1_XLAT_DESC_MASK))

/*****************************************************
 * Following definitions are as per RMM xlat library
 ****************************************************/

/* MAIR attrs indexes */

#define ST1_XLAT_ATTR_IWBWA_OWBWA_NTR_IDX	(0U)
#define ST1_XLAT_ATTR_DEVICE_IDX		(1U)
#define ST1_XLAT_ATTR_NON_CACHEABLE_IDX		(2U)

/*
 * Transient flag uses the first bit of the user reserved
 * area in the tte.
 */
#define ST1_XLAT_TRANSIENT_FLAG_SHIFT	(55U)
#define ST1_XLAT_IS_TRANSIENT_DESC(_x)				\
	((_x) & (1ULL << ST1_XLAT_TRANSIENT_FLAG_SHIFT))

#endif /* ST1_XLAT_TEST_DEFS_H */
