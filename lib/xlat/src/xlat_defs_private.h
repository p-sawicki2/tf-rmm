/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 * SPDX-FileCopyrightText: Copyright Arm Limited and Contributors.
 */

/* This file is derived from xlat_table_v2 library in TF-A project */

#ifndef XLAT_DEFS_PRIVATE_H
#define XLAT_DEFS_PRIVATE_H

#include <arch.h>
#include <arch_features.h>
#include <utils_def.h>
#include <xlat_defs.h>

/*
 * A block descriptor points to a region of memory bigger than the granule size
 * (e.g. a 2MB region when the granule size is 4KB).
 */
/* Definition of a valid descriptor mask */
#define VALID_DESC		UL(0x1)
#define BLOCK_DESC		VALID_DESC /* Table levels [0, 2] */
/* A table descriptor points to the next level of translation table. */
#define TABLE_DESC		(UL(0x2) | VALID_DESC) /* Table levels [-1, 2] */
/* Definition of an invalid descriptor */
#define INVALID_DESC		UL(0x0)
/*
 * A TTE points to a page, i.e. a memory region whose size is the
 * translation granule size (e.g. 4KB).
 */
#define PAGE_DESC		(UL(0x2) | VALID_DESC) /* Table level 3 */

#define DESC_MASK		UL(0x3)

/* Upper attributes on a TTE */
#define XN			(ULL(1) << 2)
#define UXN			(ULL(1) << 2)
#define PXN			(ULL(1) << 1)
#define CONT_HINT		(ULL(1) << 0)

#define UPPER_ATTRS_SHIFT	(52U)
#define UPPER_ATTRS_WIDTH	(3U)
#define UPPER_ATTRS_MASK	MASK(UPPER_ATTRS)
#define UPPER_ATTRS(x)		(INPLACE(UPPER_ATTRS, x) & (UPPER_ATTRS_MASK))

/* Guarded Page bit */
#define GP			(ULL(1) << 50)

#define AP2_SHIFT		UL(0x7)
#define AP2_RO			ULL(0x1)
#define AP2_RW			ULL(0x0)

#define AP1_SHIFT		UL(0x6)

/* Macro to access translation table lower attributes */
#define LOWER_ATTRS_SHIFT	(2U)
#define LOWER_ATTRS_WIDTH	(10U)
#define LOWER_ATTRS_MASK	MASK(LOWER_ATTRS)
#define LOWER_ATTRS(x)		(INPLACE(LOWER_ATTRS, x) & (LOWER_ATTRS_MASK))

/*
 * The following definitions must all be passed to the LOWER_ATTRS() macro to
 * get the right bitmask.
 */
#define NS				(UL(0x1) << UL(3))	/* Bit[5] absolutely */
#define ACCESS_FLAG			(UL(1) << UL(8))	/* Bit[10] absolutely */
#define AP_RO				(AP2_RO << UL(5))
#define AP_RW				(AP2_RW << UL(5))
#define AP_ACCESS_UNPRIVILEGED		(AP1_ACCESS_UNPRIVILEGED    << UL(4))
#define AP_NO_ACCESS_UNPRIVILEGED	(AP1_NO_ACCESS_UNPRIVILEGED << UL(4))
#define ATTR_DEVICE_INDEX		UL(0x1)
#define ATTR_IWBWA_OWBWA_NTR_INDEX	UL(0x0)
#define NG_HINT				(ULL(1) << 9)

/* Shareability within the lower attributes field of the TTE. */
#define LOWER_ATTR_SH_SHIFT	((6U) + LOWER_ATTRS_SHIFT)
#define LOWER_ATTR_SH_WIDTH	(2U)

/* Macro to set SH on TCR_EL2 when FEAT_LPA2 is enabled */
#define SET_TCR_SH(_region, _sh)	\
		(((_region) == VA_LOW_REGION) ? INPLACE(TCR_EL2_SH0, (_sh)) : \
						INPLACE(TCR_EL2_SH1, (_sh)))

/* Shareability attributes. Only ISH is supported. */
#define ISH			(UL(0x3))

/* Device-nGnRE */
#define ATTR_DEVICE			MAIR_DEV_NGNRE
/* Normal Memory, Outer Write-Back non-transient, Inner Write-Back non-transient */
#define ATTR_IWBWA_OWBWA_NTR		MAKE_MAIR_NORMAL_MEMORY(MAIR_NORM_WB_NTR_RWA, MAIR_NORM_WB_NTR_RWA)
#define MAIR_ATTR_SET(attr, index)	((attr) << (index << UL(3)))
#define ATTR_INDEX_MASK			U(0x3)
#define ATTR_INDEX_GET(attr)		(((attr) >> UL(2)) & ATTR_INDEX_MASK)

/* Output address field on a TTE given 4KB granularity. */
#define OA_SHIFT		(XLAT_GRANULARITY_SIZE_SHIFT)

/* The output address MSB for non-LPA2 format */
#define TTE_OA_MSB		(47U)

/*
 * Table descriptor format for 52 bit OA (FEAT_LPA2) is [49:12] for
 * the bits [49:12] of the table address. For bits [51:50] it is [9:8]
 * of descriptor. See D8.3.1 Table descriptor format in Issue I.a of Arm ARM.
 */
#define TTE_OA_BIT_49_LPA2	(49U)

/*
 * When FEAT_LPA2 is enabled bits [51:50] of the OA are
 * bits [9:8] on the TTE.
 */
#define TTE_OA_BITS_50_51_SHIFT		ULL(8)
#define TTE_OA_BITS_50_51_WIDTH		ULL(2)
#define TTE_OA_BITS_50_51_MASK		MASK(TTE_OA_BITS_50_51)

/* Bitfields for the MSBs on an OA for 52-OA */
#define OA_BITS_50_51_SHIFT	ULL(51)
#define OA_BITS_50_51_WIDTH	TTE_OA_BITS_50_51_WIDTH
#define OA_BITS_50_51_MASK	MASK(OA_BITS_50_51)

/* Different address masks */
#define ADDR_MASK_52_TO_63	BIT_MASK_ULL(U(63), U(52))
#define ADDR_MASK_48_TO_51	BIT_MASK_ULL(U(51), U(48))
#define ADDR_MASK_44_TO_47	BIT_MASK_ULL(U(47), U(44))
#define ADDR_MASK_42_TO_43	BIT_MASK_ULL(U(43), U(42))
#define ADDR_MASK_40_TO_41	BIT_MASK_ULL(U(41), U(40))
#define ADDR_MASK_36_TO_39	BIT_MASK_ULL(U(39), U(36))
#define ADDR_MASK_32_TO_35	BIT_MASK_ULL(U(35), U(32))

#endif /* XLAT_DEFS_PRIVATE_H */
