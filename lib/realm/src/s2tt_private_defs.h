/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef S2TT_PRIVATE_DEFS
#define S2TT_PRIVATE_DEFS

/* Only 4K pages supported */
#define BLOCK_L2_SIZE		(GRANULE_SIZE * S2TTES_PER_S2TT)

/*
 * The maximum number of bits supported by the RMM for a stage 2 translation
 * output address (including stage 2 table entries).
 */
#define S2TTE_OA_BITS			48U

/*
 * The following constants for the mapping attributes (S2_TTE_MEMATTR_*)
 * assume that HCR_EL2.FWB is set.
 */
#define S2TTE_MEMATTR_SHIFT		2
#define S2TTE_MEMATTR_MASK		(0x7UL << S2TTE_MEMATTR_SHIFT)
#define S2TTE_MEMATTR_FWB_NORMAL_WB	((1UL << 4) | (2UL << 2))
#define S2TTE_MEMATTR_FWB_RESERVED	((1UL << 4) | (0UL << 2))

#define S2TTE_AP_SHIFT			6
#define S2TTE_AP_MASK			(3UL << S2TTE_AP_SHIFT)
#define S2TTE_AP_RW			(3UL << S2TTE_AP_SHIFT)

#define S2TTE_SH_SHIFT			8
#define S2TTE_SH_MASK			(3UL << S2TTE_SH_SHIFT)
#define S2TTE_SH_NS			(0UL << S2TTE_SH_SHIFT)
#define S2TTE_SH_RESERVED		(1UL << S2TTE_SH_SHIFT)
#define S2TTE_SH_OS			(2UL << S2TTE_SH_SHIFT)
#define S2TTE_SH_IS			(3UL << S2TTE_SH_SHIFT)	/* Inner Shareable */

/*
 * We set HCR_EL2.FWB So we set bit[4] to 1 and bits[3:2] to 2 and force
 * everyting to be Normal Write-Back
 */
#define S2TTE_MEMATTR_FWB_NORMAL_WB	((1UL << 4) | (2UL << 2))

#define S2TTE_ATTRS	(S2TTE_MEMATTR_FWB_NORMAL_WB | S2TTE_AP_RW | \
			S2TTE_SH_IS | S2TTE_AF)
#define S2TTE_NS_ATTR_MASK (S2TTE_MEMATTR_MASK | S2TTE_AP_MASK | \
			    S2TTE_SH_MASK)

#define S2TTE_TABLE	S2TTE_L012_TABLE
#define S2TTE_BLOCK	(S2TTE_ATTRS | S2TTE_L012_BLOCK)
#define S2TTE_PAGE	(S2TTE_ATTRS | S2TTE_L3_PAGE)
#define S2TTE_BLOCK_NS	(S2TTE_NS | S2TTE_XN | S2TTE_AF | S2TTE_L012_BLOCK)
#define S2TTE_PAGE_NS	(S2TTE_NS | S2TTE_XN | S2TTE_AF | S2TTE_L3_PAGE)
#define S2TTE_INVALID	S2TTE_Lx_INVALID

#define NR_RTT_LEVELS	4

#endif /* S2TT_PRIVATE_DEFS */
