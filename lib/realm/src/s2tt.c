/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch_features.h>
#include <arch_helpers.h>
#include <attestation_token.h>
#include <bitmap.h>
#include <buffer.h>
#include <gic.h>
#include <granule.h>
#include <memory_alloc.h>
#include <realm.h>
#include <ripas.h>
#include <smc.h>
#include <status.h>
#include <stddef.h>
#include <string.h>
#include <table.h>
#include <utils_def.h>

/*
 * For prototyping we assume 4K pages
 */
#define BLOCK_L2_SIZE		(GRANULE_SIZE * S2TTES_PER_S2TT)

#define S2TTE_OA_BITS			48U

/*
 * The maximum number of bits supported by the RMM for a stage 2 translation
 * output address (including stage 2 table entries) with FEAT_LPA2 is 52 bits.
 */
#define S2TTE_OA_BITS_LPA2		52U

#define DESC_TYPE_MASK			0x3UL
#define S2TTE_L012_TABLE		0x3UL
#define S2TTE_L012_BLOCK		0x1UL
#define S2TTE_L3_PAGE			0x3UL
#define S2TTE_Lx_INVALID		0x0UL

/*
 * The following constants for the mapping attributes (S2_TTE_MEMATTR_*)
 * assume that HCR_EL2.FWB is set.
 */
#define S2TTE_MEMATTR_SHIFT		2U
#define S2TTE_MEMATTR_MASK		(0x7UL << S2TTE_MEMATTR_SHIFT)
#define S2TTE_MEMATTR_FWB_NORMAL_WB	((1UL << 4U) | (2UL << 2U))
#define S2TTE_MEMATTR_FWB_RESERVED	((1UL << 4U) | (0UL << 2U))

#define S2TTE_AP_SHIFT			6U
#define S2TTE_AP_MASK			(3UL << S2TTE_AP_SHIFT)
#define S2TTE_AP_RW			(3UL << S2TTE_AP_SHIFT)

#define S2TTE_SH_SHIFT			8U
#define S2TTE_SH_MASK			(3UL << S2TTE_SH_SHIFT)
#define S2TTE_SH_NS			(0UL << S2TTE_SH_SHIFT)
#define S2TTE_SH_RESERVED		(1UL << S2TTE_SH_SHIFT)
#define S2TTE_SH_OS			(2UL << S2TTE_SH_SHIFT)
#define S2TTE_SH_IS			(3UL << S2TTE_SH_SHIFT)	/* Inner Shareable */

#define S2TTE_AF			(1UL << 10U)
#define S2TTE_XN			(2UL << 53U)
#define S2TTE_NS			(1UL << 55U)

/* When FEAT_LPA2 is enabled, Shareability attributes are stored in VTCR_EL2 */
#define S2TTE_ATTRS_LPA2	(S2TTE_MEMATTR_FWB_NORMAL_WB | S2TTE_AP_RW | \
				 S2TTE_AF)
#define S2TTE_ATTRS		(S2TTE_ATTRS_LPA2 | S2TTE_SH_IS)

#define S2TTE_TABLE		S2TTE_L012_TABLE
#define S2TTE_BLOCK		(S2TTE_ATTRS | S2TTE_L012_BLOCK)
#define S2TTE_BLOCK_LPA2	(S2TTE_ATTRS_LPA2 | S2TTE_L012_BLOCK)
#define S2TTE_PAGE		(S2TTE_ATTRS | S2TTE_L3_PAGE)
#define S2TTE_PAGE_LPA2		(S2TTE_ATTRS_LPA2 | S2TTE_L3_PAGE)
#define S2TTE_BLOCK_NS		(S2TTE_NS | S2TTE_XN |			\
				 S2TTE_AF | S2TTE_L012_BLOCK)
#define S2TTE_PAGE_NS		(S2TTE_NS | S2TTE_XN |			\
				 S2TTE_AF | S2TTE_L3_PAGE)
#define S2TTE_INVALID		0UL

/*
 * When FEAT_LPA2 is enabled, the 2 MSB bits of the OA is not contiguous
 * to the rest of the address in the TTE.
 */
#define S2TTE_OA_MSB_SHIFT	50U
#define S2TTE_OA_MSB_WIDTH	2U

/* Where the 2 MSB bits of the OA are stored in the TTE */
#define S2TTE_ENTRY_MSB_SHIFT	8U
#define S2TTE_ENTRY_MSB_WIDTH	S2TTE_OA_MSB_WIDTH

/*
 * The type of an S2TTE is one of the following:
 *
 * - Invalid
 * - Valid page
 * - Valid block
 * - Table
 *
 * Within an invalid S2TTE for a Protected IPA, architecturally RES0 bits are
 * used to encode the HIPAS and RIPAS.
 *
 * A valid S2TTE for a Protected IPA implies HIPAS=ASSIGNED and RIPAS=RAM.
 *
 * An invalid S2TTE for an Unprotected IPA implies HIPAS=INVALID_NS.
 * A valid S2TTE for an Unprotected IPA implies HIPAS=VALID_NS.
 *
 * The following table defines the mapping from a (HIPAS, RIPAS) tuple to the
 * value of the S2TTE.
 *
 * ------------------------------------------------------------------------------
 * IPA		HIPAS		RIPAS		S2TTE value
 * ==============================================================================
 * Protected	UNASSIGNED	EMPTY		(S2TTE_INVALID_HIPAS_UNASSIGNED	|
 *						 S2TTE_INVALID_RIPAS_EMPTY)
 * Protected	UNASSIGNED	RAM		(S2TTE_INVALID_HIPAS_UNASSIGNED	|
 *						 S2TTE_INVALID_RIPAS_RAM)
 * Protected	ASSIGNED	EMPTY		(S2TTE_INVALID_HIPAS_ASSIGNED	|
 *						 S2TTE_INVALID_RIPAS_EMPTY)
 * Protected	ASSIGNED	RAM		Valid page / block with NS=0
 * Protected	DESTROYED	*		S2TTE_INVALID_DESTROYED
 * Unprotected	INVALID_NS	N/A		S2TTE_INVALID_UNPROTECTED
 * Unprotected	VALID_NS	N/A		Valid page / block with NS=1
 * ------------------------------------------------------------------------------
 */

#define S2TTE_INVALID_HIPAS_SHIFT	2U
#define S2TTE_INVALID_HIPAS_WIDTH	4U
#define S2TTE_INVALID_HIPAS_MASK	MASK(S2TTE_INVALID_HIPAS)

#define S2TTE_INVALID_HIPAS_UNASSIGNED	(INPLACE(S2TTE_INVALID_HIPAS, 0U))
#define S2TTE_INVALID_HIPAS_ASSIGNED	(INPLACE(S2TTE_INVALID_HIPAS, 1U))
#define S2TTE_INVALID_HIPAS_DESTROYED	(INPLACE(S2TTE_INVALID_HIPAS, 2U))

#define S2TTE_INVALID_RIPAS_SHIFT	6U
#define S2TTE_INVALID_RIPAS_WIDTH	1U
#define S2TTE_INVALID_RIPAS_MASK	MASK(S2TTE_INVALID_RIPAS)

#define S2TTE_INVALID_RIPAS_EMPTY	(INPLACE(S2TTE_INVALID_RIPAS, 0U))
#define S2TTE_INVALID_RIPAS_RAM		(INPLACE(S2TTE_INVALID_RIPAS, 1U))

#define S2TTE_INVALID_DESTROYED		S2TTE_INVALID_HIPAS_DESTROYED
#define S2TTE_INVALID_UNPROTECTED	0x0UL

#define NR_RTT_LEVELS		(RTT_PAGE_LEVEL - RTT_MIN_STARTING_LEVEL + 1U)
#define NR_RTT_LEVELS_LPA2	(RTT_PAGE_LEVEL - RTT_MIN_STARTING_LEVEL_LPA2 + 1U)

/*
 * Set of variables containing values that depend of whether FEAT_LPA2 is
 * enabled or not. We keep them separated instead of in a struct to avoid
 * member indirections, improving performance.
 */
static unsigned int s2tte_oa_bits;
static int rtt_min_starting_level;
static unsigned long s2tte_page, s2tte_block;
static unsigned long (*table_entry_to_phys)(unsigned long entry, long level);
static unsigned long (*create_empty_tte)(unsigned long pa);

static unsigned long addr_level_mask(unsigned long addr, long level)
{
	int levels = RTT_PAGE_LEVEL - level;
	unsigned int lsb = (levels * S2TTE_STRIDE) + GRANULE_SHIFT;

	return addr & BIT_MASK_ULL(s2tte_oa_bits - 1, lsb);
}

static unsigned long table_entry_to_phys_lpa2(unsigned long entry,
					      long level)
{
	unsigned long ret_addr = addr_level_mask(entry, level);

	/*
	 * When FEAT_LPA2 is enabled, the two MSBs of the OA is not
	 * contiguous to the rest of the OA.
	 */
	ret_addr = (ret_addr & ~MASK(S2TTE_OA_MSB)) |
			INPLACE(S2TTE_OA_MSB, EXTRACT(S2TTE_ENTRY_MSB, entry));

	return ret_addr;
}

/*
 * The two functions below create an empty TTE containing only the PA.
 * This functions do not make any checks or any assumption on the PA value.
 */
static unsigned long create_empty_tte_non_lpa2(unsigned long pa)
{
	return pa;
}

static unsigned long create_empty_tte_lpa2(unsigned long pa)
{
	unsigned long tte = pa & ~MASK(S2TTE_OA_MSB);

	tte |= INPLACE(S2TTE_ENTRY_MSB, EXTRACT(S2TTE_OA_MSB, pa));

	return tte;
}

/*
 * Invalidates S2 TLB entries from [ipa, ipa + size] region tagged with `vmid`.
 */
static void stage2_tlbi_ipa(const struct realm_s2_context *s2_ctx,
			    unsigned long ipa,
			    unsigned long size)
{
	/*
	 * Notes:
	 *
	 * - This follows the description provided in the Arm ARM on
	 *   "Invalidation of TLB entries from stage 2 translations".
	 *
	 * - @TODO: Provide additional information to this primitive so that
	 *   we can utilize:
	 *   - The TTL level hint, see FEAT_TTL,
	 *   - Final level lookup only invalidation,
	 *   - Address range invalidation.
	 */

	/*
	 * Save the current content of vttb_el2.
	 */
	unsigned long old_vttbr_el2 = read_vttbr_el2();

	/*
	 * Make 'vmid' the `current vmid`. Note that the tlbi instructions
	 * bellow target the TLB entries that match the `current vmid`.
	 */
	write_vttbr_el2(INPLACE(VTTBR_EL2_VMID, s2_ctx->vmid));
	isb();

	/*
	 * Invalidate entries in S2 TLB caches that
	 * match both `ipa` & the `current vmid`.
	 */
	while (size != 0UL) {
		tlbiipas2e1is(ipa >> 12);
		size -= GRANULE_SIZE;
		ipa += GRANULE_SIZE;
	}
	dsb(ish);

	/*
	 * The architecture does not require TLB invalidation by IPA to affect
	 * combined Stage-1 + Stage-2 TLBs. Therefore we must invalidate all of
	 * Stage-1 (tagged with the `current vmid`) after invalidating Stage-2.
	 */
	tlbivmalle1is();
	dsb(ish);
	isb();

	/*
	 * Restore the old content of vttb_el2.
	 */
	write_vttbr_el2(old_vttbr_el2);
	isb();
}

/*
 * Initialization of the S2TTE component. This function sets up a set of
 * function pointers as well as variables which value depend on whether
 * FEAT_LPA2 is enabled or not. This allows to optimize critical paths by
 * removing checks on the status of LPA2 on several functions later,
 * improving performance.
 */
void s2tt_init(void)
{
	if (is_feat_lpa2_4k_2_present() == true) {
		s2tte_oa_bits = S2TTE_OA_BITS_LPA2;
		rtt_min_starting_level = RTT_MIN_STARTING_LEVEL_LPA2;
		s2tte_page = S2TTE_PAGE_LPA2;
		s2tte_block = S2TTE_BLOCK_LPA2;
		table_entry_to_phys = &table_entry_to_phys_lpa2;
		create_empty_tte = &create_empty_tte_lpa2;
	} else {
		s2tte_oa_bits = S2TTE_OA_BITS;
		rtt_min_starting_level = RTT_MIN_STARTING_LEVEL;
		s2tte_page = S2TTE_PAGE;
		s2tte_block = S2TTE_BLOCK;
		table_entry_to_phys = &addr_level_mask;
		create_empty_tte = &create_empty_tte_non_lpa2;
	}
}

/*
 * Invalidate S2 TLB entries with "addr" IPA.
 * Call this function after:
 * 1.  A L3 page desc has been removed.
 */
void invalidate_page(const struct realm_s2_context *s2_ctx, unsigned long addr)
{
	stage2_tlbi_ipa(s2_ctx, addr, GRANULE_SIZE);
}

/*
 * Invalidate S2 TLB entries with "addr" IPA.
 * Call this function after:
 * 1.  A L2 block desc has been removed, or
 * 2a. A L2 table desc has been removed, where
 * 2b. All S2TTEs in L3 table that the L2 table desc was pointed
 *     to were invalid.
 */
void invalidate_block(const struct realm_s2_context *s2_ctx,
		      unsigned long addr)
{
	stage2_tlbi_ipa(s2_ctx, addr, GRANULE_SIZE);
}

/*
 * Invalidate S2 TLB entries with "addr" IPA.
 * Call this function after:
 * 1a. A L2 table desc has been removed, where
 * 1b. Some S2TTEs in the table that the L2 table desc was pointed
 *     to were valid.
 */
void invalidate_pages_in_block(const struct realm_s2_context *s2_ctx,
			       unsigned long addr)
{
	stage2_tlbi_ipa(s2_ctx, addr, BLOCK_L2_SIZE);
}

/*
 * Return the index of the entry describing @addr in the translation table at
 * level @level.  This only works for non-concatenated page tables, so should
 * not be called to get the index for the starting level.
 *
 * See the library pseudocode
 * aarch64/translation/vmsa_addrcalc/AArch64.TTEntryAddress on which this is
 * modeled.
 */
static unsigned long s2_addr_to_idx(unsigned long addr, long level)
{
	int levels = RTT_PAGE_LEVEL - level;
	int lsb = (levels * S2TTE_STRIDE) + GRANULE_SHIFT;

	addr >>= lsb;

	/* If level == -1, we only have four bits for the index ([48, 51]) */
	addr &= ((level == RTT_MIN_STARTING_LEVEL_LPA2) ?
			(1UL << 4U) - 1UL :
			(1UL << S2TTE_STRIDE) - 1UL);
	return addr;
}

/*
 * Return the index of the entry describing @addr in the translation table
 * starting level. This may return an index >= S2TTES_PER_S2TT when the
 * combination of @start_level and @ipa_bits implies concatenated
 * stage 2 tables.
 *
 * See the library pseudocode
 * aarch64/translation/vmsa_addrcalc/AArch64.S2SLTTEntryAddress on which
 * this is modeled.
 */
static unsigned long s2_sl_addr_to_idx(unsigned long addr, int start_level,
				       unsigned long ipa_bits)
{
	int levels = RTT_PAGE_LEVEL - start_level;
	int lsb = (levels * S2TTE_STRIDE) + GRANULE_SHIFT;

	addr &= ((1UL << ipa_bits) - 1UL);
	addr >>= lsb;
	return addr;
}

static inline bool entry_is_table(unsigned long entry)
{
	return (entry & DESC_TYPE_MASK) == S2TTE_L012_TABLE;
}

static unsigned long __table_get_entry(struct granule *g_tbl,
				       unsigned long idx)
{
	unsigned long *table, entry;

	table = granule_map(g_tbl, SLOT_RTT);
	entry = s2tte_read(&table[idx]);
	buffer_unmap(table);

	return entry;
}

static struct granule *__find_next_level_idx(struct granule *g_tbl,
					     unsigned long idx)
{
	const unsigned long entry = __table_get_entry(g_tbl, idx);

	if (!entry_is_table(entry)) {
		return NULL;
	}

	return addr_to_granule(table_entry_to_phys(entry, RTT_PAGE_LEVEL));
}

static struct granule *__find_lock_next_level(struct granule *g_tbl,
					      unsigned long map_addr,
					      long level)
{
	const unsigned long idx = s2_addr_to_idx(map_addr, level);
	struct granule *g = __find_next_level_idx(g_tbl, idx);

	if (g != NULL) {
		granule_lock(g, GRANULE_STATE_RTT);
	}

	return g;
}

/*
 * Walk an RTT until level @level using @map_addr.
 * @g_root is the root (level 0/-1) table and must be locked before the call.
 * @start_level is the initial lookup level used for the stage 2 translation
 * tables which may depend on the configuration of the realm, factoring in the
 * IPA size of the realm and the desired starting level (within the limits
 * defined by the Armv8 VMSA including options for stage 2 table concatenation).
 * The function uses hand-over-hand locking to avoid race conditions and allow
 * concurrent access to RTT tree which is not part of the current walk; when a
 * next level table is reached it is locked before releasing previously locked
 * table.
 * The walk stops when either:
 * - The entry found is a leaf entry (not an RTT Table entry), or
 * - Level @level is reached.
 *
 * On return:
 * - rtt_walk::last_level is the last level that has been reached by the walk.
 * - rtt_walk.g_llt points to the TABLE granule at level @rtt_walk::level.
 *   The granule is locked.
 * - rtt_walk::index is the entry index at rtt_walk.g_llt for @map_addr.
 */
void rtt_walk_lock_unlock(struct granule *g_root,
			  int start_level,
			  unsigned long ipa_bits,
			  unsigned long map_addr,
			  long level,
			  struct rtt_walk *wi)
{
	struct granule *g_tbls[NR_RTT_LEVELS_LPA2] = { NULL };
	unsigned long sl_idx;
	int i, last_level;

	assert(start_level >= rtt_min_starting_level);
	assert(level >= start_level);
	assert(map_addr < (1UL << ipa_bits));
	assert(wi != NULL);

	/* Handle concatenated starting level (SL) tables */
	sl_idx = s2_sl_addr_to_idx(map_addr, start_level, ipa_bits);
	if (sl_idx >= S2TTES_PER_S2TT) {
		unsigned int tt_num = (sl_idx >> S2TTE_STRIDE);
		struct granule *g_concat_root = g_root + tt_num;

		granule_lock(g_concat_root, GRANULE_STATE_RTT);
		granule_unlock(g_root);
		g_root = g_concat_root;
	}

	g_tbls[start_level + 1] = g_root;
	for (i = start_level; i < level; i++) {
		/*
		 * Lock next RTT level. Correct locking order is guaranteed
		 * because reference is obtained from a locked granule
		 * (previous level). Also, hand-over-hand locking/unlocking is
		 * used to avoid race conditions.
		 */
		g_tbls[i + 1 + 1] = __find_lock_next_level(g_tbls[i + 1],
							map_addr, i);
		if (g_tbls[i + 1 + 1] == NULL) {
			last_level = i;
			goto out;
		}
		granule_unlock(g_tbls[i + 1]);
	}

	last_level = level;
out:
	wi->last_level = last_level;
	wi->g_llt = g_tbls[last_level + 1];
	wi->index = s2_addr_to_idx(map_addr, last_level);
}

/*
 * Creates a value which can be OR'd with an s2tte to set RIPAS=@ripas.
 */
unsigned long s2tte_create_ripas(enum ripas ripas)
{
	if (ripas == RIPAS_EMPTY) {
		return S2TTE_INVALID_RIPAS_EMPTY;
	}
	return S2TTE_INVALID_RIPAS_RAM;
}

/*
 * Creates an invalid s2tte with HIPAS=UNASSIGNED and RIPAS=@ripas.
 */
unsigned long s2tte_create_unassigned(enum ripas ripas)
{
	return S2TTE_INVALID_HIPAS_UNASSIGNED | s2tte_create_ripas(ripas);
}

/*
 * Creates an invalid s2tte with HIPAS=DESTROYED.
 */
unsigned long s2tte_create_destroyed(void)
{
	return S2TTE_INVALID_DESTROYED;
}

/*
 * Creates an invalid s2tte with output address @pa, HIPAS=ASSIGNED and
 * RIPAS=EMPTY, at level @level.
 */
unsigned long s2tte_create_assigned_empty(unsigned long pa, long level)
{
	assert(level >= RTT_MIN_BLOCK_LEVEL);
	assert(addr_is_level_aligned(pa, level));

	return (create_empty_tte(pa) |
				S2TTE_INVALID_HIPAS_ASSIGNED |
				S2TTE_INVALID_RIPAS_EMPTY);
}

/*
 * Creates a page or block s2tte for a Protected IPA, with output address @pa.
 */
unsigned long s2tte_create_valid(unsigned long pa, long level)
{
	unsigned long tte;

	assert(level >= RTT_MIN_BLOCK_LEVEL);
	assert(addr_is_level_aligned(pa, level));

	tte = create_empty_tte(pa);

	if (level == RTT_PAGE_LEVEL) {
		return tte | s2tte_page;
	}

	return tte | s2tte_block;
}

/*
 * Creates an invalid s2tte with HIPAS=INVALID_NS.
 */
unsigned long s2tte_create_invalid_ns(void)
{
	return S2TTE_INVALID_UNPROTECTED;
}

/*
 * Creates a page or block s2tte for an Unprotected IPA at level @level.
 *
 * The following S2 TTE fields are provided through @s2tte argument:
 * - The physical address
 * - MemAttr
 * - S2AP
 * - Shareability
 */
unsigned long s2tte_create_valid_ns(unsigned long s2tte, long level)
{
	assert(level >= RTT_MIN_BLOCK_LEVEL);
	if (level == RTT_PAGE_LEVEL) {
		return (s2tte | S2TTE_PAGE_NS);
	}
	return (s2tte | S2TTE_BLOCK_NS);
}

/*
 * Validate the portion of NS S2TTE that is provided by the host.
 */
bool host_ns_s2tte_is_valid(unsigned long s2tte, long level)
{
	/*
	 * When FEAT_LPA2 is enabled, the 2 MSBs of the OA are stored
	 * on the Shareability attribute bits so they will be included anyway
	 * by addr_level_mask().
	 */
	unsigned long mask = addr_level_mask(~0UL, level) |
			     S2TTE_MEMATTR_MASK |
			     S2TTE_AP_MASK |
			     S2TTE_SH_MASK;

	/*
	 * Test that all fields that are not controlled by the host are zero
	 * and that the output address is correctly aligned. Note that
	 * the host is permitted to map any physical address outside PAR.
	 */
	if ((s2tte & ~mask) != 0UL) {
		return false;
	}

	/*
	 * Only one value masked by S2TTE_MEMATTR_MASK is invalid/reserved.
	 */
	if ((s2tte & S2TTE_MEMATTR_MASK) == S2TTE_MEMATTR_FWB_RESERVED) {
		return false;
	}

	/*
	 * Only one value masked by S2TTE_SH_MASK is invalid/reserved.
	 */
	if ((is_feat_lpa2_4k_2_present() == false) &&
	    (s2tte & S2TTE_SH_MASK) == S2TTE_SH_RESERVED) {
		return false;
	}

	/*
	 * Note that all the values that are masked by S2TTE_AP_MASK are valid.
	 */
	return true;
}

/*
 * Returns the portion of NS S2TTE that is set by the host.
 */
unsigned long host_ns_s2tte(unsigned long s2tte, long level)
{
	/*
	 * When FEAT_LPA2 is enabled, the 2 MSBs of the OA are stored
	 * on the Shareability attribute bits so they will be included anyway
	 * by addr_level_mask().
	 */
	unsigned long mask = addr_level_mask(~0UL, level) |
			     S2TTE_MEMATTR_MASK |
			     S2TTE_AP_MASK |
			     S2TTE_SH_MASK;

	return (s2tte & mask);
}

/*
 * Creates a table s2tte at level @level with output address @pa.
 */
unsigned long s2tte_create_table(unsigned long pa, long level)
{
	assert(level < RTT_PAGE_LEVEL);
	assert(GRANULE_ALIGNED(pa));

	return (create_empty_tte(pa) | S2TTE_TABLE);
}

/*
 * Returns true if @s2tte has HIPAS=@hipas.
 */
static bool s2tte_has_hipas(unsigned long s2tte, unsigned long hipas)
{
	unsigned long desc_type = s2tte & DESC_TYPE_MASK;
	unsigned long invalid_desc_hipas = s2tte & S2TTE_INVALID_HIPAS_MASK;

	if ((desc_type != S2TTE_Lx_INVALID) || (invalid_desc_hipas != hipas)) {
		return false;
	}
	return true;
}

/*
 * Returns true if @s2tte has HIPAS=UNASSIGNED or HIPAS=INVALID_NS.
 */
bool s2tte_is_unassigned(unsigned long s2tte)
{
	return s2tte_has_hipas(s2tte, S2TTE_INVALID_HIPAS_UNASSIGNED);
}

/*
 * Returns true if @s2tte has HIPAS=DESTROYED.
 */
bool s2tte_is_destroyed(unsigned long s2tte)
{
	return s2tte_has_hipas(s2tte, S2TTE_INVALID_HIPAS_DESTROYED);
}

/*
 * Returns true if @s2tte has HIPAS=ASSIGNED.
 */
bool s2tte_is_assigned(unsigned long s2tte, long level)
{
	(void)level;

	return s2tte_has_hipas(s2tte, S2TTE_INVALID_HIPAS_ASSIGNED);
}

static bool s2tte_check(unsigned long s2tte, long level, unsigned long ns)
{
	unsigned long desc_type;

	if ((s2tte & S2TTE_NS) != ns) {
		return false;
	}

	desc_type = s2tte & DESC_TYPE_MASK;

	/* Only pages at L3 and valid blocks at L2 allowed */
	if (((level == RTT_PAGE_LEVEL) && (desc_type == S2TTE_L3_PAGE)) ||
	    ((level == RTT_MIN_BLOCK_LEVEL) && (desc_type == S2TTE_L012_BLOCK))) {
		return true;
	}

	return false;
}

/*
 * Returns true if @s2tte is a page or block s2tte, and NS=0.
 */
bool s2tte_is_valid(unsigned long s2tte, long level)
{
	return s2tte_check(s2tte, level, 0UL);
}

/*
 * Returns true if @s2tte is a page or block s2tte, and NS=1.
 */
bool s2tte_is_valid_ns(unsigned long s2tte, long level)
{
	return s2tte_check(s2tte, level, S2TTE_NS);
}

/*
 * Returns true if @s2tte is a table at level @level.
 */
bool s2tte_is_table(unsigned long s2tte, long level)
{
	unsigned long desc_type = s2tte & DESC_TYPE_MASK;

	if ((level < RTT_PAGE_LEVEL) && (desc_type == S2TTE_TABLE)) {
		return true;
	}

	return false;
}

/*
 * Returns RIPAS of @s2tte.
 *
 * Caller should ensure that HIPAS=UNASSIGNED or HIPAS=ASSIGNED.
 * The s2tte must be not valid/invalid descriptor.
 */
enum ripas s2tte_get_ripas(unsigned long s2tte)
{
	unsigned long desc_ripas = s2tte & S2TTE_INVALID_RIPAS_MASK;

	/*
	 * If valid s2tte descriptor is passed, then ensure S2AP[0]
	 * bit is 1 (S2AP is set to RW for lower EL), which corresponds
	 * to RIPAS_RAM (bit[6]) on a valid descriptor.
	 */
	if (((s2tte & DESC_TYPE_MASK) != S2TTE_Lx_INVALID) &&
	     (desc_ripas != S2TTE_INVALID_RIPAS_RAM)) {
		assert(false);
	}

	if (desc_ripas == S2TTE_INVALID_RIPAS_EMPTY) {
		return RIPAS_EMPTY;
	}

	return RIPAS_RAM;
}

/*
 * Populates @s2tt with s2ttes which have HIPAS=UNASSIGNED and RIPAS=@ripas.
 *
 * The granule is populated before it is made a table,
 * hence, don't use s2tte_write for access.
 */
void s2tt_init_unassigned(unsigned long *s2tt, enum ripas ripas)
{
	for (unsigned int i = 0U; i < S2TTES_PER_S2TT; i++) {
		s2tt[i] = s2tte_create_unassigned(ripas);
	}

	dsb(ish);
}

/*
 * Populates @s2tt with s2ttes which have HIPAS=DESTROYED.
 *
 * The granule is populated before it is made a table,
 * hence, don't use s2tte_write for access.
 */
void s2tt_init_destroyed(unsigned long *s2tt)
{
	for (unsigned int i = 0U; i < S2TTES_PER_S2TT; i++) {
		s2tt[i] = s2tte_create_destroyed();
	}

	dsb(ish);
}

unsigned long s2tte_map_size(int level)
{
	int levels, lsb;

	assert(level <= RTT_PAGE_LEVEL);

	levels = RTT_PAGE_LEVEL - level;
	lsb = (levels * S2TTE_STRIDE) + GRANULE_SHIFT;
	return 1UL << lsb;
}

/*
 * Populates @s2tt with HIPAS=ASSIGNED, RIPAS=EMPTY s2ttes that refer to a
 * contiguous memory block starting at @pa, and mapped at level @level.
 *
 * The granule is populated before it is made a table,
 * hence, don't use s2tte_write for access.
 */
void s2tt_init_assigned_empty(unsigned long *s2tt, unsigned long pa, long level)
{
	const unsigned long map_size = s2tte_map_size(level);
	unsigned int i;

	for (i = 0U; i < S2TTES_PER_S2TT; i++) {
		s2tt[i] = s2tte_create_assigned_empty(pa, level);
		pa += map_size;
	}
	dsb(ish);
}

/*
 * Populates @s2tt with HIPAS=VALID, RIPAS=@ripas s2ttes that refer to a
 * contiguous memory block starting at @pa, and mapped at level @level.
 *
 * The granule is populated before it is made a table,
 * hence, don't use s2tte_write for access.
 */
void s2tt_init_valid(unsigned long *s2tt, unsigned long pa, long level)
{
	const unsigned long map_size = s2tte_map_size(level);
	unsigned int i;

	for (i = 0U; i < S2TTES_PER_S2TT; i++) {
		s2tt[i] = s2tte_create_valid(pa, level);
		pa += map_size;
	}
	dsb(ish);
}

/*
 * Populates @s2tt with HIPAS=VALID_NS, RIPAS=@ripas s2ttes that refer to a
 * contiguous memory block starting at @pa, and mapped at level @level.
 *
 * The granule is populated before it is made a table,
 * hence, don't use s2tte_write for access.
 */
void s2tt_init_valid_ns(unsigned long *s2tt, unsigned long pa, long level)
{
	const unsigned long map_size = s2tte_map_size(level);
	unsigned int i;

	for (i = 0U; i < S2TTES_PER_S2TT; i++) {
		s2tt[i] = s2tte_create_valid_ns(pa, level);
		pa += map_size;
	}
	dsb(ish);
}

/* Returns physical address of a page entry or block */
unsigned long s2tte_pa(unsigned long s2tte, long level)
{
	if (s2tte_is_unassigned(s2tte) || s2tte_is_destroyed(s2tte) ||
	    s2tte_is_table(s2tte, level)) {
		assert(false);
	}

	return table_entry_to_phys(s2tte, level);
}

/* Returns physical address of a table entry */
unsigned long s2tte_pa_table(unsigned long s2tte, long level)
{
	assert(s2tte_is_table(s2tte, level));

	return table_entry_to_phys(s2tte, RTT_PAGE_LEVEL);
}

bool addr_is_level_aligned(unsigned long addr, long level)
{
	return (addr == addr_level_mask(addr, level));
}

typedef bool (*s2tte_type_checker)(unsigned long s2tte);

static bool __table_is_uniform_block(unsigned long *table,
			      s2tte_type_checker s2tte_is_x,
			      enum ripas *ripas_ptr)
{
	unsigned long s2tte = s2tte_read(&table[0]);
	enum ripas ripas;
	unsigned int i;

	if (!s2tte_is_x(s2tte)) {
		return false;
	}

	if (ripas_ptr != NULL) {
		ripas = s2tte_get_ripas(s2tte);
	}

	for (i = 1U; i < S2TTES_PER_S2TT; i++) {
		s2tte = s2tte_read(&table[i]);

		if (!s2tte_is_x(s2tte)) {
			return false;
		}

		if ((ripas_ptr != NULL) &&
		    (s2tte_get_ripas(s2tte) != ripas)) {
			return false;
		}
	}

	if (ripas_ptr != NULL) {
		*ripas_ptr = ripas;
	}

	return true;
}

/*
 * Returns true if all s2ttes in @table have HIPAS=UNASSIGNED and
 * have the same RIPAS.
 *
 * If return value is true, the RIPAS value is returned in @ripas.
 */
bool table_is_unassigned_block(unsigned long *table, enum ripas *ripas)
{
	return __table_is_uniform_block(table, s2tte_is_unassigned, ripas);
}

/*
 * Returns true if all s2ttes in @table have HIPAS=DESTROYED.
 */
bool table_is_destroyed_block(unsigned long *table)
{
	return __table_is_uniform_block(table, s2tte_is_destroyed, NULL);
}

typedef bool (*s2tte_type_level_checker)(unsigned long s2tte, long level);

static bool __table_maps_block(unsigned long *table,
			       long level,
			       s2tte_type_level_checker s2tte_is_x)
{
	unsigned long base_pa;
	unsigned long map_size = s2tte_map_size(level);
	unsigned long s2tte = s2tte_read(&table[0]);
	unsigned int i;

	if (!s2tte_is_x(s2tte, level)) {
		return false;
	}

	base_pa = s2tte_pa(s2tte, level);
	if (!addr_is_level_aligned(base_pa, level - 1L)) {
		return false;
	}

	for (i = 1U; i < S2TTES_PER_S2TT; i++) {
		unsigned long expected_pa = base_pa + (i * map_size);

		s2tte = s2tte_read(&table[i]);

		if (!s2tte_is_x(s2tte, level)) {
			return false;
		}

		if (s2tte_pa(s2tte, level) != expected_pa) {
			return false;
		}
	}

	return true;
}

/*
 * Returns true if all s2ttes in @table have HIPAS=ASSIGNED
 * and refer to a contiguous block of granules aligned to @level - 1.
 */
bool table_maps_assigned_block(unsigned long *table, long level)
{
	return __table_maps_block(table, level, s2tte_is_assigned);
}

/*
 * Returns true if all s2ttes in @table have HIPAS=VALID and
 * refer to a contiguous block of granules aligned to @level - 1.
 */
bool table_maps_valid_block(unsigned long *table, long level)
{
	return __table_maps_block(table, level, s2tte_is_valid);
}

/*
 * Returns true if all s2ttes in @table have HIPAS=VALID_NS and
 * refer to a contiguous block of granules aligned to @level - 1.
 */
bool table_maps_valid_ns_block(unsigned long *table, long level)
{
	return __table_maps_block(table, level, s2tte_is_valid_ns);
}
