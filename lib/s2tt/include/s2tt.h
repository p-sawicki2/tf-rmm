/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef S2TT_H
#define S2TT_H

#include <arch_features.h>
#include <granule_types.h>
#include <memory.h>
#include <stdbool.h>

/*
 * Stage 2 configuration of the Realm.
 *
 * Unless otherwise stated, all the fields are identical across planes.
 */
struct s2tt_context {
	/* Number of IPA bits */
	unsigned int ipa_bits;

	/* Starting level of the stage 2 translation */
	int s2_starting_level;

	/* Number of concatenated starting level rtts */
	unsigned int num_root_rtts;

	/*
	 * First level RTT, pointed to by Realm TTBR. This field is
	 * specific for each plane.
	 */
	struct granule *g_rtt;

	/* Virtual Machine Identifier */
	unsigned int vmid;

	/* If FEAT_LPA2 is enabled */
	bool enable_lpa2;

	/* S2AP enabled */
	bool s2ap_enabled;

	/*
	 * Pointer to the overlay permissions for this context, which are
	 * stored in the Realm Descriptor.
	 * This field is specific to each plane.
	 */
	unsigned long *overlay_perm;
};

#define S2TT_MIN_IPA_BITS		U(32)
#define S2TT_MAX_IPA_BITS		U(48)

#define S2TT_MAX_IPA_BITS_LPA2		U(52)
#define S2TT_MAX_IPA_SIZE_LPA2		(UL(1) << S2TT_MAX_IPA_BITS_LPA2)

#define S2TT_MIN_STARTING_LEVEL		(0)
#define S2TT_MIN_STARTING_LEVEL_LPA2	(-1)
#define S2TT_PAGE_LEVEL			(3)
#define S2TT_MIN_BLOCK_LEVEL		(1)

/*
 * S2TTE_STRIDE: The number of bits resolved in a single level of translation
 * walk (except for the starting level which may resolve more or fewer bits).
 */
#define S2TTE_STRIDE		(U(GRANULE_SHIFT) - 3U)
#define S2TTES_PER_S2TT		(1UL << S2TTE_STRIDE)

/*
 * S2TTE_STRIDE_LM1: The number of bits resolved at Level -1 when FEAT_LPA2
 * is enabled. This value is equal to
 * MAX_IPA_BITS_LPA2 - ((4 * S2TTE_STRIDE) + GRANULE_SHIFT)
 * as Level -1 only has 4 bits for the index (bits [51:48]).
 */
#define S2TTE_STRIDE_LM1	(4U)
#define S2TTES_PER_S2TT_LM1	(1UL << S2TTE_STRIDE_LM1)

/*
 * Access permission bits.
 */
#define S2TTE_PERM_R_SHIFT		6UL
#define S2TTE_PERM_R_WIDTH		1UL
#define S2TTE_PERM_W_SHIFT		7UL
#define S2TTE_PERM_W_WIDTH		1UL
#define S2TTE_PERM_XN_SHIFT		53UL
#define S2TTE_PERM_XN_WIDTH		2UL

#define S2TTE_AP_MASK			(MASK(S2TTE_PERM_R) | MASK(S2TTE_PERM_W))
#define S2TTE_PERM_MASK			(S2TTE_AP_MASK | MASK(S2TTE_PERM_XN))

/*
 * Instruction execution permissions when FEAT_XNX is available
 */
#define S2TTE_PERM_XU_XP		(INPLACE(S2TTE_PERM_XN, 0UL))
#define S2TTE_PERM_XU_XNP		(INPLACE(S2TTE_PERM_XN, 1UL))
#define S2TTE_PERM_XNU_XNP		(INPLACE(S2TTE_PERM_XN, 2UL))
#define S2TTE_PERM_XNU_XP		(INPLACE(S2TTE_PERM_XN, 3UL))

/*
 * Possible permission access labels. For compatibility with a future S2AP
 * library based on FEAT_S2PIE and FEAT_S2PIO, the labels defined here are
 * compatible with the ones on such feature. This might be removed later
 * when the S2AP library is implemented.
 */
#define S2TTE_PERM_LABEL_NO_ACCESS		(0U)
#define S2TTE_PERM_LABEL_RESERVED_1		(1U)
#define S2TTE_PERM_LABEL_MRO			(2U)
#define S2TTE_PERM_LABEL_MRO_TL1		(3U)
#define S2TTE_PERM_LABEL_WO			(4U)
#define S2TTE_PERM_LABEL_RESERVED_5		(5U)
#define S2TTE_PERM_LABEL_MRO_TL0		(6U)
#define S2TTE_PERM_LABEL_MRO_TL01		(7U)
#define S2TTE_PERM_LABEL_RO			(8U)
#define S2TTE_PERM_LABEL_RO_uX			(9U)
#define S2TTE_PERM_LABEL_RO_pX			(10U)
#define S2TTE_PERM_LABEL_RO_upX			(11U)
#define S2TTE_PERM_LABEL_RW			(12U)
#define S2TTE_PERM_LABEL_RW_uX			(13U)
#define S2TTE_PERM_LABEL_RW_pX			(14U)
#define S2TTE_PERM_LABEL_RW_upX			(15U)

/* Number of different permission labels */
#define S2TTE_PERM_LABEL_COUNT			(16U)

/*
 * Size in bits and mask of the Permission Indirection Index value.
 * This might be removed later when the S2AP library is implemented.
 */
#define S2TTE_PII_WIDTH				(4U)
#define S2TTE_PII_MASK				((1UL << S2TTE_PII_WIDTH) - 1UL)

/*
 * Maximum number of encodings in Base or Overlay permissions.
 * This will be removed later when the S2AP library is implemented.
 */
#define S2TTE_PERM_INDEX_COUNT			(15U)

/*
 * Extract the access permission label given a permission indirection
 * register and an index.
 */
#define S2TTE_GET_PERM_LABEL(_reg, _index)				\
	(((_reg) >> ((unsigned long)(_index) * S2TTE_PII_WIDTH)) & S2TTE_PII_MASK)

/*
 * The MMU is a separate observer, and requires that translation table updates
 * are made with single-copy-atomic stores, necessitating inline assembly. For
 * consistency we use accessors for both reads and writes of translation table
 * entries.
 */
static inline void __tte_write(uint64_t *ttep, uint64_t tte)
{
	SCA_WRITE64(ttep, tte);
	dsb(ish);
}
#define s2tte_write(s2ttep, s2tte)	__tte_write(s2ttep, s2tte)

static inline uint64_t __tte_read(uint64_t *ttep)
{
	return SCA_READ64(ttep);
}
#define s2tte_read(s2ttep)		__tte_read(s2ttep)

/***************************************************************************
 * Helpers for Stage 2 Translation Table Entries (S2TTE).
 **************************************************************************/
#define s2tte_map_size(level)						\
	(1ULL << (unsigned int)(((S2TT_PAGE_LEVEL - (level)) *		\
				(int)S2TTE_STRIDE) + (int)GRANULE_SHIFT))

bool s2tte_has_ripas(const struct s2tt_context *s2_ctx,
		     unsigned long s2tte, long level);

unsigned long s2tte_create_unassigned_empty(const struct s2tt_context *s2_ctx,
					    unsigned long ap);
unsigned long s2tte_create_unassigned_ram(const struct s2tt_context *s2_ctx,
					  unsigned long ap);
unsigned long s2tte_create_unassigned_ns(const struct s2tt_context *s2_ctx);
unsigned long s2tte_create_unassigned_destroyed(const struct s2tt_context *s2_ctx,
						unsigned long ap);

unsigned long s2tte_create_assigned_empty(const struct s2tt_context *s2_ctx,
					  unsigned long pa, long level,
					  unsigned long ap);
unsigned long s2tte_create_assigned_ram(const struct s2tt_context *s2_ctx,
					unsigned long pa, long level,
					unsigned long ap);
unsigned long s2tte_create_assigned_ns(const struct s2tt_context *s2_ctx,
				       unsigned long s2tte, long level,
				       unsigned long ap);
unsigned long s2tte_create_assigned_destroyed(const struct s2tt_context *s2_ctx,
					      unsigned long pa, long level,
					      unsigned long ap);
unsigned long s2tte_create_assigned_unchanged(const struct s2tt_context *s2_ctx,
					      unsigned long s2tte,
					      unsigned long pa,
					      long level);
unsigned long s2tte_create_table(const struct s2tt_context *s2_ctx,
				 unsigned long pa, long level);

bool host_ns_s2tte_is_valid(const struct s2tt_context *s2_ctx,
			    unsigned long s2tte, long level);
unsigned long host_ns_s2tte(const struct s2tt_context *s2_ctx,
			    unsigned long s2tte, long level);

bool s2tte_is_unassigned(const struct s2tt_context *s2_ctx,
			 unsigned long s2tte);
bool s2tte_is_unassigned_empty(const struct s2tt_context *s2_ctx,
			       unsigned long s2tte);
bool s2tte_is_unassigned_ram(const struct s2tt_context *s2_ctx,
			     unsigned long s2tte);
bool s2tte_is_unassigned_ns(const struct s2tt_context *s2_ctx,
			    unsigned long s2tte);
bool s2tte_is_unassigned_destroyed(const struct s2tt_context *s2_ctx,
				   unsigned long s2tte);

bool s2tte_is_assigned_empty(const struct s2tt_context *s2_ctx,
			     unsigned long s2tte, long level);
bool s2tte_is_assigned_ram(const struct s2tt_context *s2_ctx,
			   unsigned long s2tte, long level);
bool s2tte_is_assigned_ns(const struct s2tt_context *s2_ctx,
			  unsigned long s2tte, long level);
bool s2tte_is_table(const struct s2tt_context *s2_ctx,
		    unsigned long s2tte, long level);
bool s2tte_is_assigned_destroyed(const struct s2tt_context *s2_ctx,
				 unsigned long s2tte, long level);

unsigned long s2tte_pa(const struct s2tt_context *s2_ctx,
		       unsigned long s2tte, long level);
bool s2tte_is_addr_lvl_aligned(const struct s2tt_context *s2_ctx,
			       unsigned long addr, long level);

enum ripas s2tte_get_ripas(const struct s2tt_context *s2_ctx,
			   unsigned long s2tte);

unsigned long s2tte_update_ap_from_index(const struct s2tt_context *s2_ctx,
					 unsigned long s2tte,
					 unsigned int index);

static inline bool s2tte_is_perm_index_valid(const struct s2tt_context *s2_ctx,
					     unsigned int index)
{
	(void)s2_ctx;

	return !!(index < S2TTE_PERM_INDEX_COUNT);
}

/***************************************************************************
 * Helpers for Stage 2 Translation Tables  (S2TT).
 **************************************************************************/

void s2tt_init_unassigned_empty(const struct s2tt_context *s2_ctx,
				unsigned long *s2tt, unsigned long ap);
void s2tt_init_unassigned_ram(const struct s2tt_context *s2_ctx,
			      unsigned long *s2tt, unsigned long ap);
void s2tt_init_unassigned_ns(const struct s2tt_context *s2_ctx,
			     unsigned long *s2tt);
void s2tt_init_unassigned_destroyed(const struct s2tt_context *s2_ctx,
				    unsigned long *s2tt, unsigned long ap);

void s2tt_init_assigned_empty(const struct s2tt_context *s2_ctx,
			      unsigned long *s2tt, unsigned long pa,
			      long level, unsigned long ap);
void s2tt_init_assigned_ram(const struct s2tt_context *s2_ctx,
			    unsigned long *s2tt, unsigned long pa, long level,
			    unsigned long ap);
void s2tt_init_assigned_ns(const struct s2tt_context *s2_ctx,
			   unsigned long *s2tt, unsigned long attrs,
			   unsigned long pa, long level, unsigned long ap);
void s2tt_init_assigned_destroyed(const struct s2tt_context *s2_ctx,
				  unsigned long *s2tt, unsigned long pa,
				  long level, unsigned long ap);

void s2tt_invalidate_page(const struct s2tt_context *s2_ctx, unsigned long addr);
void s2tt_invalidate_block(const struct s2tt_context *s2_ctx, unsigned long addr);
void s2tt_invalidate_pages_in_block(const struct s2tt_context *s2_ctx,
				    unsigned long addr);

bool s2tt_is_unassigned_empty_block(const struct s2tt_context *s2_ctx,
				    unsigned long *table, unsigned long *ap);
bool s2tt_is_unassigned_ram_block(const struct s2tt_context *s2_ctx,
				  unsigned long *table, unsigned long *ap);
bool s2tt_is_unassigned_ns_block(const struct s2tt_context *s2_ctx,
				 unsigned long *table);
bool s2tt_is_unassigned_destroyed_block(const struct s2tt_context *s2_ctx,
					unsigned long *table, unsigned long *ap);

bool s2tt_maps_assigned_empty_block(const struct s2tt_context *s2_ctx,
				    unsigned long *table, long level,
				    unsigned long *ap);
bool s2tt_maps_assigned_ram_block(const struct s2tt_context *s2_ctx,
				  unsigned long *table, long level,
				  unsigned long *ap);
bool s2tt_maps_assigned_ns_block(const struct s2tt_context *s2_ctx,
				 unsigned long *table, long level,
				 unsigned long *ap);
bool s2tt_maps_assigned_destroyed_block(const struct s2tt_context *s2_ctx,
					unsigned long *table, long level,
					unsigned long *ap);

struct s2tt_walk {
	struct granule *g_llt;
	unsigned long index;
	long last_level;
};

void s2tt_walk_lock_unlock(const struct s2tt_context *s2_ctx,
			   unsigned long map_addr,
			   long level,
			   struct s2tt_walk *wi);

unsigned long s2tt_skip_non_live_entries(const struct s2tt_context *s2_ctx,
					 unsigned long addr,
					 unsigned long *table,
					 const struct s2tt_walk *wi);

/*
 * Set a S2 context overlay permissions while holding the RD granule lock.
 */
static inline void s2tt_set_ctx_overlay_perm(const struct s2tt_context *s2_ctx,
					     unsigned long val)
{
	assert(s2_ctx != NULL);

	SCA_WRITE64_RELEASE(*(s2_ctx->overlay_perm), val);
}

/*
 * Get a S2 context overlay permissions while holding the RD granule lock.
 */
static inline unsigned long s2tt_get_ctx_overlay_perm_locked(
					const struct s2tt_context *s2_ctx)
{
	assert(s2_ctx != NULL);

	return SCA_READ64(s2_ctx->overlay_perm);
}

/*
 * Get a S2 overlay permissions without holding the RD granule lock.
 */
static inline unsigned long s2tt_get_ctx_overlay_perm_unlocked(
					const struct s2tt_context *s2_ctx)
{
	assert(s2_ctx != NULL);

	return SCA_READ64_ACQUIRE(s2_ctx->overlay_perm);
}

/*
 * Update the Access Permission @perm[@index] with the value @perm.
 */
static inline unsigned long s2tt_update_overlay_perms(
					const struct s2tt_context *s2_ctx,
					unsigned long perms,
					unsigned int index,
					unsigned int perm)
{
	assert(s2tte_is_perm_index_valid(s2_ctx, index));
	assert(perm < S2TTE_PERM_LABEL_COUNT);

	perms &= ~(S2TTE_PII_MASK << (S2TTE_PII_WIDTH * index));
	return perms | ((unsigned long)perm  << (S2TTE_PII_WIDTH * index));
}

#endif /* S2TT_H */
