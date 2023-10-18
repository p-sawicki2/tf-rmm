/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef TABLE_H
#define TABLE_H

#include <arch_features.h>
#include <memory.h>

#define MIN_IPA_BITS		32U
#define MAX_IPA_BITS		48U
#define MAX_IPA_SIZE		(1UL << MAX_IPA_BITS)

#define MIN_STARTING_LEVEL	0
#define RTT_PAGE_LEVEL		3
#define RTT_MIN_BLOCK_LEVEL	2

/* TODO: Fix this when introducing LPA2 support */
COMPILER_ASSERT(MIN_STARTING_LEVEL >= 0);

/* TODO: Allow the NS caller to select the stage 2 starting level */
#define RTT_STARTING_LEVEL	0

/*
 * S2TTE_STRIDE: The number of bits resolved in a single level of translation
 * walk (except for the starting level which may resolve more or fewer bits).
 */
#define S2TTE_STRIDE		(GRANULE_SHIFT - 3U)
#define S2TTES_PER_S2TT		(1UL << S2TTE_STRIDE)

/*
 * The type of stage 2 translation table entry (s2tte) is defined by:
 * 1. Table level where it resides
 * 2. DESC_TYPE field[1:0]
 * 4. HIPAS field [4:2]
 * 4. RIPAS field [6:5]
 * 5. NS field [55]
 *
 * ======================================================================================
 * s2tte type           level DESC_TYPE[1:0] HIPAS[4:2]    RIPAS[6:5]   NS  OA alignment
 * ======================================================================================
 * unassigned_empty     any   invalid[0]     unassigned[0] empty[0]     0   n/a
 * --------------------------------------------------------------------------------------
 * unassigned_ram       any   invalid[0]     unassigned[0] ram[1]       0   n/a
 * --------------------------------------------------------------------------------------
 * unassigned_destroyed any   invalid[0]     unassigned[0] destroyed[2] 0   n/a
 * --------------------------------------------------------------------------------------
 * assigned_empty       2,3   invalid[0]     assigned[1]   empty[0]     0   to level
 * --------------------------------------------------------------------------------------
 * assigned_ram         3     page[3]        n/a           n/a          0   to level
 *                      2     block[1]       n/a           n/a          0   to level
 * --------------------------------------------------------------------------------------
 * assigned_destroyed   any   invalid[0]     assigned[1]   destroyed[2] 0   n/a
 * ======================================================================================
 * unassigned_ns        any   invalid[0]     unassigned[0] n/a          1   n/a
 * --------------------------------------------------------------------------------------
 * assigned_ns	        3     page[3]        n/a           n/a          1   to level
 *                      2     block[1]       n/a           n/a          1   to level
 * ======================================================================================
 * table              <=2     table[3]       n/a           n/a          n/a to 4K
 * ======================================================================================
 */

#define S2TTE_INVALID_HIPAS_SHIFT	2
#define S2TTE_INVALID_HIPAS_WIDTH	3U
#define S2TTE_INVALID_HIPAS_MASK	MASK(S2TTE_INVALID_HIPAS)

#define S2TTE_INVALID_HIPAS_UNASSIGNED	(INPLACE(S2TTE_INVALID_HIPAS, 0UL))
#define S2TTE_INVALID_HIPAS_ASSIGNED	(INPLACE(S2TTE_INVALID_HIPAS, 1UL))

#define S2TTE_INVALID_RIPAS_SHIFT	5
#define S2TTE_INVALID_RIPAS_WIDTH	2U
#define S2TTE_INVALID_RIPAS_MASK	MASK(S2TTE_INVALID_RIPAS)

#define S2TTE_INVALID_RIPAS_EMPTY	(INPLACE(S2TTE_INVALID_RIPAS, 0UL))
#define S2TTE_INVALID_RIPAS_RAM		(INPLACE(S2TTE_INVALID_RIPAS, 1UL))
#define S2TTE_INVALID_RIPAS_DESTROYED	(INPLACE(S2TTE_INVALID_RIPAS, 2UL))

#define S2TTE_INVALID_UNPROTECTED	0x0UL

#define S2TTE_NS			(1UL << 55)
#define S2TTE_AF			(1UL << 10)
#define S2TTE_XN			(2UL << 53)

/*
 * Descriptor types
 */
#define DESC_TYPE_MASK			3UL
#define S2TTE_Lx_INVALID		0UL
#define S2TTE_L012_BLOCK		1UL
#define S2TTE_L012_TABLE		3UL
#define S2TTE_L3_PAGE			3UL

/*
 * Creates an unassigned_empty s2tte.
 */
inline unsigned long s2tte_create_unassigned_empty(void)
{
	return (S2TTE_INVALID_HIPAS_UNASSIGNED | S2TTE_INVALID_RIPAS_EMPTY);
}

/*
 * Creates an unassigned_ram s2tte.
 */
inline unsigned long s2tte_create_unassigned_ram(void)
{
	return (S2TTE_INVALID_HIPAS_UNASSIGNED | S2TTE_INVALID_RIPAS_RAM);
}

/*
 * Creates an unassigned_destroyed s2tte.
 */
inline unsigned long s2tte_create_unassigned_destroyed(void)
{
	return (S2TTE_INVALID_HIPAS_UNASSIGNED | S2TTE_INVALID_RIPAS_DESTROYED);
}

/*
 * Returns true if @s2tte is a table at level @level.
 */
inline bool s2tte_is_table(unsigned long s2tte, long level)
{
	return ((level < RTT_PAGE_LEVEL) &&
		((s2tte & DESC_TYPE_MASK) == S2TTE_L012_TABLE));
}

/*
 * Returns true if s2tte has defined ripas value, namely if it is one of:
 * - unassigned_empty
 * - unassigned_ram
 * - unassigned_destroyed
 * - assigned_empty
 * - assigned_ram
 * - assigned_destroyed
 */
inline bool s2tte_has_ripas(unsigned long s2tte, long level)
{
	return (((s2tte & S2TTE_NS) == 0UL) && !s2tte_is_table(s2tte, level));
}

unsigned long s2tte_create_unassigned_ns(void);
unsigned long s2tte_create_assigned_empty(unsigned long pa, long level);
unsigned long s2tte_create_assigned_ram(unsigned long pa, long level);
unsigned long s2tte_create_assigned_ns(unsigned long s2tte, long level);
unsigned long s2tte_create_assigned_destroyed(unsigned long pa, long level);
unsigned long s2tte_create_assigned_unchanged(unsigned long s2tte,
					      unsigned long pa,
					      long level);
unsigned long s2tte_create_table(unsigned long pa, long level);

bool host_ns_s2tte_is_valid(unsigned long s2tte, long level);
unsigned long host_ns_s2tte(unsigned long s2tte, long level);

bool s2tte_is_unassigned(unsigned long s2tte);
bool s2tte_is_unassigned_empty(unsigned long s2tte);
bool s2tte_is_unassigned_ram(unsigned long s2tte);
bool s2tte_is_unassigned_ns(unsigned long s2tte);
bool s2tte_is_unassigned_destroyed(unsigned long s2tte);

bool s2tte_is_assigned_empty(unsigned long s2tte, long level);
bool s2tte_is_assigned_ram(unsigned long s2tte, long level);
bool s2tte_is_assigned_ns(unsigned long s2tte, long level);
bool s2tte_is_assigned_destroyed(unsigned long s2tte, long level);

enum ripas s2tte_get_ripas(unsigned long s2tte);

void s2tt_init_unassigned_empty(unsigned long *s2tt);
void s2tt_init_unassigned_ram(unsigned long *s2tt);
void s2tt_init_unassigned_ns(unsigned long *s2tt);
void s2tt_init_unassigned_destroyed(unsigned long *s2tt);

void s2tt_init_assigned_empty(unsigned long *s2tt, unsigned long pa, long level);
void s2tt_init_assigned_ram(unsigned long *s2tt, unsigned long pa, long level);
void s2tt_init_assigned_ns(unsigned long *s2tt, unsigned long attrs,
			   unsigned long pa, long level);
void s2tt_init_assigned_destroyed(unsigned long *s2tt, unsigned long pa, long level);

unsigned long s2tte_pa(unsigned long s2tte, long level);
unsigned long s2tte_pa_table(unsigned long s2tte, long level);
bool addr_is_level_aligned(unsigned long addr, long level);
unsigned long s2tte_map_size(long level);

struct realm_s2_context;
void invalidate_page(const struct realm_s2_context *s2_ctx, unsigned long addr);
void invalidate_block(const struct realm_s2_context *s2_ctx, unsigned long addr);
void invalidate_pages_in_block(const struct realm_s2_context *s2_ctx,
				unsigned long addr);

bool table_is_unassigned_empty_block(unsigned long *table);
bool table_is_unassigned_ram_block(unsigned long *table);
bool table_is_unassigned_ns_block(unsigned long *table);
bool table_is_unassigned_destroyed_block(unsigned long *table);

bool table_maps_assigned_empty_block(unsigned long *table, long level);
bool table_maps_assigned_ram_block(unsigned long *table, long level);
bool table_maps_assigned_ns_block(unsigned long *table, long level);
bool table_maps_assigned_destroyed_block(unsigned long *table, long level);

struct rtt_walk {
	struct granule *g_llt;
	unsigned long index;
	long last_level;
};

void rtt_walk_lock_unlock(struct granule *g_root,
			  int start_level,
			  unsigned long ipa_bits,
			  unsigned long map_addr,
			  long level,
			  struct rtt_walk *wi);

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
#define s1tte_write(s1ttep, s1tte)	__tte_write(s1ttep, s1tte)
#define s2tte_write(s2ttep, s2tte)	__tte_write(s2ttep, s2tte)

static inline uint64_t __tte_read(uint64_t *ttep)
{
	return SCA_READ64(ttep);
}
#define s1tte_read(s1ttep)	__tte_read(s1ttep)
#define s2tte_read(s2ttep)	__tte_read(s2ttep)

/*
 * At the moment, RMM doesn't support FEAT_LPA2 for stage 2 address
 * translation, so the maximum IPA size is 48 bits.
 */
static inline unsigned int max_ipa_size(void)
{
	unsigned int ipa_size = arch_feat_get_pa_width();

	return (ipa_size > MAX_IPA_BITS) ? MAX_IPA_BITS : ipa_size;
}

unsigned long skip_non_live_entries(unsigned long addr,
				    unsigned long *s2tt,
				    const struct rtt_walk *wi);
#endif /* TABLE_H */
