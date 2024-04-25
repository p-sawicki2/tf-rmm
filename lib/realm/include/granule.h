/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef GRANULE_H
#define GRANULE_H

#include <assert.h>
#include <atomics.h>
#include <buffer.h>
#include <errno.h>
#include <granule_lock.h>
#include <memory.h>
#include <status.h>

/* Granule descriptor fields access macros */
#define LOCKED(g)	\
		(((g)->descriptor & GRN_LOCK_BIT) != 0U)

#define REFCOUNT(g)	\
		(((g)->descriptor) & (unsigned short)MASK(GRN_REFCOUNT))

#define STATE(g)	\
		((unsigned short)EXTRACT(GRN_STATE, (g)->descriptor))

static inline void granule_refcount_write_relaxed(struct granule *g,
						  unsigned short val)
{
	g->descriptor &= ~(unsigned short)MASK(GRN_REFCOUNT);
	g->descriptor |= val;
}

static inline unsigned short granule_refcount_read_relaxed(struct granule *g)
{
	return __sca_read16(&g->descriptor) &
			(unsigned short)MASK(GRN_REFCOUNT);
}

static inline unsigned short granule_refcount_read_acquire(struct granule *g)
{
	return __sca_read16_acquire(&g->descriptor) &
			(unsigned short)MASK(GRN_REFCOUNT);
}

/*
 * Sanity-check unlocked granule invariants.
 *
 * These invariants must hold for any granule which is unlocked.
 *
 * These invariants may not hold transiently while a granule is locked (e.g.
 * when transitioning to/from delegated state).
 *
 * Note: this function is purely for debug/documentation purposes, and is not
 * intended as a mechanism to ensure correctness.
 */
static inline void __granule_assert_unlocked_invariants(struct granule *g,
							unsigned int state)
{
	switch (state) {
	case GRANULE_STATE_NS:
		assert(granule_refcount_read_relaxed(g) == 0U);
		break;
	case GRANULE_STATE_DELEGATED:
		assert(REFCOUNT(g) == 0U);
		break;
	case GRANULE_STATE_RD:
		/*
		 * refcount is used to check if RD and associated granules can
		 * be freed because they're no longer referenced by any other
		 * object. Can be any non-negative number.
		 */
		break;
	case GRANULE_STATE_REC:
		assert(granule_refcount_read_relaxed(g) <= 1U);
		break;
	case GRANULE_STATE_DATA:
		assert(REFCOUNT(g) == 0U);
		break;
	case GRANULE_STATE_RTT:
		/* Refcount cannot be greater that number of entries in an RTT */
		assert(REFCOUNT(g) <=
			(unsigned short)(GRANULE_SIZE / sizeof(uint64_t)));
		break;
	case GRANULE_STATE_REC_AUX:
		assert(REFCOUNT(g) == 0U);
		break;
	default:
		/* Unknown granule type */
		assert(false);
	}
}

/* Must be called with g->lock held */
static inline unsigned int granule_get_state(struct granule *g)
{
	assert(g != NULL);

	/* NOLINTNEXTLINE(clang-analyzer-core.NullDereference) */
	return STATE(g);
}

/* Must be called with g->lock held */
static inline void granule_set_state(struct granule *g, unsigned int state)
{
	assert(g != NULL);

	/* NOLINTNEXTLINE(clang-analyzer-core.NullDereference) */
	g->descriptor = (g->descriptor &
				~(unsigned short)MASK((unsigned long)GRN_STATE)) |
				 (unsigned short)INPLACE(GRN_STATE,
							(unsigned long)state);
}

/*
 * Acquire the bitlock and then check expected state
 * Fails if unexpected locking sequence detected.
 * Also asserts if invariant conditions are met.
 */
static inline bool granule_lock_on_state_match(struct granule *g,
						unsigned int expected_state)
{
	granule_bitlock_acquire(g);

	if (granule_get_state(g) != expected_state) {
		granule_bitlock_release(g);
		return false;
	}

	__granule_assert_unlocked_invariants(g, expected_state);
	return true;
}

/*
 * Used when we're certain of the type of an object (e.g. because we hold a
 * reference to it). In these cases we should never fail to acquire the lock.
 */
static inline void granule_lock(struct granule *g,
				unsigned int expected_state)
{
	__unused bool locked = granule_lock_on_state_match(g, expected_state);

	assert(locked);
}

static inline void granule_unlock(struct granule *g)
{
	__granule_assert_unlocked_invariants(g, granule_get_state(g));
	granule_bitlock_release(g);
}

/* Transtion state to @new_state and unlock the granule */
static inline void granule_unlock_transition(struct granule *g,
						unsigned int new_state)
{
	granule_set_state(g, new_state);
	granule_unlock(g);
}

unsigned long granule_addr(const struct granule *g);
struct granule *addr_to_granule(unsigned long addr);
struct granule *find_granule(unsigned long addr);
struct granule *find_lock_granule(unsigned long addr,
				  unsigned int expected_state);

bool find_lock_two_granules(unsigned long addr1,
			    unsigned int expected_state1,
			    struct granule **g1,
			    unsigned long addr2,
			    unsigned int expected_state2,
			    struct granule **g2);

void granule_memzero(struct granule *g, enum buffer_slot slot);

void granule_memzero_mapped(void *buf);

void *aux_granules_map(struct granule *rec_aux_pages[], unsigned int num_aux);
void aux_granules_unmap(void *rec_aux, unsigned int num_aux);

/* Must be called with g->lock held */
static inline void __granule_get(struct granule *g)
{
	assert(LOCKED(g));
	g->descriptor++;
}

/* Must be called with g->lock held */
static inline void __granule_put(struct granule *g)
{
	assert(LOCKED(g));
	assert(REFCOUNT(g) != 0U);
	g->descriptor--;
}

/* Must be called with g->lock held */
static inline void __granule_refcount_inc(struct granule *g, unsigned short val)
{
	assert(LOCKED(g));
	g->descriptor += val;
}

/* Must be called with g->lock held */
static inline void __granule_refcount_dec(struct granule *g, unsigned short val)
{
	assert(LOCKED(g));
	assert(REFCOUNT(g) >= val);
	g->descriptor -= val;
}

/*
 * Atomically increments the reference counter of the granule.
 */
static inline void atomic_granule_get(struct granule *g)
{
	atomic_add_16(&g->descriptor, 1);
}

/*
 * Atomically decrements the reference counter of the granule.
 */
static inline void atomic_granule_put(struct granule *g)
{
	atomic_add_16(&g->descriptor, (uint16_t)(-1));
}

/*
 * Atomically decrements the reference counter of the granule.
 * Stores to memory with release semantics.
 */
static inline void atomic_granule_put_release(struct granule *g)
{
	unsigned short old_refcount __unused;

	old_refcount = atomic_load_add_release_16(&g->descriptor, (uint16_t)(-1));
	assert(old_refcount != 0U);
}

/*
 * Obtain a pointer to a locked unused granule at @addr if @addr is a valid
 * granule physical address, the state of the granule at @addr is
 * @expected_state, and the granule at @addr is unused.
 *
 * Returns:
 * 0, @*g - address of the granule,
 *	if @addr is a valid granule physical address.
 * -EINVAL, @*g = NULL,
 *	if @addr is not aligned to the size of a granule,
 *	@addr is out of range, or if the state of the granule at @addr
 *	is not @expected_state.
 * -EBUSY, @*g = NULL,
 *	if the granule at @addr has a non-zero reference count.
 */
static inline int find_lock_unused_granule(unsigned long addr,
					   unsigned int expected_state,
					   struct granule **g)
{
	*g = find_lock_granule(addr, expected_state);
	if (*g == NULL) {
		return -EINVAL;
	}

	/*
	 * Granules can have lock-free access (e.g. REC), thus using acquire
	 * semantics to avoid race conditions.
	 */
	if (granule_refcount_read_acquire(*g) != 0U) {
		granule_unlock(*g);
		*g = NULL;
		return -EBUSY;
	}

	return 0;
}

#endif /* GRANULE_H */
