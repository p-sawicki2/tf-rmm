#include "granule.h"
#include "granule_types.h"
#include "tb_lock.h"
#include "tb_common.h"
#include "spinlock.h"

bool lock_order_invariable(size_t index)
{

    if(index <= 0) return true;

    struct lock_trace_entry after = lock_traces[index];

    if (after.has_parent) {
        // check if `after` parent is locked.
        for(int prev = index - 1; prev >= 0; prev--) {
            struct lock_trace_entry before = lock_traces[prev];
            for(int i = 0; i < next_relation_entry && i < MAX_LOCK_RELATION; i++) {
                if( after.is_lock
                        && lock_children_granules[i] == after.granule_addr
                        && lock_parents_granules[i] == before.granule_addr ) return true;
            }
        }
        // No parent is found.
        return false;
    } else {
        // The first locked granule that is not in a page table, must be order.
        for(int prev = index - 1; prev >= 0; prev--) {
            struct lock_trace_entry before = lock_traces[prev];
            if( before.is_lock && !before.has_parent ) {
                // Found the first locked granule 
                return before.granule_addr < after.granule_addr;
            } 
        }
        // All previous non-rtt granules are unlocked 
        return true;
    }

    UNREACHABLE;
    return false;
}

// Shadow granule_lock_on_state_match at lib/realm/inlcude/granule.h
bool granule_lock_on_state_match(struct granule *g,
				    enum granule_state expected_state)
{
#ifdef CBMC
    __ASSERT(!(g->lock.val), "The granule lock must be free.");
#endif
	spinlock_acquire(&g->lock);

	if (granule_get_state(g) != expected_state) {
		spinlock_release(&g->lock);
		return false;
	}

#ifdef CBMC
    struct lock_trace_entry new_entry = {
        .is_lock = true,
        .has_parent = (expected_state == GRANULE_STATE_RTT || expected_state == GRANULE_STATE_DATA),
        .granule_addr = g
    };

    lock_traces[next_lock_trace_entry++] = new_entry;
    __ASSERT(next_lock_trace_entry <= MAX_LOCK_TRACE, "Internal: next_lock_trace_entry in range");
    if(next_lock_trace_entry >= 2) {
        __ASSERT(lock_order_invariable(next_lock_trace_entry - 1), "Locking order: take a lock.");
    }
#endif

	__granule_assert_unlocked_invariants(g, expected_state);
	return true;
}

// Shadow granule_unlock at lib/realm/inlcude/granule.h
void granule_unlock(struct granule *g)
{
#ifdef CBMC
    __ASSERT(g->lock.val, "The granule must be locked.");
#endif
	__granule_assert_unlocked_invariants(g, granule_get_state(g));
	spinlock_release(&g->lock);
#ifdef CBMC
    for(int i = 0; i < next_lock_trace_entry && i < MAX_LOCK_TRACE; i++) {
        if(lock_traces[i].is_lock && lock_traces[i].granule_addr == g) {
            lock_traces[i].is_lock = false;
            break;
        }
    }
#endif
}

void add_lock_relation(struct granule * before, struct granule * after)
{
    lock_parents_granules[next_relation_entry] = before;
    lock_children_granules[next_relation_entry++] = after;
    __ASSERT(next_relation_entry <= MAX_LOCK_RELATION, "Internal: next_relation_entry in range");
}
