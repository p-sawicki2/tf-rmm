#include "granule.h"
#include "tb_common.h"
#include "tb_granules.h"
#include "tb_rtt.h"
#include "tb_realm.h"
#include "tb_lock.h"
#include "realm.h"
#include "ripas.h"

// Global lookup table.
uint64_t entry_values[5] = { 0 };
uint64_t entry_to_phys[5] = { 0 };
size_t next_available_entry_map = 0;

// A function CBMC shadow
uint64_t table_entry_to_phys(uint64_t entry)
{
    for(int i = 0; i < sizeof(entry_values)/sizeof(uint64_t) && i < next_available_entry_map; i++)
        if(entry_values[i] == entry)
            return entry_to_phys[i];

	return 0;
}

bool valid_rmm_rtt_entry(struct rmm_rtt_entry value)
{
    return ( value.state == UNASSIGNED
    || value.state == UNASSIGNED_NS
    || value.state == ASSIGNED
    || value.state == ASSIGNED_NS
    || value.state == DESTROYED
    || value.state == TABLE )
    && ( value.ripas == RMI_RAM
    || value.ripas == RMI_EMPTY );
}

struct rmm_rtt_entry init_rmm_rtt_entry(void)
{
    struct rmm_rtt_entry rst = nondet_rmm_rtt_entry();
    __CPROVER_assume(valid_rmm_rtt_entry(rst));
    return rst;
}

bool valid_rmm_rtt_walk_result(struct rmm_rtt_walk_result value)
{
    return valid_rmm_rtt_entry(value.entry);
}

struct rmm_rtt_walk_result init_rmm_rtt_walk_result(void)
{
    struct rmm_rtt_walk_result rst = nondet_rmm_rtt_walk_result();
    __CPROVER_assume(valid_rmm_rtt_walk_result(rst));
    return rst;
}

// it is smaller than the specification
bool valid_num_root_rtts(unsigned int num_root_rtts)
{
    return num_root_rtts >= 1 && num_root_rtts <= 2;
}

extern struct granule granules[RMM_MAX_GRANULES];

struct granule * init_rtt_root_page(unsigned int num_root_rtts) 
{
    __CPROVER_assert(valid_num_root_rtts(num_root_rtts), "Internel: `init_rtt_page` valid numbers of root rtt");
    
    // The first root rtt granule is granules[index].
    size_t index = next_index();
    struct granule* before = &granules[index];
    for(size_t i = index; i < index + num_root_rtts && i < index + 16; ++i) {
        __CPROVER_assume(unused_index(i));
        struct granule g = init_granule();
        __CPROVER_assume(g.state == GRANULE_STATE_RTT);
        // We assume there are at least one unused slot.
        __CPROVER_assume(g.refcount < NB_RTT_GRANULE );
		char rtt_content[GRANULE_SIZE] = { 0 };
		struct granule* after = inject_granule_at(&g, rtt_content, sizeof(rtt_content), i);

        // Add root_rtt -> other root_rtt to the lock order relationship.
        if(i != index) add_lock_relation(before, after);
    }
    return &granules[index];
}

bool valid_max_walk_path_level(int64_t start_level, uint64_t level)
{
    return level >= 0 && level <= 3 && start_level <= level;
}

#define DESC_TYPE_MASK			0x3UL
#define S2TTE_Lx_INVALID		0x0UL
#define S2TTE_INVALID_RIPAS_SHIFT	6
#define S2TTE_INVALID_RIPAS_WIDTH	1
#define S2TTE_INVALID_RIPAS_MASK	MASK(S2TTE_INVALID_RIPAS)
#define S2TTE_INVALID_RIPAS_RAM		(INPLACE(S2TTE_INVALID_RIPAS, 1))

bool valid_entry_value(uint64_t entry_value, int level)
{
    if(entry_value == 0) return false;
    for(size_t i = 0; i < 5; i++)
        if(entry_value == entry_values[i]) return false;

    // Must have a valid ripas value, ref: s2tte_get_ripas at lib/realm/src/s2tt.c
	uint64_t desc_ripas = entry_value & S2TTE_INVALID_RIPAS_MASK;
	if (!((entry_value & DESC_TYPE_MASK) == S2TTE_Lx_INVALID ||
	     desc_ripas == S2TTE_INVALID_RIPAS_RAM)) return false;

	if (!(s2tte_is_unassigned(entry_value)
	      || s2tte_is_destroyed(entry_value)
	      || s2tte_is_assigned(entry_value, level)
	      || s2tte_is_valid(entry_value, level)
	      || s2tte_is_valid_ns(entry_value, level)
	      || s2tte_is_table(entry_value, level)))
        return false;

    return true;
}

struct granule * init_walk_path(struct granule * g_root, int start_level, uint64_t max_level)
{
    __CPROVER_assert(max_level <= RTT_PAGE_LEVEL, "Internel: `init_walk_path`, a valid `max_level`");
    struct granule *g_cur_rtt = g_root;
    // Invariant of this loop: `cur_level` is the current level and `g_cur_rtt` is table at level `cur_level`.
    // In each iteration, a new granule is created for the `cur_level + 1` level. The new granule must be RTT if the level is not `max_level`
    // A synbolic value is picked and written to an arbitrary location in the table at level `cur_level`.
    for(int cur_level = start_level; cur_level <= max_level; cur_level++) {
        // Create the next level rtt.
        struct granule next_rtt = init_granule();
        // Ensure the intermediate note is RTT
        if(cur_level != RTT_PAGE_LEVEL) __CPROVER_assume(next_rtt.state == GRANULE_STATE_RTT);
        else __CPROVER_assume(next_rtt.state == GRANULE_STATE_DATA || next_rtt.state == GRANULE_STATE_NS);
        // We assume there are at least one unused slot.
        __CPROVER_assume(next_rtt.refcount <= (GRANULE_SIZE / sizeof(uint64_t)) - 1);
		char next_rtt_content[GRANULE_SIZE] = { 0 };
		struct granule *g_next = inject_granule(&next_rtt, next_rtt_content, sizeof(next_rtt_content));

        // Link the newly created rtt to the prev level.
        uint64_t addr = granule_metadata_ptr_to_pa(g_next);
        uint64_t * prev_rtt_content = granule_metadata_ptr_to_buffer_ptr(g_cur_rtt);
        uint64_t index = nondet_unsigned_long();
        __CPROVER_assume(index >= 0 && index < NB_RTT_GRANULE);
        uint64_t entry_st2tte_value = nondet_unsigned_long();
        __CPROVER_assume(valid_entry_value(entry_st2tte_value, cur_level));
        // add into the entry table
        entry_values[next_available_entry_map] = entry_st2tte_value;
        entry_to_phys[next_available_entry_map++] = addr;
        prev_rtt_content[index] = entry_st2tte_value;

        // Inc the ref count of the old cur_rtt. 
        ++(g_cur_rtt->refcount);

        // Update for next iteration
        g_cur_rtt = g_next;
    }
    return g_cur_rtt;
}

struct SPEC_rtt Rtt(uint64_t addr) 
{
    if (!valid_pa(addr)) return nondet_rtt();

    uint64_t *rtt = pa_to_granule_buffer_ptr(addr);
    struct SPEC_rtt rtt_content = { 0 };

    for(int i = 0; i < NB_RTT_GRANULE; ++i)
        rtt_content.entries[i] = RttEntryFromDescriptor(*(rtt + i));

    return rtt_content;
}

struct rmm_rtt_entry RttFold(struct SPEC_rtt rtt)
{
	struct rmm_rtt_entry rst;
	return rst;
}

bool read_entry_from_s2tte(uint64_t s2tte, int level, struct rmm_rtt_entry *entry) 
{
    *entry = RttEntryFromDescriptor(s2tte);

    /* TODO 
    // Extra the state of the Rtt entry. Note that 
    // it cannot be done inside  `RttEntryFromDescriptor`
    // since many states are influenced by `level`.
    bool ns_flag = false;
    // it is a secured page, i.e., in protected ipa.
	if (s2tte_is_valid(s2tte, level)) {
        ns_flag = false;
        entry->ripas = s2tte_get_ripas(s2tte);
	} else if (s2tte_is_valid_ns(s2tte, level)) {
        ns_flag = true;
    } else {
        // It can reach here given entry_values are not all valid
        return false;
    }

    // Assign state
    if (s2tte_is_unassigned(s2tte)) {
        entry->state = ns_flag?UNASSIGNED_NS:UNASSIGNED;
    } else if (s2tte_is_destroyed(s2tte)) {
        entry->state = DESTROYED;
	} else if (s2tte_is_assigned(s2tte, level)) {
        entry->state = ns_flag?ASSIGNED_NS:ASSIGNED;
	} else if (s2tte_is_table(s2tte, level)) {
        entry->state = TABLE;
	} else {
        // It can reach here given entry_values are not all valid
        return false;
	}
    return true;
    */

	if (s2tte_is_unassigned(s2tte)) {
		enum ripas ripas = s2tte_get_ripas(s2tte);

		entry->state = RMI_UNASSIGNED;
		entry->ripas = (uint64_t)ripas;
	} else if (s2tte_is_destroyed(s2tte)) {
		entry->state = RMI_DESTROYED;
	} else if (s2tte_is_assigned(s2tte, level)) {
		entry->state = RMI_ASSIGNED;
		entry->ripas = RIPAS_EMPTY;
	} else if (s2tte_is_valid(s2tte, level)) {
		entry->state = RMI_ASSIGNED;
		entry->ripas = RIPAS_RAM;
	} else if (s2tte_is_valid_ns(s2tte, level)) {
		entry->state = RMI_VALID_NS;
	} else if (s2tte_is_table(s2tte, level)) {
		entry->state = RMI_TABLE;
	} else {
		assert(false);
	}
}

struct rmm_rtt_walk_result RttWalk(uint64_t rd_addr,
			       uint64_t ipa,
			       uint64_t level) 
{
    // Invalid rd_addr, hence return nondet result.
    if (!valid_pa(rd_addr) || pa_to_granule_metadata_ptr(rd_addr)->state != GRANULE_STATE_RD)
        return init_rmm_rtt_walk_result();

    struct rd *rd_ptr = pa_to_granule_buffer_ptr(rd_addr);
    
    // invalid level
    if( !(level >= rd_ptr->s2_ctx.s2_starting_level && level <= RTT_PAGE_LEVEL) ) return init_rmm_rtt_walk_result();

    __CPROVER_cover(rd_ptr->s2_ctx.s2_starting_level >= -1 && rd_ptr->s2_ctx.s2_starting_level <= 3);
    __CPROVER_cover(rd_ptr->s2_ctx.s2_starting_level < level);

	struct rmm_rtt_walk_result rst = {
        // Current visited rtt and level
        .rtt_addr = rd_ptr->s2_ctx.g_rtt,
        .level = rd_ptr->s2_ctx.s2_starting_level,
        // Initial to nondet value
        .entry = init_rmm_rtt_entry()
    };

    uint64_t ipa_bits = rd_ptr->s2_ctx.ipa_bits;
    unsigned int rtt_num_start = rd_ptr->s2_ctx.num_root_rtts;

    // deal with the concatenated rtt.
    uint64_t sl_idx = s2_sl_addr_to_idx(ipa, rst.level, ipa_bits);
    if (sl_idx >= S2TTES_PER_S2TT) {
        unsigned int tt_num = (sl_idx >> S2TTE_STRIDE);
        rst.rtt_addr += tt_num;
    }

    // Walks to the direct parent of the target entry
    // Invariant: rst.rtt_addr and rst.level match and rst.rtt_addr is a valid rtt granule.
    // The loop ends when rst.level == level.
    for(; rst.level < level; ++rst.level) {
        uint64_t idx = s2_addr_to_idx(ipa, rst.level);

        // Get the table.
        uint64_t *table = granule_metadata_ptr_to_buffer_ptr(rst.rtt_addr);

        uint64_t pa = table_entry_to_phys(table[idx]);
        if (!valid_pa(pa)) {
            break;
        }

	    rst.rtt_addr = pa_to_granule_metadata_ptr(pa);
    }
    

    // Extract the final entry and store it into the rst.entry.
    uint64_t idx = s2_addr_to_idx(ipa, rst.level);
    uint64_t *table = granule_metadata_ptr_to_buffer_ptr(rst.rtt_addr);

    // Extract entry state
    uint64_t entry_value = table[idx];
	uint64_t s2tte = s2tte_read(&entry_value);
    read_entry_from_s2tte(s2tte, rst.level, &(rst.entry));

    // TODO fill all the rst.rtt: reads the table and 
    return rst;
}


bool RttLevelIsValid(uint64_t rd, uint64_t level)
{
	return level >= Realm(rd).rtt_level_start && level <= RTT_PAGE_LEVEL;
}

bool RttLevelIsStarting(uint64_t rd, uint64_t level)
{
	return level == Realm(rd).rtt_level_start;
}


bool AddrIsRttLevelAligned(uint64_t map_addr, uint64_t level)
{
    // Use the function defined in `table.h`
	return addr_is_level_aligned(map_addr, level);
}

uint64_t UInt(uint64_t ipa)
{
    return ipa;
}

uint64_t RttEntryIndex(uint64_t ipa, uint64_t level) 
{
	return s2_addr_to_idx(ipa, level);
}

#define S2TTE_MEMATTR_SHIFT		2
#define S2TTE_MEMATTR_MASK		(0x7UL << S2TTE_MEMATTR_SHIFT)
#define S2TTE_MEMATTR_FWB_RESERVED	((1UL << 4) | (0UL << 2))

#define S2TTE_AP_SHIFT			6
#define S2TTE_AP_MASK			(3UL << S2TTE_AP_SHIFT)

#define S2TTE_SH_SHIFT			8
#define S2TTE_SH_MASK			(3UL << S2TTE_SH_SHIFT)
#define S2TTE_SH_RESERVED		(1UL << S2TTE_SH_SHIFT)

bool RttDescriptorIsValidForUnprotected(uint64_t s2tte)
{

    // ref: host_ns_s2tte_is_valid in lib/realm/src/s2tt.c
	if ( (s2tte & S2TTE_MEMATTR_MASK) == S2TTE_MEMATTR_FWB_RESERVED
       || (s2tte & S2TTE_SH_MASK) == S2TTE_SH_RESERVED ) {
		return false;
	}
    return true;
}

bool RttLevelIsBlockOrPage(uint64_t rd, uint64_t level) 
{
	return level >= RTT_MIN_BLOCK_LEVEL && level <= RTT_PAGE_LEVEL;
}

bool RttIsHomogeneous(struct SPEC_rtt rtt)
{
    return true;
}

uint64_t RttSkipNonLiveEntries(struct SPEC_rtt rtt, uint64_t level, uint64_t ipa)
{
    return 0;
}

/*
 * If rtt contains a live entry from ipa, returns the IPA of the live entry.
 */
uint64_t RttEntryState(enum SPEC_rtt_state rtt_state)
{
    return rtt_state;
}

// This function leave the state of the rtt entry unspecified 
// hence a non-deterministic value
struct rmm_rtt_entry RttEntryFromDescriptor(uint64_t desc)
{
    struct rmm_rtt_entry rst = nondet_rmm_rtt_entry();

    rst.MemAttr = desc & S2TTE_MEMATTR_MASK;
    rst.S2AP = desc & S2TTE_AP_MASK;
    rst.SH = desc & S2TTE_SH_MASK;
    rst.addr = table_entry_to_phys(desc);

    return rst;
}

bool RttAllEntriesRipas(struct SPEC_rtt rtt, enum ripas ripas)
{
    for(int i = 0; i < NB_RTT_GRANULE; ++i)
        if(rtt.entries[i].ripas != ripas) return false;

    return true;
}

bool RttAllEntriesState(struct SPEC_rtt rtt, enum SPEC_rtt_state state)
{
    for(int i = 0; i < NB_RTT_GRANULE; ++i)
        if(rtt.entries[i].state != state) return false;

    return true;
}

bool RttAllEntriesContiguous(struct SPEC_rtt rtt, uint64_t addr, uint64_t level)
{
    //TODO: impl
    return nondet_bool();
}
