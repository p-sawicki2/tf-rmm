#include "realm.h"
#include "smc-rmi.h"
#include "granule.h"
#include "tb_common.h"
#include "tb_granules.h"
#include "tb_measurement.h"
#include "tb_realm.h"
#include "tb_lock.h"
#include "arch_features.h"
#include "tb_rtt.h"
#include "feature.h"
#include <stdint.h>

#define VMID8_COUNT		(1U << 8)
#define VMID16_COUNT		(1U << 16)
#define MAX_VMID_COUNT		VMID16_COUNT
#define VMID_ARRAY_LONG_SIZE	(MAX_VMID_COUNT / BITS_PER_UL)

extern unsigned long vmids[VMID_ARRAY_LONG_SIZE];

struct rmm_realm nondet_struct_rmm_realm(void);
struct rmi_realm_params_buffer nondet_struct_rmi_realm_params_buffer(void);
struct rmi_realm_params nondet_struct_rmi_realm_params(void);

bool valid_realm_state(uint64_t value)
{
	return value == (uint64_t)REALM_STATE_NEW
	       || value == (uint64_t)REALM_STATE_ACTIVE
	       || value == (uint64_t)REALM_STATE_SYSTEM_OFF;
}

// Detail of the valid state
bool valid_realm_s2_context(struct realm_s2_context value)
{
	unsigned int vmid_count = is_feat_vmid16_present() ? VMID16_COUNT : VMID8_COUNT;
    return  value.s2_starting_level >= 0
        && value.s2_starting_level <= 3
        // TODO focus on standard size of root rtt for now
        && value.num_root_rtts >= 1
        /*&& value.num_root_rtts <= 16*/
        && value.num_root_rtts <= 2
        && valid_granule_metadata_ptr(value.g_rtt)
        && value.g_rtt->state == GRANULE_STATE_RTT
        /* TODO: what is the ranges here */
        && value.ipa_bits == ( 3 - value.s2_starting_level + 1 ) * S2TTE_STRIDE + value.num_root_rtts
        //TODO check 
        && value.vmid < vmid_count;
}

bool valid_rd(struct rd value) 
{
    return valid_realm_state(value.state)
        && valid_realm_s2_context(value.s2_ctx)
        && valid_hash_algo(value.algorithm)
        && value.num_rec_aux <= MAX_REC_AUX_GRANULES;
}

struct rd init_rd(void)
{
    struct rd value = nondet_struct_rd();

    unsigned int num_root_rtts = nondet_unsigned_int();
    __CPROVER_assume(valid_num_root_rtts(num_root_rtts));
    struct granule * g_root_rtt = init_rtt_root_page(num_root_rtts);
    value.s2_ctx.num_root_rtts = num_root_rtts;
    value.s2_ctx.g_rtt = g_root_rtt;
    // If the `g_root_rtt` does not satisfy the assume condition, all following `cover` checks fail.
    __CPROVER_assume(valid_rd(value));

    // Non-deterministically if the vmid is registered.
    uint64_t vmid = value.s2_ctx.vmid;
    unsigned int offset = vmid / BITS_PER_UL;
    vmid %= BITS_PER_UL;
    uint64_t bit_mask = (uint64_t)(1UL << vmid);
    if (nondet_bool()) {
        vmids[offset] |= bit_mask;
    }

    return value;
}

// Fill in arbitrary `number` numbers of nondet realm into page_table
struct granule * init_realm_descriptor_page(void)
{
    struct granule g = init_granule();
    __CPROVER_assume(g.state == GRANULE_STATE_RD);
    struct rd rd = init_rd();
    struct granule* rd_granule = inject_granule(&g, &rd, sizeof(rd));

    // Add rd_granule -> all root rtt granules to the lock order relationship.
    for(unsigned int i = 0; i < rd.s2_ctx.num_root_rtts; i++) {
        add_lock_relation(rd_granule, rd.s2_ctx.g_rtt + i);
    }

    return rd_granule;
}

struct granule * root_rtt_from_realm_descriptor(struct granule * g_rd)
{
    struct rd * realm = granule_metadata_ptr_to_buffer_ptr(g_rd);
    return realm->s2_ctx.g_rtt;
}

int64_t start_level_from_realm_descriptor(struct granule * g_rd)
{
    struct rd * realm = granule_metadata_ptr_to_buffer_ptr(g_rd);
    // Lift the original type, int, to a 64-bit signed integer.
    return (int64_t)(realm->s2_ctx.s2_starting_level);
}

bool valid_rmi_realm_params(struct rmi_realm_params value)
{
    // Note that rtt_level is maximum of 3 but we allow range to expand to 4.
    return true;
}

struct rmi_realm_params init_rmi_realm_params(void)
{
    struct rmi_realm_params value = nondet_struct_rmi_realm_params();
    __CPROVER_assume(valid_rmi_realm_params(value));
    return value;
}

struct granule * init_realm_param_page(void)
{
    struct granule g = init_granule();
    struct rmi_realm_params param = init_rmi_realm_params();
    return inject_granule(&g, &param, sizeof(param));
}


struct rmm_realm Realm(uint64_t addr)
{
    //TODO change to a unified function call
	// Find the realm ptr related to `addr`.
	// If it is NULL, return the `nondet_realm` realm.
    if (!valid_pa(addr))
        return nondet_struct_rmm_realm();
    struct rd *rd_ptr = pa_to_granule_buffer_ptr(addr);

	// convert the type
	struct rmm_realm spec_rd = {
        .ipa_width = rd_ptr->s2_ctx.ipa_bits,
        .hash_algo = rd_ptr->algorithm,
        .rec_index = rd_ptr->rec_count,
        .rtt_base = granule_metadata_ptr_to_pa(rd_ptr->s2_ctx.g_rtt),
        .rtt_level_start = rd_ptr->s2_ctx.s2_starting_level,
        .rtt_num_start = rd_ptr->s2_ctx.num_root_rtts,
        .state = rd_ptr->state,
        .vmid = rd_ptr->s2_ctx.vmid
    };

    memcpy(&spec_rd.measurements[0], &(rd_ptr->measurement[0][0]), MEASUREMENT_SLOT_NR * MAX_MEASUREMENT_SIZE);
    // rpv is typed uint8_t
    memcpy(&spec_rd.rpv[0], &(rd_ptr->rpv[0]), RPV_SIZE);
    
	return spec_rd;
}

struct rmi_realm_params_buffer RealmParams(uint64_t addr)
{
    if (!valid_pa(addr))
        return nondet_struct_rmi_realm_params_buffer();
    struct rmi_realm_params *params_ptr = pa_to_granule_buffer_ptr(addr);

	// convert the type
	struct rmi_realm_params_buffer spec_realmparam = {
        .s2sz = params_ptr->s2sz,
        .sve_vl = params_ptr->sve_vl,
        .pmu_num_ctrs = params_ptr->pmu_num_ctrs,
        // TODO extract other fields
        .hash_algo = (uint8_t)params_ptr->hash_algo,
        .vmid = params_ptr->vmid,
        .rtt_level_start = params_ptr->rtt_level_start,
        .rtt_num_start = params_ptr->rtt_num_start
    };

    memcpy(&spec_realmparam.rpv[0], &(params_ptr->rpv[0]), RPV_SIZE);

	return spec_realmparam;
}

//TODO if the inplementation is correct?
bool RealmIsLive(uint64_t rd_addr)
{
	/* TODO either update or remove
	 * From Alp05 spec:
	 * R 0013:  A Realm is live if any of the following is true:
	 *     • The number of RECs owned by the Realm is not zero
	 *     • The level 0 RTT of the Realm is live
	 *
	 * I 0014:
	 *   If a Realm owns a non-zero number of Data Granules,
	 *   this implies that its level 0 RTT is live,
	 *   and therefore that the Realm itself is live.
	*/

    // TODO find a better way to assert the rd_addr.
    if (!valid_pa(rd_addr)) 
        return nondet_bool();

    struct granule *g_rd = pa_to_granule_metadata_ptr(rd_addr);
    __ASSERT(g_rd, "internal: `RealmIsLive`, rd is not null");

    if (g_rd->refcount != 0) return true;

	struct rd *rd = pa_to_granule_buffer_ptr(rd_addr);
    __ASSERT(rd, "internal: `RealmIsLive`, rd is not null");

    for(size_t i = 0; i < rd->s2_ctx.num_root_rtts; ++i) 
        if (((rd->s2_ctx.g_rtt) + i)->refcount != 0) return true;

    return false;
}

//TODO check the implementation
bool VmidIsFree(uint64_t value)
{
	unsigned int offset = value / BITS_PER_UL;
    uint64_t bit_mask = (uint64_t)(1UL << value);
    // return TRUE if the bit at the bit_mask is ZERO.
    return ~(vmids[offset] & bit_mask);
}

bool AddrIsProtected(uint64_t ipa, struct rmm_realm realm)
{
    return ipa < ( 1UL << ( realm.ipa_width - 1 ) );
}


bool AddrInRange(uint64_t map_addr, uint64_t base, uint64_t size) 
{
	return map_addr >= base && map_addr <= base + size;
}

bool AddrIsAligned(uint64_t addr, uint64_t align) 
{
    return (addr % align) == 0;
}

bool RttConfigIsValid(uint64_t ipa_width, uint64_t rtt_level_start, uint64_t rtt_number_start)
{
    return ipa_width >= MIN_IPA_BITS 
           && ipa_width <= MAX_IPA_BITS
           && rtt_level_start >= MIN_STARTING_LEVEL
           && rtt_level_start <= RTT_PAGE_LEVEL
           && s2_num_root_rtts(ipa_width, rtt_level_start) == rtt_number_start;
}

bool RttsStateEqual(uint64_t base, uint64_t number_start, uint64_t state)
{
    if (!valid_pa(base)) 
        return nondet_bool();

    struct granule *g_base = pa_to_granule_metadata_ptr(base);
    __ASSERT(g_base, "internal: `RttsStateEqual`, base is not null");
    // hardcord the max number of root rtts
    // TODO find a macro
    for(int i = 0; i < number_start && i < 16; i++) {
        if((g_base + i)->state != state) return false;
    }
    return true;
}

bool VmidIsValid(uint64_t vmid) 
{
	unsigned int vmid_count = is_feat_vmid16_present() ? VMID16_COUNT : VMID8_COUNT;
	if (vmid >= vmid_count) {
		return false;
	}

	unsigned int offset = vmid / BITS_PER_UL;
	vmid %= BITS_PER_UL;
    uint64_t bit_mask = (uint64_t)(1UL << vmid);

    return (vmids[offset] & bit_mask) == 0;
}

bool RttsAllEntriesState(uint64_t x1, uint64_t x2, uint64_t x3)
{
    return true;
}

bool RttsAllEntriesRipas(uint64_t x1, uint64_t x2, uint64_t x3)
{
    return true;
}

bool Equal(uint64_t lhs, uint64_t rhs)
{
    return lhs == rhs;
}

bool RimInit(uint64_t x1, struct rmi_realm_params_buffer x2)
{
    return true;
}

bool RmiRealmParamsIsValid(uint64_t params_addr)
{
    if (!valid_pa(params_addr)) 
        return nondet_bool();

    struct rmi_realm_params *realm_params_buf = pa_to_granule_buffer_ptr(params_addr);
    __ASSERT(realm_params_buf, "internal: `RmiRealmParamsIsValid`, param is not null");
    return validate_realm_params(realm_params_buf);
}

bool RealmParamsSupported(struct rmi_realm_params_buffer params)
{
    // TODO assume always supported ?
    return true;
}

bool RttsAllProtectedEntriesState(uint64_t x1, uint64_t x2, uint64_t x3)
{
    return true;
}

bool RttsAllUnprotectedEntriesState(uint64_t x1, uint64_t x2, uint64_t x3)
{
    return true;
}

bool RttsAllProtectedEntriesRipas(uint64_t x1, uint64_t x2, uint64_t x3)
{
    return true;
}

uint64_t RecAuxCount(uint64_t rd_addr)
{
    if (!valid_pa(rd_addr))
        return nondet_uint64_t();

    struct rd *rd_ptr = pa_to_granule_buffer_ptr(rd_addr);
    return rd_ptr->num_rec_aux;
}
