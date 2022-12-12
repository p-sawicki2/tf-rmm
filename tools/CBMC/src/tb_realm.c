#include "realm.h"
#include "granule.h"
#include "tb_common.h"
#include "tb_granules.h"
#include "tb_measurement.h"
#include "tb_realm.h"
#include "arch_features.h"
#include "tb_rtt.h"
#include <stdint.h>

#define VMID8_COUNT		(1U << 8)
#define VMID16_COUNT		(1U << 16)
#define MAX_VMID_COUNT		VMID16_COUNT
#define VMID_ARRAY_LONG_SIZE	(MAX_VMID_COUNT / BITS_PER_UL)

extern unsigned long vmids[VMID_ARRAY_LONG_SIZE];

struct rmm_realm nondet_struct_rmm_realm();
struct rmi_realm_params_buffer nondet_struct_rmi_realm_params_buffer(void);

bool valid_realm_state(uint64_t value)
{
	return value == (uint64_t)REALM_STATE_NEW
	       || value == (uint64_t)REALM_STATE_ACTIVE
	       || value == (uint64_t)REALM_STATE_SYSTEM_OFF;
}

// Detail of the valid state
bool valid_realm_s2_context(struct realm_s2_context value)
{
    __CPROVER_cover(true);
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
    return inject_granule(&g, &rd, sizeof(rd));
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

void init_realm_param_page(void)
{
    struct granule g = init_granule();
    struct rmi_realm_params param = init_rmi_realm_params();
    inject_granule(&g, &param, sizeof(param));
}


//TODO change to a unified function call
//TODO finish the impl
struct rmm_realm Realm(uint64_t addr)
{
    //TODO change to a unified function call
	// Find the realm ptr related to `addr`.
	// If it is NULL, return the `nondet_realm` realm.
    if (!valid_pa(addr))
        return nondet_struct_rmm_realm();
    struct rd *rd_ptr = pa_to_granule_buffer_ptr(addr);

	// convert the type
	struct rmm_realm spec_rd = { 0 };

    // TODO change
    spec_rd.state = rd_ptr->state;
    spec_rd.rtt_base = granule_metadata_ptr_to_pa(rd_ptr->s2_ctx.g_rtt);
    spec_rd.hash_algo = rd_ptr->algorithm;
    // We do not verify the measurement field for now
    /*spec_rd.measurement = rd_ptr->measurement;*/
    spec_rd.rec_index = rd_ptr->rec_count;
    spec_rd.rtt_level_start = rd_ptr->s2_ctx.s2_starting_level;
    spec_rd.rtt_num_start = rd_ptr->s2_ctx.num_root_rtts;
    spec_rd.ipa_width = rd_ptr->s2_ctx.ipa_bits;
    spec_rd.vmid = rd_ptr->s2_ctx.vmid;
    // We do not verify the rpv field for now
    /*spec_rd.rpv = rd_ptr->rpv;*/
    spec_rd.aux_count = rd_ptr->num_rec_aux;
    
	return spec_rd;
}

struct rmi_realm_params_buffer RealmParams(uint64_t addr)
{
    if (!valid_pa(addr))
        return nondet_struct_rmi_realm_params_buffer();
    struct realm_params *params_ptr = pa_to_granule_buffer_ptr(addr);

	// convert the type
	struct rmi_realm_params_buffer spec_realmparam;

    //TODO: change
	//spec_realmparam.par_base = params_ptr->par_base;
	//spec_realmparam.par_size = params_ptr->par_size;
	//spec_realmparam.rtt_base = params_ptr->rtt_addr;
	//spec_realmparam.hash_algo = params_ptr->hash_algo;

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

bool RttConfigIsValid(uint64_t x1, uint64_t x2, uint64_t x3)
{
    return true;
}

bool RttsStateEqual(uint64_t x1, uint64_t x2, uint64_t x3)
{
    return true;
}

bool VmidIsValid(uint64_t value) 
{
    return true;
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

bool RmiRealmParamsIsValid(uint64_t x1)
{
    /*return value == RMI_HASH_ALGO_SHA256 || value == RMI_HASH_ALGO_SHA512;*/
    return true;
}

bool RealmParamsSupported(struct rmi_realm_params_buffer x1)
{
    /*return value == RMI_HASH_ALGO_SHA256 || value == RMI_HASH_ALGO_SHA512;*/
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

uint64_t Zeros(void)
{
    return UINT64_C(0);
}

