/*
 * Copyright (c) 2021-2022, Arm Limited. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

#ifndef TB_REALM_H
#define TB_REALM_H

#include "realm.h"
#include "tb_common.h"
#include "tb_granules.h"
#include "tb_measurement.h"


#define NEW REALM_STATE_NEW
#define ACTIVE REALM_STATE_ACTIVE

// Realm descriptor
struct realm_s2_context nondet_struct_realm_s2_context(void);
struct rd nondet_struct_rd(void);
struct granule * init_realm_descriptor_page();

// Realm parameter
struct rmi_realm_params nondet_struct_rmi_realm_params(void);
struct rmi_realm_params init_rmi_realm_params(void);
void init_realm_param_page(void);
struct granule * root_rtt_from_realm_descriptor(struct granule * rd);
int64_t start_level_from_realm_descriptor(struct granule * g_rd);

// In the spec, Realm predicate must return a concrete realm.
// We use a global fallback realm to by-pass this constraint.
// There is a mismatch in the type of `struct rd` against spec.
struct rmm_realm {
	uint64_t state;
    uint64_t rtt_base;
	uint64_t hash_algo;
    uint64_t measurements[4];
    uint64_t rec_index;
    uint64_t rtt_level_start;
    uint64_t rtt_num_start;
    uint64_t ipa_width;
    uint64_t vmid;
    uint64_t rpv;
    uint64_t aux_count;
};

struct rmi_realm_params_buffer {
	uint64_t par_base;
	uint64_t par_size;
	uint64_t rtt_base;
	uint8_t hash_algo;
    uint64_t rtt_num_start;
    uint64_t s2sz;
    uint64_t rtt_level_start;
    uint64_t vmid;
    uint64_t rpv;
};

/*
 * Predicates for Realm.
 */
struct rmm_realm Realm(uint64_t addr);
struct rmi_realm_params_buffer RealmParams(uint64_t addr);
bool RealmIsLive(uint64_t rd_addr);
bool VmidIsFree(uint64_t value);
bool AddrIsProtected(uint64_t ipa, struct rmm_realm realm);
bool AddrIsInRange(uint64_t map_addr, uint64_t base, uint64_t size);
bool AddrIsAligned(uint64_t addr, uint64_t align);
bool RttConfigIsValid(uint64_t x1, uint64_t x2, uint64_t x3);
bool RttsStateEqual(uint64_t x1, uint64_t x2, uint64_t x3);
bool VmidIsValid(uint64_t value);
bool RttsAllEntriesState(uint64_t x1, uint64_t x2, uint64_t x3);
bool RttsAllEntriesRipas(uint64_t x1, uint64_t x2, uint64_t x3);
bool Equal(uint64_t lhs, uint64_t rhs);
bool RimInit(uint64_t x1, struct rmi_realm_params_buffer x2);
bool RmiRealmParamsIsValid(uint64_t x1);
bool RealmParamsSupported(struct rmi_realm_params_buffer x1);
bool RttsAllProtectedEntriesState(uint64_t x1, uint64_t x2, uint64_t x3);
bool RttsAllUnprotectedEntriesState(uint64_t x1, uint64_t x2, uint64_t x3);
bool RttsAllProtectedEntriesRipas(uint64_t x1, uint64_t x2, uint64_t x3);
uint64_t Zeros(void);

#endif /* !TB_REALM_H */
