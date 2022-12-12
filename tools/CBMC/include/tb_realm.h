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

#define RMM_IPA_WIDTH IPA_BITS
#define RMM_IPASIZE IPA_BITS


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
int start_level_from_realm_descriptor(struct granule * g_rd);

// In the spec, Realm predicate must return a concrete realm.
// We use a global fallback realm to by-pass this constraint.
// There is a mismatch in the type of `struct rd` against spec.
struct rmm_realm {
	unsigned long state;
    unsigned long rtt_base;
	unsigned long hash_algo;
    unsigned long measurements[4];
    uint64_t rec_index;
    uint64_t rtt_level_start;
    uint64_t rtt_num_start;
    uint64_t ipa_width;
    uint64_t vmid;
    uint64_t rpv;
    unsigned long aux_count;
};
struct rmm_realm nondet_struct_rmm_realm();

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
struct rmi_realm_params_buffer nondet_struct_rmi_realm_params_buffer(void);


struct rmm_realm Realm(unsigned long addr);
struct rmi_realm_params_buffer RealmParams(unsigned long addr);
bool RealmIsLive(unsigned long rd_addr);
bool RealmMeasurementAlgorithmIsValid(unsigned long algo);
bool RmiHashAlgorithmIsValid(unsigned long value);
bool RmiHashAlgorithmIsSupported(unsigned long value);
bool VmidIsFree(uint64_t value);
bool AddrIsProtected(uint64_t ipa, struct rmm_realm realm);
bool RmiFeatureRegister0IsValid(unsigned long value);
bool AddrInRange(unsigned long rd, unsigned long lower, unsigned long upper);
bool AddrIsAligned(unsigned long lower, unsigned long upper);
bool RttConfigIsValid(unsigned long x1, unsigned long x2, unsigned long x3);
bool RttsStateEqual(unsigned long x1, unsigned long x2, unsigned long x3);
bool VmidIsValid(unsigned long value);
bool RttsAllEntriesState(unsigned long x1, unsigned long x2, unsigned long x3);
bool RttsAllEntriesRipas(unsigned long x1, unsigned long x2, unsigned long x3);
bool Equal(unsigned long x1, unsigned long x2);
bool RimInit(unsigned long x1, struct rmi_realm_params_buffer x2);
bool RmiRealmParamsIsValid(unsigned long x1);
bool RealmParamsSupported(struct rmi_realm_params_buffer x1);
bool RttsAllProtectedEntriesState(unsigned long x1, unsigned long x2, unsigned long x3);
bool RttsAllUnprotectedEntriesState(unsigned long x1, unsigned long x2, unsigned long x3);
bool RttsAllProtectedEntriesRipas(unsigned long x1, unsigned long x2, unsigned long x3);
int Zeros(void);

#endif /* !TB_REALM_H */
