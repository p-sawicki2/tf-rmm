/*
 * Copyright (c) 2021-2022, Arm Limited. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

#ifndef TB_REALM_H
#define TB_REALM_H

#include <measurement.h>
#include <tb_granules.h>
#include <smc-rmi.h>

#define DESTROYED RIPAS_DESTROYED
#define EMPTY RIPAS_EMPTY
#define RAM RIPAS_RAM

enum rmm_realm_state {
	REALM_ACTIVE,
	REALM_NEW,
	REALM_SYSTEM_OFF
};

enum rmm_rtt_entry_state {
	ASSIGNED,
	ASSIGNED_NS,
	TABLE,
	UNASSIGNED,
	UNASSIGNED_NS,
};

struct rmm_realm {
	uint64_t ipa_width;
	uint64_t measurements[5];
	uint64_t hash_algo;
	uint64_t rec_index;
	uint64_t rtt_base;
	uint64_t rtt_level_start;
	uint64_t rtt_num_start;
	uint64_t state;
	uint64_t vmid;
	uint8_t rpv[RPV_SIZE];
};

struct rmi_realm_params_buffer {
	uint8_t flags;
	uint8_t s2sz;
	uint8_t sve_vl;
	uint8_t num_bps;
	uint8_t num_wps;
	uint8_t pmu_num_ctrs;
	uint8_t hash_algo;
	uint8_t rpv[RPV_SIZE];
	uint16_t vmid;
	uint64_t rtt_base;
	int64_t rtt_level_start;
	uint32_t rtt_num_start;
};

struct rmi_realm_params_buffer RealmParams(uint64_t addr);
bool GranuleAccessPermitted(uint64_t addr, enum granule_pas pas);
bool RmiRealmParamsIsValid(uint64_t addr);
bool RealmParamsSupported(struct rmi_realm_params_buffer params);
bool AddrInRange(uint64_t addr, uint64_t base, size_t size);
bool AddrIsAligned(uint64_t addr, int n);
bool RttConfigIsValid(int ipa_width, int rtt_level_start, int rtt_num_start);
bool RttsStateEqual(uint64_t rtt_base, int rtt_num_start, enum granule_state state);
bool VmidIsValid(uint16_t vmid);
bool VmidIsFree(uint16_t vmid);
struct rmm_realm Realm(uint64_t rd);
bool RttsAllProtectedEntriesState(uint64_t rtt_base,
				  int rtt_num_start,
				  enum rmm_rtt_entry_state state);
bool RttsAllUnprotectedEntriesState(uint64_t rtt_base,
				    int rtt_num_start,
				    enum rmm_rtt_entry_state state);
bool RttsAllProtectedEntriesRipas(uint64_t rtt_base, int rtt_num_start, enum ripas ripas);
bool Equal(uint64_t lhs, uint64_t rhs);
uint64_t RimInit(enum hash_algo hash_algo, struct rmi_realm_params_buffer params);

struct rmi_realm_params_buffer nondet_struct_rmi_realm_params_buffer(void);
struct rmi_realm_params nondet_struct_rmi_realm_params(void);

struct granule *init_realm_param_page(void);

#endif /* TB_REALM_H */

