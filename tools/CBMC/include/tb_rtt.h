/*
 * Copyright (c) 2021-2022, Arm Limited. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

#ifndef TB_RTT_H
#define TB_RTT_H

#include "table.h"
#include "granule.h"
#include "tb_common.h"

#define MIN_STARTING_LEVEL 0
#define REC_STATE_READY 0;
#define REC_STATE_RUNNING 1;

#define REC_RUNNABLE_NOT_RUNNABLE false;
#define REC_RUNNABLE_RUNNABLE true;

#define SMC_RMM_RTT_MAPUNPROTECTED SMC_RMM_RTT_MAP_NON_SECURE
#define SMC_RMM_RTT_UNMAPUNPROTECTED SMC_RMM_RTT_UNMAP_NON_SECURE

#define RMM_RTT_PAGE_LEVEL RTT_PAGE_LEVEL

#define NB_RTT_GRANULE (GRANULE_SIZE / sizeof(uint64_t))

#define EMPTY RMI_EMPTY	/* Unused IPA for Realm */
#define RAM RMI_RAM		/* IPA used for Code/Data by Realm */

bool valid_num_root_rtts(unsigned int num_root_rtts);
struct granule * init_rtt_root_page(unsigned int num_root_rtts);
bool valid_max_walk_path_level(int64_t start_level, uint64_t level);
struct granule * init_walk_path(struct granule * g_root, int start_level, uint64_t max_level);

enum SPEC_rtt_state {
    UNASSIGNED,
    ASSIGNED,
    UNASSIGNED_NS,
    ASSIGNED_NS,
    DESTROYED,
    TABLE,
};

struct rmm_rtt_entry {
    uint64_t MemAttr;
    uint64_t S2AP;
    uint64_t SH;
	enum SPEC_rtt_state	state;
	uint64_t addr;
	enum ripas ripas;
};
// Declare the nondet function.
struct rmm_rtt_entry nondet_rmm_rtt_entry(void);
struct rmm_rtt_entry init_rmm_rtt_entry(void);

struct SPEC_rtt {
	struct rmm_rtt_entry entries[NB_RTT_GRANULE];
};
struct SPEC_rtt nondet_rtt(void);
struct SPEC_rtt Rtt(uint64_t addr);

struct rmm_rtt_walk_result {
    struct granule * rtt_addr;
	uint64_t level;
    struct rmm_rtt_entry entry;
};
struct rmm_rtt_walk_result init_rmm_rtt_walk_result(void);


struct rmm_rtt_walk_result RttWalk(uint64_t rd_addr, uint64_t ipa, uint64_t level);
struct rmm_rtt_entry RttFold(struct SPEC_rtt rtt);
bool RttLevelIsValid(uint64_t rd, uint64_t level);
bool RttLevelIsStarting(uint64_t rd, uint64_t level);
bool AddrIsRttLevelAligned(uint64_t map_addr, uint64_t level);
uint64_t UInt(uint64_t ipa);
bool RttIsHomogeneous(struct SPEC_rtt rtt);
uint64_t RttEntryIndex(uint64_t ipa, uint64_t level);
bool RttDescriptorIsValidForUnprotected(uint64_t desc);
bool RttLevelIsBlockOrPage(uint64_t rd, uint64_t level);
uint64_t RttSkipNonLiveEntries(struct SPEC_rtt rtt, uint64_t level, uint64_t ipa);
uint64_t RttEntryState(enum SPEC_rtt_state rtt);
struct rmm_rtt_entry RttEntryFromDescriptor(uint64_t desc);
bool RttAllEntriesRipas(struct SPEC_rtt rtt, enum ripas ripas);
bool RttAllEntriesState(struct SPEC_rtt rtt, enum SPEC_rtt_state state);
bool RttAllEntriesContiguous(struct SPEC_rtt rtt, uint64_t addr, uint64_t level);


#endif /* !TB_RTT_H */
