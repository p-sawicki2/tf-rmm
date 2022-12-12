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

#define NB_RTT_GRANULE (GRANULE_SIZE / sizeof(unsigned long))

#define EMPTY RMI_EMPTY	/* Unused IPA for Realm */
#define RAM RMI_RAM		/* IPA used for Code/Data by Realm */

bool valid_num_root_rtts(unsigned int num_root_rtts);
struct granule * init_rtt_root_page(unsigned int num_root_rtts);
bool valid_max_walk_path_level(int start_level, unsigned long level);
struct granule * init_walk_path(struct granule * g_root, int start_level, unsigned long max_level);

enum SPEC_rtt_state {
    ASSIGNED,
    ASSIGNED_NS,
    DESTROYED,
    TABLE,
    UNASSIGNED,
    UNASSIGNED_NS,
};
struct rmm_rtt_entry {
    unsigned long MemAttr;
    unsigned long S2AP;
    unsigned long SH;
	enum SPEC_rtt_state	state;
	unsigned long addr;
	enum ripas ripas;
};
// Declare the nondet function.
struct rmm_rtt_entry nondet_rmm_rtt_entry(void);
struct rmm_rtt_entry init_rmm_rtt_entry(void);

struct SPEC_rtt {
	struct rmm_rtt_entry entries[NB_RTT_GRANULE];
};
struct SPEC_rtt nondet_rtt(void);
struct SPEC_rtt Rtt(unsigned long addr);

struct rmm_rtt_walk_result {
    struct granule * rtt_addr;
    struct SPEC_rtt rtt;
	unsigned long level;
    struct rmm_rtt_entry entry;
};
// Declare the nondet function.
struct rmm_rtt_walk_result nondet_rmm_rtt_walk_result(void);
struct rmm_rtt_walk_result init_rmm_rtt_walk_result(void);


struct rmm_rtt_walk_result RttWalk(uint64_t rd_addr, uint64_t ipa, unsigned long level);
struct rmm_rtt_entry RttFold(struct SPEC_rtt rtt);
bool RttLevelIsValid(unsigned long rd, unsigned long level);
bool RttLevelIsStarting(unsigned long rd, unsigned long level);
bool AddrIsRttLevelAligned(unsigned long map_addr, unsigned long level);
unsigned long UInt(uint64_t ipa);
bool RttIsHomogeneous(struct SPEC_rtt rtt);
uint64_t RttEntryIndex(uint64_t ipa, unsigned long level);
bool RttDescriptorIsValidForUnprotected(uint64_t desc);
bool RttLevelIsBlockOrPage(unsigned long rd, unsigned long level);
uint64_t RttSkipNonLiveEntries(struct SPEC_rtt rtt, uint64_t level, unsigned long ipa);
uint64_t RttEntryState(enum SPEC_rtt_state rtt);
struct rmm_rtt_entry RttEntryFromDescriptor(unsigned long desc);
bool RttAllEntriesRipas(struct SPEC_rtt rtt, enum ripas ripas);
bool RttAllEntriesState(struct SPEC_rtt rtt, enum SPEC_rtt_state state);
bool RttAllEntriesContiguous(struct SPEC_rtt rtt, uint64_t addr, uint64_t level);


#endif /* !TB_RTT_H */
