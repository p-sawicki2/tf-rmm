/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef TB_GRANULES_H
#define TB_GRANULES_H

#include "buffer.h"
#include "granule.h"
#include "granule_types.h"
#include "sizes.h"
#include "host_defs.h"
#include "host_utils.h"
#include "platform_api.h"

/*
 * The granule states and pas state
 */
#define UNDELEGATED GRANULE_STATE_UNDELEGATED
#define DELEGATED GRANULE_STATE_DELEGATED
#define RD GRANULE_STATE_RD
#define DATA GRANULE_STATE_DATA
#define REC GRANULE_STATE_REC
#define RTT GRANULE_STATE_RTT

#define RMM_GRANULE_SIZE GRANULE_SIZE

enum granule_pas {
	/* TODO the name is conflict with a macro */
	NS,
	OTHER,
	REALM
};

struct SPEC_granule {
	enum granule_pas pas;
	enum granule_state state;
};

extern unsigned char granules_buffer[HOST_MEM_SIZE];

/*
 * Declare nondet_* functions.
 * CBMC automatically returns nondet values based on the return types.
 * However, enum is treated as integer hence the value might out of range.
 */
struct granule nondet_struct_granule(void);
struct SPEC_granule nondet_struct_SPEC_granule(void);

bool valid_granule_ptr(struct granule *p);
struct granule init_granule(void);
void init_granule_and_page(void);

/*
 * Pedicates
 */
bool AddrIsGranuleAligned(uint64_t addr);
bool PaIsDelegable(uint64_t addr);
struct SPEC_granule Granule(uint64_t addr);

#endif /* !TB_GRANULES_H */
