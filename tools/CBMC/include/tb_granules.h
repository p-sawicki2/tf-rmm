/*
 * Copyright (c) 2021-2022, Arm Limited. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-3-Clause
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
	PHYSICAL_ADDRESS_SPACE_NS,
	PHYSICAL_ADDRESS_SPACE_SECURE,
	PHYSICAL_ADDRESS_SPACE_REALM,
	PHYSICAL_ADDRESS_SPACE_ROOT
};

struct SPEC_granule {
	enum granule_pas pas;
	enum granule_state state;
	unsigned long owner;
};

// Declare nondet_* functions.
// CBMC automatically returns nondet values based on the return types.
// However, enum is treated as integer hence the value might out of range.
struct granule nondet_struct_granule(void);
struct SPEC_granule nondet_struct_SPEC_granule(void);
unsigned long nondet_granule_addr();

bool valid_granule_ptr(struct granule *p);
bool valid_granule_state(enum granule_state value);
bool valid_granule(struct granule value); 
struct granule init_granule(); 
void init_delegated_granule(void);
void init_ns_granule(void);

/////////////////////////////
// Pedicates
/////////////////////////////
bool AddrIsGranuleAligned(unsigned long addr);
bool PaIsDelegable(unsigned long addr);
struct SPEC_granule Granule(unsigned long addr);

#endif /* !TB_GRANULES_H */
