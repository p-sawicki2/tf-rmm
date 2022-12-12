/*
 * Copyright (c) 2020-2022, Arm Limited. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

#ifndef TB_H__
#define TB_H__

#include "assert.h"
#include "exit.h"
#include "smc-handler.h"
#include "smc-rmi.h"
#include "smc-rsi.h"
#include "stdbool.h"
#include "stdint.h"
#include "string.h"
#include "tb_common.h"
#include "tb_realm.h"
#include "tb_granules.h"
#include "tb_interface.h"
#include "tb_xlat.h"
#include "tb_rec.h"
#include "tb_rtt.h"
#include "spinlock.h"
#include "utils_def.h"

/*******************************************************************************
 * Forward declaration of a few Non-deterministic generation of ground C types.
 *******************************************************************************
 */

#define SMC_RMM_DATA_CREATEUNKNOWN SMC_RMM_DATA_CREATE_UNKNOWN
#define SMC_RMM_RTT_MAPPROTECTED SMC_RMM_RTT_MAP_PROTECTED
#define SMC_RMM_RTT_UNMAPPROTECTED SMC_RMM_RTT_UNMAP_PROTECTED
#define SMC_RMM_RTT_MAPNONSECURE SMC_RMM_RTT_MAP_NON_SECURE
#define SMC_RMM_RTT_UNMAPNONSECURE SMC_RMM_RTT_UNMAP_NON_SECURE
//#define SMC_RMM_RTT_READENTRY SMC_RMM_RTT_READ_ENTRY
//#define SMC_RMM_VERSION SMC_RMM_SYSTEM_INTERFACE_VERSION
#define SMC_RMM_SYSTEM_INTERFACEVERSION SMC_RMM_SYSTEM_INTERFACE_VERSION
#define SMC_RMM_MEMORY_DISPOSE SMC_RSI_MEMORY_DISPOSE
#define SMC_RMM_READ_MEASUREMENT SMC_RSI_MEASUREMENT_READ
//TODO what are these?
#define RMM_PASIZE 52UL
#define RMM_REALM_NULL 0UL

//#define REALM PHYSICAL_ADDRESS_SPACE_REALM
#define SMC_RMM_DATA_CREATEUNKNOWN SMC_RMM_DATA_CREATE_UNKNOWN


// Initialize the global state based on the commands
void __init_global_state(unsigned long cmd);

// Sanity check on the implementation of CBMC
void global_sanity_check();

// Call the function based on the X0 value in `config`
uint64_t tb_handle_smc(struct tb_regs* config);

#endif /* !TB_H */
