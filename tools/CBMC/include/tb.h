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
#include "tb_xlat.h"
#include "tb_rec.h"
#include "tb_rtt.h"
#include "spinlock.h"
#include "utils_def.h"

// Initialize the global state based on the commands
void __init_global_state(unsigned long cmd);

// Sanity check on the implementation of CBMC
void global_sanity_check();

// Call the function based on the X0 value in `config`
void tb_handle_smc(struct tb_regs* config);

// Assertion used to check consistency of the testbench
void __tb_expect_fail();

#endif /* !TB_H */
