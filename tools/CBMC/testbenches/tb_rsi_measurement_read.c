/*
 * (C) COPYRIGHT 2021 Arm Limited or its affiliates
 * ALL RIGHTS RESERVED
 *
 * This file was AUTOGENERATED from the RMM specification.
 * RMM specification source version: e9d4d747
 */

#include "tb.h"
#include "tb_rsi_measurement_read.h"

bool tb_rsi_measurement_read(
    uint64_t index)
{
    // Initialize registers
    struct tb_regs __tb_regs = __tb_arb_regs();
    __tb_regs.X0 = SMC_RMM_MEASUREMENT_READ;
    __tb_regs.X1 = (uint64_t)index;

    // Initialize global state
    __init_global_state(__tb_regs.X0);

    // Pre-conditions
    bool failure_index_bound_pre = index > 4;
    bool no_failures_pre = !failure_index_bound_pre;

    // Execute command
    uint64_t result = tb_handle_smc(&__tb_regs);

    // Post-conditions
    bool failure_index_bound_post = result == RSI_ERROR_INPUT;

    // Failure condition assertions
    bool prop_failure_index_bound_ante = failure_index_bound_pre;
    __COVER(prop_failure_index_bound_ante);
    if (prop_failure_index_bound_ante) {
        bool prop_failure_index_bound_cons = failure_index_bound_post;
        __COVER(prop_failure_index_bound_cons);
        __ASSERT(prop_failure_index_bound_cons, "prop_failure_index_bound_cons");
    }

    // Assertion used to check consistency of the testbench
    __tb_expect_fail();

    return no_failures_pre;
}

void entry_point(
    void)
{
    tb_rsi_measurement_read(nondet_uint64_t());
}

