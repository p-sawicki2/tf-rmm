/*
 * (C) COPYRIGHT 2021 Arm Limited or its affiliates
 * ALL RIGHTS RESERVED
 *
 * This file was AUTOGENERATED from the RMM specification.
 * RMM specification source version: e9d4d747
 */

#include "tb.h"
#include "tb_psci_features.h"

bool tb_psci_features(
    uint32_t psci_func_id)
{
    // Initialize registers
    struct tb_regs __tb_regs = __tb_arb_regs();
    __tb_regs.X0 = SMC_RMM_FEATURES;
    __tb_regs.X1 = (uint64_t)psci_func_id;

    // Initialize global state
    __init_global_state(__tb_regs.X0);

    // Pre-conditions
    bool no_failures_pre = true;
    bool success_func_ok_pre = __tb_arb_bool();
    bool success_func_not_ok_pre = __tb_arb_bool();

    // Execute command
    uint64_t result = tb_handle_smc(&__tb_regs);

    // Post-conditions
    bool success_func_ok_post = success_func_ok_pre;
    bool success_func_not_ok_post = success_func_not_ok_pre;

    // Assertion used to check consistency of the testbench
    __tb_expect_fail();

    return no_failures_pre;
}

void entry_point(
    void)
{
    tb_psci_features(nondet_uint32_t());
}

