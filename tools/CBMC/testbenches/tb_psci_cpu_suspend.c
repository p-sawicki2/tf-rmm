/*
 * (C) COPYRIGHT 2021 Arm Limited or its affiliates
 * ALL RIGHTS RESERVED
 *
 * This file was AUTOGENERATED from the RMM specification.
 * RMM specification source version: 9f097087-dirty
 */

#include "tb.h"
#include "tb_psci_cpu_suspend.h"

bool tb_psci_cpu_suspend(
    uint32_t power_state,
    uint64_t entry_point_address,
    uint64_t context_id)
{
    // Initialize registers
    struct tb_regs __tb_regs = __tb_arb_regs();
    __tb_regs.X0 = SMC_RMM_CPU_SUSPEND;
    __tb_regs.X1 = (uint64_t)power_state;
    __tb_regs.X2 = (uint64_t)entry_point_address;
    __tb_regs.X3 = (uint64_t)context_id;

    // Initialize global state
    __init_global_state(__tb_regs.X0);

    // Pre-conditions
    bool no_failures_pre = true;

    // Execute command and read the result.
    tb_handle_smc(&__tb_regs);

    // Assertion used to check consistency of the testbench
    __tb_expect_fail();

    return no_failures_pre;
}

