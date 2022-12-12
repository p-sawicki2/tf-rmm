/*
 * (C) COPYRIGHT 2021 Arm Limited or its affiliates
 * ALL RIGHTS RESERVED
 *
 * This file was AUTOGENERATED from the RMM specification.
 * RMM specification source version: e9d4d747
 */

#include "tb.h"
#include "tb_psci_system_reset.h"

bool tb_psci_system_reset(
    void)
{
    // Initialize registers
    struct tb_regs __tb_regs = __tb_arb_regs();
    __tb_regs.X0 = SMC_RMM_SYSTEM_RESET;

    // Initialize global state
    __init_global_state(__tb_regs.X0);

    // Declare context variables
    struct rmm_realm realm;

    // Assign context variables before command execution
    realm = CurrentRealm();

    // Pre-conditions
    bool no_failures_pre = true;

    // Execute command
    uint64_t result = tb_handle_smc(&__tb_regs);

    // Assign context variables after command execution
    realm = CurrentRealm();

    // Assertion used to check consistency of the testbench
    __tb_expect_fail();

    return no_failures_pre;
}

void entry_point(
    void)
{
    tb_psci_system_reset();
}

