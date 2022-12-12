/*
 * (C) COPYRIGHT 2021 Arm Limited or its affiliates
 * ALL RIGHTS RESERVED
 *
 * This file was AUTOGENERATED from the RMM specification.
 * RMM specification source version: e9d4d747
 */

#include "tb.h"
#include "tb_rsi_attestation_token_continue.h"

bool tb_rsi_attestation_token_continue(
    uint64_t addr)
{
    // Initialize registers
    struct tb_regs __tb_regs = __tb_arb_regs();
    __tb_regs.X0 = SMC_RMM_ATTESTATION_TOKEN_CONTINUE;
    __tb_regs.X1 = (uint64_t)addr;

    // Initialize global state
    __init_global_state(__tb_regs.X0);

    // Declare context variables
    struct rmm_realm realm;
    struct rmm_rec rec;

    // Assign context variables before command execution
    realm = CurrentRealm();
    rec = CurrentRec();

    // Pre-conditions
    bool failure_addr_pre = addr != rec.attest_addr;
    bool failure_state_pre = rec.attest_state != ATTEST_IN_PROGRESS;
    bool no_failures_pre = !failure_addr_pre
        && !failure_state_pre;
    bool success_incomplete_pre = __tb_arb_bool();
    bool success_complete_pre = __tb_arb_bool();

    // Execute command
    uint64_t result = tb_handle_smc(&__tb_regs);

    // Assign context variables after command execution
    realm = CurrentRealm();
    rec = CurrentRec();

    // Post-conditions
    bool failure_addr_post = result == RSI_ERROR_INPUT;
    bool failure_state_post = result == RSI_ERROR_STATE;
    bool success_incomplete_post = success_incomplete_pre;
    bool success_complete_post = success_complete_pre;

    // Failure condition assertions
    bool prop_failure_addr_ante = failure_addr_pre;
    __COVER(prop_failure_addr_ante);
    if (prop_failure_addr_ante) {
        bool prop_failure_addr_cons = failure_addr_post;
        __COVER(prop_failure_addr_cons);
        __ASSERT(prop_failure_addr_cons, "prop_failure_addr_cons");
    }

    bool prop_failure_state_ante = !failure_addr_pre
        && failure_state_pre;
    __COVER(prop_failure_state_ante);
    if (prop_failure_state_ante) {
        bool prop_failure_state_cons = failure_state_post;
        __COVER(prop_failure_state_cons);
        __ASSERT(prop_failure_state_cons, "prop_failure_state_cons");
    }

    // Success condition assertions
    bool prop_success_incomplete_ante = no_failures_pre
        && success_incomplete_pre;
    __COVER(prop_success_incomplete_ante);
    if (prop_success_incomplete_ante) {
        bool prop_success_incomplete_cons = success_incomplete_post;
        __COVER(prop_success_incomplete_cons);
        __ASSERT(prop_success_incomplete_cons, "prop_success_incomplete_cons");
    }

    bool prop_success_complete_ante = no_failures_pre
        && success_complete_pre;
    __COVER(prop_success_complete_ante);
    if (prop_success_complete_ante) {
        bool prop_success_complete_cons = success_complete_post;
        __COVER(prop_success_complete_cons);
        __ASSERT(prop_success_complete_cons, "prop_success_complete_cons");
    }

    // Assertion used to check consistency of the testbench
    __tb_expect_fail();

    return no_failures_pre;
}

void entry_point(
    void)
{
    tb_rsi_attestation_token_continue(nondet_uint64_t());
}

