/*
 * (C) COPYRIGHT 2021 Arm Limited or its affiliates
 * ALL RIGHTS RESERVED
 *
 * This file was AUTOGENERATED from the RMM specification.
 * RMM specification source version: 404016e5-dirty
 */

#include "tb.h"
#include "tb_rsi_host_call.h"

bool tb_rsi_host_call(
    uint64_t addr)
{
    // Initialize registers
    struct tb_regs __tb_regs = __tb_arb_regs();
    __tb_regs.X0 = SMC_RMM_HOST_CALL;
    __tb_regs.X1 = (uint64_t)addr;

    // Initialize global state
    __init_global_state(__tb_regs.X0);

    // Declare context variables
    struct rmm_realm realm;
    struct rmm_rec rec;
    struct rsi_host_call_buffer data;

    // Assign context variables before command execution
    realm = CurrentRealm();
    rec = CurrentRec();
    data = RealmHostCall(addr);

    // Pre-conditions
    bool failure_addr_align_pre = !AddrIsAligned(addr, 256);
    bool failure_addr_bound_pre = !AddrIsProtected(addr, realm);
    bool no_failures_pre = !failure_addr_align_pre
        && !failure_addr_bound_pre;

    // Execute command and read the result.
    tb_handle_smc(&__tb_regs);
    uint64_t result =  __tb_regs.X0;

    // Assign context variables after command execution
    realm = CurrentRealm();
    rec = CurrentRec();
    data = RealmHostCall(addr);

    // Post-conditions
    bool failure_addr_align_post = result == RSI_ERROR_INPUT;
    bool failure_addr_bound_post = result == RSI_ERROR_INPUT;

    // Failure condition assertions
    bool prop_failure_addr_align_ante = failure_addr_align_pre;
    __COVER(prop_failure_addr_align_ante);
    if (prop_failure_addr_align_ante) {
        bool prop_failure_addr_align_cons = failure_addr_align_post;
        __COVER(prop_failure_addr_align_cons);
        __ASSERT(prop_failure_addr_align_cons, "prop_failure_addr_align_cons");
    }

    bool prop_failure_addr_bound_ante = !failure_addr_align_pre
        && failure_addr_bound_pre;
    __COVER(prop_failure_addr_bound_ante);
    if (prop_failure_addr_bound_ante) {
        bool prop_failure_addr_bound_cons = failure_addr_bound_post;
        __COVER(prop_failure_addr_bound_cons);
        __ASSERT(prop_failure_addr_bound_cons, "prop_failure_addr_bound_cons");
    }

    // Assertion used to check consistency of the testbench
    __tb_expect_fail();

    return no_failures_pre;
}

