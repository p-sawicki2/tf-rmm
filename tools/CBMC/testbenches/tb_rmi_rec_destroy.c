/*
 * (C) COPYRIGHT 2021 Arm Limited or its affiliates
 * ALL RIGHTS RESERVED
 *
 * This file was AUTOGENERATED from the RMM specification.
 * RMM specification source version: e9d4d747
 */

#include "tb.h"
#include "tb_rmi_rec_destroy.h"

bool tb_rmi_rec_destroy(
    uint64_t rec)
{
    // Initialize registers
    struct tb_regs __tb_regs = __tb_arb_regs();
    __tb_regs.X0 = SMC_RMM_REC_DESTROY;
    __tb_regs.X1 = (uint64_t)rec;

    // Initialize global state
    __init_global_state(__tb_regs.X0);

    // Declare context variables
    uint64_t rd;
    struct rmm_rec rec_obj;

    // Assign context variables before command execution
    rd = Rec(rec).owner;
    rec_obj = Rec(rec);

    // Pre-conditions
    bool failure_rec_align_pre = !AddrIsGranuleAligned(rec);
    bool failure_rec_bound_pre = !PaIsDelegable(rec);
    bool failure_rec_gran_state_pre = Granule(rec).state != REC;
    bool failure_rec_state_pre = Rec(rec).state == RUNNING;
    bool no_failures_pre = !failure_rec_align_pre
        && !failure_rec_bound_pre
        && !failure_rec_gran_state_pre
        && !failure_rec_state_pre;

    // Execute command
    uint64_t result = tb_handle_smc(&__tb_regs);

    // Post-conditions
    bool failure_rec_align_post = ResultEqual_2(result, RMI_ERROR_INPUT);
    bool failure_rec_bound_post = ResultEqual_2(result, RMI_ERROR_INPUT);
    bool failure_rec_gran_state_post = ResultEqual_2(result, RMI_ERROR_INPUT);
    bool failure_rec_state_post = ResultEqual_2(result, RMI_ERROR_REC);
    bool success_rec_gran_state_post = Granule(rec).state == DELEGATED;
    bool success_rec_aux_state_post = RecAuxStateEqual(rec_obj.aux, RecAuxCount(rd), DELEGATED);

    // Failure condition assertions
    bool prop_failure_rec_align_ante = failure_rec_align_pre;
    __COVER(prop_failure_rec_align_ante);
    if (prop_failure_rec_align_ante) {
        bool prop_failure_rec_align_cons = failure_rec_align_post;
        __COVER(prop_failure_rec_align_cons);
        __ASSERT(prop_failure_rec_align_cons, "prop_failure_rec_align_cons");
    }

    bool prop_failure_rec_bound_ante = !failure_rec_align_pre
        && failure_rec_bound_pre;
    __COVER(prop_failure_rec_bound_ante);
    if (prop_failure_rec_bound_ante) {
        bool prop_failure_rec_bound_cons = failure_rec_bound_post;
        __COVER(prop_failure_rec_bound_cons);
        __ASSERT(prop_failure_rec_bound_cons, "prop_failure_rec_bound_cons");
    }

    bool prop_failure_rec_gran_state_ante = !failure_rec_align_pre
        && !failure_rec_bound_pre
        && failure_rec_gran_state_pre;
    __COVER(prop_failure_rec_gran_state_ante);
    if (prop_failure_rec_gran_state_ante) {
        bool prop_failure_rec_gran_state_cons = failure_rec_gran_state_post;
        __COVER(prop_failure_rec_gran_state_cons);
        __ASSERT(prop_failure_rec_gran_state_cons, "prop_failure_rec_gran_state_cons");
    }

    bool prop_failure_rec_state_ante = !failure_rec_align_pre
        && !failure_rec_bound_pre
        && !failure_rec_gran_state_pre
        && failure_rec_state_pre;
    __COVER(prop_failure_rec_state_ante);
    if (prop_failure_rec_state_ante) {
        bool prop_failure_rec_state_cons = failure_rec_state_post;
        __COVER(prop_failure_rec_state_cons);
        __ASSERT(prop_failure_rec_state_cons, "prop_failure_rec_state_cons");
    }

    // Result assertion
    bool prop_result_ante = no_failures_pre;
    __COVER(prop_result_ante);
    if (prop_result_ante) {
        bool prop_result_cons = result == RMI_SUCCESS;
        __COVER(prop_result_cons);
        __ASSERT(prop_result_cons, "prop_result_cons");
    }

    // Success condition assertions
    bool prop_success_rec_gran_state_ante = no_failures_pre;
    __COVER(prop_success_rec_gran_state_ante);
    if (prop_success_rec_gran_state_ante) {
        bool prop_success_rec_gran_state_cons = success_rec_gran_state_post;
        __COVER(prop_success_rec_gran_state_cons);
        __ASSERT(prop_success_rec_gran_state_cons, "prop_success_rec_gran_state_cons");
    }

    bool prop_success_rec_aux_state_ante = no_failures_pre;
    __COVER(prop_success_rec_aux_state_ante);
    if (prop_success_rec_aux_state_ante) {
        bool prop_success_rec_aux_state_cons = success_rec_aux_state_post;
        __COVER(prop_success_rec_aux_state_cons);
        __ASSERT(prop_success_rec_aux_state_cons, "prop_success_rec_aux_state_cons");
    }

    // Assertion used to check consistency of the testbench
    __tb_expect_fail();

    return no_failures_pre;
}

void entry_point(
    void)
{
    tb_rmi_rec_destroy(nondet_uint64_t());
}

