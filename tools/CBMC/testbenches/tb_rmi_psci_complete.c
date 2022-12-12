/*
 * (C) COPYRIGHT 2021 Arm Limited or its affiliates
 * ALL RIGHTS RESERVED
 *
 * This file was AUTOGENERATED from the RMM specification.
 * RMM specification source version: 9f097087-dirty
 */

#include "tb.h"
#include "tb_rmi_psci_complete.h"

bool tb_rmi_psci_complete(
    uint64_t calling_rec,
    uint64_t target_rec)
{
    // Initialize registers
    struct tb_regs __tb_regs = __tb_arb_regs();
    __tb_regs.X0 = SMC_RMM_PSCI_COMPLETE;
    __tb_regs.X1 = (uint64_t)calling_rec;
    __tb_regs.X2 = (uint64_t)target_rec;

    // Initialize global state
    __init_global_state(__tb_regs.X0);

    // Pre-conditions
    bool failure_alias_pre = calling_rec == target_rec;
    bool failure_calling_align_pre = !AddrIsGranuleAligned(calling_rec);
    bool failure_calling_bound_pre = !PaIsDelegable(calling_rec);
    bool failure_calling_state_pre = Granule(calling_rec).state != REC;
    bool failure_target_align_pre = !AddrIsGranuleAligned(target_rec);
    bool failure_target_bound_pre = !PaIsDelegable(target_rec);
    bool failure_target_state_pre = Granule(target_rec).state != REC;
    bool failure_pending_pre = Rec(calling_rec).psci_pending != PSCI_REQUEST_PENDING;
    bool failure_owner_pre = Rec(target_rec).owner != Rec(calling_rec).owner;
    bool failure_target_pre = Rec(target_rec).mpidr != Rec(calling_rec).gprs[1];
    bool no_failures_pre = !failure_alias_pre
        && !failure_calling_align_pre
        && !failure_calling_bound_pre
        && !failure_calling_state_pre
        && !failure_target_align_pre
        && !failure_target_bound_pre
        && !failure_target_state_pre
        && !failure_pending_pre
        && !failure_owner_pre
        && !failure_target_pre;
    bool success_on_already_pre = (Rec(calling_rec).gprs[0] == FID_PSCI_CPU_ON && Rec(target_rec).flags.runnable == RUNNABLE);
    bool success_on_success_pre = (Rec(calling_rec).gprs[0] == FID_PSCI_CPU_ON && Rec(target_rec).flags.runnable != RUNNABLE);
    bool success_affinity_on_pre = (Rec(calling_rec).gprs[0] == FID_PSCI_AFFINITY_INFO && Rec(target_rec).flags.runnable == RUNNABLE);
    bool success_affinity_off_pre = (Rec(calling_rec).gprs[0] == FID_PSCI_AFFINITY_INFO && Rec(target_rec).flags.runnable != RUNNABLE);

    // Execute command and read the result.
    tb_handle_smc(&__tb_regs);
    uint64_t result =  __tb_regs.X0;

    // Post-conditions
    bool failure_alias_post = ResultEqual_2(result, RMI_ERROR_INPUT);
    bool failure_calling_align_post = ResultEqual_2(result, RMI_ERROR_INPUT);
    bool failure_calling_bound_post = ResultEqual_2(result, RMI_ERROR_INPUT);
    bool failure_calling_state_post = ResultEqual_2(result, RMI_ERROR_INPUT);
    bool failure_target_align_post = ResultEqual_2(result, RMI_ERROR_INPUT);
    bool failure_target_bound_post = ResultEqual_2(result, RMI_ERROR_INPUT);
    bool failure_target_state_post = ResultEqual_2(result, RMI_ERROR_INPUT);
    bool failure_pending_post = ResultEqual_2(result, RMI_ERROR_INPUT);
    bool failure_owner_post = ResultEqual_2(result, RMI_ERROR_INPUT);
    bool failure_target_post = ResultEqual_2(result, RMI_ERROR_INPUT);
    bool success_pending_post = Rec(calling_rec).psci_pending == NO_PSCI_REQUEST_PENDING;
    bool success_on_already_post = (Rec(calling_rec).gprs[0] == PsciReturnCodeEncode(PSCI_ALREADY_ON));
    bool success_on_success_post = (Rec(target_rec).gprs[0] == Rec(calling_rec).gprs[2] && Rec(target_rec).gprs[1] == Zeros() && Rec(target_rec).gprs[2] == Zeros() && Rec(target_rec).gprs[3] == Zeros() && Rec(target_rec).gprs[4] == Zeros() && Rec(target_rec).gprs[5] == Zeros() && Rec(target_rec).gprs[6] == Zeros() && Rec(target_rec).gprs[7] == Zeros() && Rec(target_rec).gprs[8] == Zeros() && Rec(target_rec).gprs[9] == Zeros() && Rec(target_rec).gprs[10] == Zeros() && Rec(target_rec).gprs[11] == Zeros() && Rec(target_rec).gprs[12] == Zeros() && Rec(target_rec).gprs[13] == Zeros() && Rec(target_rec).gprs[14] == Zeros() && Rec(target_rec).gprs[15] == Zeros() && Rec(target_rec).gprs[16] == Zeros() && Rec(target_rec).gprs[17] == Zeros() && Rec(target_rec).gprs[18] == Zeros() && Rec(target_rec).gprs[19] == Zeros() && Rec(target_rec).gprs[20] == Zeros() && Rec(target_rec).gprs[21] == Zeros() && Rec(target_rec).gprs[22] == Zeros() && Rec(target_rec).gprs[23] == Zeros() && Rec(target_rec).gprs[24] == Zeros() && Rec(target_rec).gprs[25] == Zeros() && Rec(target_rec).gprs[26] == Zeros() && Rec(target_rec).gprs[27] == Zeros() && Rec(target_rec).gprs[28] == Zeros() && Rec(target_rec).gprs[29] == Zeros() && Rec(target_rec).gprs[30] == Zeros() && Rec(target_rec).gprs[31] == Zeros() && Rec(target_rec).pc == Rec(calling_rec).gprs[2] && Rec(target_rec).flags.runnable == RUNNABLE && Rec(calling_rec).gprs[0] == PsciReturnCodeEncode(PSCI_SUCCESS));
    bool success_affinity_on_post = (Rec(calling_rec).gprs[0] == PsciReturnCodeEncode(PSCI_SUCCESS));
    bool success_affinity_off_post = (Rec(calling_rec).gprs[0] == PsciReturnCodeEncode(PSCI_OFF));
    bool success_gprs_post = (Rec(calling_rec).gprs[1] == Zeros() && Rec(calling_rec).gprs[2] == Zeros() && Rec(calling_rec).gprs[3] == Zeros());

    // Failure condition assertions
    bool prop_failure_alias_ante = failure_alias_pre;
    __COVER(prop_failure_alias_ante);
    if (prop_failure_alias_ante) {
        bool prop_failure_alias_cons = failure_alias_post;
        __COVER(prop_failure_alias_cons);
        __ASSERT(prop_failure_alias_cons, "prop_failure_alias_cons");
    }

    bool prop_failure_calling_align_ante = !failure_alias_pre
        && failure_calling_align_pre;
    __COVER(prop_failure_calling_align_ante);
    if (prop_failure_calling_align_ante) {
        bool prop_failure_calling_align_cons = failure_calling_align_post;
        __COVER(prop_failure_calling_align_cons);
        __ASSERT(prop_failure_calling_align_cons, "prop_failure_calling_align_cons");
    }

    bool prop_failure_calling_bound_ante = !failure_alias_pre
        && !failure_calling_align_pre
        && failure_calling_bound_pre;
    __COVER(prop_failure_calling_bound_ante);
    if (prop_failure_calling_bound_ante) {
        bool prop_failure_calling_bound_cons = failure_calling_bound_post;
        __COVER(prop_failure_calling_bound_cons);
        __ASSERT(prop_failure_calling_bound_cons, "prop_failure_calling_bound_cons");
    }

    bool prop_failure_calling_state_ante = !failure_alias_pre
        && !failure_calling_align_pre
        && !failure_calling_bound_pre
        && failure_calling_state_pre;
    __COVER(prop_failure_calling_state_ante);
    if (prop_failure_calling_state_ante) {
        bool prop_failure_calling_state_cons = failure_calling_state_post;
        __COVER(prop_failure_calling_state_cons);
        __ASSERT(prop_failure_calling_state_cons, "prop_failure_calling_state_cons");
    }

    bool prop_failure_target_align_ante = !failure_alias_pre
        && !failure_calling_align_pre
        && !failure_calling_bound_pre
        && !failure_calling_state_pre
        && failure_target_align_pre;
    __COVER(prop_failure_target_align_ante);
    if (prop_failure_target_align_ante) {
        bool prop_failure_target_align_cons = failure_target_align_post;
        __COVER(prop_failure_target_align_cons);
        __ASSERT(prop_failure_target_align_cons, "prop_failure_target_align_cons");
    }

    bool prop_failure_target_bound_ante = !failure_alias_pre
        && !failure_calling_align_pre
        && !failure_calling_bound_pre
        && !failure_calling_state_pre
        && !failure_target_align_pre
        && failure_target_bound_pre;
    __COVER(prop_failure_target_bound_ante);
    if (prop_failure_target_bound_ante) {
        bool prop_failure_target_bound_cons = failure_target_bound_post;
        __COVER(prop_failure_target_bound_cons);
        __ASSERT(prop_failure_target_bound_cons, "prop_failure_target_bound_cons");
    }

    bool prop_failure_target_state_ante = !failure_alias_pre
        && !failure_calling_align_pre
        && !failure_calling_bound_pre
        && !failure_calling_state_pre
        && !failure_target_align_pre
        && !failure_target_bound_pre
        && failure_target_state_pre;
    __COVER(prop_failure_target_state_ante);
    if (prop_failure_target_state_ante) {
        bool prop_failure_target_state_cons = failure_target_state_post;
        __COVER(prop_failure_target_state_cons);
        __ASSERT(prop_failure_target_state_cons, "prop_failure_target_state_cons");
    }

    bool prop_failure_pending_ante = !failure_alias_pre
        && !failure_calling_align_pre
        && !failure_calling_bound_pre
        && !failure_calling_state_pre
        && !failure_target_align_pre
        && !failure_target_bound_pre
        && !failure_target_state_pre
        && failure_pending_pre;
    __COVER(prop_failure_pending_ante);
    if (prop_failure_pending_ante) {
        bool prop_failure_pending_cons = failure_pending_post;
        __COVER(prop_failure_pending_cons);
        __ASSERT(prop_failure_pending_cons, "prop_failure_pending_cons");
    }

    bool prop_failure_owner_ante = !failure_alias_pre
        && !failure_calling_align_pre
        && !failure_calling_bound_pre
        && !failure_calling_state_pre
        && !failure_target_align_pre
        && !failure_target_bound_pre
        && !failure_target_state_pre
        && !failure_pending_pre
        && failure_owner_pre;
    __COVER(prop_failure_owner_ante);
    if (prop_failure_owner_ante) {
        bool prop_failure_owner_cons = failure_owner_post;
        __COVER(prop_failure_owner_cons);
        __ASSERT(prop_failure_owner_cons, "prop_failure_owner_cons");
    }

    bool prop_failure_target_ante = !failure_alias_pre
        && !failure_calling_align_pre
        && !failure_calling_bound_pre
        && !failure_calling_state_pre
        && !failure_target_align_pre
        && !failure_target_bound_pre
        && !failure_target_state_pre
        && !failure_pending_pre
        && !failure_owner_pre
        && failure_target_pre;
    __COVER(prop_failure_target_ante);
    if (prop_failure_target_ante) {
        bool prop_failure_target_cons = failure_target_post;
        __COVER(prop_failure_target_cons);
        __ASSERT(prop_failure_target_cons, "prop_failure_target_cons");
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
    bool prop_success_pending_ante = no_failures_pre;
    __COVER(prop_success_pending_ante);
    if (prop_success_pending_ante) {
        bool prop_success_pending_cons = success_pending_post;
        __COVER(prop_success_pending_cons);
        __ASSERT(prop_success_pending_cons, "prop_success_pending_cons");
    }

    bool prop_success_on_already_ante = no_failures_pre
        && success_on_already_pre;
    __COVER(prop_success_on_already_ante);
    if (prop_success_on_already_ante) {
        bool prop_success_on_already_cons = success_on_already_post;
        __COVER(prop_success_on_already_cons);
        __ASSERT(prop_success_on_already_cons, "prop_success_on_already_cons");
    }

    bool prop_success_on_success_ante = no_failures_pre
        && success_on_success_pre;
    __COVER(prop_success_on_success_ante);
    if (prop_success_on_success_ante) {
        bool prop_success_on_success_cons = success_on_success_post;
        __COVER(prop_success_on_success_cons);
        __ASSERT(prop_success_on_success_cons, "prop_success_on_success_cons");
    }

    bool prop_success_affinity_on_ante = no_failures_pre
        && success_affinity_on_pre;
    __COVER(prop_success_affinity_on_ante);
    if (prop_success_affinity_on_ante) {
        bool prop_success_affinity_on_cons = success_affinity_on_post;
        __COVER(prop_success_affinity_on_cons);
        __ASSERT(prop_success_affinity_on_cons, "prop_success_affinity_on_cons");
    }

    bool prop_success_affinity_off_ante = no_failures_pre
        && success_affinity_off_pre;
    __COVER(prop_success_affinity_off_ante);
    if (prop_success_affinity_off_ante) {
        bool prop_success_affinity_off_cons = success_affinity_off_post;
        __COVER(prop_success_affinity_off_cons);
        __ASSERT(prop_success_affinity_off_cons, "prop_success_affinity_off_cons");
    }

    bool prop_success_gprs_ante = no_failures_pre;
    __COVER(prop_success_gprs_ante);
    if (prop_success_gprs_ante) {
        bool prop_success_gprs_cons = success_gprs_post;
        __COVER(prop_success_gprs_cons);
        __ASSERT(prop_success_gprs_cons, "prop_success_gprs_cons");
    }

    // Assertion used to check consistency of the testbench
    __tb_expect_fail();

    return no_failures_pre;
}

