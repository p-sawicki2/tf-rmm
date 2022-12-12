/*
 * (C) COPYRIGHT 2021 Arm Limited or its affiliates
 * ALL RIGHTS RESERVED
 *
 * This file was AUTOGENERATED from the RMM specification.
 * RMM specification source version: 9f097087-dirty
 */

#include "tb.h"
#include "tb_rmi_rtt_fold.h"

bool tb_rmi_rtt_fold(
    uint64_t rd,
    uint64_t ipa,
    int64_t level)
{
    // Initialize registers
    struct tb_regs __tb_regs = __tb_arb_regs();
    __tb_regs.X0 = SMC_RMM_RTT_FOLD;
    __tb_regs.X1 = (uint64_t)rd;
    __tb_regs.X2 = (uint64_t)ipa;
    __tb_regs.X3 = (uint64_t)level;

    // Initialize global state
    __init_global_state(__tb_regs.X0);

    // Declare context variables
    struct rmm_rtt_walk_result walk;
    uint64_t entry_idx;
    struct rmm_rtt_entry fold;

    // Assign context variables before command execution
    walk = RttWalk(
        rd, ipa,
        level - 1);
    entry_idx = RttEntryIndex(
        ipa, walk.level);
    fold = RttFold(
        Rtt(walk.entry.addr));

    // Pre-conditions
    bool failure_rd_align_pre = !AddrIsGranuleAligned(rd);
    bool failure_rd_bound_pre = !PaIsDelegable(rd);
    bool failure_rd_state_pre = Granule(rd).state != RD;
    bool failure_level_bound_pre = (!RttLevelIsValid(rd, level) || RttLevelIsStarting(rd, level));
    bool failure_ipa_align_pre = !AddrIsRttLevelAligned(ipa, level - 1);
    bool failure_ipa_bound_pre = UInt(ipa) >= (pow(2, Realm(rd).ipa_width));
    bool failure_rtt_walk_pre = walk.level < level - 1;
    bool failure_rtte_state_pre = walk.entry.state != TABLE;
    bool failure_rtt_homo_pre = !RttIsHomogeneous(Rtt(walk.entry.addr));
    bool no_failures_pre = !failure_rd_align_pre
        && !failure_rd_bound_pre
        && !failure_rd_state_pre
        && !failure_level_bound_pre
        && !failure_ipa_align_pre
        && !failure_ipa_bound_pre
        && !failure_rtt_walk_pre
        && !failure_rtte_state_pre
        && !failure_rtt_homo_pre;
    bool success_rtte_addr_pre = (fold.state != UNASSIGNED && fold.state != UNASSIGNED_NS);
    bool success_rtte_attr_pre = (fold.state == ASSIGNED || fold.state == ASSIGNED_NS);
    bool success_rtte_ripas_pre = AddrIsProtected(ipa, Realm(rd));

    // Execute command and read the result.
    tb_handle_smc(&__tb_regs);
    uint64_t result =  __tb_regs.X0;
    uint64_t rtt =  __tb_regs.X1;

    // Assign context variables after command execution
    walk = RttWalk(
        rd, ipa,
        level - 1);
    entry_idx = RttEntryIndex(
        ipa, walk.level);

    // Post-conditions
    bool failure_rd_align_post = ResultEqual_2(result, RMI_ERROR_INPUT);
    bool failure_rd_bound_post = ResultEqual_2(result, RMI_ERROR_INPUT);
    bool failure_rd_state_post = ResultEqual_2(result, RMI_ERROR_INPUT);
    bool failure_level_bound_post = ResultEqual_2(result, RMI_ERROR_INPUT);
    bool failure_ipa_align_post = ResultEqual_2(result, RMI_ERROR_INPUT);
    bool failure_ipa_bound_post = ResultEqual_2(result, RMI_ERROR_INPUT);
    bool failure_rtt_walk_post = ResultEqual_3(result, RMI_ERROR_RTT, walk.level);
    bool failure_rtte_state_post = ResultEqual_3(result, RMI_ERROR_RTT, walk.level);
    bool failure_rtt_homo_post = ResultEqual_3(result, RMI_ERROR_RTT, level);
    bool success_rtte_state_post = walk.entry.state == fold.state;
    bool success_rtte_addr_post = walk.entry.addr == fold.addr;
    bool success_rtte_attr_post = (walk.entry.MemAttr == fold.MemAttr && walk.entry.S2AP == fold.S2AP && walk.entry.SH == fold.SH);
    bool success_rtte_ripas_post = walk.entry.ripas == fold.ripas;
    bool success_rtt_state_post = Granule(walk.entry.addr).state == DELEGATED;
    bool success_rtt_post = rtt == walk.entry.addr;

    // Failure condition assertions
    bool prop_failure_rd_align_ante = failure_rd_align_pre;
    __COVER(prop_failure_rd_align_ante);
    if (prop_failure_rd_align_ante) {
        bool prop_failure_rd_align_cons = failure_rd_align_post;
        __COVER(prop_failure_rd_align_cons);
        __ASSERT(prop_failure_rd_align_cons, "prop_failure_rd_align_cons");
    }

    bool prop_failure_rd_bound_ante = !failure_rd_align_pre
        && failure_rd_bound_pre;
    __COVER(prop_failure_rd_bound_ante);
    if (prop_failure_rd_bound_ante) {
        bool prop_failure_rd_bound_cons = failure_rd_bound_post;
        __COVER(prop_failure_rd_bound_cons);
        __ASSERT(prop_failure_rd_bound_cons, "prop_failure_rd_bound_cons");
    }

    bool prop_failure_rd_state_ante = !failure_rd_align_pre
        && !failure_rd_bound_pre
        && failure_rd_state_pre;
    __COVER(prop_failure_rd_state_ante);
    if (prop_failure_rd_state_ante) {
        bool prop_failure_rd_state_cons = failure_rd_state_post;
        __COVER(prop_failure_rd_state_cons);
        __ASSERT(prop_failure_rd_state_cons, "prop_failure_rd_state_cons");
    }

    bool prop_failure_level_bound_ante = !failure_rd_align_pre
        && !failure_rd_bound_pre
        && !failure_rd_state_pre
        && failure_level_bound_pre;
    __COVER(prop_failure_level_bound_ante);
    if (prop_failure_level_bound_ante) {
        bool prop_failure_level_bound_cons = failure_level_bound_post;
        __COVER(prop_failure_level_bound_cons);
        __ASSERT(prop_failure_level_bound_cons, "prop_failure_level_bound_cons");
    }

    bool prop_failure_ipa_align_ante = !failure_rd_align_pre
        && !failure_rd_bound_pre
        && !failure_rd_state_pre
        && !failure_level_bound_pre
        && failure_ipa_align_pre;
    __COVER(prop_failure_ipa_align_ante);
    if (prop_failure_ipa_align_ante) {
        bool prop_failure_ipa_align_cons = failure_ipa_align_post;
        __COVER(prop_failure_ipa_align_cons);
        __ASSERT(prop_failure_ipa_align_cons, "prop_failure_ipa_align_cons");
    }

    bool prop_failure_ipa_bound_ante = !failure_rd_align_pre
        && !failure_rd_bound_pre
        && !failure_rd_state_pre
        && !failure_level_bound_pre
        && !failure_ipa_align_pre
        && failure_ipa_bound_pre;
    __COVER(prop_failure_ipa_bound_ante);
    if (prop_failure_ipa_bound_ante) {
        bool prop_failure_ipa_bound_cons = failure_ipa_bound_post;
        __COVER(prop_failure_ipa_bound_cons);
        __ASSERT(prop_failure_ipa_bound_cons, "prop_failure_ipa_bound_cons");
    }

    bool prop_failure_rtt_walk_ante = !failure_rd_align_pre
        && !failure_rd_bound_pre
        && !failure_rd_state_pre
        && !failure_level_bound_pre
        && !failure_ipa_align_pre
        && !failure_ipa_bound_pre
        && failure_rtt_walk_pre;
    __COVER(prop_failure_rtt_walk_ante);
    if (prop_failure_rtt_walk_ante) {
        bool prop_failure_rtt_walk_cons = failure_rtt_walk_post;
        __COVER(prop_failure_rtt_walk_cons);
        __ASSERT(prop_failure_rtt_walk_cons, "prop_failure_rtt_walk_cons");
    }

    bool prop_failure_rtte_state_ante = !failure_rd_align_pre
        && !failure_rd_bound_pre
        && !failure_rd_state_pre
        && !failure_level_bound_pre
        && !failure_ipa_align_pre
        && !failure_ipa_bound_pre
        && !failure_rtt_walk_pre
        && failure_rtte_state_pre;
    __COVER(prop_failure_rtte_state_ante);
    if (prop_failure_rtte_state_ante) {
        bool prop_failure_rtte_state_cons = failure_rtte_state_post;
        __COVER(prop_failure_rtte_state_cons);
        __ASSERT(prop_failure_rtte_state_cons, "prop_failure_rtte_state_cons");
    }

    bool prop_failure_rtt_homo_ante = !failure_rd_align_pre
        && !failure_rd_bound_pre
        && !failure_rd_state_pre
        && !failure_level_bound_pre
        && !failure_ipa_align_pre
        && !failure_ipa_bound_pre
        && !failure_rtt_walk_pre
        && !failure_rtte_state_pre
        && failure_rtt_homo_pre;
    __COVER(prop_failure_rtt_homo_ante);
    if (prop_failure_rtt_homo_ante) {
        bool prop_failure_rtt_homo_cons = failure_rtt_homo_post;
        __COVER(prop_failure_rtt_homo_cons);
        __ASSERT(prop_failure_rtt_homo_cons, "prop_failure_rtt_homo_cons");
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
    bool prop_success_rtte_state_ante = no_failures_pre;
    __COVER(prop_success_rtte_state_ante);
    if (prop_success_rtte_state_ante) {
        bool prop_success_rtte_state_cons = success_rtte_state_post;
        __COVER(prop_success_rtte_state_cons);
        __ASSERT(prop_success_rtte_state_cons, "prop_success_rtte_state_cons");
    }

    bool prop_success_rtte_addr_ante = no_failures_pre
        && success_rtte_addr_pre;
    __COVER(prop_success_rtte_addr_ante);
    if (prop_success_rtte_addr_ante) {
        bool prop_success_rtte_addr_cons = success_rtte_addr_post;
        __COVER(prop_success_rtte_addr_cons);
        __ASSERT(prop_success_rtte_addr_cons, "prop_success_rtte_addr_cons");
    }

    bool prop_success_rtte_attr_ante = no_failures_pre
        && success_rtte_attr_pre;
    __COVER(prop_success_rtte_attr_ante);
    if (prop_success_rtte_attr_ante) {
        bool prop_success_rtte_attr_cons = success_rtte_attr_post;
        __COVER(prop_success_rtte_attr_cons);
        __ASSERT(prop_success_rtte_attr_cons, "prop_success_rtte_attr_cons");
    }

    bool prop_success_rtte_ripas_ante = no_failures_pre
        && success_rtte_ripas_pre;
    __COVER(prop_success_rtte_ripas_ante);
    if (prop_success_rtte_ripas_ante) {
        bool prop_success_rtte_ripas_cons = success_rtte_ripas_post;
        __COVER(prop_success_rtte_ripas_cons);
        __ASSERT(prop_success_rtte_ripas_cons, "prop_success_rtte_ripas_cons");
    }

    bool prop_success_rtt_state_ante = no_failures_pre;
    __COVER(prop_success_rtt_state_ante);
    if (prop_success_rtt_state_ante) {
        bool prop_success_rtt_state_cons = success_rtt_state_post;
        __COVER(prop_success_rtt_state_cons);
        __ASSERT(prop_success_rtt_state_cons, "prop_success_rtt_state_cons");
    }

    bool prop_success_rtt_ante = no_failures_pre;
    __COVER(prop_success_rtt_ante);
    if (prop_success_rtt_ante) {
        bool prop_success_rtt_cons = success_rtt_post;
        __COVER(prop_success_rtt_cons);
        __ASSERT(prop_success_rtt_cons, "prop_success_rtt_cons");
    }

    // Assertion used to check consistency of the testbench
    __tb_expect_fail();

    return no_failures_pre;
}

