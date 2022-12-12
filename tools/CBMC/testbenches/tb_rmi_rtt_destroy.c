/*
 * (C) COPYRIGHT 2021 Arm Limited or its affiliates
 * ALL RIGHTS RESERVED
 *
 * This file was AUTOGENERATED from the RMM specification.
 * RMM specification source version: e9d4d747
 */

#include "tb.h"
#include "tb_rmi_rtt_destroy.h"

bool tb_rmi_rtt_destroy(
    uint64_t rd,
    uint64_t ipa,
    int64_t level)
{
    // Initialize registers
    struct tb_regs __tb_regs = __tb_arb_regs();
    __tb_regs.X0 = SMC_RMM_RTT_DESTROY;
    __tb_regs.X1 = (uint64_t)rd;
    __tb_regs.X2 = (uint64_t)ipa;
    __tb_regs.X3 = (uint64_t)level;

    // Initialize global state
    __init_global_state(__tb_regs.X0);

    // Declare context variables
    struct rmm_rtt_walk_result walk;
    uint64_t entry_idx;
    uint64_t walk_top;

    // Assign context variables before command execution
    walk = RttWalk(
        rd, ipa,
        level - 1);
    entry_idx = RttEntryIndex(
        ipa, walk.level);
    walk_top = RttSkipNonLiveEntries(
        walk.rtt,
        walk.level,
        ipa);

    // Pre-conditions
    bool failure_rd_align_pre = !AddrIsGranuleAligned(rd);
    bool failure_rd_bound_pre = !PaIsDelegable(rd);
    bool failure_rd_state_pre = Granule(rd).state != RD;
    bool failure_level_bound_pre = (!RttLevelIsValid(rd, level) || RttLevelIsStarting(rd, level));
    bool failure_ipa_align_pre = !AddrIsRttLevelAligned(ipa, level - 1);
    bool failure_ipa_bound_pre = UInt(ipa) >= (pow(2, Realm(rd).ipa_width));
    bool failure_rtt_walk_pre = walk.level < level - 1;
    bool failure_rtte_state_pre = walk.entry.state != TABLE;
    bool failure_rtt_live_pre = RttIsLive(Rtt(walk.entry.addr));
    bool no_failures_pre = !failure_rd_align_pre
        && !failure_rd_bound_pre
        && !failure_rd_state_pre
        && !failure_level_bound_pre
        && !failure_ipa_align_pre
        && !failure_ipa_bound_pre
        && !failure_rtt_walk_pre
        && !failure_rtte_state_pre
        && !failure_rtt_live_pre;

    // Execute command
    uint64_t result = tb_handle_smc(&__tb_regs);

    // Assign context variables after command execution
    walk = RttWalk(
        rd, ipa,
        level - 1);
    entry_idx = RttEntryIndex(
        ipa, walk.level);
    walk_top = RttSkipNonLiveEntries(
        walk.rtt,
        walk.level,
        ipa);

    // Post-conditions
    bool failure_rd_align_post = ResultEqual_2(result, RMI_ERROR_INPUT);
    bool failure_rd_bound_post = ResultEqual_2(result, RMI_ERROR_INPUT);
    bool failure_rd_state_post = ResultEqual_2(result, RMI_ERROR_INPUT);
    bool failure_level_bound_post = ResultEqual_2(result, RMI_ERROR_INPUT);
    bool failure_ipa_align_post = ResultEqual_2(result, RMI_ERROR_INPUT);
    bool failure_ipa_bound_post = ResultEqual_2(result, RMI_ERROR_INPUT);
    bool failure_rtt_walk_post = (ResultEqual_3(result, RMI_ERROR_RTT, walk.level) && (top == walk_top));
    bool failure_rtte_state_post = (ResultEqual_3(result, RMI_ERROR_RTT, walk.level) && (top == walk_top));
    bool failure_rtt_live_post = (ResultEqual_3(result, RMI_ERROR_RTT, level) && (top == ipa));
    bool success_rtte_state_post = walk.entry.state == DESTROYED;
    bool success_rtt_state_post = Granule(walk.entry.addr).state == DELEGATED;
    bool success_rtt_post = rtt == walk.entry.addr;
    bool success_top_post = top == walk_top;

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

    bool prop_failure_rtt_live_ante = !failure_rd_align_pre
        && !failure_rd_bound_pre
        && !failure_rd_state_pre
        && !failure_level_bound_pre
        && !failure_ipa_align_pre
        && !failure_ipa_bound_pre
        && !failure_rtt_walk_pre
        && !failure_rtte_state_pre
        && failure_rtt_live_pre;
    __COVER(prop_failure_rtt_live_ante);
    if (prop_failure_rtt_live_ante) {
        bool prop_failure_rtt_live_cons = failure_rtt_live_post;
        __COVER(prop_failure_rtt_live_cons);
        __ASSERT(prop_failure_rtt_live_cons, "prop_failure_rtt_live_cons");
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

    bool prop_success_top_ante = no_failures_pre;
    __COVER(prop_success_top_ante);
    if (prop_success_top_ante) {
        bool prop_success_top_cons = success_top_post;
        __COVER(prop_success_top_cons);
        __ASSERT(prop_success_top_cons, "prop_success_top_cons");
    }

    // Assertion used to check consistency of the testbench
    __tb_expect_fail();

    return no_failures_pre;
}

void entry_point(
    void)
{
    tb_rmi_rtt_destroy(nondet_uint64_t(), nondet_uint64_t(), nondet_int64_t());
}

