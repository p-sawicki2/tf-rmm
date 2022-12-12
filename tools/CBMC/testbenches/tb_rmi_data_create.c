/*
 * (C) COPYRIGHT 2021 Arm Limited or its affiliates
 * ALL RIGHTS RESERVED
 *
 * This file was AUTOGENERATED from the RMM specification.
 * RMM specification source version: 9f097087-dirty
 */

#include "tb.h"
#include "tb_rmi_data_create.h"

bool tb_rmi_data_create(
    uint64_t rd,
    uint64_t data,
    uint64_t ipa,
    uint64_t src,
    rmi_data_flags_t flags)
{
    // Initialize registers
    struct tb_regs __tb_regs = __tb_arb_regs();
    __tb_regs.X0 = SMC_RMM_DATA_CREATE;
    __tb_regs.X1 = (uint64_t)rd;
    __tb_regs.X2 = (uint64_t)data;
    __tb_regs.X3 = (uint64_t)ipa;
    __tb_regs.X4 = (uint64_t)src;
    __tb_regs.X5 = (uint64_t)flags;

    // Initialize global state
    __init_global_state(__tb_regs.X0);

    // Declare context variables
    struct rmm_realm realm;
    struct rmm_rtt_walk_result walk;
    uint64_t entry_idx;

    // Assign context variables before command execution
    realm = Realm(rd);
    walk = RttWalk(
        rd, ipa,
        RMM_RTT_PAGE_LEVEL);
    entry_idx = RttEntryIndex(
        ipa, walk.level);

    // Pre-conditions
    bool failure_src_align_pre = !AddrIsGranuleAligned(src);
    bool failure_src_bound_pre = !PaIsDelegable(src);
    bool failure_src_pas_pre = Granule(src).pas != NS;
    bool failure_data_align_pre = !AddrIsGranuleAligned(data);
    bool failure_data_bound_pre = !PaIsDelegable(data);
    bool failure_data_state_pre = Granule(data).state != DELEGATED;
    bool failure_rd_align_pre = !AddrIsGranuleAligned(rd);
    bool failure_rd_bound_pre = !PaIsDelegable(rd);
    bool failure_rd_state_pre = Granule(rd).state != RD;
    bool failure_ipa_align_pre = !AddrIsGranuleAligned(ipa);
    bool failure_ipa_bound_pre = !AddrIsProtected(ipa, realm);
    bool failure_realm_state_pre = realm.state != NEW;
    bool failure_rtt_walk_pre = walk.level < RMM_RTT_PAGE_LEVEL;
    bool failure_rtte_state_pre = walk.entry.state != UNASSIGNED;
    bool failure_rtte_ripas_pre = walk.entry.ripas != RAM;
    bool no_failures_pre = !failure_src_align_pre
        && !failure_src_bound_pre
        && !failure_src_pas_pre
        && !failure_data_align_pre
        && !failure_data_bound_pre
        && !failure_data_state_pre
        && !failure_rd_align_pre
        && !failure_rd_bound_pre
        && !failure_rd_state_pre
        && !failure_ipa_align_pre
        && !failure_ipa_bound_pre
        && !failure_realm_state_pre
        && !failure_rtt_walk_pre
        && !failure_rtte_state_pre
        && !failure_rtte_ripas_pre;

    // Execute command and read the result.
    tb_handle_smc(&__tb_regs);
    uint64_t result =  __tb_regs.X0;

    // Assign context variables after command execution
    walk = RttWalk(
        rd, ipa,
        RMM_RTT_PAGE_LEVEL);
    entry_idx = RttEntryIndex(
        ipa, walk.level);

    // Post-conditions
    bool failure_src_align_post = ResultEqual_2(result, RMI_ERROR_INPUT);
    bool failure_src_bound_post = ResultEqual_2(result, RMI_ERROR_INPUT);
    bool failure_src_pas_post = ResultEqual_2(result, RMI_ERROR_INPUT);
    bool failure_data_align_post = ResultEqual_2(result, RMI_ERROR_INPUT);
    bool failure_data_bound_post = ResultEqual_2(result, RMI_ERROR_INPUT);
    bool failure_data_state_post = ResultEqual_2(result, RMI_ERROR_INPUT);
    bool failure_rd_align_post = ResultEqual_2(result, RMI_ERROR_INPUT);
    bool failure_rd_bound_post = ResultEqual_2(result, RMI_ERROR_INPUT);
    bool failure_rd_state_post = ResultEqual_2(result, RMI_ERROR_INPUT);
    bool failure_ipa_align_post = ResultEqual_2(result, RMI_ERROR_INPUT);
    bool failure_ipa_bound_post = ResultEqual_2(result, RMI_ERROR_INPUT);
    bool failure_realm_state_post = ResultEqual_2(result, RMI_ERROR_REALM);
    bool failure_rtt_walk_post = ResultEqual_3(result, RMI_ERROR_RTT, walk.level);
    bool failure_rtte_state_post = ResultEqual_3(result, RMI_ERROR_RTT, walk.level);
    bool failure_rtte_ripas_post = ResultEqual_3(result, RMI_ERROR_RTT, walk.level);
    bool success_data_state_post = Granule(data).state == DATA;
    bool success_rtte_state_post = walk.entry.state == ASSIGNED;
    bool success_rtte_addr_post = walk.entry.addr == data;
    bool success_rim_post = Realm(rd).measurements[0] == RimExtendData(realm, ipa, data, flags);

    // Failure condition assertions
    bool prop_failure_src_align_ante = failure_src_align_pre;
    __COVER(prop_failure_src_align_ante);
    if (prop_failure_src_align_ante) {
        bool prop_failure_src_align_cons = failure_src_align_post;
        __COVER(prop_failure_src_align_cons);
        __ASSERT(prop_failure_src_align_cons, "prop_failure_src_align_cons");
    }

    bool prop_failure_src_bound_ante = !failure_src_align_pre
        && failure_src_bound_pre;
    __COVER(prop_failure_src_bound_ante);
    if (prop_failure_src_bound_ante) {
        bool prop_failure_src_bound_cons = failure_src_bound_post;
        __COVER(prop_failure_src_bound_cons);
        __ASSERT(prop_failure_src_bound_cons, "prop_failure_src_bound_cons");
    }

    bool prop_failure_src_pas_ante = !failure_src_align_pre
        && !failure_src_bound_pre
        && failure_src_pas_pre;
    __COVER(prop_failure_src_pas_ante);
    if (prop_failure_src_pas_ante) {
        bool prop_failure_src_pas_cons = failure_src_pas_post;
        __COVER(prop_failure_src_pas_cons);
        __ASSERT(prop_failure_src_pas_cons, "prop_failure_src_pas_cons");
    }

    bool prop_failure_data_align_ante = !failure_src_align_pre
        && !failure_src_bound_pre
        && !failure_src_pas_pre
        && failure_data_align_pre;
    __COVER(prop_failure_data_align_ante);
    if (prop_failure_data_align_ante) {
        bool prop_failure_data_align_cons = failure_data_align_post;
        __COVER(prop_failure_data_align_cons);
        __ASSERT(prop_failure_data_align_cons, "prop_failure_data_align_cons");
    }

    bool prop_failure_data_bound_ante = !failure_src_align_pre
        && !failure_src_bound_pre
        && !failure_src_pas_pre
        && !failure_data_align_pre
        && failure_data_bound_pre;
    __COVER(prop_failure_data_bound_ante);
    if (prop_failure_data_bound_ante) {
        bool prop_failure_data_bound_cons = failure_data_bound_post;
        __COVER(prop_failure_data_bound_cons);
        __ASSERT(prop_failure_data_bound_cons, "prop_failure_data_bound_cons");
    }

    bool prop_failure_data_state_ante = !failure_src_align_pre
        && !failure_src_bound_pre
        && !failure_src_pas_pre
        && !failure_data_align_pre
        && !failure_data_bound_pre
        && failure_data_state_pre;
    __COVER(prop_failure_data_state_ante);
    if (prop_failure_data_state_ante) {
        bool prop_failure_data_state_cons = failure_data_state_post;
        __COVER(prop_failure_data_state_cons);
        __ASSERT(prop_failure_data_state_cons, "prop_failure_data_state_cons");
    }

    bool prop_failure_rd_align_ante = !failure_src_align_pre
        && !failure_src_bound_pre
        && !failure_src_pas_pre
        && !failure_data_align_pre
        && !failure_data_bound_pre
        && !failure_data_state_pre
        && failure_rd_align_pre;
    __COVER(prop_failure_rd_align_ante);
    if (prop_failure_rd_align_ante) {
        bool prop_failure_rd_align_cons = failure_rd_align_post;
        __COVER(prop_failure_rd_align_cons);
        __ASSERT(prop_failure_rd_align_cons, "prop_failure_rd_align_cons");
    }

    bool prop_failure_rd_bound_ante = !failure_src_align_pre
        && !failure_src_bound_pre
        && !failure_src_pas_pre
        && !failure_data_align_pre
        && !failure_data_bound_pre
        && !failure_data_state_pre
        && !failure_rd_align_pre
        && failure_rd_bound_pre;
    __COVER(prop_failure_rd_bound_ante);
    if (prop_failure_rd_bound_ante) {
        bool prop_failure_rd_bound_cons = failure_rd_bound_post;
        __COVER(prop_failure_rd_bound_cons);
        __ASSERT(prop_failure_rd_bound_cons, "prop_failure_rd_bound_cons");
    }

    bool prop_failure_rd_state_ante = !failure_src_align_pre
        && !failure_src_bound_pre
        && !failure_src_pas_pre
        && !failure_data_align_pre
        && !failure_data_bound_pre
        && !failure_data_state_pre
        && !failure_rd_align_pre
        && !failure_rd_bound_pre
        && failure_rd_state_pre;
    __COVER(prop_failure_rd_state_ante);
    if (prop_failure_rd_state_ante) {
        bool prop_failure_rd_state_cons = failure_rd_state_post;
        __COVER(prop_failure_rd_state_cons);
        __ASSERT(prop_failure_rd_state_cons, "prop_failure_rd_state_cons");
    }

    bool prop_failure_ipa_align_ante = !failure_src_align_pre
        && !failure_src_bound_pre
        && !failure_src_pas_pre
        && !failure_data_align_pre
        && !failure_data_bound_pre
        && !failure_data_state_pre
        && !failure_rd_align_pre
        && !failure_rd_bound_pre
        && !failure_rd_state_pre
        && failure_ipa_align_pre;
    __COVER(prop_failure_ipa_align_ante);
    if (prop_failure_ipa_align_ante) {
        bool prop_failure_ipa_align_cons = failure_ipa_align_post;
        __COVER(prop_failure_ipa_align_cons);
        __ASSERT(prop_failure_ipa_align_cons, "prop_failure_ipa_align_cons");
    }

    bool prop_failure_ipa_bound_ante = !failure_src_align_pre
        && !failure_src_bound_pre
        && !failure_src_pas_pre
        && !failure_data_align_pre
        && !failure_data_bound_pre
        && !failure_data_state_pre
        && !failure_rd_align_pre
        && !failure_rd_bound_pre
        && !failure_rd_state_pre
        && !failure_ipa_align_pre
        && failure_ipa_bound_pre;
    __COVER(prop_failure_ipa_bound_ante);
    if (prop_failure_ipa_bound_ante) {
        bool prop_failure_ipa_bound_cons = failure_ipa_bound_post;
        __COVER(prop_failure_ipa_bound_cons);
        __ASSERT(prop_failure_ipa_bound_cons, "prop_failure_ipa_bound_cons");
    }

    bool prop_failure_realm_state_ante = !failure_src_align_pre
        && !failure_src_bound_pre
        && !failure_src_pas_pre
        && !failure_data_align_pre
        && !failure_data_bound_pre
        && !failure_data_state_pre
        && !failure_rd_align_pre
        && !failure_rd_bound_pre
        && !failure_rd_state_pre
        && !failure_ipa_align_pre
        && !failure_ipa_bound_pre
        && failure_realm_state_pre;
    __COVER(prop_failure_realm_state_ante);
    if (prop_failure_realm_state_ante) {
        bool prop_failure_realm_state_cons = failure_realm_state_post;
        __COVER(prop_failure_realm_state_cons);
        __ASSERT(prop_failure_realm_state_cons, "prop_failure_realm_state_cons");
    }

    bool prop_failure_rtt_walk_ante = !failure_src_align_pre
        && !failure_src_bound_pre
        && !failure_src_pas_pre
        && !failure_data_align_pre
        && !failure_data_bound_pre
        && !failure_data_state_pre
        && !failure_rd_align_pre
        && !failure_rd_bound_pre
        && !failure_rd_state_pre
        && !failure_ipa_align_pre
        && !failure_ipa_bound_pre
        && !failure_realm_state_pre
        && failure_rtt_walk_pre;
    __COVER(prop_failure_rtt_walk_ante);
    if (prop_failure_rtt_walk_ante) {
        bool prop_failure_rtt_walk_cons = failure_rtt_walk_post;
        __COVER(prop_failure_rtt_walk_cons);
        __ASSERT(prop_failure_rtt_walk_cons, "prop_failure_rtt_walk_cons");
    }

    bool prop_failure_rtte_state_ante = !failure_src_align_pre
        && !failure_src_bound_pre
        && !failure_src_pas_pre
        && !failure_data_align_pre
        && !failure_data_bound_pre
        && !failure_data_state_pre
        && !failure_rd_align_pre
        && !failure_rd_bound_pre
        && !failure_rd_state_pre
        && !failure_ipa_align_pre
        && !failure_ipa_bound_pre
        && !failure_realm_state_pre
        && !failure_rtt_walk_pre
        && failure_rtte_state_pre;
    __COVER(prop_failure_rtte_state_ante);
    if (prop_failure_rtte_state_ante) {
        bool prop_failure_rtte_state_cons = failure_rtte_state_post;
        __COVER(prop_failure_rtte_state_cons);
        __ASSERT(prop_failure_rtte_state_cons, "prop_failure_rtte_state_cons");
    }

    bool prop_failure_rtte_ripas_ante = !failure_src_align_pre
        && !failure_src_bound_pre
        && !failure_src_pas_pre
        && !failure_data_align_pre
        && !failure_data_bound_pre
        && !failure_data_state_pre
        && !failure_rd_align_pre
        && !failure_rd_bound_pre
        && !failure_rd_state_pre
        && !failure_ipa_align_pre
        && !failure_ipa_bound_pre
        && !failure_realm_state_pre
        && !failure_rtt_walk_pre
        && !failure_rtte_state_pre
        && failure_rtte_ripas_pre;
    __COVER(prop_failure_rtte_ripas_ante);
    if (prop_failure_rtte_ripas_ante) {
        bool prop_failure_rtte_ripas_cons = failure_rtte_ripas_post;
        __COVER(prop_failure_rtte_ripas_cons);
        __ASSERT(prop_failure_rtte_ripas_cons, "prop_failure_rtte_ripas_cons");
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
    bool prop_success_data_state_ante = no_failures_pre;
    __COVER(prop_success_data_state_ante);
    if (prop_success_data_state_ante) {
        bool prop_success_data_state_cons = success_data_state_post;
        __COVER(prop_success_data_state_cons);
        __ASSERT(prop_success_data_state_cons, "prop_success_data_state_cons");
    }

    bool prop_success_rtte_state_ante = no_failures_pre;
    __COVER(prop_success_rtte_state_ante);
    if (prop_success_rtte_state_ante) {
        bool prop_success_rtte_state_cons = success_rtte_state_post;
        __COVER(prop_success_rtte_state_cons);
        __ASSERT(prop_success_rtte_state_cons, "prop_success_rtte_state_cons");
    }

    bool prop_success_rtte_addr_ante = no_failures_pre;
    __COVER(prop_success_rtte_addr_ante);
    if (prop_success_rtte_addr_ante) {
        bool prop_success_rtte_addr_cons = success_rtte_addr_post;
        __COVER(prop_success_rtte_addr_cons);
        __ASSERT(prop_success_rtte_addr_cons, "prop_success_rtte_addr_cons");
    }

    bool prop_success_rim_ante = no_failures_pre;
    __COVER(prop_success_rim_ante);
    if (prop_success_rim_ante) {
        bool prop_success_rim_cons = success_rim_post;
        __COVER(prop_success_rim_cons);
        __ASSERT(prop_success_rim_cons, "prop_success_rim_cons");
    }

    // Assertion used to check consistency of the testbench
    __tb_expect_fail();

    return no_failures_pre;
}

