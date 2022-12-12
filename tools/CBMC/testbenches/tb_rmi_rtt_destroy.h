/*
 * (C) COPYRIGHT 2021 Arm Limited or its affiliates
 * ALL RIGHTS RESERVED
 *
 * This file was AUTOGENERATED from the RMM specification.
 * RMM specification source version: 404016e5-dirty
 */

#ifndef __TB_RMI_RTT_DESTROY_H
#define __TB_RMI_RTT_DESTROY_H

/*
 * Testbench for RMI_RTT_DESTROY command. Check via CBMC with flag `--entry-
 * point tb_rmi_rtt_destroy`.
 *
 * Arguments:
 *     rd: PA of the RD for the target Realm.
 *     ipa: Base of the IPA range described by the RTT.
 *     level: RTT level.
 *
 * Returns:
 *     bool: Output value.
 */
bool tb_rmi_rtt_destroy(
    uint64_t rd,
    uint64_t ipa,
    int64_t level);

#endif // __TB_RMI_RTT_DESTROY_H
