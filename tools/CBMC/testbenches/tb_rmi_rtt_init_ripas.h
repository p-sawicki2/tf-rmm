/*
 * (C) COPYRIGHT 2021 Arm Limited or its affiliates
 * ALL RIGHTS RESERVED
 *
 * This file was AUTOGENERATED from the RMM specification.
 * RMM specification source version: 9f097087-dirty
 */

#ifndef __TB_RMI_RTT_INIT_RIPAS_H
#define __TB_RMI_RTT_INIT_RIPAS_H

/*
 * Testbench for RMI_RTT_INIT_RIPAS command. Check via CBMC with flag `--entry-
 * point tb_rmi_rtt_init_ripas`.
 *
 * Arguments:
 *     rd: PA of the RD for the target Realm.
 *     base: Base of target IPA region.
 *     top: Top of target IPA region.
 *
 * Returns:
 *     bool: Output value.
 */
bool tb_rmi_rtt_init_ripas(
    uint64_t rd,
    uint64_t base,
    uint64_t top);

#endif // __TB_RMI_RTT_INIT_RIPAS_H
