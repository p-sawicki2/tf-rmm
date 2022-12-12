/*
 * (C) COPYRIGHT 2021 Arm Limited or its affiliates
 * ALL RIGHTS RESERVED
 *
 * This file was AUTOGENERATED from the RMM specification.
 * RMM specification source version: 9f097087-dirty
 */

#ifndef __TB_PSCI_CPU_SUSPEND_H
#define __TB_PSCI_CPU_SUSPEND_H

/*
 * Testbench for PSCI_CPU_SUSPEND command. Check via CBMC with flag `--entry-
 * point tb_psci_cpu_suspend`.
 *
 * Arguments:
 *     power_state: Identifier for a specific local state.
 *     entry_point_address: Address at which the core must resume execution.
 *     context_id: This parameter is only meaningful to the caller (must be
 * present in X0 upon first entry to Non-Secure exception level).
 *
 * Returns:
 *     bool: Output value.
 */
bool tb_psci_cpu_suspend(
    uint32_t power_state,
    uint64_t entry_point_address,
    uint64_t context_id);

#endif // __TB_PSCI_CPU_SUSPEND_H
