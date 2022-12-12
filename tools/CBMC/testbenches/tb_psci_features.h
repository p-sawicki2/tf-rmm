/*
 * (C) COPYRIGHT 2021 Arm Limited or its affiliates
 * ALL RIGHTS RESERVED
 *
 * This file was AUTOGENERATED from the RMM specification.
 * RMM specification source version: 9f097087-dirty
 */

#ifndef __TB_PSCI_FEATURES_H
#define __TB_PSCI_FEATURES_H

/*
 * Testbench for PSCI_FEATURES command. Check via CBMC with flag `--entry-point
 * tb_psci_features`.
 *
 * Arguments:
 *     psci_func_id: Function ID for a PSCI Function.
 *
 * Returns:
 *     bool: Output value.
 */
bool tb_psci_features(
    uint32_t psci_func_id);

#endif // __TB_PSCI_FEATURES_H
