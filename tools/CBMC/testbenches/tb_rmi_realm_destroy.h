/*
 * (C) COPYRIGHT 2021 Arm Limited or its affiliates
 * ALL RIGHTS RESERVED
 *
 * This file was AUTOGENERATED from the RMM specification.
 * RMM specification source version: 9f097087-dirty
 */

#ifndef __TB_RMI_REALM_DESTROY_H
#define __TB_RMI_REALM_DESTROY_H

/*
 * Testbench for RMI_REALM_DESTROY command. Check via CBMC with flag `--entry-
 * point tb_rmi_realm_destroy`.
 *
 * Arguments:
 *     rd: PA of the RD.
 *
 * Returns:
 *     bool: Output value.
 */
bool tb_rmi_realm_destroy(
    uint64_t rd);

#endif // __TB_RMI_REALM_DESTROY_H
