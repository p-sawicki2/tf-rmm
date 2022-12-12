/*
 * (C) COPYRIGHT 2021 Arm Limited or its affiliates
 * ALL RIGHTS RESERVED
 *
 * This file was AUTOGENERATED from the RMM specification.
 * RMM specification source version: 404016e5-dirty
 */

#ifndef __TB_RSI_HOST_CALL_H
#define __TB_RSI_HOST_CALL_H

/*
 * Testbench for RSI_HOST_CALL command. Check via CBMC with flag `--entry-point
 * tb_rsi_host_call`.
 *
 * Arguments:
 *     addr: IPA of the Host call data structure.
 *
 * Returns:
 *     bool: Output value.
 */
bool tb_rsi_host_call(
    uint64_t addr);

#endif // __TB_RSI_HOST_CALL_H
