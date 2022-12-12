/*
 * (C) COPYRIGHT 2021 Arm Limited or its affiliates
 * ALL RIGHTS RESERVED
 *
 * This file was AUTOGENERATED from the RMM specification.
 * RMM specification source version: e9d4d747
 */

#ifndef __TB_RSI_IPA_STATE_GET_H
#define __TB_RSI_IPA_STATE_GET_H

/*
 * Testbench for RSI_IPA_STATE_GET command.
 *
 * Arguments:
 *     addr: IPA of target page.
 *
 * Returns:
 *     bool: Output value.
 */
bool tb_rsi_ipa_state_get(
    uint64_t addr);

#endif // __TB_RSI_IPA_STATE_GET_H
