/*
 * (C) COPYRIGHT 2021 Arm Limited or its affiliates
 * ALL RIGHTS RESERVED
 *
 * This file was AUTOGENERATED from the RMM specification.
 * RMM specification source version: 9f097087-dirty
 */

#ifndef __TB_RSI_MEASUREMENT_EXTEND_H
#define __TB_RSI_MEASUREMENT_EXTEND_H

/*
 * Testbench for RSI_MEASUREMENT_EXTEND command. Check via CBMC with flag
 * `--entry-point tb_rsi_measurement_extend`.
 *
 * Arguments:
 *     index: Measurement index.
 *     size: Measurement size in bytes.
 *     value_0: Doubleword 0 of the measurement value.
 *     value_1: Doubleword 1 of the measurement value.
 *     value_2: Doubleword 2 of the measurement value.
 *     value_3: Doubleword 3 of the measurement value.
 *     value_4: Doubleword 4 of the measurement value.
 *     value_5: Doubleword 5 of the measurement value.
 *     value_6: Doubleword 6 of the measurement value.
 *     value_7: Doubleword 7 of the measurement value.
 *
 * Returns:
 *     bool: Output value.
 */
bool tb_rsi_measurement_extend(
    uint64_t index,
    uint64_t size,
    uint64_t value_0,
    uint64_t value_1,
    uint64_t value_2,
    uint64_t value_3,
    uint64_t value_4,
    uint64_t value_5,
    uint64_t value_6,
    uint64_t value_7);

#endif // __TB_RSI_MEASUREMENT_EXTEND_H
