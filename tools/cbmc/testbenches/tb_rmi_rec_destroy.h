/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 *
 * This file was AUTOGENERATED from the RMM specification.
 * RMM specification source version: 790fd539
 */

#ifndef __TB_RMI_REC_DESTROY_H
#define __TB_RMI_REC_DESTROY_H

#include "stdbool.h"
#include "stdint.h"

/*
 * Testbench for RMI_REC_DESTROY command. Check via CBMC with flag
 * `--entry-point tb_rmi_rec_destroy`.
 *
 * Arguments:
 *     rec: PA of the target REC.
 *
 * Returns:
 *     bool: Output value.
 */
bool tb_rmi_rec_destroy(
	uint64_t rec);

#endif /* __TB_RMI_REC_DESTROY_H */
