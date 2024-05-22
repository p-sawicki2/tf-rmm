/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <smc-rsi.h>
#include <stddef.h>
#include <utils_def.h>

ASSERT_TYPE_SIZE_EQUAL(struct rsi_realm_config, 0x1000UL);
ASSERT_FIELD_OFFSET(struct rsi_realm_config, ipa_width, 0U);
ASSERT_FIELD_OFFSET(struct rsi_realm_config, algorithm, 8U);

ASSERT_TYPE_SIZE_EQUAL(struct rsi_host_call, 0x100UL);
ASSERT_FIELD_OFFSET(struct rsi_host_call, imm, 0U);
ASSERT_FIELD_OFFSET(struct rsi_host_call, gprs[0U], 8U);
ASSERT_FIELD_OFFSET(struct rsi_host_call,
			 gprs[RSI_HOST_CALL_NR_GPRS - 1U],
			 U(8U * RSI_HOST_CALL_NR_GPRS));
