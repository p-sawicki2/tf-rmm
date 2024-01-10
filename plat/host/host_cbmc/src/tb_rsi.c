/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <rec.h>
#include <rsi-handler.h>
#include <tb.h>
#include <tb_common.h>

void handle_rsi_version(struct rec *rec, struct rsi_result *res)
{
	ASSERT(false, "handle_rsi_version");
}
void handle_rsi_features(struct rec *rec, struct rsi_result *res)
{
	ASSERT(false, "handle_rsi_features");
}

void handle_rsi_attest_token_init(struct rec *rec, struct rsi_result *res)
{
	ASSERT(false, "handle_rsi_attest_token_init");
}

void handle_rsi_attest_token_continue(struct rec *rec,
				      struct rmi_rec_exit *rec_exit,
				      struct rsi_result *res)
{
	ASSERT(false, "handle_rsi_attest_token_continue");
}
void handle_rsi_measurement_read(struct rec *rec, struct rsi_result *res)
{
	ASSERT(false, "handle_rsi_measurement_read");
}
void handle_rsi_measurement_extend(struct rec *rec, struct rsi_result *res)
{
	ASSERT(false, "handle_rsi_measurement_extend");
}
void handle_rsi_realm_config(struct rec *rec, struct rsi_result *res)
{
	ASSERT(false, "handle_rsi_realm_config");
}
void handle_rsi_ipa_state_set(struct rec *rec,
			      struct rmi_rec_exit *rec_exit,
			      struct rsi_result *res)
{
	ASSERT(false, "handle_rsi_ipa_state_set");
}
void handle_rsi_ipa_state_get(struct rec *rec,
			      struct rsi_result *res)
{
	ASSERT(false, "handle_rsi_ipa_state_get");
}
void handle_rsi_host_call(struct rec *rec, struct rmi_rec_exit *rec_exit,
			  struct rsi_result *res)
{
	ASSERT(false, "handle_rsi_host_call");
}
