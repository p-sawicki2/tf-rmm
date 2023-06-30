/*
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <realm.h>
#include <ripas.h>
#include <rsi-handler.h>
#include <smc-rsi.h>
#include <status.h>

void handle_rsi_ipa_state_set(struct rec *rec,
			      struct rmi_rec_exit *rec_exit,
			      struct rsi_result *res)
{
	unsigned long start = rec->regs[1];
	unsigned long size = rec->regs[2];
	unsigned long end = start + size;
	enum ripas ripas = (enum ripas)rec->regs[3];

	if ((ripas > RIPAS_RAM)	    ||
	    !GRANULE_ALIGNED(start) || !GRANULE_ALIGNED(size) ||
	    (end <= start)	    || /* Size is zero, or range overflows */
	    !region_in_rec_par(rec, start, end)) {
		res->action = UPDATE_REC_RETURN_TO_REALM;
		res->smc_res.x[0] = RSI_ERROR_INPUT;
		return;
	}

	rec->set_ripas.base = start;
	rec->set_ripas.top = end;
	rec->set_ripas.addr = start;
	rec->set_ripas.ripas = ripas;

	rec_exit->exit_reason = RMI_EXIT_RIPAS_CHANGE;
	rec_exit->ripas_base = start;
	rec_exit->ripas_size = size;
	rec_exit->ripas_value = (unsigned int)ripas;

	res->action = UPDATE_REC_EXIT_TO_HOST;
}

void handle_rsi_ipa_state_get(struct rec *rec,
			      struct rsi_result *res)
{
	unsigned long ipa = rec->regs[1];
	unsigned long rtt_level;
	enum s2_walk_status ws;
	enum ripas ripas;

	res->action = UPDATE_REC_RETURN_TO_REALM;

	if (!GRANULE_ALIGNED(ipa) || !addr_in_rec_par(rec, ipa)) {
		res->smc_res.x[0] = RSI_ERROR_INPUT;
		return;
	}

	ws = realm_ipa_get_ripas(rec, ipa, &ripas, &rtt_level);
	if (ws == WALK_SUCCESS) {
		res->smc_res.x[0] = RSI_SUCCESS;
		res->smc_res.x[1] = ripas;
	} else {
		/* Exit to Host */
		res->action = STAGE_2_TRANSLATION_FAULT;
		res->rtt_level = rtt_level;
		res->smc_res.x[0] = RSI_ERROR_INPUT;
	}
}
