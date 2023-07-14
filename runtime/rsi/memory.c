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
	unsigned long base = rec->regs[1];
	unsigned long top = rec->regs[2];
	enum ripas ripas = (enum ripas)rec->regs[3];
	unsigned long flags = rec->regs[4];	

	if ((ripas > RIPAS_RAM)	   ||
	    !GRANULE_ALIGNED(base) || !GRANULE_ALIGNED(top) ||
	    (top <= base)	   || /* Size is zero, or range overflows */
	    !region_in_rec_par(rec, base, top)) {
		res->action = UPDATE_REC_RETURN_TO_REALM;
		res->smc_res.x[0] = RSI_ERROR_INPUT;
		return;
	}

	/* Check if RIPAS change from DESTROYED is permitted */
	if ((flags & RSI_CHANGE_DESTROYED) == 0UL) {
		if (realm_ipa_check_ripas_range(rec, base, top) != 0) {
			res->action = UPDATE_REC_RETURN_TO_REALM;
			res->smc_res.x[0] = RSI_ERROR_INPUT;
			return;
		}
	}

	rec->set_ripas.base = base;
	rec->set_ripas.top = top;
	rec->set_ripas.addr = base;
	rec->set_ripas.ripas = ripas;

	rec_exit->exit_reason = RMI_EXIT_RIPAS_CHANGE;
	rec_exit->ripas_base = base;
	rec_exit->ripas_top = top;
	rec_exit->ripas_value = (unsigned char)ripas;

	res->action = UPDATE_REC_EXIT_TO_HOST;
}

void handle_rsi_ipa_state_get(struct rec *rec,
			      struct rsi_result *res)
{
	unsigned long ipa = rec->regs[1];
	enum s2_walk_status ws;
	enum ripas ripas;

	res->action = UPDATE_REC_RETURN_TO_REALM;

	if (!GRANULE_ALIGNED(ipa) || !addr_in_rec_par(rec, ipa)) {
		res->smc_res.x[0] = RSI_ERROR_INPUT;
		return;
	}

	ws = realm_ipa_get_ripas(rec, ipa, &ripas);
	if (ws == WALK_SUCCESS) {
		res->smc_res.x[0] = RSI_SUCCESS;
		res->smc_res.x[1] = ripas;
	} else {
		res->smc_res.x[0] = RSI_ERROR_INPUT;
	}
}
