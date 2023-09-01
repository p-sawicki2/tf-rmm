/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <granule.h>
#include <realm.h>
#include <rsi-handler.h>
#include <smc-rsi.h>

void handle_rsi_realm_config(struct rec *rec, struct rsi_result *res)
{
	unsigned long ipa = rec->regs[1];
	enum s2_walk_status walk_status;
	struct s2_walk_result walk_res;
	struct granule *gr;
	struct rsi_realm_config *config;

	res->action = UPDATE_REC_RETURN_TO_REALM;

	if (!GRANULE_ALIGNED(ipa) || !addr_in_rec_par(rec, ipa)) {
		res->smc_res.x[0] = RSI_ERROR_INPUT;
		return;
	}

	walk_status = realm_ipa_to_pa(rec, ipa, &walk_res);

	if (walk_status == WALK_FAIL) {
		if (walk_res.ripas_val == RIPAS_EMPTY) {
			res->smc_res.x[0] = RSI_ERROR_INPUT;
		} else {
			res->action = STAGE_2_TRANSLATION_FAULT;
			res->rtt_level = walk_res.rtt_level;
		}
		return;
	}

	if (walk_status == WALK_INVALID_PARAMS) {
		res->smc_res.x[0] = RSI_ERROR_INPUT;
		return;
	}

	/* Map Realm data granule to RMM address space */
	gr = find_granule(walk_res.pa);
	config = (struct rsi_realm_config *)granule_map(gr, SLOT_RSI_CALL);
	assert(config != NULL);

	/* Populate config structure */
	config->ipa_width = rec->realm_info.ipa_bits;
	if (rec->realm_info.algorithm == HASH_SHA_256) {
		config->algorithm = RSI_HASH_SHA_256;
	} else {
		config->algorithm = RSI_HASH_SHA_512;
	}

	/* Unmap Realm data granule */
	buffer_unmap(config);

	/* Unlock last level RTT */
	granule_unlock(walk_res.llt);

	/* Write output values */
	res->smc_res.x[0] = RSI_SUCCESS;
}
