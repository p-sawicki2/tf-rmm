/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef	RSI_MEMORY_H
#define	RSI_MEMORY_H

#include <rsi-walk.h>
#include <smc.h>

struct rec;
struct rmi_rec_exit;

struct rsi_ripas_get_res {
	/* Result of RTT walk performed by RSI command */
	struct rsi_walk_result walk_result;

	/*
	 * If @walk_result.abort is false, @smc_res contains GPR values to be
	 * returned to the Realm.
	 */
	struct smc_result smc_res;
};

bool handle_rsi_ipa_state_set(struct rec *rec, struct rmi_rec_exit *rec_exit);

struct rsi_ripas_get_res handle_rsi_ipa_state_get(struct rec *rec);

#endif /* RSI_MEMORY_H */
