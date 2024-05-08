/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */
#include <assert.h>
#include <rec.h>
#include <rsi-handler.h>
#include <smc-rsi.h>

COMPILER_ASSERT(RSI_ABI_VERSION_MAJOR <= UL(0x7FFF));
COMPILER_ASSERT(RSI_ABI_VERSION_MINOR <= UL(0xFFFF));

void handle_rsi_version(struct rec *rec, struct rsi_result *res)
{
	struct rec_plane *plane = rec_active_plane(rec);

	/* RSI calls can only be issued by the primary plane */
	assert(plane == rec_primary_plane(rec));

	res->action = UPDATE_REC_RETURN_TO_REALM;

	if (plane->regs[1] != RSI_ABI_VERSION) {
		res->smc_res.x[0] = RSI_ERROR_INPUT;
	} else {
		res->smc_res.x[0] = RSI_SUCCESS;
	}

	res->smc_res.x[1] = RSI_ABI_VERSION;
	res->smc_res.x[2] = RSI_ABI_VERSION;
}
