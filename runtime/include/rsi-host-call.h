/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef RSI_HOST_CALL_H
#define RSI_HOST_CALL_H

#include <rsi-walk.h>

struct rec;
struct rmi_rec_enter;

#ifndef CBMC
struct rsi_walk_result complete_rsi_host_call(struct rec *rec,
					      struct rmi_rec_enter *rec_enter);
#else /* CBMC */
static inline struct rsi_walk_result complete_rsi_host_call(struct rec *rec,
							    struct rmi_rec_enter *rec_enter)
{
	struct rsi_walk_result r = {0};

	ASSERT(false, "complete_rsi_host_call");
	return r;
}
#endif /* CBMC */

#endif /* RSI_HOST_CALL_H */
