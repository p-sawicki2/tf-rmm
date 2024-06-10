/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef T_COSE_RMM_HES_CRYPTO_H
#define T_COSE_RMM_HES_CRYPTO_H

#include <mbedtls/hkdf.h>
#include <mbedtls/md.h>
#include <psa/crypto.h>
#include <spinlock.h>
#include <stddef.h>
#include <stdint.h>
#include <t_cose_crypto.h>
#include <utils_def.h>

struct t_cose_rmm_hes_ctx {
	spinlock_t lock;
	struct {
		bool is_req_queued : 1;
		bool is_sig_valid : 1;
		bool is_hes_err : 1;
		psa_algorithm_t alg_id;
		size_t hash_len;
		uintptr_t rec_granule;
		uint64_t req_ticket;
		uint16_t sig_len;
		uint8_t sig_buffer[512];
		uint8_t c_buffer_for_tbs_hash[T_COSE_CRYPTO_MAX_HASH_SIZE];
	} state;
};

typedef bool (*t_cose_crypto_hes_enqueue_t)(struct t_cose_rmm_hes_ctx *hes_ctx,
						uint64_t *ticket);

void t_cose_crypto_hes_init(t_cose_crypto_hes_enqueue_t enqueue);
void t_cose_crypto_hes_ctx_init(struct t_cose_rmm_hes_ctx *hes_ctx,
				uintptr_t granule_addr);

#endif /* T_COSE_RMM_HES_CRYPTO_H */
