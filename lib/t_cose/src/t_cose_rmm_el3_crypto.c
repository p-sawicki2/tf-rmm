/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

/*
 * This file contains alternative implementations of the signing related
 * functions defined in the t_cose crypto adaption layer.
 * Instead of calling the PSA crypto interface, these implementations use the
 * HES to perform the signing operation.
 *
 * These functions are called from the patched
 * ext/t_cose/crypto_adapters/t_cose_psa_crypto.c file.
 *
 * For signing, we only use restartable signing since it allows returning
 * to the caller without completing signing, which is required for
 * offloading signing operations HES asynchronously.
 */
#include <assert.h>
#include <memory.h>
#include <t_cose_crypto.h> /* The interface this implements */
#include <t_cose_rmm_el3_crypto.h>
#include <t_cose_util.h>

static t_cose_crypto_el3_enqueue_t t_cose_crypto_el3_enqueue;
static bool lib_initialized;

static void
t_cose_crypto_init_el3_ctx_crypto(struct t_cose_rmm_el3_ctx *el3_ctx_locked,
				  int32_t cose_algorithm_id,
				  struct q_useful_buf_c hash_to_sign,
				  struct q_useful_buf signature_buffer)
{
	/* Assumes lock is held for context */
	el3_ctx_locked->state.alg_id = cose_alg_id_to_psa_alg_id(cose_algorithm_id);
	el3_ctx_locked->state.sig_len = signature_buffer.len;
	el3_ctx_locked->state.sig_buffer = signature_buffer.ptr;
	el3_ctx_locked->state.hash_len = hash_to_sign.len;
	el3_ctx_locked->state.c_buffer_for_tbs_hash = hash_to_sign.ptr;
}

void t_cose_crypto_el3_enqueue_cb_init(t_cose_crypto_el3_enqueue_t enqueue)
{
	t_cose_crypto_el3_enqueue = enqueue;
	lib_initialized = true;
}

void t_cose_crypto_el3_ctx_init(struct t_cose_rmm_el3_ctx *el3_ctx,
				uintptr_t granule_addr)
{
	assert(lib_initialized);

	spinlock_acquire(&el3_ctx->lock);
	(void)memset(&el3_ctx->state, 0, sizeof(el3_ctx->state));
	el3_ctx->state.is_req_queued = false;
	el3_ctx->state.is_sig_valid = false;
	el3_ctx->state.is_el3_err = false;
	el3_ctx->state.rec_granule = granule_addr;
	spinlock_release(&el3_ctx->lock);
}

/*
 * See documentation in t_cose_crypto.h
 */
enum t_cose_err_t t_cose_crypto_sign_restart_el3(
	bool started, int32_t cose_algorithm_id, struct t_cose_key signing_key,
	void *crypto_context, struct q_useful_buf_c hash_to_sign,
	struct q_useful_buf signature_buffer, struct q_useful_buf_c *signature)
{
	enum t_cose_err_t return_value;
	struct t_cose_rmm_el3_ctx *el3_crypto_context;
	psa_algorithm_t psa_alg_id;

	(void)signing_key;

	assert(lib_initialized);

	psa_alg_id = cose_alg_id_to_psa_alg_id(cose_algorithm_id);
	if (!PSA_ALG_IS_ECDSA(psa_alg_id) && !PSA_ALG_IS_RSA_PSS(psa_alg_id)) {
		return_value = T_COSE_ERR_UNSUPPORTED_SIGNING_ALG;
		goto done;
	}

	if (!crypto_context) {
		return_value = T_COSE_ERR_FAIL;
		goto done;
	}

	el3_crypto_context = (struct t_cose_rmm_el3_ctx *)crypto_context;

	/*
	 * Since the response corresponding to this REC can be updated by
	 * another REC we need to protect the below from concurrent access.
	 */
	spinlock_acquire(&el3_crypto_context->lock);
	if (!started) {
		t_cose_crypto_init_el3_ctx_crypto(el3_crypto_context,
						  cose_algorithm_id,
						  hash_to_sign,
						  signature_buffer);
	}

	if (!el3_crypto_context->state.is_req_queued) {
		if (t_cose_crypto_el3_enqueue(el3_crypto_context,
			&el3_crypto_context->state.req_ticket)) {
			el3_crypto_context->state.is_req_queued = true;
		}
	}

	/*
	 * Responses for this request are pulled outside the current function
	 */
	if (el3_crypto_context->state.is_el3_err) {
		return_value = T_COSE_ERR_FAIL;
		goto release;
	}

	return_value = T_COSE_ERR_SIG_IN_PROGRESS;

	if (el3_crypto_context->state.is_sig_valid) {
		assert(el3_crypto_context->state.is_req_queued == true);
		assert(el3_crypto_context->state.sig_len <= signature_buffer.len);
		signature->ptr = signature_buffer.ptr;
		signature->len = el3_crypto_context->state.sig_len;
		return_value = T_COSE_SUCCESS;
	}

release:
	spinlock_release(&el3_crypto_context->lock);
done:
	return return_value;
}

enum t_cose_err_t t_cose_crypto_sign_el3(int32_t cose_algorithm_id,
					 struct t_cose_key signing_key,
					 void *crypto_context,
					 struct q_useful_buf_c hash_to_sign,
					 struct q_useful_buf signature_buffer,
					 struct q_useful_buf_c *signature)
{
	(void)cose_algorithm_id;
	(void)signing_key;
	(void)crypto_context;
	(void)hash_to_sign;
	(void)signature_buffer;
	(void)signature;

	return T_COSE_ERR_UNSUPPORTED_SIGNING_ALG;
}
