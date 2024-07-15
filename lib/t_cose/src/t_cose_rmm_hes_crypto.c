/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright Laurence Lundblade.
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

/*
 * This file is derived from:
 *    ext/t_cose/crypto_adapters/t_cose_psa_crypto.c
 *
 * \brief Crypto Adaptation for t_cose to use HES for realm attestation
 *
 * This connects up the abstract interface in t_cose_crypto.h to the
 * implementations of signing and hashing in the HES. Currently, only
 * the signing functions are overridden to offload to HES, but hashing
 * continues to use the mbedTLS implementation. Other functionality for
 * verifying signatures and generating keys is not implemented here and
 * can be added as needed.
 * For signing, we only use restartable signing since it allows returning
 * to the caller without completing signing, which is required for
 * offloading signing operations HES asyncronously.
 */
#include <assert.h>
#include <memory.h>
#include <t_cose_crypto.h> /* The interface this implements */
#include <t_cose_psa_crypto.h>
#include <t_cose_rmm_hes_crypto.h>
#include <t_cose_util.h>

static t_cose_crypto_hes_enqueue_t t_cose_crypto_hes_enqueue;
static bool lib_initialized;

/**
 * \brief Map a COSE signing algorithm ID to a PSA signing algorithm ID
 *
 * \param[in] cose_alg_id  The COSE algorithm ID.
 *
 * \return The PSA algorithm ID or 0 if this doesn't map the COSE ID.
 */
static psa_algorithm_t cose_alg_id_to_psa_alg_id(int32_t cose_alg_id)
{
	/* The #ifdefs save a little code when algorithms are disabled */
	switch (cose_alg_id) {
	case T_COSE_ALGORITHM_ES256:
		return PSA_ALG_ECDSA(PSA_ALG_SHA_256);
#ifndef T_COSE_DISABLE_ES384
	case T_COSE_ALGORITHM_ES384:
		return PSA_ALG_ECDSA(PSA_ALG_SHA_384);
#endif
#ifndef T_COSE_DISABLE_ES512
	case T_COSE_ALGORITHM_ES512:
		return PSA_ALG_ECDSA(PSA_ALG_SHA_512);
#endif
#ifndef T_COSE_DISABLE_PS256
	case T_COSE_ALGORITHM_PS256:
		return PSA_ALG_RSA_PSS(PSA_ALG_SHA_256);
#endif
#ifndef T_COSE_DISABLE_PS384
	case T_COSE_ALGORITHM_PS384:
		return PSA_ALG_RSA_PSS(PSA_ALG_SHA_384);
#endif
#ifndef T_COSE_DISABLE_PS512
	case T_COSE_ALGORITHM_PS512:
		return PSA_ALG_RSA_PSS(PSA_ALG_SHA_512);
#endif
	default:
		return 0;
	}

	/*
	 * psa/crypto_values.h doesn't seem to define a "no alg" value,
	 * but zero seems OK for that use in the signing context.
	 */
}

/**
 * \brief Map a PSA error into a t_cose error for signing.
 *
 * \param[in] err   The PSA status.
 *
 * \return The \ref t_cose_err_t.
 */
static enum t_cose_err_t psa_status_to_t_cose_error_signing(psa_status_t err)
{
	/* See documentation for t_cose_int16_map(). Its use gives smaller
	 * object code than a switch statement here.
	 */
	static const int16_t error_map[][2] = {
		{ PSA_SUCCESS, T_COSE_SUCCESS },
		{ PSA_ERROR_INVALID_SIGNATURE, T_COSE_ERR_SIG_VERIFY },
		{ PSA_ERROR_NOT_SUPPORTED, T_COSE_ERR_UNSUPPORTED_SIGNING_ALG },
		{ PSA_ERROR_INSUFFICIENT_MEMORY,
		  T_COSE_ERR_INSUFFICIENT_MEMORY },
		{ PSA_ERROR_CORRUPTION_DETECTED,
		  T_COSE_ERR_TAMPERING_DETECTED },
		{ PSA_OPERATION_INCOMPLETE, T_COSE_ERR_SIG_IN_PROGRESS },
		{ INT16_MIN, T_COSE_ERR_SIG_FAIL },
	};

	return (enum t_cose_err_t)t_cose_int16_map(error_map, (int16_t)err);
}

static void
t_cose_crypto_init_hes_ctx_crypto(struct t_cose_rmm_hes_ctx *hes_ctx_locked,
				  int32_t cose_algorithm_id,
				  struct q_useful_buf_c hash_to_sign,
				  struct q_useful_buf signature_buffer)
{
	/* Assumes lock is held for context */
	hes_ctx_locked->state.alg_id = cose_alg_id_to_psa_alg_id(cose_algorithm_id);
	hes_ctx_locked->state.sig_len = signature_buffer.len;
	hes_ctx_locked->state.sig_buffer = signature_buffer.ptr;
	hes_ctx_locked->state.hash_len = hash_to_sign.len;
	hes_ctx_locked->state.c_buffer_for_tbs_hash = hash_to_sign.ptr;
}

void t_cose_crypto_hes_init(t_cose_crypto_hes_enqueue_t enqueue)
{
	t_cose_crypto_hes_enqueue = enqueue;
	lib_initialized = true;
}

void t_cose_crypto_hes_ctx_init(struct t_cose_rmm_hes_ctx *hes_ctx,
				uintptr_t granule_addr)
{
	assert(lib_initialized);

	spinlock_acquire(&hes_ctx->lock);
	(void)memset(&hes_ctx->state, 0, sizeof(hes_ctx->state));
	hes_ctx->state.is_req_queued = false;
	hes_ctx->state.is_sig_valid = false;
	hes_ctx->state.is_hes_err = false;
	hes_ctx->state.rec_granule = granule_addr;
	spinlock_release(&hes_ctx->lock);
}

/*
 * See documentation in t_cose_crypto.h
 */
enum t_cose_err_t t_cose_crypto_sign_restart(
	bool started, int32_t cose_algorithm_id, struct t_cose_key signing_key,
	void *crypto_context, struct q_useful_buf_c hash_to_sign,
	struct q_useful_buf signature_buffer, struct q_useful_buf_c *signature)
{
	enum t_cose_err_t return_value;
	struct t_cose_rmm_hes_ctx *hes_crypto_context;
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

	hes_crypto_context = (struct t_cose_rmm_hes_ctx *)crypto_context;

	spinlock_acquire(&hes_crypto_context->lock);
	if (!started) {
		t_cose_crypto_init_hes_ctx_crypto(hes_crypto_context,
						  cose_algorithm_id,
						  hash_to_sign,
						  signature_buffer);
	}

	if (!hes_crypto_context->state.is_req_queued) {
		if (t_cose_crypto_hes_enqueue(hes_crypto_context,
			&hes_crypto_context->state.req_ticket)) {
			hes_crypto_context->state.is_req_queued = true;
		}
	}

	if (hes_crypto_context->state.is_hes_err) {
		return_value = T_COSE_ERR_FAIL;
		goto release;
	}

	return_value = T_COSE_ERR_SIG_IN_PROGRESS;

	if (hes_crypto_context->state.is_sig_valid) {
		assert(hes_crypto_context->state.is_req_queued == true);
		assert(hes_crypto_context->state.sig_len <= signature_buffer.len);
		signature->ptr = signature_buffer.ptr;
		signature->len = hes_crypto_context->state.sig_len;
		return_value = T_COSE_SUCCESS;
	}

release:
	spinlock_release(&hes_crypto_context->lock);
done:
	return return_value;
}

/*
 * See documentation in t_cose_crypto.h
 */
enum t_cose_err_t t_cose_crypto_sig_size(int32_t cose_algorithm_id,
					 struct t_cose_key signing_key,
					 size_t *sig_size)
{
	enum t_cose_err_t return_value;
	psa_algorithm_t psa_alg_id;
	mbedtls_svc_key_id_t signing_key_psa;
	psa_key_attributes_t key_attributes;
	psa_key_type_t key_type;
	size_t key_len_bits;
	psa_status_t status;

	assert(lib_initialized);

	psa_alg_id = cose_alg_id_to_psa_alg_id(cose_algorithm_id);
	if (!PSA_ALG_IS_ECDSA(psa_alg_id) && !PSA_ALG_IS_RSA_PSS(psa_alg_id)) {
		return_value = T_COSE_ERR_UNSUPPORTED_SIGNING_ALG;
		goto Done;
	}

	signing_key_psa = (psa_key_handle_t)signing_key.key.handle;
	key_attributes = psa_key_attributes_init();
	status = psa_get_key_attributes(signing_key_psa, &key_attributes);
	return_value = psa_status_to_t_cose_error_signing(status);
	if (return_value != T_COSE_SUCCESS) {
		goto Done;
	}

	key_type = psa_get_key_type(&key_attributes);
	key_len_bits = psa_get_key_bits(&key_attributes);
	/* cppcheck-suppress misra-c2012-10.4 */
	*sig_size = (size_t)PSA_SIGN_OUTPUT_SIZE((unsigned long)key_type,
						 (unsigned long)key_len_bits,
						 psa_alg_id);

	return_value = T_COSE_SUCCESS;

Done:
	return return_value;
}

/**
 * \brief Convert COSE hash algorithm ID to a PSA hash algorithm ID
 *
 * \param[in] cose_hash_alg_id   The COSE-based ID for the
 *
 * \return PSA-based hash algorithm ID, or USHRT_MAX on error.
 *
 */
static psa_algorithm_t cose_hash_alg_id_to_psa(int32_t cose_hash_alg_id)
{
	return (cose_hash_alg_id == T_COSE_ALGORITHM_SHA_256) ? PSA_ALG_SHA_256 :
#if !defined(T_COSE_DISABLE_ES384) || !defined(T_COSE_DISABLE_PS384)
	       (cose_hash_alg_id == T_COSE_ALGORITHM_SHA_384) ? PSA_ALG_SHA_384 :
#endif
#if !defined(T_COSE_DISABLE_ES512) || !defined(T_COSE_DISABLE_PS512)
	       (cose_hash_alg_id == T_COSE_ALGORITHM_SHA_512) ? PSA_ALG_SHA_512 :
#endif
							      UINT16_MAX;
}

/**
 * \brief Map a PSA error into a t_cose error for hashes.
 *
 * \param[in] status   The PSA status.
 *
 * \return The \ref t_cose_err_t.
 */
static enum t_cose_err_t psa_status_to_t_cose_error_hash(psa_status_t status)
{
	static const int16_t error_map[][2] = {
		{ PSA_SUCCESS, T_COSE_SUCCESS },
		{ PSA_ERROR_NOT_SUPPORTED, T_COSE_ERR_UNSUPPORTED_HASH },
		{ PSA_ERROR_INVALID_ARGUMENT, T_COSE_ERR_UNSUPPORTED_HASH },
		{ PSA_ERROR_BUFFER_TOO_SMALL, T_COSE_ERR_HASH_BUFFER_SIZE },
		{ INT16_MIN, T_COSE_ERR_HASH_GENERAL_FAIL },
	};

	return (enum t_cose_err_t)t_cose_int16_map(error_map, (int16_t)status);
}

/*
 * See documentation in t_cose_crypto.h
 */
enum t_cose_err_t t_cose_crypto_hash_start(struct t_cose_crypto_hash *hash_ctx,
					   int32_t cose_hash_alg_id)
{
	psa_algorithm_t psa_alg;

	/* Map the algorithm ID */
	psa_alg = cose_hash_alg_id_to_psa(cose_hash_alg_id);

	/* initialize PSA hash context */
	hash_ctx->ctx = psa_hash_operation_init();

	/* Actually do the hash set up */
	hash_ctx->status = psa_hash_setup(&(hash_ctx->ctx), psa_alg);

	/* Map errors and return */
	return psa_status_to_t_cose_error_hash(hash_ctx->status);
}

/*
 * See documentation in t_cose_crypto.h
 */
void t_cose_crypto_hash_update(struct t_cose_crypto_hash *hash_ctx,
			       struct q_useful_buf_c data_to_hash)
{
	if (hash_ctx->status != PSA_SUCCESS) {
		/* In error state. Nothing to do. */
		return;
	}

	if (data_to_hash.ptr == NULL) {
		/* This allows for NULL buffers to be passed in all the way at
		 * the top of signer or message creator when all that is
		 * happening is the size of the result is being computed.
		 */
		return;
	}

	/* Actually hash the data */
	hash_ctx->status = psa_hash_update(&(hash_ctx->ctx), data_to_hash.ptr,
					   data_to_hash.len);
}

/*
 * See documentation in t_cose_crypto.h
 */
enum t_cose_err_t
t_cose_crypto_hash_finish(struct t_cose_crypto_hash *hash_ctx,
			  struct q_useful_buf buffer_to_hold_result,
			  struct q_useful_buf_c *hash_result)
{
	if (hash_ctx->status != PSA_SUCCESS) {
		/* Error state. Nothing to do */
		goto Done;
	}

	/* Actually finish up the hash */
	hash_ctx->status =
		psa_hash_finish(&(hash_ctx->ctx), buffer_to_hold_result.ptr,
				buffer_to_hold_result.len, &(hash_result->len));

	hash_result->ptr = buffer_to_hold_result.ptr;

Done:
	return psa_status_to_t_cose_error_hash(hash_ctx->status);
}

/*
 * See documentation in t_cose_crypto.h
 */
enum t_cose_err_t t_cose_crypto_sign(int32_t cose_algorithm_id,
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

/*
 * See documentation in t_cose_crypto.h
 */
enum t_cose_err_t t_cose_crypto_verify(int32_t cose_algorithm_id,
				       struct t_cose_key verification_key,
				       void *crypto_context,
				       struct q_useful_buf_c hash_to_verify,
				       struct q_useful_buf_c signature)
{
	(void)verification_key;
	(void)crypto_context;
	(void)hash_to_verify;
	(void)signature;
	(void)cose_algorithm_id;

	return T_COSE_ERR_UNSUPPORTED;
}

enum t_cose_err_t
t_cose_crypto_hmac_compute_setup(struct t_cose_crypto_hmac *hmac_ctx,
				 struct t_cose_key signing_key,
				 const int32_t cose_alg_id)
{
	(void)hmac_ctx;
	(void)signing_key;
	(void)cose_alg_id;
	return T_COSE_ERR_UNSUPPORTED_SIGNING_ALG;
}

enum t_cose_err_t t_cose_crypto_hmac_update(struct t_cose_crypto_hmac *hmac_ctx,
					    struct q_useful_buf_c payload)
{
	(void)hmac_ctx;
	(void)payload;
	return T_COSE_ERR_UNSUPPORTED_SIGNING_ALG;
}

enum t_cose_err_t
t_cose_crypto_hmac_compute_finish(struct t_cose_crypto_hmac *hmac_ctx,
				  struct q_useful_buf tag_buf,
				  struct q_useful_buf_c *tag)
{
	(void)hmac_ctx;
	(void)tag_buf;
	(void)tag;
	return T_COSE_ERR_UNSUPPORTED_SIGNING_ALG;
}

enum t_cose_err_t
t_cose_crypto_hmac_validate_setup(struct t_cose_crypto_hmac *hmac_ctx,
				  const int32_t cose_alg_id,
				  struct t_cose_key validation_key)
{
	(void)hmac_ctx;
	(void)cose_alg_id;
	(void)validation_key;
	return T_COSE_ERR_UNSUPPORTED_SIGNING_ALG;
}

enum t_cose_err_t
t_cose_crypto_hmac_validate_finish(struct t_cose_crypto_hmac *hmac_ctx,
				   struct q_useful_buf_c tag)
{
	(void)hmac_ctx;
	(void)tag;
	return T_COSE_ERR_UNSUPPORTED_SIGNING_ALG;
}

/*
 * See documentation in t_cose_crypto.h
 */
enum t_cose_err_t t_cose_crypto_sign_eddsa(struct t_cose_key signing_key,
					   void *crypto_context,
					   struct q_useful_buf_c tbs,
					   struct q_useful_buf signature_buffer,
					   struct q_useful_buf_c *signature)
{
	(void)signing_key;
	(void)crypto_context;
	(void)tbs;
	(void)signature_buffer;
	(void)signature;
	return T_COSE_ERR_UNSUPPORTED_SIGNING_ALG;
}

/*
 * See documentation in t_cose_crypto.h
 */
enum t_cose_err_t t_cose_crypto_verify_eddsa(struct t_cose_key verification_key,
					     void *crypto_context,
					     struct q_useful_buf_c tbs,
					     struct q_useful_buf_c signature)
{
	(void)verification_key;
	(void)crypto_context;
	(void)tbs;
	(void)signature;
	return T_COSE_ERR_UNSUPPORTED_SIGNING_ALG;
}

/*
 * See documentation in t_cose_crypto.h
 */
enum t_cose_err_t t_cose_crypto_generate_ec_key(const int32_t cose_ec_curve_id,
						struct t_cose_key *key)
{
	(void)key;
	(void)cose_ec_curve_id;
	return T_COSE_ERR_KEY_GENERATION_FAILED;
}

/*
 * See documentation in t_cose_crypto.h
 */
enum t_cose_err_t t_cose_crypto_get_random(struct q_useful_buf buffer,
					   size_t number,
					   struct q_useful_buf_c *random)
{
	(void)buffer;
	(void)number;
	(void)random;

	return T_COSE_ERR_UNSUPPORTED;
}

/*
 * See documentation in t_cose_crypto.h
 */
enum t_cose_err_t
t_cose_crypto_make_symmetric_key_handle(int32_t cose_algorithm_id,
					struct q_useful_buf_c symmetric_key,
					struct t_cose_key *key_handle)
{
	(void)cose_algorithm_id;
	(void)symmetric_key;
	(void)key_handle;

	return T_COSE_ERR_UNSUPPORTED;
}

/*
 * See documentation in t_cose_crypto.h
 */
void t_cose_crypto_free_symmetric_key(struct t_cose_key key)
{
	(void)key;
}

/*
 * See documentation in t_cose_crypto.h
 */
enum t_cose_err_t t_cose_crypto_aead_encrypt(
	const int32_t cose_algorithm_id, struct t_cose_key key,
	struct q_useful_buf_c nonce, struct q_useful_buf_c aad,
	struct q_useful_buf_c plaintext, struct q_useful_buf ciphertext_buffer,
	struct q_useful_buf_c *ciphertext)
{
	(void)nonce;
	(void)aad;
	(void)cose_algorithm_id;
	(void)key;
	(void)ciphertext_buffer;
	(void)ciphertext;
	(void)plaintext;

	return T_COSE_ERR_UNSUPPORTED;
}

/*
 * See documentation in t_cose_crypto.h
 */
enum t_cose_err_t t_cose_crypto_aead_decrypt(
	const int32_t cose_algorithm_id, struct t_cose_key key,
	struct q_useful_buf_c nonce, struct q_useful_buf_c aad,
	struct q_useful_buf_c ciphertext, struct q_useful_buf plaintext_buffer,
	struct q_useful_buf_c *plaintext)
{
	(void)nonce;
	(void)aad;
	(void)cose_algorithm_id;
	(void)key;
	(void)plaintext_buffer;
	(void)plaintext;
	(void)ciphertext;

	return T_COSE_ERR_UNSUPPORTED;
}

enum t_cose_err_t
t_cose_crypto_kw_wrap(int32_t cose_algorithm_id, struct t_cose_key kek,
		      struct q_useful_buf_c plaintext,
		      struct q_useful_buf ciphertext_buffer,
		      struct q_useful_buf_c *ciphertext_result)
{
	(void)cose_algorithm_id;
	(void)kek;
	(void)plaintext;
	(void)ciphertext_buffer;
	(void)ciphertext_result;

	return T_COSE_ERR_UNSUPPORTED;
}

enum t_cose_err_t
t_cose_crypto_kw_unwrap(int32_t cose_algorithm_id, struct t_cose_key kek,
			struct q_useful_buf_c ciphertext,
			struct q_useful_buf plaintext_buffer,
			struct q_useful_buf_c *plaintext_result)
{
	(void)cose_algorithm_id;
	(void)kek;
	(void)ciphertext;
	(void)plaintext_buffer;
	(void)plaintext_result;

	return T_COSE_ERR_UNSUPPORTED;
}

enum t_cose_err_t t_cose_crypto_hkdf(const int32_t cose_hash_algorithm_id,
				     const struct q_useful_buf_c salt,
				     const struct q_useful_buf_c ikm,
				     const struct q_useful_buf_c info,
				     const struct q_useful_buf okm_buffer)
{
	(void)cose_hash_algorithm_id;
	(void)salt;
	(void)ikm;
	(void)info;
	(void)okm_buffer;

	return T_COSE_ERR_UNSUPPORTED;
}

/*
 * See documentation in t_cose_crypto.h
 */
enum t_cose_err_t t_cose_crypto_import_ec2_pubkey(int32_t cose_ec_curve_id,
						  struct q_useful_buf_c x_coord,
						  struct q_useful_buf_c y_coord,
						  bool y_bool,
						  struct t_cose_key *pub_key)
{
	(void)cose_ec_curve_id;
	(void)x_coord;
	(void)y_coord;
	(void)y_bool;
	(void)pub_key;

	return T_COSE_ERR_UNSUPPORTED;
}

enum t_cose_err_t t_cose_crypto_export_ec2_key(struct t_cose_key pub_key,
					       int32_t *curve,
					       struct q_useful_buf x_coord_buf,
					       struct q_useful_buf_c *x_coord,
					       struct q_useful_buf y_coord_buf,
					       struct q_useful_buf_c *y_coord,
					       bool *y_bool)
{
	(void)curve;
	(void)x_coord;
	(void)x_coord_buf;
	(void)y_coord_buf;
	(void)y_coord;
	(void)y_bool;
	(void)pub_key;

	return T_COSE_ERR_UNSUPPORTED;
}

enum t_cose_err_t t_cose_crypto_ecdh(struct t_cose_key private_key,
				     struct t_cose_key public_key,
				     struct q_useful_buf shared_key_buf,
				     struct q_useful_buf_c *shared_key)
{
	(void)private_key;
	(void)public_key;
	(void)shared_key_buf;
	(void)shared_key;

	return T_COSE_ERR_UNSUPPORTED;
}
