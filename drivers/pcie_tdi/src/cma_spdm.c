/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <cma_spdm.h>
#include <cma_spdm_private.h>
#include <debug.h>
#include <library/spdm_crypt_lib.h>
#include <psa/crypto.h>
#include <psa/crypto_struct.h>
#include <string.h>

/* Custom libspdm status code */
#define LIBSPDM_STATUS_IO_WAIT		((libspdm_return_t)0x80008000)

typedef void (*libspdm_cmd_main_t)(void);

static libspdm_return_t cma_spdm_send_message(void *spdm_context,
					      size_t request_size,
					      const void *request,
					      uint64_t timeout)
{
	struct cma_spdm_context *cma;
	int rc;

	cma = spdm_to_cma(spdm_context);

	assert(cma->comm_ops != NULL);
	rc = cma->comm_ops->send(cma->dev_handle, request, request_size,
				 cma->is_msg_sspdm, timeout);
	if (rc != 0U) {
		return LIBSPDM_STATUS_SEND_FAIL;
	}

	cma->libspdm_cmd_rc = LIBSPDM_STATUS_IO_WAIT;
	rc = swapcontext(&cma->libspdm_cmd_ctx, &cma->main_ctx);
	assert(rc == 0);

	return LIBSPDM_STATUS_SUCCESS;
}

static libspdm_return_t cma_spdm_receive_message(void *spdm_context,
						 size_t *response_size,
						 void **response,
						 uint64_t timeout)
{
	struct cma_spdm_context *cma;
	int rc;

	cma = spdm_to_cma(spdm_context);

	assert(cma->comm_ops != NULL);
	rc = cma->comm_ops->recv(cma->dev_handle, *response, response_size);
	if (rc != 0U) {
		return LIBSPDM_STATUS_RECEIVE_FAIL;
	}

	return LIBSPDM_STATUS_SUCCESS;
}

static libspdm_return_t
cma_spdm_transport_encode_message(void *spdm_context, const uint32_t *session_id,
				  bool is_app_message, bool is_request_message,
				  size_t message_size, void *message,
				  size_t *transport_message_size,
				  void **transport_message)
{
	struct cma_spdm_context *cma;

	cma = spdm_to_cma(spdm_context);

	cma->is_msg_sspdm = false;

	*transport_message_size = message_size;
	*transport_message = (void *)message;
	return LIBSPDM_STATUS_SUCCESS;
}

static psa_algorithm_t spdm_to_psa_hash_algo(uint32_t spdm_hash_algo)
{
	if (spdm_hash_algo == SPDM_ALGORITHMS_BASE_HASH_ALGO_TPM_ALG_SHA_256) {
		return PSA_ALG_SHA_256;
	} else if (spdm_hash_algo ==
		   SPDM_ALGORITHMS_BASE_HASH_ALGO_TPM_ALG_SHA_384) {
		return PSA_ALG_SHA_384;
	}

	return PSA_ALG_NONE;
}

/*
 * Incrementally compute hash as device response is processed.
 * todo: This needs to be moved to common lib
 */
#define HASH_OP_FLAG_SETUP	0x1
#define HASH_OP_FLAG_UPDATE	0x2
#define HASH_OP_FLAG_FINISH	0x4

static int rmm_psa_hash_compute(psa_algorithm_t algo, psa_hash_operation_t *op,
				uint8_t op_flags, const uint8_t *src,
				size_t src_length, uint8_t *hash,
				size_t hash_size, size_t *hash_length)
{
	psa_status_t psa_rc;
	int rc;

	if (op_flags & HASH_OP_FLAG_SETUP) {
		*op = psa_hash_operation_init();
		psa_rc = psa_hash_setup(op, algo);
		if (psa_rc != PSA_SUCCESS) {
			rc = -1;
			goto out_psa_err;
		}
		rc = 0;
	}

	if (op_flags & HASH_OP_FLAG_UPDATE) {
		psa_rc = psa_hash_update(op, src, src_length);
		if (psa_rc != PSA_SUCCESS) {
			rc = -1;
			goto out_psa_err;
		}
		rc = 0;
	}

	if (op_flags & HASH_OP_FLAG_FINISH) {
		psa_rc = psa_hash_finish(op, hash, hash_size, hash_length);
		if (psa_rc != PSA_SUCCESS) {
			rc = -1;
			goto out_psa_err;
		}
		rc = 0;
	}

out_psa_err:
	if (rc == -1 || (op_flags & HASH_OP_FLAG_FINISH)) {
		psa_hash_abort(op);
	}

	return rc;
}

/* Cache spdm certificate response */
static int cma_spdm_cache_certificate(struct cma_spdm_context *cma,
				      spdm_certificate_response_t *cert_rsp)
{
	size_t cache_offset, cache_len;
	libspdm_return_t status;
	uint8_t hash_op_flags = 0;
	int rc;

	/* Start of certificate chain */
	if (cma->spdm_cert_chain_len == 0) {
		libspdm_data_parameter_t param;
		size_t cert_chain_offset;
		uint32_t spdm_hash_algo;
		size_t data_sz;

		memset(&param, 0, sizeof(libspdm_data_parameter_t));
		param.location = LIBSPDM_DATA_LOCATION_CONNECTION;
		data_sz = sizeof(uint32_t);
		status = libspdm_get_data((void *)&cma->libspdm_context,
					  LIBSPDM_DATA_BASE_HASH_ALGO,
					  &param, &spdm_hash_algo,
					  &data_sz);
		if (status != LIBSPDM_STATUS_SUCCESS) {
			return -1;
		}

		/* Set SPDM cert_chain hash algo */
		cma->spdm_cert_chain_algo =
			spdm_to_psa_hash_algo(spdm_hash_algo);
		hash_op_flags |= HASH_OP_FLAG_SETUP;

		/*
		 * For the start of the certificate chain ignore the hash of
		 * root certificate included in the response buffer.
		 */
		cert_chain_offset = sizeof(spdm_cert_chain_t) +
			libspdm_get_hash_size(spdm_hash_algo);
		cache_offset = sizeof(spdm_certificate_response_t) +
			cert_chain_offset;
		cache_len = cert_rsp->portion_length - cert_chain_offset;
	} else {
		cache_offset = sizeof(spdm_certificate_response_t);
		cache_len = cert_rsp->portion_length;
	}

	hash_op_flags |= HASH_OP_FLAG_UPDATE;
	if (cert_rsp->remainder_length == 0) {
		hash_op_flags |= HASH_OP_FLAG_FINISH;
	}

	/*
	 * Compute the hash for the entire spdm_certificate_response. This hash
	 * will be later used to set it in SPDM connection
	 */
	rc = rmm_psa_hash_compute(cma->spdm_cert_chain_algo,
				  &cma->spdm_cert_chain_hash_op, hash_op_flags,
				  ((uint8_t *)cert_rsp +
				   sizeof(spdm_certificate_response_t)),
				  cert_rsp->portion_length,
				  cma->spdm_cert_chain_digest,
				  sizeof(cma->spdm_cert_chain_digest),
				  &cma->spdm_cert_chain_digest_length);
	if (rc != 0) {
		return -1;
	}

	/*
	 * As certificate is received (in parts or whole) invoke cache callback
	 * to let NS Host to cache device certificate.
	 */
	rc = cma->comm_ops->cache(cma->dev_handle, NULL, cache_offset,
				  cache_len);

	cma->spdm_cert_chain_len += cert_rsp->portion_length;

	return rc;
}

static libspdm_return_t
cma_spdm_transport_decode_message(void *spdm_context, uint32_t **session_id,
				  bool *is_app_message, bool is_request_message,
				  size_t transport_message_size,
				  void *transport_message,
				  size_t *message_size, void **message)
{
	struct cma_spdm_context *cma;
	spdm_message_header_t *spdm_hdr;
	int rc;

	cma = spdm_to_cma(spdm_context);

	/*
	 * As no transport headers are available, the type of the received
	 * message is SPDM or SECURED_SPDM based on last sent request type.
	 */
	if (cma->is_msg_sspdm) {
		/*
		 * Get session ID from encrpyted message and check against the
		 * session id in CMA SPDM context.
		 */

		/* Convert secured mssage to normal message */
	} else {
		*session_id = NULL;
	}

	*message_size = transport_message_size;
	*message = (void *)transport_message;

	/*
	 * Cache device objects like certificate, interface_report, measurements
	 * once the message is decrypted.
	 */
	spdm_hdr = (spdm_message_header_t *)*message;
	if (spdm_hdr->request_response_code == SPDM_CERTIFICATE) {
		spdm_certificate_response_t *cert_rsp;

		cert_rsp = (spdm_certificate_response_t *)spdm_hdr;
		rc = cma_spdm_cache_certificate(cma, cert_rsp);
		if (rc != 0) {
			return LIBSPDM_STATUS_RECEIVE_FAIL;
		}
	}

	return LIBSPDM_STATUS_SUCCESS;
}

static libspdm_return_t cma_spdm_acquire_sender_buffer(void *spdm_context,
						       void **msg_buf_ptr)
{
	struct cma_spdm_context *cma;

	cma = spdm_to_cma(spdm_context);
	*msg_buf_ptr = cma->send_recv_buffer;

	return LIBSPDM_STATUS_SUCCESS;
}

static void cma_spdm_release_sender_buffer(void *spdm_context,
					   const void *msg_buf_ptr)
{
	struct cma_spdm_context *cma __unused;

	cma = spdm_to_cma(spdm_context);
	assert(cma->send_recv_buffer == msg_buf_ptr);
}

static libspdm_return_t cma_spdm_acquire_receiver_buffer(void *spdm_context,
							 void **msg_buf_ptr)
{
	struct cma_spdm_context *cma;

	cma = spdm_to_cma(spdm_context);
	*msg_buf_ptr = cma->send_recv_buffer;

	return LIBSPDM_STATUS_SUCCESS;
}

static void cma_spdm_release_receiver_buffer(void *spdm_context,
					     const void *msg_buf_ptr)
{
	struct cma_spdm_context *cma __unused;

	cma = spdm_to_cma(spdm_context);
	assert(cma->send_recv_buffer == msg_buf_ptr);
}

static bool cma_spdm_verify_cert_chain(void *spdm_context, uint8_t slot_id,
				       size_t cert_chain_size,
				       const void *cert_chain,
				       const void **trust_anchor,
				       size_t *trust_anchor_size)
{
	assert(cert_chain == NULL);
	return true;
}

/*
 * todo:
 * Process the libspdm connection state. Check if the responder (DSM) supports
 * the required version, capabilities, algorithms as mentioned by PCIE CMA-SPDM
 */
static int process_cma_spdm_init_connection(struct cma_spdm_context *cma)
{
	return LIBSPDM_STATUS_SUCCESS;
}

/* cma_spdm_init_connection_main */
void cma_spdm_init_connection_main(struct cma_spdm_context *cma)
{
	size_t cert_chain_size;
	libspdm_data_parameter_t parameter;
	libspdm_return_t status;
	void *spdm_context;
	int rc;

	spdm_context = (void *)&cma->libspdm_context;

	/*
	 * Below are list of SPDM requester commands send to the device to
	 * init connection and get certificate. These commands will result in
	 * multiple async IO from libspdm layer followed by IO resume to libspdm
	 * layer.
	 */

	/*
	 * Initialize the connection. This does GET_VERSION, GET_CAPABILITIES
	 * NEGOTIATE_ALGORITHMS
	 */
	cma->libspdm_cmd_rc = libspdm_init_connection(spdm_context, false);
	if (cma->libspdm_cmd_rc != LIBSPDM_STATUS_SUCCESS) {
		return;
	}

	rc = process_cma_spdm_init_connection(cma);
	if (rc != 0) {
		cma->libspdm_cmd_rc = LIBSPDM_STATUS_UNSUPPORTED_CAP;
		return;
	}

	/*
	 * Get device certificate. The certificate is not kept in RMM instead
	 * during certificate retrival the NS host cache the certificate in
	 * parts. Due to this the buffer allocated to cache the certificate chain
	 * is not known to RMM. So set cert_chain_size to the max value limited
	 * by SPDM spec which is 64kb.
	 */
	cert_chain_size = SPDM_MAX_CERTIFICATE_CHAIN_SIZE;
	cma->libspdm_cmd_rc = libspdm_get_certificate(spdm_context,
						      NULL, /* session_id */
						      cma->cert_slot_id,
						      &cert_chain_size,
						      NULL /* cert_chain */);
	if (cma->libspdm_cmd_rc != LIBSPDM_STATUS_SUCCESS) {
		return;
	}

	/*
	 * Set libspdm data LIBSPDM_DATA_PEER_USED_CERT_CHAIN_HASH.
	 * During certificate retrival RMM calcuates spdm_cert_chain digest based
	 * on negotiated base hash algorithm. Update the details in libspdm
	 * context.
	 */
	memset(&parameter, 0, sizeof(parameter));
	parameter.location = LIBSPDM_DATA_LOCATION_CONNECTION;
	parameter.additional_data[0] = cma->cert_slot_id;
	status = libspdm_set_data(spdm_context,
				  LIBSPDM_DATA_PEER_USED_CERT_CHAIN_HASH,
				  &parameter, &cma->spdm_cert_chain_digest,
				  cma->spdm_cert_chain_digest_length);

	cma->libspdm_cmd_rc = status;
}

/* cma_spdm_deinit_connection_main */
void cma_spdm_deinit_connection_main(struct cma_spdm_context *cma)
{
	/* Terminate the connection. This closes the secure session */
	cma->libspdm_cmd_rc = libspdm_init_connection((void *)
						      &cma->libspdm_context,
						      true);

	/* todo: cleanup/reset CMA spdm context */
}

/* cma_spdm_start_session_main */
void cma_spdm_start_session_main(struct cma_spdm_context *cma)
{
	uint32_t session_id;
	libspdm_return_t status;

	/*
	 * 1.1-alp7 removed the need for CHAL code. Retain the call to
	 * libspdm_challenge as it helps to validate spdm_cert_chain_hash and
	 * public key before key_exchange call. Useful for debugging.
	 */
	status = libspdm_challenge((void *)&cma->libspdm_context, NULL, 0,
			SPDM_CHALLENGE_REQUEST_NO_MEASUREMENT_SUMMARY_HASH,
				NULL, NULL);
	cma->libspdm_cmd_rc = status;
	INFO("libspdm_challenge: 0x%x\n", status);
	if (cma->libspdm_cmd_rc != LIBSPDM_STATUS_SUCCESS) {
		return;
	}

	/*
	 * SPDM_REQUEST_NO_MEASUREMENT_SUMMARY_HASH
	 * SPDM_REQUEST_ALL_MEASUREMENTS_HASH
	 */
	status = libspdm_start_session((void *)&cma->libspdm_context,
				       false, /* use_psk */
				       NULL, /* psk_hint */
				       0, /* psk_hint size */
	       SPDM_REQUEST_NO_MEASUREMENT_SUMMARY_HASH, /* meas hash type */
				       cma->cert_slot_id, /* slot id */
				       0, /* session policy */
				       &session_id,
				       NULL, /* hbeat period */
				       NULL /* measurement_hash */);
	if (status == LIBSPDM_STATUS_SUCCESS) {
		cma->session_id = session_id;
		INFO("SPDM secure session id: 0x%x\n", cma->session_id);
	}

	cma->libspdm_cmd_rc = status;
}

/* cma_spdm_cmd_dispatch */
int cma_spdm_cmd_dispatch(int cmd, void *cma_spdm_context)
{
	struct cma_spdm_context *cma;
	libspdm_cmd_main_t cmd_main;
	int rc;

	cma = (struct cma_spdm_context *)cma_spdm_context;

	/* Return error if the previous command is in pending state */
	if (cma->libspdm_cmd_rc == LIBSPDM_STATUS_IO_WAIT) {
		return CMA_SPDM_STATUS_ERROR;
	}

	if (cmd == SPDM_INIT_CONNECTION) {
		cmd_main = (libspdm_cmd_main_t)cma_spdm_init_connection_main;
	} else if (cmd == SPDM_DEINIT_CONNECTION) {
		cmd_main = (libspdm_cmd_main_t)cma_spdm_deinit_connection_main;
	} else if (cmd == SPDM_SECURE_SESSION) {
		cmd_main = (libspdm_cmd_main_t)cma_spdm_start_session_main;
	} else {
		return CMA_SPDM_STATUS_ERROR;
	}

	rc = getcontext(&cma->libspdm_cmd_ctx);
	assert(rc == 0);

	makecontext_setup(&cma->libspdm_cmd_ctx, cma->libspdm_stack,
			  LIBSPMD_STACK_SIZE, &cma->main_ctx);

	makecontext(&cma->libspdm_cmd_ctx, cmd_main, 1, cma);
	rc = swapcontext(&cma->main_ctx, &cma->libspdm_cmd_ctx);
	assert(rc == 0);

	if (cma->libspdm_cmd_rc == LIBSPDM_STATUS_IO_WAIT) {
		rc = CMA_SPDM_STATUS_IO_WAIT;
	} else if (cma->libspdm_cmd_rc != LIBSPDM_STATUS_SUCCESS) {
		rc = CMA_SPDM_STATUS_ERROR;
	} else {
		rc = CMA_SPDM_STATUS_SUCCESS;
	}

	return rc;
}

/* cma_spdm_resume_cmd */
int cma_spdm_cmd_resume(void *cma_spdm_context)
{
	struct cma_spdm_context *cma;
	int rc;

	cma = (struct cma_spdm_context *)cma_spdm_context;

	if (cma->libspdm_cmd_rc != LIBSPDM_STATUS_IO_WAIT) {
		return CMA_SPDM_STATUS_ERROR;
	}

	rc = swapcontext(&cma->main_ctx, &cma->libspdm_cmd_ctx);
	assert(rc == 0);

	if (cma->libspdm_cmd_rc == LIBSPDM_STATUS_IO_WAIT) {
		rc = CMA_SPDM_STATUS_IO_WAIT;
	} else if (cma->libspdm_cmd_rc != LIBSPDM_STATUS_SUCCESS) {
		rc = CMA_SPDM_STATUS_ERROR;
	} else {
		rc = CMA_SPDM_STATUS_SUCCESS;
	}

	return rc;
}

/*
 * Set public key context in libspdm connection
 */
int cma_spdm_set_key(void *cma_spdm_context, uint8_t *key, size_t key_len,
		     uint8_t key_sig_algo)
{
	struct cma_spdm_context *cma;
	libspdm_data_parameter_t parameter;
	libspdm_return_t status;
	void *data_ptr;
	int rc;

	cma = (struct cma_spdm_context *)cma_spdm_context;

	if (key_sig_algo == CMA_SPDM_SIG_ECDSA_P256 ||
	    key_sig_algo == CMA_SPDM_SIG_ECDSA_P384) {
		mbedtls_ecdh_context *ecdh;
		mbedtls_ecp_keypair kp;
		mbedtls_ecp_group grp;
		mbedtls_ecp_point pt;

		ecdh = &cma->pk_ctx.ecdh;

		mbedtls_ecdh_init(ecdh);
		mbedtls_ecp_keypair_init(&kp);
		mbedtls_ecp_group_init(&grp);
		mbedtls_ecp_point_init(&pt);

		/* todo: call keypair/group/point_free upon error */
		if (key_sig_algo == CMA_SPDM_SIG_ECDSA_P256) {
			INFO("MBEDTLS_ECP_DP_SECP256R1\n");
			rc = mbedtls_ecp_group_load(&grp,
						    MBEDTLS_ECP_DP_SECP256R1);
		} else {
			INFO("MBEDTLS_ECP_DP_SECP384R1\n");
			rc = mbedtls_ecp_group_load(&grp,
						    MBEDTLS_ECP_DP_SECP384R1);
		}
		if (rc != 0) {
			return -1;
		}

		rc = mbedtls_ecp_point_read_binary(&grp, &pt, key, key_len);
		if (rc != 0) {
			return -1;
		}

		rc = mbedtls_ecp_set_public_key(grp.id, &kp, &pt);
		if (rc != 0) {
			return -1;
		}

		rc = mbedtls_ecdh_get_params(ecdh, &kp, MBEDTLS_ECDH_OURS);
		if (rc != 0) {
			return -1;
		}
	} else if (key_sig_algo == CMA_SPDM_SIG_RSASSA_3072) {
		/* Public exponent of RSA3072 key is 65537 */
		uint8_t rsa_e[] = { 0x01, 0x00, 0x01 };
		mbedtls_rsa_context *ctx;

		ctx = &cma->pk_ctx.rsa;

		mbedtls_rsa_init(ctx);
		rc = mbedtls_rsa_import_raw(ctx, key, key_len, NULL, 0, NULL, 0,
					    NULL, 0, rsa_e, sizeof(rsa_e));
		if (rc != 0) {
			return -1;
		}
	} else {
		return -1;
	}

	/* Set LIBSPDM_DATA_PEER_USED_CERT_CHAIN_PUBLIC_KEY in spdm connection */
	memset(&parameter, 0, sizeof(parameter));
	parameter.location = LIBSPDM_DATA_LOCATION_CONNECTION;
	parameter.additional_data[0] = cma->cert_slot_id;
	data_ptr = (void *)&cma->pk_ctx;
	status = libspdm_set_data((void *)&cma->libspdm_context,
				  LIBSPDM_DATA_PEER_USED_CERT_CHAIN_PUBLIC_KEY,
				  &parameter, &data_ptr, sizeof(data_ptr));
	if (status != LIBSPDM_STATUS_SUCCESS) {
		return -1;
	}

	return 0;
}

/*
 * Returns CMA SPDM context size. This include libspdm context, libspdm
 * secured message context, libspdm send/recv buffer, libspdm scratch space and
 * libspdm stack.
 */
size_t cma_spdm_get_context_size(void)
{
	size_t total;

	/*
	 * As libspdm public headers do not export the type of libsdpm_context.
	 * RMM reserves 8192 bytes and check at runtime if the size is enough.
	 */
	assert(libspdm_get_context_size() <= LIBSPMD_CONTEXT_SIZE);

	total = sizeof(struct cma_spdm_context) + LIBSPMD_CONTEXT_SIZE +
		SEND_RECV_BUF_SIZE + LIBSPMD_SCRATCH_BUF_SIZE +
		LIBSPMD_STACK_SIZE;
	total = round_up(total, 4096);

	return total;
}

/*
 * Assigns buffers to various objects as mentioned in the below mapping starting
 * from address 'cma_spdm_priv_data'.
 *
 *           --------------------------------
 *          |  | struct cma_spdm_context |   | sizeof(struct cma_spdm_context)
 *          |--|                         |---|
 *          |  |     libspdm_context     |   | 0x2000
 *          |--------------------------------|
 *          |      send_recv_buffer          | 0x1000
 *          |--------------------------------|
 *          |    libspdm scratch_buffer      | 0xC000
 *          |--------------------------------|
 *          |         libspdm stack          | 0x3000
 *           --------------------------------
 *
 * Inits libspdm context using libspdm helper routines and registers send/recv
 * buffer acquire/release routines. Registers device send/recv callback handlers.
 */
int cma_spdm_context_init(void *cma_spdm_priv_data,
			  size_t cma_spdm_priv_data_size, dev_handle_t handle,
			  uint8_t cert_slot_id,
			  const struct dev_comm_ops *comm_ops)
{
	spdm_version_number_t cma_spdm_version;
	spdm_version_number_t cma_sspdm_version;
	libspdm_data_parameter_t parameter;
	struct cma_spdm_context *cma;
	libspdm_return_t status __unused;
	void *spdm_ctx;
	uint32_t data32;
	uint16_t data16;
	uint8_t data8;
	size_t sb_size;

	if (cma_spdm_priv_data_size != cma_spdm_get_context_size()) {
		return -1;
	}

	if (cert_slot_id >= SPDM_MAX_SLOT_COUNT) {
		return -1;
	}

	/* Assign the start of priv data to cma_spdm_context */
	cma = (struct cma_spdm_context *)cma_spdm_priv_data;

	cma->send_recv_buffer = cma_spdm_priv_data +
		sizeof(struct cma_spdm_context) + LIBSPMD_CONTEXT_SIZE;
	cma->scratch_buffer = cma->send_recv_buffer + SEND_RECV_BUF_SIZE;
	cma->libspdm_stack = cma->scratch_buffer + LIBSPMD_SCRATCH_BUF_SIZE;

	/* Initialize cma_spdm_context */
	cma->dev_handle = handle;
	cma->cert_slot_id = cert_slot_id;
	cma->comm_ops = comm_ops;

	/*
	 * Initialize SPDM and Secure SPDM context. 'spdm_ctx' is a combination
	 * of both SPDM context and secured message context.
	 */
	spdm_ctx = (void *)&cma->libspdm_context;
	libspdm_init_context(spdm_ctx);

	/* Register device send/recv handlers */
	libspdm_register_device_io_func(spdm_ctx, cma_spdm_send_message,
					cma_spdm_receive_message);

	/*
	 * No transport encodings used as this is handled by NS host. So the
	 * transport_header_size and transport_tail_size are passed as 0.
	 */
	libspdm_register_transport_layer_func(spdm_ctx, CMA_SPDM_MSG_SIZE_MAX,
					      0U, /* transport_header_size */
					      0U, /* transport_tail_size */
					      cma_spdm_transport_encode_message,
					      cma_spdm_transport_decode_message);

	/* Register send/recv buffer acquire/release functions */
	libspdm_register_device_buffer_func(spdm_ctx,
					    CMA_SPDM_SENDER_BUFFER_SIZE,
					    CMA_SPDM_RECEIVER_BUFFER_SIZE,
					    cma_spdm_acquire_sender_buffer,
					    cma_spdm_release_sender_buffer,
					    cma_spdm_acquire_receiver_buffer,
					    cma_spdm_release_receiver_buffer);

	/* Set scratch buffer size */
	sb_size = libspdm_get_sizeof_required_scratch_buffer(spdm_ctx);

	INFO("libspdm_context_size: 0x%lx\n", libspdm_get_context_size());
	INFO("libspdm_scratch_buffer_size: 0x%lx\n", sb_size);
	INFO("struct cma_spdm_context size: 0x%lx\n",
	     sizeof(struct cma_spdm_context));
	INFO("cma_spdm_get_context_size: 0x%lx\n", cma_spdm_get_context_size());

	/* todo: Find options to reduce scratch buffer size */
	assert(sb_size <= LIBSPMD_SCRATCH_BUF_SIZE);
	libspdm_set_scratch_buffer(spdm_ctx, cma->scratch_buffer, sb_size);

	/* Check libspdm context */
	if (!libspdm_check_context(spdm_ctx)) {
		assert(0);
	}

	/* Set SPDM version */
	memset(&parameter, 0, sizeof(parameter));
	parameter.location = LIBSPDM_DATA_LOCATION_LOCAL;
	cma_spdm_version = CMA_SPDM_VERSION << SPDM_VERSION_NUMBER_SHIFT_BIT;
	status = libspdm_set_data(spdm_ctx, LIBSPDM_DATA_SPDM_VERSION,
				  &parameter, &cma_spdm_version,
				  sizeof(cma_spdm_version));
	assert(status == LIBSPDM_STATUS_SUCCESS);

	/*
	 * todo: Skip setting SPDM and Secured message version and post init
	 * connection check if these version matches the minimal version
	 * remommended by PCIe CMA-SPDM
	 */

	/* Set secured message version */
	memset(&parameter, 0, sizeof(parameter));
	parameter.location = LIBSPDM_DATA_LOCATION_LOCAL;
	cma_sspdm_version = CMA_SECURED_SPDM_VERSION <<
		SPDM_VERSION_NUMBER_SHIFT_BIT;
	status = libspdm_set_data(spdm_ctx, LIBSPDM_DATA_SECURED_MESSAGE_VERSION,
				  &parameter, &cma_sspdm_version,
				  sizeof(cma_sspdm_version));
	assert(status == LIBSPDM_STATUS_SUCCESS);

	/*
	 * Set GET_CAPABILITY fields
	 * Note: DataTransferSize and MaxSPDMmsgSize is automatically set by
	 * libspdm during init connection based on CMA_SPDM_SENDER_BUFFER_SIZE
	 * and CMA_SPDM_MSG_SIZE_MAX respectivelky.
	 */
	memset(&parameter, 0, sizeof(parameter));
	parameter.location = LIBSPDM_DATA_LOCATION_LOCAL;
	data8 = CMA_SPDM_GET_CAPABILITY_CT_EXPONENT;
	status = libspdm_set_data(spdm_ctx, LIBSPDM_DATA_CAPABILITY_CT_EXPONENT,
				  &parameter, &data8, sizeof(data8));
	assert(status == LIBSPDM_STATUS_SUCCESS);

	data32 = CMA_SPDM_GET_CAPABILITIES_REQUEST_FLAGS;
	status = libspdm_set_data(spdm_ctx, LIBSPDM_DATA_CAPABILITY_FLAGS,
				  &parameter, &data32, sizeof(data32));
	assert(status == LIBSPDM_STATUS_SUCCESS);

	/* Set NEGOTIATE_ALGORITHMS fields */
	data8 = CMA_SPDM_ALGORITHMS_MEASUREMENT_SPEC;
	status = libspdm_set_data(spdm_ctx, LIBSPDM_DATA_MEASUREMENT_SPEC,
				  &parameter, &data8, sizeof(data8));
	assert(status == LIBSPDM_STATUS_SUCCESS);

	data8 = CMA_SPDM_ALGORITHMS_OTHER_PARAMS_SUPPORT;
	status = libspdm_set_data(spdm_ctx, LIBSPDM_DATA_OTHER_PARAMS_SUPPORT,
				  &parameter, &data8, sizeof(data8));
	assert(status == LIBSPDM_STATUS_SUCCESS);

	data32 = CMA_SPDM_ALGORITHMS_BASE_ASYM_ALGOS;
	status = libspdm_set_data(spdm_ctx, LIBSPDM_DATA_BASE_ASYM_ALGO,
				  &parameter, &data32, sizeof(data32));
	assert(status == LIBSPDM_STATUS_SUCCESS);

	data32 = CMA_SPDM_ALGORITHMS_BASE_HASH_ALGOS;
	status = libspdm_set_data(spdm_ctx, LIBSPDM_DATA_BASE_HASH_ALGO,
				  &parameter, &data32, sizeof(data32));
	assert(status == LIBSPDM_STATUS_SUCCESS);

	data16 = CMA_SPDM_ALGORITHMS_DHE_GROUPS;
	status = libspdm_set_data(spdm_ctx, LIBSPDM_DATA_DHE_NAME_GROUP,
				  &parameter, &data16, sizeof(data16));
	assert(status == LIBSPDM_STATUS_SUCCESS);

	data16 = CMA_SPDM_ALGORITHMS_AEAD_CIPHER_SUITES;
	status = libspdm_set_data(spdm_ctx, LIBSPDM_DATA_AEAD_CIPHER_SUITE,
				  &parameter, &data16, sizeof(data16));
	assert(status == LIBSPDM_STATUS_SUCCESS);

	data16 = CMA_SPDM_ALGORITHMS_KEY_SCHEDULE;
	status = libspdm_set_data(spdm_ctx, LIBSPDM_DATA_KEY_SCHEDULE,
				  &parameter, &data16, sizeof(data16));
	assert(status == LIBSPDM_STATUS_SUCCESS);

	data16 = CMA_SPDM_ALGORITHMS_REQ_BASE_ASYM_ALGOS;
	status = libspdm_set_data(spdm_ctx, LIBSPDM_DATA_REQ_BASE_ASYM_ALG,
				  &parameter, &data16, sizeof(data16));
	assert(status == LIBSPDM_STATUS_SUCCESS);

	/*
	 * RMM do not maintain full certificate chain. Register function handler
	 * to skip certificate verification.
	 */
	libspdm_register_verify_spdm_cert_chain_func(spdm_ctx,
						     cma_spdm_verify_cert_chain);

	return 0;
}
