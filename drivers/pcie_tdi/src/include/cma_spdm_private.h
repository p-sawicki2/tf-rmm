/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef CMA_SPDM_PRIVATE_H
#define CMA_SPDM_PRIVATE_H

#include <assert.h>
#include <context.h>
#include <industry_standard/spdm.h>
#include <industry_standard/spdm_secured_message.h>
#include <library/spdm_requester_lib.h>
#include <library/spdm_secured_message_lib.h>
#include <mbedtls/ecdh.h>
#include <mbedtls/rsa.h>
#include <psa/crypto.h>
#include <utils_def.h>

/*
 * Requester SPDM version is 1.2. This is the minimum SPDM version required to
 * support TDISP.
 *
 * From PCIe spec: CMA requires SPDM Version 1.0 or above. IDE requires SPDM
 * Version 1.1 or above. TDISP requires version 1.2 or above.
 */
#define CMA_SPDM_VERSION		SPDM_MESSAGE_VERSION_12

/*
 * Secured Messages using SPDM Specification (IDE requires version 1.0 or above)
 * Set this to 1.2 to match with CMA_SPDM_VERSION
 */
#define CMA_SECURED_SPDM_VERSION	SECURED_SPDM_VERSION_12

/*
 * Responders must implement a Cryptographic Timeout (CT), as defined by SPDM
 * specification, of not more than 2^23 μs.
 */
#define CMA_SPDM_GET_CAPABILITY_CT_EXPONENT		20

/*
 * List of capabilities enabled and supported by SPDM requester. These flags are
 * passed to GET_CAPABILITIES request message. Currently these flags are specific
 * to PCIe TDI off-chip device.
 *
 * CERT_CAP	- Supports DIGESTS and CERTIFICATE response messages.
 * ENCRYPT_CAP	- Supports message encryption in a secure session.
 * KEY_EX_CAP	- Support KEY_EXCHANGE request message. Needs ENCRYPT_CAP and
 *		  MAC_CAP.
 * MAC_CAP	- Supports message authentication in a secure session.
 * CHUNK_CAP	- Supports large SPDM message transfer mechanism messages.
 *		  Note: Add SPDM_GET_CAPABILITIES_REQUEST_FLAGS_CHUNK_CAP.
 *			CHUNK retrieval is not verified.
 */
#define CMA_SPDM_GET_CAPABILITIES_REQUEST_FLAGS				( \
	SPDM_GET_CAPABILITIES_REQUEST_FLAGS_CERT_CAP			| \
	SPDM_GET_CAPABILITIES_REQUEST_FLAGS_ENCRYPT_CAP			| \
	SPDM_GET_CAPABILITIES_REQUEST_FLAGS_MAC_CAP			| \
	SPDM_GET_CAPABILITIES_REQUEST_FLAGS_KEY_EX_CAP			| \
	SPDM_GET_CAPABILITIES_REQUEST_FLAGS_HANDSHAKE_IN_THE_CLEAR_CAP)

/*
 * List of minimum set of capabilities required to be supported by the responder.
 * These flags are checked against CAPABILITIES response message. Currently these
 * flags are specific to PCIe TDI off-chip device.
 */
#define CMA_SPDM_GET_CAPABILITIES_RESPONSE_FLAGS			( \
	SPDM_GET_CAPABILITIES_RESPONSE_FLAGS_CERT_CAP			| \
	SPDM_GET_CAPABILITIES_RESPONSE_FLAGS_ENCRYPT_CAP		| \
	SPDM_GET_CAPABILITIES_RESPONSE_FLAGS_MAC_CAP			| \
	SPDM_GET_CAPABILITIES_RESPONSE_FLAGS_MEAS_CAP			| \
	SPDM_GET_CAPABILITIES_RESPONSE_FLAGS_KEY_EX_CAP)

/*
 * Optional set of capabilities that can be supported by the responder. These
 * flags are checked against CAPABILITIES response message.
 */
#define CMA_SPDM_GET_CAPABILITIES_RESPONSE_OPTIONAL_FLAGS		( \
	SPDM_GET_CAPABILITIES_RESPONSE_FLAGS_MEAS_FRESH_CAP		| \
	SPDM_GET_CAPABILITIES_RESPONSE_FLAGS_CHUNK_CAP)

/*
 * The measurement specification is used in the MEASUREMENTS response. This is
 * not explicitly mentioned in PCIe CMA-SPDM.
 */
#define CMA_SPDM_ALGORITHMS_MEASUREMENT_SPEC				\
	SPDM_MEASUREMENT_SPECIFICATION_DMTF

/*
 * OtherParamsSupport: Opaque data format used is DMTF. This is not explicitly
 * mentioned in PCIe CMA-SPDM.
 */
#define CMA_SPDM_ALGORITHMS_OTHER_PARAMS_SUPPORT			\
	SPDM_ALGORITHMS_OPAQUE_DATA_FORMAT_1

/*
 * Requesters are required to support responders that implement any of these
 * choices of BaseAsymAlgo:
 *	TPM_ALG_RSASSA_3072
 *	TPM_ALG_ECDSA_ECC_NIST_P256
 *	TPM_ALG_ECDSA_ECC_NIST_P384
 */
#define CMA_SPDM_ALGORITHMS_BASE_ASYM_ALGOS				( \
	SPDM_ALGORITHMS_BASE_ASYM_ALGO_TPM_ALG_RSASSA_3072		| \
	SPDM_ALGORITHMS_BASE_ASYM_ALGO_TPM_ALG_ECDSA_ECC_NIST_P256	| \
	SPDM_ALGORITHMS_BASE_ASYM_ALGO_TPM_ALG_ECDSA_ECC_NIST_P384)

/*
 * Requesters and responders must, for MeasurementHashAlgo, support one or both
 * of the following:
 *	TPM_ALG_SHA_256
 *	TPM_ALG_SHA_384
 */
#define CMA_SPDM_ALGORITHMS_BASE_HASH_ALGOS				( \
	SPDM_ALGORITHMS_BASE_HASH_ALGO_TPM_ALG_SHA_256			| \
	SPDM_ALGORITHMS_BASE_HASH_ALGO_TPM_ALG_SHA_384)

/*
 * Requester are required to responders that implement any of these DHE groups
 *	SECP_256_R1
 *	SECP_384_R1
 */
#define CMA_SPDM_ALGORITHMS_DHE_GROUPS					( \
	SPDM_ALGORITHMS_DHE_NAMED_GROUP_SECP_256_R1			| \
	SPDM_ALGORITHMS_DHE_NAMED_GROUP_SECP_384_R1)

/*
 * Requester are required to responders that implement any of these AEAD Cipher
 * Suite
 *	AES-128-GCM
 *	AES-256-GCM
 */
#define CMA_SPDM_ALGORITHMS_AEAD_CIPHER_SUITES				( \
	SPDM_ALGORITHMS_AEAD_CIPHER_SUITE_AES_128_GCM			| \
	SPDM_ALGORITHMS_AEAD_CIPHER_SUITE_AES_256_GCM)

/* Requester-supported SPDM-enumerated Key Schedule algorithms. */
#define CMA_SPDM_ALGORITHMS_KEY_SCHEDULE				\
	SPDM_ALGORITHMS_KEY_SCHEDULE_HMAC_HASH

/*
 * Requesters supported asym algorithm.
 *	TPM_ALG_RSAPSS_3072
 *	TPM_ALG_RSAPSS_2048
 *	TPM_ALG_RSASSA_3072
 *	TPM_ALG_RSASSA_2048
 */
#define CMA_SPDM_ALGORITHMS_REQ_BASE_ASYM_ALGOS				( \
	SPDM_ALGORITHMS_BASE_ASYM_ALGO_TPM_ALG_RSAPSS_3072		| \
	SPDM_ALGORITHMS_BASE_ASYM_ALGO_TPM_ALG_RSAPSS_2048		| \
	SPDM_ALGORITHMS_BASE_ASYM_ALGO_TPM_ALG_RSASSA_3072		| \
	SPDM_ALGORITHMS_BASE_ASYM_ALGO_TPM_ALG_RSASSA_2048)

/* todo: SPDM chunk send/recv */
#define CMA_SPDM_MSG_SIZE_MAX		0x2000
#define CMA_SPDM_SENDER_BUFFER_SIZE	(CMA_SPDM_MSG_SIZE_MAX)
#define CMA_SPDM_RECEIVER_BUFFER_SIZE	(CMA_SPDM_MSG_SIZE_MAX)

#define LIBSPMD_CONTEXT_SIZE		0x2000
#define SEND_RECV_BUF_SIZE		0x1000
#define LIBSPMD_SCRATCH_BUF_SIZE	0xC000
#define LIBSPMD_STACK_SIZE		0x3000

#define spdm_to_cma(spdm) ((struct cma_spdm_context *)((unsigned long)(spdm) -	\
		       offsetof(struct cma_spdm_context, libspdm_context)))

struct cma_spdm_context {
	dev_handle_t dev_handle;
	uint8_t cert_slot_id;

	context_t main_ctx;
	context_t libspdm_cmd_ctx;
	libspdm_return_t libspdm_cmd_rc;
	bool is_msg_sspdm;

	/* spdm_cert_chain digest details */
	psa_hash_operation_t spdm_cert_chain_hash_op;
	psa_algorithm_t spdm_cert_chain_algo;
	uint8_t spdm_cert_chain_digest[64];
	size_t spdm_cert_chain_digest_length;
	size_t spdm_cert_chain_len;

	/* Public key context */
	union {
		mbedtls_ecdh_context ecdh;
		mbedtls_rsa_context rsa;
	} pk_ctx __aligned(32);

	/*
	 * Device communication callbacks ops to send, recv and cache device
	 * request and responses.
	 */
	const struct dev_comm_ops *comm_ops;

	void *send_recv_buffer;
	void *scratch_buffer;
	void *libspdm_stack;

	/*
	 * End of this structure holds libspdm context. This is kept inside this
	 * structure so that during callback from libspdm pointer to
	 * 'cma_spdm_context' can be dereferenced.
	 */
	uint8_t libspdm_context[0] __aligned(128);
};
COMPILER_ASSERT(sizeof(struct cma_spdm_context) <= 4096U);

#endif /* CMA_SPDM_PRIVATE_H */
