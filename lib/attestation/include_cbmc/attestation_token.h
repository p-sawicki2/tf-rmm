/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright Laurence Lundblade.
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

/*
 *****************************************
 * This header is only for CBMC analysis *
 *****************************************
 */

/*
 * This file is derived from:
 *    trusted-firmware-m/secure_fw/partitions/initial_attestation/attest_token.h
 */

#ifndef ATTESTATION_TOKEN_H
#define ATTESTATION_TOKEN_H

#include <measurement.h>

#define ATTEST_TOKEN_BUFFER_SIZE		GRANULE_SIZE

enum attest_token_err_t {
	/* Success */
	ATTEST_TOKEN_ERR_SUCCESS = 0,
	/* Signing is in progress, function should be called with the same
	 * parameters again.
	 */
	ATTEST_TOKEN_ERR_COSE_SIGN_IN_PROGRESS
};

/* The state of the realm token generation */
enum attest_token_gen_state_t {
	ATTEST_SIGN_NOT_STARTED,
	ATTEST_SIGN_IN_PROGRESS,
	ATTEST_SIGN_TOKEN_WRITE_IN_PROGRESS,
};

struct attest_token_encode_ctx {
	uint32_t unused;
};

#define ATTEST_CHALLENGE_SIZE			(1)

/*
 * The context for signing an attestation token. Each REC contains one context
 * that is passed to the attestation library during attestation token creation
 * to keep track of the signing state.
 */
struct token_sign_cntxt {
	/*
	 * 'state' is used to implement a state machine
	 * to track the current state of signing.
	 */
	enum attest_token_gen_state_t state;
	struct attest_token_encode_ctx ctx;
	/* Data saved in the first iteration */
	unsigned long token_ipa;
	unsigned char challenge[ATTEST_CHALLENGE_SIZE];
};

static enum attest_token_err_t
attest_realm_token_sign(struct attest_token_encode_ctx *me,
			size_t *completed_token_len)
{
	return ATTEST_TOKEN_ERR_SUCCESS;
}

static size_t attest_cca_token_create(void *attest_token_buf,
				      size_t attest_token_buf_size,
				      const void *realm_token_buf,
				      size_t realm_token_len)
{
	return 0;
}

static int
attest_realm_token_create(enum hash_algo algorithm,
			  unsigned char measurements[][MAX_MEASUREMENT_SIZE],
			  unsigned int num_measurements,
			  const void *rpv_buf,
			  size_t rpv_len,
			  struct token_sign_cntxt *ctx,
			  void *realm_token_buf,
			  size_t realm_token_buf_size)
{
	return ATTEST_TOKEN_ERR_SUCCESS;
}

#endif /* ATTESTATION_TOKEN_H */
