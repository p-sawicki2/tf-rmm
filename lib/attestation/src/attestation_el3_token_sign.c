/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <atomics.h>
#include <attestation_token.h>
#include <buffer.h>
#include <cpuid.h>
#include <debug.h>
#include <errno.h>
#include <granule.h>
#include <memory.h>
#include <rmm_el3_ifc.h>
#include <spinlock.h>
#include <stdbool.h>
#include <string.h>


#define EL3_TOKEN_SIGN_REQUEST_VERSION 0x10
#define EL3_TOKEN_SIGN_RESPONSE_VERSION 0x10

/* Structure format in which EL3 expects a request */
struct el3_token_sign_request_s {
	SET_MEMBER(psa_algorithm_t alg_id, 0x0, 0x8);
	SET_MEMBER(uintptr_t rec_granule, 0x8, 0x10);
	SET_MEMBER(uint64_t req_ticket, 0x10, 0x18);
	SET_MEMBER(size_t hash_len, 0x18, 0x20);
	SET_MEMBER(uint8_t hash_buf[64], 0x20, 0x60);
};
COMPILER_ASSERT(U(offsetof(struct el3_token_sign_request_s, alg_id)) == 0x0U);
COMPILER_ASSERT(U(offsetof(struct el3_token_sign_request_s, rec_granule)) == 0x8U);
COMPILER_ASSERT(U(offsetof(struct el3_token_sign_request_s, req_ticket)) == 0x10U);
COMPILER_ASSERT(U(offsetof(struct el3_token_sign_request_s, hash_len)) == 0x18U);
COMPILER_ASSERT(U(offsetof(struct el3_token_sign_request_s, hash_buf)) == 0x20U);

/* Structure format in which EL3 is expected to return data */
struct el3_token_sign_response_s {
	SET_MEMBER(uintptr_t rec_granule, 0x8, 0x8);
	SET_MEMBER(uint64_t req_ticket, 0x8, 0x10);
	SET_MEMBER(uint16_t sig_len, 0x10, 0x12);
	SET_MEMBER(uint8_t signature_buf[512], 0x12, 0x212);
};

COMPILER_ASSERT(U(offsetof(struct el3_token_sign_response_s, rec_granule)) == 0x0U);
COMPILER_ASSERT(U(offsetof(struct el3_token_sign_response_s, req_ticket)) == 0x8U);
COMPILER_ASSERT(U(offsetof(struct el3_token_sign_response_s, sig_len)) == 0x10U);
COMPILER_ASSERT(U(offsetof(struct el3_token_sign_response_s, signature_buf)) ==
		0x12U);

static uint64_t el3_token_sign_ticket = 1;

static struct el3_token_sign_response_s el3_token_sign_response[MAX_CPUS] = { 0 };

static bool el3_attest_queue_try_enqueue(struct t_cose_rmm_el3_ctx *ctx_locked,
					 uint64_t *ticket)
{
	int ret = 0;
	struct el3_token_sign_request_s *req;

	if (!ctx_locked || !ticket ||
		ctx_locked->state.hash_len > sizeof(req->hash_buf)) {
		return false;
	}

	req = (struct el3_token_sign_request_s *)rmm_el3_ifc_get_shared_buf_locked();
	req->alg_id = ctx_locked->state.alg_id;
	req->rec_granule = ctx_locked->state.rec_granule;
	req->hash_len = ctx_locked->state.hash_len;
	memcpy(req->hash_buf, ctx_locked->state.c_buffer_for_tbs_hash,
		req->hash_len);

	/*
	 * Overflow of the 64 bit number will occur after ~580 years at
	 * 1 ns resolution. Even if it does overflow, the ticket will be
	 * 0 and is still valid. Overflow is not expected to be a problem.
	 */
	req->req_ticket = atomic_load_add_64(&el3_token_sign_ticket, 1);
	*ticket = req->req_ticket;

	ret = rmm_el3_ifc_push_el3_attest_sign_request((uintptr_t)req,
					   rmm_el3_ifc_get_shared_buf_size());

	rmm_el3_ifc_release_shared_buf();

	if (ret == -ENOMEM) {
		VERBOSE("EL3 asked to retry push\n");
		return false;
	}

	/* Fatal error, unable to push to EL3. */
	if (ret != 0) {
		ERROR("%s: rmm_el3_ifc_push_el3_attest_sign_request failed with error %d\n",
		       __func__, ret);
		panic();
	}

	return true;
}

int el3_token_sign_queue_init(void)
{
	t_cose_crypto_el3_enqueue_cb_init(el3_attest_queue_try_enqueue);
	return 0;
}

/*
 * Pull the response from EL3 into the per cpu response buffer. The function
 * returns the granule address of the REC for which the response was received
 * and is expected to passed into el3_token_write_response_to_ctx().
 */
uintptr_t attest_el3_token_sign_pull_response_from_el3(void)
{
	uintptr_t shared_buf;
	int ret = 0;
	size_t resp_len = 0;
	struct el3_token_sign_response_s *el3_resp = &el3_token_sign_response[my_cpuid()];

	shared_buf = rmm_el3_ifc_get_shared_buf_locked();
	ret = rmm_el3_ifc_pull_el3_attest_sign_response(
		shared_buf, rmm_el3_ifc_get_shared_buf_size(), &resp_len);
	if (ret == -ENOMEM) {
		VERBOSE("EL3 asked to retry pull\n");
		rmm_el3_ifc_release_shared_buf();
		return 0UL;
	}

	if (ret != 0 || resp_len != sizeof(*el3_resp)) {
		ERROR("%s:%d Failed to pull response from EL3: %d %d %d\n",
			__func__, __LINE__, ret, -EAGAIN, -ENOMEM);
		panic();
	}

	memcpy((void *)el3_resp, (void *)shared_buf, sizeof(*el3_resp));
	rmm_el3_ifc_release_shared_buf();
	return el3_resp->rec_granule;
}

/*
 * Write the response from EL3 to the context. The response is written only if the context
 * is valid and the response is for the right request. If the function returns an error
 * the caller must treat it as a fatal error. The granule_addr is checked against the
 * per cpu response buffer to ensure that the response is for the right request.
 * The caller must ensure that the REC granule lock is held so that it cannot be deleted
 * while the response is being written. The auxillary granules must be mapped before
 * this function is called. If the REC is not the currently running REC, ctx is expected
 * to be relocated to the correct high VA.
 */
int attest_el3_token_write_response_to_ctx(struct token_sign_cntxt *sign_ctx,
					   uintptr_t granule_addr)
{
	struct el3_token_sign_response_s *el3_resp = &el3_token_sign_response[my_cpuid()];

	if (!sign_ctx) {
		ERROR("%s:%d Invalid context\n", __func__, __LINE__);
		return -EINVAL;
	}

	if (granule_addr != el3_resp->rec_granule) {
		VERBOSE("Response for REC granule %lx not found\n",
			 el3_resp->rec_granule);
		return -EINVAL;
	}

	struct t_cose_rmm_el3_ctx *ctx = &(sign_ctx->ctx.crypto_ctx);
	spinlock_acquire(&ctx->lock);

	/*
	 * Check the ticket to ensure that the response is for the right
	 * request. If the ticket does not match, drop the response.
	 * The ticket may not match if the request was cancelled by
	 * the realm calling token_init again. It is also possible that
	 * the realm has initialized and queued another request.
	 */
	if (ctx->state.req_ticket != el3_resp->req_ticket) {
		assert(ctx->state.req_ticket == 0UL ||
			ctx->state.req_ticket >= el3_resp->req_ticket);
		ERROR("%s:%d ticket mismatch %lx %lx, dropping response\n",
			__func__, __LINE__, ctx->state.req_ticket,
			el3_resp->req_ticket);
		goto out_buf_lock;
	}

	if (el3_resp->sig_len > ctx->state.sig_len) {
		ERROR("%s:%d sig len mismatch %x %x\n", __func__, __LINE__,
		      ctx->state.sig_len, el3_resp->sig_len);
		ctx->state.is_el3_err = true;
		goto out_buf_lock;
	}

	ctx->state.sig_len = el3_resp->sig_len;
	memcpy(ctx->state.sig_buffer,
		(void *)el3_resp->signature_buf, el3_resp->sig_len);
	ctx->state.is_sig_valid = true;

out_buf_lock:
	spinlock_release(&ctx->lock);
	return 0;
}
