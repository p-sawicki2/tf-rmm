/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <atomics.h>
#include <buffer.h>
#include <cpuid.h>
#include <debug.h>
#include <errno.h>
#include <granule.h>
#include <memory.h>
#include <rec.h>
#include <rmm_el3_ifc.h>
#include <spinlock.h>
#include <stdbool.h>
#include <string.h>


#define EL3_TOKEN_SIGN_REQUEST_VERSION 0x10
#define EL3_TOKEN_SIGN_RESPONSE_VERSION 0x10

/* Structure format in which EL3 expects a request */
struct el3_token_sign_request_s {
	SET_MEMBER(uint8_t version, 0x0, 0x2);
	SET_MEMBER(uint16_t struct_size, 0x2, 0x4);
	SET_MEMBER(psa_algorithm_t alg_id, 0x4, 0x8);
	SET_MEMBER(uintptr_t rec_granule, 0x8, 0x10);
	SET_MEMBER(uint64_t req_ticket, 0x10, 0x18);
	SET_MEMBER(size_t hash_len, 0x18, 0x20);
	SET_MEMBER(uint8_t hash_buf[64], 0x20, 0x60);
};
COMPILER_ASSERT(U(offsetof(struct el3_token_sign_request_s, version)) == 0x0U);
COMPILER_ASSERT(U(offsetof(struct el3_token_sign_request_s, struct_size)) == 0x2U);
COMPILER_ASSERT(U(offsetof(struct el3_token_sign_request_s, alg_id)) == 0x4U);
COMPILER_ASSERT(U(offsetof(struct el3_token_sign_request_s, rec_granule)) == 0x8U);
COMPILER_ASSERT(U(offsetof(struct el3_token_sign_request_s, req_ticket)) == 0x10U);
COMPILER_ASSERT(U(offsetof(struct el3_token_sign_request_s, hash_len)) == 0x18U);
COMPILER_ASSERT(U(offsetof(struct el3_token_sign_request_s, hash_buf)) == 0x20U);

/* Structure format in which EL3 is expected to return data */
struct el3_token_sign_response_s {
	SET_MEMBER(uint8_t version, 0x0, 0x2);
	SET_MEMBER(uint16_t struct_size, 0x2, 0x8);
	SET_MEMBER(uintptr_t rec_granule, 0x8, 0x10);
	SET_MEMBER(uint64_t req_ticket, 0x10, 0x18);
	SET_MEMBER(uint16_t sig_len, 0x18, 0x20);
	SET_MEMBER(uint8_t signature_buf[512], 0x20, 0x220);
};

COMPILER_ASSERT(U(offsetof(struct el3_token_sign_response_s, version)) == 0x0U);
COMPILER_ASSERT(U(offsetof(struct el3_token_sign_response_s, struct_size)) == 0x2U);
COMPILER_ASSERT(U(offsetof(struct el3_token_sign_response_s, rec_granule)) == 0x8U);
COMPILER_ASSERT(U(offsetof(struct el3_token_sign_response_s, req_ticket)) == 0x10U);
COMPILER_ASSERT(U(offsetof(struct el3_token_sign_response_s, sig_len)) == 0x18U);
COMPILER_ASSERT(U(offsetof(struct el3_token_sign_response_s, signature_buf)) ==
		0x20U);

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
	req->version = EL3_TOKEN_SIGN_REQUEST_VERSION;
	req->struct_size = sizeof(*req);
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

	(void)memset(((void *)req + sizeof(*req)), 0,
			(rmm_el3_ifc_get_shared_buf_size() - sizeof(*req)));

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

void el3_token_sign_pull_response_from_el3(void)
{
	uintptr_t shared_buf;
	int ret = 0;
	size_t resp_len = 0;
	struct granule *rec_granule;
	struct rec *rec;
	struct t_cose_rmm_el3_ctx *ctx;
	void *rec_aux = NULL;
	struct rec_attest_data *attest_data = NULL;
	struct el3_token_sign_response_s *el3_resp = &el3_token_sign_response[my_cpuid()];

	shared_buf = rmm_el3_ifc_get_shared_buf_locked();
	ret = rmm_el3_ifc_pull_el3_attest_sign_response(
		shared_buf, rmm_el3_ifc_get_shared_buf_size(), &resp_len);
	if (ret == -ENOMEM) {
		VERBOSE("EL3 asked to retry pull\n");
		rmm_el3_ifc_release_shared_buf();
		return;
	}

	if (ret != 0 || resp_len != sizeof(*el3_resp)) {
		ERROR("%s:%d Failed to pull response from EL3: %d %d %d\n",
			__func__, __LINE__, ret, -EAGAIN, -ENOMEM);
		panic();
	}

	memcpy((void *)el3_resp, (void *)shared_buf, sizeof(*el3_resp));
	rmm_el3_ifc_release_shared_buf();

	assert(el3_resp->version == EL3_TOKEN_SIGN_RESPONSE_VERSION);
	assert(el3_resp->struct_size == sizeof(*el3_resp));

	rec_granule = find_lock_granule(
		el3_resp->rec_granule, GRANULE_STATE_REC);
	if (!rec_granule) {
		/*
		 * REC must have been destroyed, drop the response.
		 */
		VERBOSE("REC granule %lx not found\n", el3_resp->rec_granule);
		return;
	}

	rec = buffer_granule_map(rec_granule, SLOT_EL3_SIGN_REC);
	assert(rec != NULL);

	/*
	 * Map auxiliary granules. Note that the aux graules are mapped at a
	 * different high VA than during realm creation since this function
	 * may be executing with another rec mapped at the same high VA.
	 * Any accesses to aux granules via initialized pointers such as
	 * attest_data, need to be recaluclated at the new high VA.
	 */
	rec_aux = buffer_aux_granules_map_el3_sign_slot(rec->g_aux, rec->num_rec_aux);
	assert(rec_aux != NULL);

	attest_data = rec_aux + REC_HEAP_SIZE + REC_PMU_SIZE + REC_SIMD_SIZE;
	ctx = &attest_data->token_sign_ctx.ctx.crypto_ctx;

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

	if (el3_resp->sig_len > sizeof(ctx->state.sig_buffer) ||
	    el3_resp->sig_len > ctx->state.sig_len) {
		ERROR("%s:%d sig len mismatch %x %x\n", __func__, __LINE__,
		      ctx->state.sig_len, el3_resp->sig_len);
		ctx->state.is_el3_err = true;
		goto out_buf_lock;
	}

	ctx->state.sig_len = el3_resp->sig_len;
	memcpy((void *)ctx->state.sig_buffer,
		(void *)el3_resp->signature_buf, el3_resp->sig_len);
	ctx->state.is_sig_valid = true;

out_buf_lock:
	spinlock_release(&ctx->lock);
	/* Unmap auxiliary granules */
	buffer_aux_unmap(rec_aux, rec->num_rec_aux);
	buffer_unmap(rec);
	granule_unlock(rec_granule);
}
