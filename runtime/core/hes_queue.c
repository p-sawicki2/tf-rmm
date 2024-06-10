/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <buffer.h>
#include <cpuid.h>
#include <debug.h>
#include <errno.h>
#include <granule.h>
#include <memory.h>
#include <queue.h>
#include <rec.h>
#include <rmm_el3_ifc.h>
#include <spinlock.h>
#include <stdbool.h>
#include <string.h>
#include <t_cose_rmm_hes_crypto.h>


#define HES_ATTEST_REQUEST_VERSION 0x10
#define HES_ATTEST_RESPONSE_VERSION 0x10

/* Structure format in which EL3 expects a request */
struct hes_attest_request_s {
	SET_MEMBER(uint8_t version, 0x0, 0x2);
	SET_MEMBER(uint16_t struct_size, 0x2, 0x4);
	SET_MEMBER(psa_algorithm_t alg_id, 0x4, 0x8);
	SET_MEMBER(uintptr_t rec_granule, 0x8, 0x10);
	SET_MEMBER(uint64_t req_ticket, 0x10, 0x18);
	SET_MEMBER(size_t hash_len, 0x18, 0x20);
	SET_MEMBER(uint8_t hash_buf[64], 0x20, 0x60);
};
COMPILER_ASSERT(U(offsetof(struct hes_attest_request_s, version)) == 0x0U);
COMPILER_ASSERT(U(offsetof(struct hes_attest_request_s, struct_size)) == 0x2U);
COMPILER_ASSERT(U(offsetof(struct hes_attest_request_s, alg_id)) == 0x4U);
COMPILER_ASSERT(U(offsetof(struct hes_attest_request_s, rec_granule)) == 0x8U);
COMPILER_ASSERT(U(offsetof(struct hes_attest_request_s, req_ticket)) == 0x10U);
COMPILER_ASSERT(U(offsetof(struct hes_attest_request_s, hash_len)) == 0x18U);
COMPILER_ASSERT(U(offsetof(struct hes_attest_request_s, hash_buf)) == 0x20U);

/* Structure format in which EL3 is expected to return data */
struct hes_attest_response_s {
	SET_MEMBER(uint8_t version, 0x0, 0x2);
	SET_MEMBER(uint16_t struct_size, 0x2, 0x8);
	SET_MEMBER(uintptr_t rec_granule, 0x8, 0x10);
	SET_MEMBER(uint64_t req_ticket, 0x10, 0x18);
	SET_MEMBER(uint16_t sig_len, 0x18, 0x20);
	SET_MEMBER(uint8_t signature_buf[512], 0x20, 0x220);
};

COMPILER_ASSERT(U(offsetof(struct hes_attest_response_s, version)) == 0x0U);
COMPILER_ASSERT(U(offsetof(struct hes_attest_response_s, struct_size)) == 0x2U);
COMPILER_ASSERT(U(offsetof(struct hes_attest_response_s, rec_granule)) == 0x8U);
COMPILER_ASSERT(U(offsetof(struct hes_attest_response_s, req_ticket)) == 0x10U);
COMPILER_ASSERT(U(offsetof(struct hes_attest_response_s, sig_len)) == 0x18U);
COMPILER_ASSERT(U(offsetof(struct hes_attest_response_s, signature_buf)) ==
		0x20U);

CIRCULAR_Q_DECLARE(hes_attest_queue, HES_ATTEST_QUEUE_SIZE,
		   HES_ATTEST_QUEUE_ELEMENT_SIZE);
COMPILER_ASSERT(sizeof(struct hes_attest_request_s) <=
		HES_ATTEST_QUEUE_ELEMENT_SIZE);
static spinlock_t hes_attest_queue_lock = { 0U };
static uint64_t hes_attest_ticket;

static struct hes_attest_response_s hes_attest_response[MAX_CPUS] = { 0 };

static bool hes_attest_queue_try_enqueue(struct t_cose_rmm_hes_ctx *hes_ctx_locked,
					 uint64_t *ticket)
{
	int ret = 0;
	struct hes_attest_request_s req;

	if (!hes_ctx_locked || !ticket ||
		hes_ctx_locked->state.hash_len > sizeof(req.hash_buf)) {
		return false;
	}


	req.version = HES_ATTEST_REQUEST_VERSION;
	req.struct_size = sizeof(req);
	req.alg_id = hes_ctx_locked->state.alg_id;
	req.rec_granule = hes_ctx_locked->state.rec_granule;
	req.hash_len = hes_ctx_locked->state.hash_len;
	memcpy(req.hash_buf, hes_ctx_locked->state.c_buffer_for_tbs_hash,
	       req.hash_len);

	spinlock_acquire(&hes_attest_queue_lock);
	/*
	 * Update ticket inside lock, for atomicity. We can use atomics but
	 * we have a lock anyway and this is a simple increment.
	 */
	req.req_ticket = ++hes_attest_ticket;
	*ticket = req.req_ticket;
	ret = q_push(&hes_attest_queue, &req, sizeof(req));
	spinlock_release(&hes_attest_queue_lock);

	assert(ret == 0 || ret == -EAGAIN);
	return (ret == 0);
}

/*
 * The parent REC granules lock is expected to be acquired before functions
 * buffer_aux_granules_map() and buffer_aux_unmap() are called.
 */
static void *buffer_aux_granules_map_hes_slot(struct granule *g_rec_aux[], unsigned int num_aux)
{
	return buffer_aux_granules_map(g_rec_aux, num_aux,
					SLOT_REC_AUX0_HES_QUEUE);
}

int hes_attest_queue_init(void)
{
	int ret = q_init_check(&hes_attest_queue);

	if (ret != 0) {
		ERROR("hes_queue_init: q_init_check failed with error %d\n",
		      ret);
		return ret;
	}

	if (rmm_el3_ifc_get_shared_buf_size() < HES_ATTEST_QUEUE_ELEMENT_SIZE) {
		ERROR("hes_queue_init: shared buffer size is smaller than queue element size\n");
		return -EINVAL;
	}

	t_cose_crypto_hes_init(hes_attest_queue_try_enqueue);
	return 0;
}

void hes_attest_push_request_to_hes(void)
{
	uintptr_t shared_buf;
	int ret = 0;
	struct hes_attest_request_s *req;
	bool queue_lock = false;
	bool shared_buf_lock = false;
	struct circular_q_iter iter;

	spinlock_acquire(&hes_attest_queue_lock);
	queue_lock = true;

	if (q_empty(&hes_attest_queue)) {
		goto out_lock;
	}

	/*
	 * Peek into element that will be popped. We should only pop the
	 * element if we are able to push it to HES. This is to avoid
	 * dropping the request in case of an error while pushing to HES
	 * or EL3 has a temporary condition that requires a retry (ex.
	 * queue in EL3 is full)
	 */
	if (q_init_iterator(&hes_attest_queue, &iter)) {
		panic();
	}

	req = (struct hes_attest_request_s *)q_iter_get_next(&iter);
	if (!req) {
		panic();
	}

	shared_buf = rmm_el3_ifc_get_shared_buf_locked();
	shared_buf_lock = true;

	(void)memcpy((void *)shared_buf, (void *)req, sizeof(*req));
	(void)memset(((void *)shared_buf + sizeof(*req)), 0,
			(rmm_el3_ifc_get_shared_buf_size() - sizeof(*req)));
	assert(req->version == HES_ATTEST_REQUEST_VERSION);
	assert(req->struct_size == sizeof(*req));

	ret = rmm_el3_ifc_push_hes_request(shared_buf,
					   rmm_el3_ifc_get_shared_buf_size());

	rmm_el3_ifc_release_shared_buf();
	shared_buf_lock = false;

	if (ret == -ENOMEM) {
		VERBOSE("HES asked to retry push\n");
		goto out_lock;
	}

	/* Fatal error, unable to push to EL3. */
	if (ret != 0) {
		ERROR("%s: rmm_el3_ifc_push_hes_request failed with error %d\n",
		       __func__, ret);
		panic();
	}

	/*
	 * Now that we have pushed to EL3, we can pop from the queue. We dont
	 * expect the pop to fail.
	 */
	ret = q_pop(&hes_attest_queue, (void *)shared_buf,
		    rmm_el3_ifc_get_shared_buf_size());
	if (ret != 0) {
		ERROR("%s: q_pop failed with error %d\n",
		       __func__, ret);
		panic();
	}

	spinlock_release(&hes_attest_queue_lock);
	queue_lock = false;

out_lock:
	if (queue_lock) {
		spinlock_release(&hes_attest_queue_lock);
	}
	if (shared_buf_lock) {
		rmm_el3_ifc_release_shared_buf();
	}
}

void hes_attest_pull_response_from_hes(void)
{
	uintptr_t shared_buf;
	int ret = 0;
	size_t resp_len = 0;
	struct granule *rec_granule;
	struct rec *rec;
	struct t_cose_rmm_hes_ctx *hes_ctx;
	void *rec_aux = NULL;
	struct rec_attest_data *attest_data = NULL;
	struct hes_attest_response_s *hes_resp = &hes_attest_response[my_cpuid()];

	shared_buf = rmm_el3_ifc_get_shared_buf_locked();
	ret = rmm_el3_ifc_pull_hes_response(
		shared_buf, rmm_el3_ifc_get_shared_buf_size(), &resp_len);
	if (ret == -ENOMEM) {
		VERBOSE("HES asked to retry pull\n");
		rmm_el3_ifc_release_shared_buf();
		return;
	}

	if (ret != 0 || resp_len != sizeof(*hes_resp)) {
		ERROR("%s:%d Failed to pull response from HES: %d %d %d\n",
			__func__, __LINE__, ret, -EAGAIN, -ENOMEM);
		panic();
	}

	memcpy((void *)hes_resp, (void *)shared_buf, sizeof(*hes_resp));
	rmm_el3_ifc_release_shared_buf();

	assert(hes_resp->version == HES_ATTEST_RESPONSE_VERSION);
	assert(hes_resp->struct_size == sizeof(*hes_resp));

	rec_granule = find_lock_granule(
		hes_resp->rec_granule, GRANULE_STATE_REC);
	if (!rec_granule) {
		/*
		 * REC must have been destroyed, remove any cancel requests for
		 * this REC
		 */
		VERBOSE("REC granule %lx not found\n", hes_resp->rec_granule);
		return;
	}

	rec = buffer_granule_map(rec_granule, SLOT_REC_HES_QUEUE);
	assert(rec != NULL);

	/*
	 * Map auxiliary granules. Note that the aux graules are mapped at a
	 * different high VA than during realm creation since this function
	 * may be executing with another rec mapped at the same high VA.
	 * Any accesses to aux granules via initialized pointers such as
	 * attest_data, need to be recaluclated at the new high VA.
	 */
	rec_aux = buffer_aux_granules_map_hes_slot(rec->g_aux, rec->num_rec_aux);
	assert(rec_aux != NULL);

	attest_data = rec_aux + REC_HEAP_SIZE + REC_PMU_SIZE + REC_SIMD_SIZE;
	hes_ctx = &attest_data->token_sign_ctx.ctx.crypto_ctx;

	spinlock_acquire(&hes_ctx->lock);

	/*
	 * Check the ticket to ensure that the response is for the right
	 * request. If the ticket does not match, drop the response.
	 * The ticket may not match if the request was cancelled by
	 * the realm calling token_init again. It is also possible that
	 * the realm has initialized and queued another request.
	 */
	if (hes_ctx->state.req_ticket != hes_resp->req_ticket) {
		assert(hes_ctx->state.req_ticket == 0UL ||
			hes_ctx->state.req_ticket >= hes_resp->req_ticket);
		ERROR("%s:%d ticket mismatch %lx %lx, dropping response\n",
			__func__, __LINE__, hes_ctx->state.req_ticket,
			hes_resp->req_ticket);
		goto out_buf_lock;
	}

	if (hes_resp->sig_len > sizeof(hes_ctx->state.sig_buffer) ||
	    hes_resp->sig_len > hes_ctx->state.sig_len) {
		ERROR("%s:%d sig len mismatch %x %x\n", __func__, __LINE__,
		      hes_ctx->state.sig_len, hes_resp->sig_len);
		hes_ctx->state.is_hes_err = true;
		goto out_buf_lock;
	}

	hes_ctx->state.sig_len = hes_resp->sig_len;
	memcpy((void *)hes_ctx->state.sig_buffer,
		(void *)hes_resp->signature_buf, hes_resp->sig_len);
	hes_ctx->state.is_sig_valid = true;

out_buf_lock:
	spinlock_release(&hes_ctx->lock);
	/* Unmap auxiliary granules */
	buffer_aux_unmap(rec_aux, rec->num_rec_aux);
	buffer_unmap(rec);
	granule_unlock(rec_granule);
}
