/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef ATTESTATION_H
#define ATTESTATION_H

#include <stddef.h>
#ifdef CBMC
#include <tb_common.h>
#endif

struct buffer_alloc_ctx;

/*
 * Performs any early initialization needed for the crypto library.
 */
#ifndef CBMC
int attestation_init(void);
#else /* CBMC */
static inline int attestation_init(void)
{
	ASSERT(false, "attestation_init");
	return 0;
}
#endif /* CBMC */

/*
 * Return the platform token that was previously retrieved from the monitor.
 *
 * Arguments:
 * buf - pointer to a buffer where the address of the platform token will
 *       be returned.
 * len - pointer to an unsigned integer where the length of the platform token
 *       will be returned.
 *
 * Returns 0 on success, and a negative error code otherwise.
 */
int attest_get_platform_token(const void **buf, size_t *len);

/*
 * Initialize the heap buffer to be used with the given buffer_alloc_ctx.
 * This is done when a REC is created.
 *
 * As a pre-requisite, ensure that a buffer_alloc_ctx has been assigned to this
 * PE prior to calling this function.
 *
 * Arguments:
 * buf - pointer to start of heap
 * buf_size -  size of the heap
 *
 * Returns 0 on success, negative error code on error.
 */
#ifndef CBMC
int attestation_heap_ctx_init(unsigned char *buf, size_t buf_size);
#else /* CBMC */
static inline int attestation_heap_ctx_init(unsigned char *buf, size_t buf_size)
{
	ASSERT(false, "attestation_heap_ctx_init");
	return 0;
}
#endif /* CBMC */

/*
 * Assign a given buf_alloc_ctx to this CPU. This needs to be called
 * prior to entering a Realm to allow it invoking RMM crypto operations.
 *
 * Arguments:
 * ctx - pointer to buffer_alloc_ctx
 *
 * Returns 0 on success, negative error code on error.
 */
#ifndef CBMC
int attestation_heap_ctx_assign_pe(struct buffer_alloc_ctx *ctx);
#else /* CBMC */
static inline int attestation_heap_ctx_assign_pe(struct buffer_alloc_ctx *ctx)
{
	ASSERT(false, "attestation_heap_ctx_assign_pe");
	return 0;
}
#endif /* CBMC */


/*
 * Unassign a given buf_alloc_ctx from CPU. This needs to be called
 * after exiting the realm.
 *
 * Arguments:
 * ctx - pointer to buffer_alloc_ctx
 *
 * Returns 0 on success, negative error code on error.
 */
#ifndef CBMC
int attestation_heap_ctx_unassign_pe(void);
#else /* CBMC */
static inline int attestation_heap_ctx_unassign_pe(void)
{
	ASSERT(false, "attestation_heap_ctx_unassign_pe");
	return 0;
}
#endif /* CBMC */

/*
 * Reinit the heap on this CPU used for attestation operations.
 *
 * Arguments:
 * buf		- Buffer to use as heap.
 * buf_size	- Size of the buffer to use as heap.
 *
 * Returns 0 on success, negative error code otherwise.
 *
 * Note: This function assumes that a the allocator has a
 * buffer_alloc_ctx assigned to it.
 */
int attestation_heap_reinit_pe(unsigned char *buf, size_t buf_size);

#endif /* ATTESTATION_H */
