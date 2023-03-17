/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <attestation.h>
#include <attestation_priv.h>
#include <debug.h>
#include <errno.h>
#include <mbedtls/memory_buffer_alloc.h>
#include <memory_alloc.h>
#include <psa/crypto.h>
#include <simd.h>
#include <sizes.h>

/*
 * Memory buffer for the allocator during key initialization.
 *
 * Used to compute the public key and setup a PRNG object per CPU. PRNGs are
 * needed for key blinding during EC signing.
 *
 * Memory requirements:
 * +------------------------+-------+ ------------------------+
 * |                        |  MAX  |  Persisting allocation  |
 * +------------------------+-------+-------------------------+
 * | Public key computation |  2.4K |         0.4K            |
 * +------------------------+-------+-------------------------+
 * |      PRNG setup        |  6.1K |          3.7K           |
 * +------------------------+-------+-------------------------+
 *
 * Measured with:
 *	src/lib/memory_buffer_alloc.c: mbedtls_memory_buffer_alloc_status()
 */
#define INIT_HEAP_PAGES		3

static unsigned char mem_buf[INIT_HEAP_PAGES * SZ_4K]
					__aligned(sizeof(unsigned long));

static bool attest_initialized;

struct buffer_alloc_ctx init_ctx;

int attestation_init(void)
{
	int ret;
	psa_status_t psa_status;

	/*
	 * Associate the allocated heap for mbedtls with the current CPU.
	 */
	buffer_alloc_ctx_assign(&init_ctx);

	SIMD_FPU_ALLOW(mbedtls_memory_buffer_alloc_init(mem_buf,
							sizeof(mem_buf)));

	SIMD_FPU_ALLOW(ret = attest_rnd_prng_init());
	if (ret != 0) {
		return ret;
	}

	SIMD_FPU_ALLOW(psa_status = psa_crypto_init());
	if (psa_status != PSA_SUCCESS) {
		return -EINVAL;
	}

	/*
	 * Set the number of max operations per ECC signing iteration to the
	 * configured value.
	 *
	 * This adjusts the length of a single signing loop.
	 */
	SIMD_FPU_ALLOW(psa_interruptible_set_max_ops(MBEDTLS_ECP_MAX_OPS));

	/* Retrieve the platform key from root world */
	SIMD_FPU_ALLOW(ret = attest_init_realm_attestation_key());
	if (ret != 0) {
		return ret;
	}

	/* Retrieve the platform token from root world */
	ret = attest_setup_platform_token();
	if (ret != 0) {
		return ret;
	}

	buffer_alloc_ctx_unassign();

	attest_initialized = true;

	return 0;
}

int attestation_heap_ctx_init(unsigned char *buf, size_t buf_size)
{
	assert(buf != NULL);

	if (attest_initialized == false) {
		return -EINVAL;
	}

	/* Initialise the mbedTLS heap */
	mbedtls_memory_buffer_alloc_init(buf, buf_size);

	return 0;
}

int attestation_heap_ctx_assign_pe(struct buffer_alloc_ctx *ctx)
{
	assert(ctx != NULL);

	if (attest_initialized == false) {
		return -EINVAL;
	}

	/*
	 * Associate the buffer_alloc_ctx to this CPU
	 */
	buffer_alloc_ctx_assign(ctx);
	return 0;
}

int attestation_heap_ctx_unassign_pe(void)
{
	if (attest_initialized == false) {
		return -EINVAL;
	}

	buffer_alloc_ctx_unassign();
	return 0;
}

inline int attestation_heap_reinit_pe(unsigned char *buf, size_t buf_size)
{
	mbedtls_memory_buffer_alloc_init(buf, buf_size);

	return 0;
}
