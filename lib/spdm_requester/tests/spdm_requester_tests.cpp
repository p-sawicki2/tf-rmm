/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <CppUTest/CommandLineTestRunner.h>
#include <CppUTest/TestHarness.h>

/*
 * This unittest doesn't depend on PDEV object. So manually set the size
 * required for heap.
 */
#define HEAP_SIZE_SPDM_TEST	(4U * SZ_4K)

extern "C"
{
	#include <mbedtls/memory_buffer_alloc.h>
	#include <memory_alloc.h>
	#include <sizes.h>

	int test_crypt_main(void);

	static struct buffer_alloc_ctx unittest_buffer_alloc_ctx;
	static unsigned char mbedtls_heap[HEAP_SIZE_SPDM_TEST]
					__aligned(sizeof(unsigned long));
}

TEST_GROUP(spdm_requester)
{
	int rc;

	TEST_SETUP() {
		/* Assign buffer context for mbedtls heap */
		rc = buffer_alloc_ctx_assign(&unittest_buffer_alloc_ctx);
		CHECK_TRUE(rc == 0);

		mbedtls_memory_buffer_alloc_init(mbedtls_heap,
						 sizeof(mbedtls_heap));
	}

	TEST_TEARDOWN() {
		buffer_alloc_ctx_unassign();
	}
};

TEST(spdm_requester, test_crypt)
{
	int rc = 0;

	rc = test_crypt_main();
	CHECK_TRUE(rc == 0);
}
