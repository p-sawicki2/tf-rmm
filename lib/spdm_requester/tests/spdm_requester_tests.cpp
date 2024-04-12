/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <CppUTest/CommandLineTestRunner.h>
#include <CppUTest/TestHarness.h>

extern "C"
{
	/* Included from <libspdm_src>/unit_test/test_crypt */
	#include "test_crypt.h"
}

TEST_GROUP(spdm_requester)
{
	TEST_SETUP() {
	}

	TEST_TEARDOWN() {
	}
};

TEST(spdm_requester, test_crypt)
{
	int rc = 0;

	rc = test_crypt_main();
	CHECK_TRUE(rc == 0);

	return;
}
