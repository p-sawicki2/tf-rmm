/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <CppUTest/TestHarness.h>

extern "C" {

	void test_helpers_private_fail_test(char *message)
	{
		FAIL_TEST(message);
	}

	void test_helpers_private_pass_test(void)
	{
		TEST_EXIT;
	}

}
