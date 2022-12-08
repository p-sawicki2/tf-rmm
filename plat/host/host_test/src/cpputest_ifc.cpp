/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <CppUTest/TestHarness.h>

extern "C" {

	void cpputest_ifc_fail_test(char *message)
	{
		FAIL_TEST(message);
	}

	void cpputest_ifc_pass_test(void)
	{
		TEST_EXIT;
	}

}
