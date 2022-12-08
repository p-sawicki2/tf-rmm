/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef TEST_HELPERS_H
#define TEST_HELPERS_H

/*
 * Defines whether we expect or not an assert to fail.
 *
 * Arguments:
 *	- expected: True if we are expecting assertion to fail.
 *		    False if we do not expect an assertion to fail.
 *	- check: If NULL and expected is True, it will consider any
 *		 assertion failure as valid. If not NULL, the assertion check
 *		 that failed must match the one in check to be considered
 *		 valid.
 *
 * If, during the execution of the test, an assertion happens and it is not
 * expected or the check fails, the current unittest with FAIL.
 *
 * Conversely, if an expected assertion happens, the test will FINISH and
 * will be marked as PASSED.
 *
 * NOTE: After an assertion failure, regardless of whether it was expected or
 * not, the next assertion failure will be considered unexpected and
 * therefore the test will fail. If we expect another assertion to fail, then
 * this API must be called again to indicate that. It is recommended to setup
 * the expected assert() behavior during TEST_SETUP().
 *
 * NOTE2: If an assertion failure was expected but did not happen, it will
 * not cause the test to FAIL and therefore the test will continue. If no
 * other condition causes a test failure and the call that was expected to
 * cause the assert failure manages to return, the unittest must fail
 * inmediately.
 * See test_helper_fail_if_not_assertion()
 */
void test_helper_expect_assert_with_check(bool expected, char *check);

/*
 * Defines whether we expect or not an assert to fail.
 *
 * Arguments:
 *	- expected: True if we are expecting assertion to fail.
 *		    False if we do not expect an assertion to fail.
 *
 * If, during the execution of the test, an assertion happens and it is not
 * expected or the check fails, the current unittest with FAIL.
 *
 * Conversely, if an expected assertion happens, the test will FINISH and
 * will be marked as PASSED.
 *
 * NOTE: After an assertion failure, regardless of whether it was expected or
 * not, the next assertion failure will be considered unexpected and
 * therefore the test will fail. If we expect another assertion to fail, then
 * this API must be called again to indicate that. It is recommended to setup
 * the expected assert() behavior during TEST_SETUP().
 *
 * NOTE2: If an assertion failure was expected but did not happen, it will
 * not cause the test to FAIL and therefore the test will continue. If no
 * other condition causes a test failure and the call that was expected to
 * cause the assert failure manages to return, the unittest must fail
 * inmediately.
 * See test_helper_fail_if_not_assertion()
 */
void test_helper_expect_assert(bool expected);

/*
 * Call this function to fail a test if an expected assert fail did not happen.
 * This is preferred than fail with FAIL_TEST().
 */
void test_helper_fail_if_no_assertion(void);

/*
 * Helper function to fully initialize RMM.
 *
 * Args
 *	secondaries - If true, support for secondary PEs is enabled.
 */
void test_helper_rmm_start(bool secondaries);

/*
 * Helper function to get the total number of memory granules available
 * to the system.
 */
unsigned int test_helper_get_nr_granules(void);

#endif
