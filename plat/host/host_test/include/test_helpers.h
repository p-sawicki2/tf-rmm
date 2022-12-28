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
 * If, during the execution of the test, an assertion fails and it is not
 * expected or the check fails, the current unittest with FAIL.
 *
 * Conversely, if an expected assertion failure happens, the test will FINISH
 * and will be marked as PASSED.
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
 * immediately.
 * See test_helper_fail_if_not_assertion()
 */
void test_helper_expect_assert_fail_with_check(bool expected, char *check);

/*
 * Defines whether we expect or not an assert to fail.
 *
 * Arguments:
 *	- expected: True if we are expecting assertion to fail.
 *		    False if we do not expect an assertion to fail.
 *
 * If, during the execution of the test, an assertion fails and it is not
 * expected, the current unittest with FAIL.
 *
 * Conversely, if an expected assertion failure happens, the test will FINISH
 * and will be marked as PASSED.
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
 * immediately.
 * See test_helper_fail_if_not_assertion()
 */
void test_helper_expect_assert_fail(bool expected);

/*
 * Defines whether we expect or not for panic() to be called.
 *
 * Arguments:
 *	- expected: True if we are expecting panic() to be called.
 *		    False if we do not expect a panic() to be called.
 *
 * If, during the execution of the test, panic() is unexpectedly called,
 * the current unittest with FAIL.
 *
 * Conversely, if an expected call to panic() happens, the test will FINISH
 * and will be marked as PASSED.
 *
 * NOTE: After a panic() invocation, regardless of whether it was expected or
 * not, the next panic() call will be considered unexpected and therefore the
 * test will fail. If we expect panic() to be invoked again, then this API must
 * be invoked again to indicate that. It is recommended to setup the expected
 * panic() behavior during TEST_SETUP().
 *
 * NOTE2: If a panic() call was expected but did not happen, the test will not
 * FAIL. In that case, the unittest must fail inmediately after the returning
 * from the call that was expected to call panic().
 * See test_helper_fail_if_not_panic()
 */
void test_helper_expect_panic(bool expected);

/*
 * Call this function to fail a test if an expected assert fail did not happen.
 * This is preferred than fail with FAIL_TEST().
 */
void test_helper_fail_if_no_assert_failed(void);

/*
 * Call this function to fail a test if an expected call to panic() did not
 * happen. This is preferred than fail with FAIL_TEST().
 */
void test_helper_fail_if_no_panic(void);

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
