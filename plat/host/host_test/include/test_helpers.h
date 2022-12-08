/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef TEST_HELPERS_H
#define TEST_HELPERS_H

/*
 * Defines whether we expect or not an assert to occur.
 *
 * Arguments:
 *	- expected: True if we are expecting assertion to happen.
 *		    False if we do not expect an assertion to happen.
 *	- check: If NULL and expected is True, it will consider any
 *		 assertion as valid. If not NULL, the assertion check
 *		 that failed must much the one on check to be considered
 *		 valid.
 *
 * If, during the execution of the test, an assertion happens and it is not
 * expected or the check fails, the current unittest with FAIL.
 *
 * Conversely, if an expected assertion happens, the test will FINISH and
 * will be marked as PASSED.
 *
 * NOTE: After an assertion, regardless of whether it was expected or
 * not, the next assertion will be considered unexpected and therefore the
 * test will fail. If we expect another assertion, then this API must be called
 * again to indicate that. It is recommended to setup the expected assert()
 * behavior during TEST_SETUP().
 *
 * NOTE2: If an assertion was expected but did not happen, the test will not
 * FAIL. In that case, the unittest must fail inmediately after the returning
 * from the call that was expected to assert.
 * See test_helper_fail_if_not_assertion()
 */
void test_helper_expect_assert_with_check(bool expected, char *check);

/*
 * Defines whether we expect or not an assert to occur.
 *
 * Arguments:
 *	- expected: True if we are expecting assertion to happen.
 *		    False if we do not expect an assertion to happen.
 *
 * If, during the execution of the test, an assertion happens and it is not
 * expected, the current unittest with FAIL.
 *
 * Conversely, if an expected assertion happens, the test will FINISH and
 * will be marked as PASSED.
 *
 * NOTE: After an assertion, regardless of whether it was expected or
 * not, the next assertion will be considered unexpected and therefore the
 * test will fail. If we expect another assertion, then this API must be called
 * again to indicate that. It is recommended to setup the expected assert()
 * behavior during TEST_SETUP().
 *
 * NOTE2: If an assertion was expected but did not happen, the test will not
 * FAIL. In that case, the unittest must fail inmediately after the returning
 * from the call that was expected to assert.
 * See test_helper_fail_if_not_assertion()
 */
void test_helper_expect_assert(bool expected);

/*
 * Call this function to fail a test if an expected assertion did not happen.
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
