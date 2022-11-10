/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <CppUTest/CommandLineTestRunner.h>
#include <CppUTest/TestHarness.h>

extern "C" {
#include <buffer.h>
#include <buffer_private.h>
#include <cpuid.h>
#include <granule.h>	/* Interface to exercise */
#include <host_harness.h>
#include <host_utils.h>
#include <status.h>
#include <stdlib.h>
#include <string.h>
#include <test_helpers.h>
#include <time.h>
#include <unistd.h>
#include <utils_def.h>
}

/* Function to get a random value within [min, max] range. */
static inline int get_rand_in_range(int min, int max)
{
	return (rand() % (max - min + 1)) + min;
}

/*
 * Function to get a random address within the granules range.
 * The address will be aligned to granule size.
 */
static inline unsigned long get_rand_granule_addr(void) {
	unsigned long addr;
	int random_granule = get_rand_in_range(0,
					test_get_platform_nr_granules() - 1);

	addr = (unsigned long)(random_granule * GRANULE_SIZE)
						+ host_util_get_granule_base();

	return addr;
}

/*
 * Function to return a pointer to the first granule structure.
 * This function relays on add_to_granule() API to be validated.
 */
static inline struct granule *get_granule_struct(void)
{
	return addr_to_granule(host_util_get_granule_base());
}

TEST_GROUP(granule) {


	TEST_SETUP()
	{
		static int random_seed = 0;

		if (random_seed == 0) {
			/* Enable the platform with support for multiple PEs */
			test_platform_setup(true);
		}

		/* Make sure current cpu id is 0 (primary processor) */
		host_set_cpuid(0U);

		/* Initialize the random seed */
		while (random_seed == 0) {
			random_seed = (int)time(NULL);
			srand(random_seed);
		}

		/*
		 * Clean RMM's internal struct granule array
		 * to be sure tests start with a fresh copy.
		 */
		memset((void *)get_granule_struct(), 0,
			sizeof(struct granule) *
					test_get_platform_nr_granules());
	}

	TEST_TEARDOWN()
	{}
};

TEST(granule, addr_to_granule_TC1)
{
	struct granule *granule;
	struct granule *expected_granule = get_granule_struct();
	int granule_index = get_rand_in_range(0,
					test_get_platform_nr_granules() - 1);
	unsigned long addr = (granule_index * GRANULE_SIZE) +
						host_util_get_granule_base();

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Verify the granule address for a valid physical address.
	 ******************************************************************/
	expected_granule += granule_index; /* Expected granule address */
	granule = addr_to_granule(addr);
	POINTERS_EQUAL(expected_granule, granule);

	/*
	 * addr_to_granule() asserts if the addr is a NULL pointer, if the
	 * alignment is not correct or if the address is outside of the valid
	 * range, so skip these tests.
	 */
}

TEST(granule, granule_addr_TC1)
{
	struct granule *granule = get_granule_struct();
	int granule_index = get_rand_in_range(0,
					test_get_platform_nr_granules() - 1);
	unsigned long expected_address = (granule_index * GRANULE_SIZE) +
					  host_util_get_granule_base();
	unsigned long addr;

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Get a random granule and verify that the physical address
	 * returned by granule_addr() matches the manually calculated one.
	 ******************************************************************/
	granule += granule_index;
	addr = granule_addr(granule);
	POINTERS_EQUAL(expected_address, addr);

	/* Verify that not other parameters of the granule are altered */
	CHECK_EQUAL(0, granule->state);
	CHECK_EQUAL(0, granule->lock.val);

	/*
	 * granule_addr() asserts if the pointer to granule is NULL of if
	 * the granule index > NR_GRANULES, so skip these tests.
	 */
}

TEST(granule, granule_refcount_read_relaxed_TC1)
{
	struct granule *granule;
	unsigned long addr = get_rand_granule_addr();
	unsigned long val = (unsigned long)get_rand_in_range(10, INT_MAX);
	unsigned long read_val;

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Set the refcount for a granule manually and verify with
	 * granule_refcount_read_relaxed that the status is correct.
	 ******************************************************************/
	granule = addr_to_granule(addr);

	/* Set the refcount */
	granule->refcount = val;

	/* Read the value */
	read_val = granule_refcount_read_relaxed(granule);
	CHECK_EQUAL(val, read_val);

	/* Verify that not other parameters of the granule are altered */
	CHECK_EQUAL(0, granule->state);
	CHECK_EQUAL(0, granule->lock.val);

	/*
	 * granule_refcount_read_relaxed doesn't validate that the pointer
	 * to the granule is not NULL, so skip that test.
	 */
}

TEST(granule, granule_refcount_read_acquire_TC1)
{
	struct granule *granule;
	unsigned long addr = get_rand_granule_addr();
	unsigned long val = (unsigned long)get_rand_in_range(10, 10000);
	unsigned long read_val;

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Set the refcount for a granule manually and verify with
	 * granule_refcount_read_acquire that the status is correct.
	 ******************************************************************/
	granule = addr_to_granule(addr);

	/* Set the refcount */
	granule->refcount = val;

	/* Read the value */
	read_val = granule_refcount_read_acquire(granule);
	CHECK_EQUAL(val, read_val);

	/* Verify that not other parameters of the granule are altered */
	CHECK_EQUAL(0, granule->state);
	CHECK_EQUAL(0, granule->lock.val);

	/*
	 * granule_refcount_read_acquire doesn't validate that the pointer
	 * to the granule is not NULL, so skip that test.
	 */
}

TEST(granule, find_granule_TC1)
{
	struct granule *expected_granule = get_granule_struct();
	int granule_index = get_rand_in_range(0,
					test_get_platform_nr_granules() - 1);
	unsigned long address = (granule_index * GRANULE_SIZE) +
				 host_util_get_granule_base();
	struct granule *granule;

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Get a random granule and verify that its physical address
	 * matches the calculated one.
	 ******************************************************************/
	expected_granule += granule_index; /* Expected address */
	granule = find_granule(address);
	POINTERS_EQUAL(expected_granule, granule);

	/* Verify that not other parameters of the granule are altered */
	CHECK_TEXT(granule->state == 0, "Invalid granule state");
	CHECK_TEXT(granule->lock.val == 0, "Invalid granule lock status");
}


TEST(granule, find_granule_TC2)
{
	unsigned long address;
	struct granule *granule;

	/***************************************************************
	 * TEST CASE 2:
	 *
	 * Try to get a granule for an unaligned address.
	 ***************************************************************/
	address = get_rand_granule_addr();
	address += get_rand_in_range(1, GRANULE_SIZE - 1);
	granule = find_granule(address);
	POINTERS_EQUAL(NULL, granule);
}

TEST(granule, find_granule_TC3)
{
	unsigned long address;
	struct granule *granule;
	int granules_below = (int)(host_util_get_granule_base() /
							GRANULE_SIZE);

	/***************************************************************
	 * TEST CASE 3:
	 *
	 * Try to get a granule for an address outside the valid range.
	 ***************************************************************/
	address = (unsigned long)((get_rand_in_range(
					test_get_platform_nr_granules(),
					test_get_platform_nr_granules() + 10) *
								GRANULE_SIZE));
	address += host_util_get_granule_base();
	granule = find_granule(address);

	POINTERS_EQUAL(NULL, granule);

	if (granules_below > 0) {

		/* Try the lower boundary as well */
		address = host_util_get_granule_base();
		address -= (GRANULE_SIZE * get_rand_in_range(1,
							granules_below - 1));
		granule = find_granule(address);
		POINTERS_EQUAL(NULL, granule);
	}
}

TEST(granule, find_lock_two_granules_TC1)
{
	int g1_index, g2_index;
	struct granule *exp_g1, *exp_g2;
	struct granule *g1, *g2;
	unsigned long addr1, addr2;
	bool retval;

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Find and lock two valid granules, with valid expected states
	 * (GRANULE_STATE_NS).
	 ******************************************************************/

	/* Get random indexes for the granules */
	do {
		g1_index = get_rand_in_range(1, GRANULE_SIZE - 1);
		g2_index = get_rand_in_range(1, GRANULE_SIZE - 1);
	} while (g1_index == g2_index);

	/* Get the expected address for the granules */
	exp_g1 = get_granule_struct() + g1_index;
	exp_g2 = get_granule_struct() + g2_index;

	/* Get the expected PA for the corresponding granules */
	addr1 = (g1_index * GRANULE_SIZE) + host_util_get_granule_base();
	addr2 = (g2_index * GRANULE_SIZE) + host_util_get_granule_base();

	g1 = NULL;
	g2 = NULL;

	/* Lock the granules */
	retval = find_lock_two_granules(addr1, GRANULE_STATE_NS, &g1,
					addr2, GRANULE_STATE_NS, &g2);

	CHECK(retval);
	CHECK_FALSE(g1 == NULL);
	CHECK_FALSE(g2 == NULL);
	POINTERS_EQUAL(exp_g1, g1);
	POINTERS_EQUAL(exp_g2, g2);
	CHECK_FALSE(g1->lock.val == 0);
	CHECK_FALSE(g2->lock.val == 0);
	CHECK_EQUAL(GRANULE_STATE_NS, g1->state);
	CHECK_EQUAL(GRANULE_STATE_NS, g2->state);
}

TEST(granule, find_lock_two_granules_TC2)
{
	struct granule *g1, *g2;
	unsigned long addr;
	bool retval;

	/******************************************************************
	 * TEST CASE 2:
	 *
	 * Find and lock two valid granules, with valid expected states
	 * (GRANULE_STATE_NS). Both granules' addresses are the same.
	 ******************************************************************/

	addr = get_rand_granule_addr();
	g1 = NULL;
	g2 = NULL;

	/* Lock the granules */
	retval = find_lock_two_granules(addr, GRANULE_STATE_NS, &g1,
					addr, GRANULE_STATE_NS, &g2);

	CHECK_FALSE(retval);

	/* Check that the granule address are the same as before calling */
	POINTERS_EQUAL(NULL, g1);
	POINTERS_EQUAL(NULL, g2);
}

TEST(granule, find_lock_two_granules_TC3)
{
	struct granule *g1, *g2;
	unsigned long addr1, addr2, tmp_addr;
	bool retval;

	/******************************************************************
	 * TEST CASE 3:
	 *
	 * Find and lock two valid granules, one of them to a valid address
	 * and the other to a misaligned one.
	 *
	 * Try all possible valid, non-valid permutations.
	 ******************************************************************/

	/* Get random PAs for two different granules */
	do {
		addr1 = get_rand_granule_addr();
		addr2 = get_rand_granule_addr();
	} while (addr1 == addr2);

	g1 = NULL;
	g2 = NULL;

	/* Get a misaligned address */
	tmp_addr = addr2 + get_rand_in_range(1, GRANULE_SIZE - 1);

	retval = find_lock_two_granules(tmp_addr, GRANULE_STATE_NS, &g1,
					addr1, GRANULE_STATE_NS, &g2);

	CHECK_FALSE(retval);

	/* Check that the granule address are the same as before calling */
	POINTERS_EQUAL(NULL, g1);
	POINTERS_EQUAL(NULL, g2);

	retval = find_lock_two_granules(addr1, GRANULE_STATE_NS, &g1,
					tmp_addr, GRANULE_STATE_NS, &g2);

	CHECK_FALSE(retval);

	/* Check that the granule address are the same as before calling */
	POINTERS_EQUAL(NULL, g1);
	POINTERS_EQUAL(NULL, g2);
}

TEST(granule, find_lock_two_granules_TC4)
{
	struct granule *g1, *g2;
	unsigned long addr1, addr2, tmp_addr;
	bool retval;
	int granules_below = (int)(host_util_get_granule_base() /
							GRANULE_SIZE);

	/******************************************************************
	 * TEST CASE 4:
	 *
	 * Find and lock two valid granules, one of them to a valid address
	 * and the other to an out of range one.
	 *
	 * Try all possible valid, non-valid permutations.
	 ******************************************************************/

	/* Get random PAs for two different granules */
	do {
		addr1 = get_rand_granule_addr();
		addr2 = get_rand_granule_addr();
	} while (addr1 == addr2);

	g1 = NULL;
	g2 = NULL;

	tmp_addr = (unsigned long)((get_rand_in_range(
					test_get_platform_nr_granules(),
					test_get_platform_nr_granules() + 10) *
								GRANULE_SIZE));
	tmp_addr += host_util_get_granule_base();

	retval = find_lock_two_granules(tmp_addr, GRANULE_STATE_NS, &g1,
					addr2, GRANULE_STATE_NS, &g2);

	CHECK_FALSE(retval);

	/* Check that the granule address are the same as before calling */
	POINTERS_EQUAL(NULL, g1);
	POINTERS_EQUAL(NULL, g2);

	if (granules_below > 0) {

		/* Try the lower boundary as well */
		tmp_addr = host_util_get_granule_base();
		tmp_addr -= (GRANULE_SIZE * get_rand_in_range(1,
							granules_below - 1));

		retval = find_lock_two_granules(tmp_addr, GRANULE_STATE_NS,
					&g1, addr2, GRANULE_STATE_NS, &g2);

		CHECK_FALSE(retval);

		/* Check that the granule address are the same as before calling */
		POINTERS_EQUAL(NULL, g1);
		POINTERS_EQUAL(NULL, g2);
	}

	retval = find_lock_two_granules(addr1, GRANULE_STATE_NS, &g1,
					tmp_addr, GRANULE_STATE_NS, &g2);

	CHECK_FALSE(retval);

	/* Check that the granule address are the same as before calling */
	POINTERS_EQUAL(NULL, g1);
	POINTERS_EQUAL(NULL, g2);

	if (granules_below > 0) {

		/* Try the lower boundary as well */
		tmp_addr = host_util_get_granule_base();
		tmp_addr -= (GRANULE_SIZE * get_rand_in_range(1,
							granules_below - 1));

		retval = find_lock_two_granules(addr1, GRANULE_STATE_NS, &g1,
					tmp_addr, GRANULE_STATE_NS, &g2);

		CHECK_FALSE(retval);

		/* Check that the granule address are the same as before calling */
		POINTERS_EQUAL(NULL, g1);
		POINTERS_EQUAL(NULL, g2);
	}
}

TEST(granule, find_lock_two_granules_TC5)
{
	struct granule *g1, *g2;
	unsigned long addr1, addr2;
	bool retval;

	/******************************************************************
	 * TEST CASE 5:
	 *
	 * Try to find and lock the granules for two valid addresses
	 * with an incorrect expected granule state.
	 *
	 * Try all possible non valid state combinations.
	 ******************************************************************/

	/* Get random PAs for two different granules */
	do {
		addr1 = get_rand_granule_addr();
		addr2 = get_rand_granule_addr();
	} while (addr1 == addr2);

	g1 = NULL;
	g2 = NULL;

	for(unsigned int state1 = GRANULE_STATE_NS;
	    state1 <= GRANULE_STATE_LAST; state1++) {

		for(unsigned int state2 = GRANULE_STATE_NS;
		    state2 <= GRANULE_STATE_LAST; state2++) {
			if(state1 == GRANULE_STATE_NS &&
			   state2 == GRANULE_STATE_NS) {
				/* Skip. Test case already checked. */
				continue;
			}
			retval = find_lock_two_granules(addr1,
					(enum granule_state)state1, &g1,
					addr2, (enum granule_state)state2, &g2);

			CHECK_FALSE(retval);

			/*
			 * Check that the granule address are the same
			 * as before calling
			 */
			POINTERS_EQUAL(NULL, g1);
			POINTERS_EQUAL(NULL, g2);
		} /* granule 2 state. */
	} /* granule 1 state. */

	/*
	 * find_lock_two_granules() will assert if any of the references
	 * to the granule pointers passed as arguments is NULL, so skip that
	 * testcase.
	 */
}

TEST(granule, find_lock_granule_TC1)
{
	struct granule *granule;
	unsigned long addr;

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Find and lock a random granule and verify that it is on the
	 * right state (granules should be in GRANULE_STATE_NS) by default
	 ******************************************************************/
	addr = get_rand_granule_addr();
	granule = find_lock_granule(addr, GRANULE_STATE_NS);
	CHECK_FALSE(granule == NULL);
	CHECK_FALSE(granule->lock.val == 0);
}

TEST(granule, find_lock_granule_TC2)
{
	struct granule *granule;
	unsigned long addr;

	/***************************************************************
	 * TEST CASE 2:
	 *
	 * Try to find and lock a random granule to all possible
	 * possible unexpected states.
	 ***************************************************************/
	addr = get_rand_granule_addr();
	for(unsigned int state = GRANULE_STATE_DELEGATED;
	    state <= GRANULE_STATE_LAST; state++)
	{
		granule = find_lock_granule(addr,
					    (enum granule_state)state);
		POINTERS_EQUAL(NULL, granule);
	}
}

TEST(granule, find_lock_granule_TC3)
{
	struct granule *granule;
	unsigned long addr;

	/***************************************************************
	 * TEST CASE 3:
	 *
	 * Try to find and lock a granule for a misaligned address
	 * to all possible states.
	 ***************************************************************/
	addr = get_rand_granule_addr();
	addr += get_rand_in_range(1, GRANULE_SIZE - 1);
	for(unsigned int state = GRANULE_STATE_NS;
	    state <= GRANULE_STATE_LAST; state++)
	{
		granule = find_lock_granule(addr,
					    (enum granule_state)state);
		POINTERS_EQUAL(NULL, granule);
	}
}

TEST(granule, find_lock_granule_TC4)
{
	struct granule *granule;
	unsigned long addr;
	int granules_below = (int)(host_util_get_granule_base() /
							GRANULE_SIZE);

	/***************************************************************
	 * TEST CASE 4:
	 *
	 * Try to find and lock a granule for an address outside the
	 * valid range to all possible states.
	 ***************************************************************/
	addr = (unsigned long)((get_rand_in_range(
					test_get_platform_nr_granules(),
					test_get_platform_nr_granules() + 10) *
								GRANULE_SIZE));
	addr += host_util_get_granule_base();

	for(unsigned int state = GRANULE_STATE_NS;
	    state <= GRANULE_STATE_LAST; state++)
	{
		granule = find_lock_granule(addr,
					    (enum granule_state)state);
		POINTERS_EQUAL(NULL, granule);

		if (granules_below > 0) {

			/* Try the lower boundary as well */
			addr = host_util_get_granule_base();
			addr -= (GRANULE_SIZE * get_rand_in_range(1,
							granules_below - 1));
			granule = find_lock_granule(addr,
						    (enum granule_state)state);
			POINTERS_EQUAL(NULL, granule);
		}
	}
}

TEST(granule, granule_lock_TC1)
{
	struct granule *granule;
	unsigned long addr;

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Get a random granule and set it to a specific state. Then lock
	 * it. Repeat for every possible state.
	 ******************************************************************/
	granule = addr_to_granule(get_rand_granule_addr());

	for (unsigned int state = GRANULE_STATE_NS;
	     state <= GRANULE_STATE_LAST; state++) {

		/* Ensure the granule is unlocked */
		granule_unlock(granule);

		/* Set the granule state */
		granule_set_state(granule, (enum granule_state)state);

		/* Lock the granule */
		granule_lock(granule, (enum granule_state)state);
		CHECK_FALSE(granule->lock.val == 0);
	}

	/*
	 * granule_lock() implementation expects to always
	 * receive a valid granule hence it doesn't make any checks
	 * to ensure the correctness of the granule. Therefore, skip any tests
	 * with invalid granules.
	 *
	 * In addition to that, granule_lock() also expects:
	 * 	* That the expected state belongs to enum granule_state,
	 * 	  so it doesn't perform any checks on that either.
	 *	* That we are certain of the type of granule we want to lock
	 *	  so it will assert if the new state is incorrect.
	 */
}

TEST(granule, granule_lock_on_state_match_TC1)
{
	struct granule *granule;

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Get a random granule and set it to a specific state. Then lock
	 * it. Repeat for every possible state.
	 ******************************************************************/
	granule = addr_to_granule(get_rand_granule_addr());

	for (unsigned int state = GRANULE_STATE_NS;
	     state <= GRANULE_STATE_LAST; state++) {
		bool retval;

		/* Ensure the granule is unlocked */
		granule_unlock(granule);

		/* Set the granule state */
		granule_set_state(granule, (enum granule_state)state);

		/* Lock the granule */
		retval = granule_lock_on_state_match(granule,
						(enum granule_state)state);
		CHECK(retval);
		CHECK_FALSE(granule->lock.val == 0);
	}
}

TEST(granule, granule_lock_on_state_match_TC2)
{
	struct granule *granule;

	/***************************************************************
	 * TEST CASE 2:
	 *
	 * Get a random granule and for all possible states, try
	 * to lock with all possible states other than the actual
	 * one on the granule
	 ***************************************************************/
	granule = addr_to_granule(get_rand_granule_addr());

	for (unsigned int state = GRANULE_STATE_NS;
	     state <= GRANULE_STATE_LAST; state++) {
		/* Set the granule state */
		granule_set_state(granule, (enum granule_state)state);

		for (unsigned int lock_state = GRANULE_STATE_NS;
		     lock_state <= GRANULE_STATE_LAST; lock_state++) {
			bool retval;

			if (lock_state == state) {
				/* skip this case. Already tested */
				continue;
			}

			/* Lock the granule */
			retval = granule_lock_on_state_match(granule,
					(enum granule_state)lock_state);
			CHECK_FALSE(retval);
			CHECK_EQUAL(0, granule->lock.val);
		}
	}

	/*
	 * granule_lock_on_state_match() implementation expects to always
	 * receive a valid granule hence it doesn't make any checks
	 * to ensure the correctness of the granule. Therefore, skip any tests
	 * with invalid granules.
	 *
	 * Likewise, it also expects that the next state belongs to
	 * enum granule_state, so it doesn't perform any checks on that either.
	 */
}

TEST(granule, granule_set_get_state_TC1)
{
	struct granule *granule;
	unsigned long addr;

	/***************************************************************
	 * TEST CASE 1:
	 *
	 * Find a random granule and transition it through all possible
	 * states. Then check that the states are correct.
	 ***************************************************************/
	addr = get_rand_granule_addr();

	for (unsigned int state = GRANULE_STATE_NS;
	     state <= GRANULE_STATE_LAST;
	     state++) {
		unsigned int next_state = (state + 1) %
					((int)GRANULE_STATE_LAST + 1);

		/* Find and lock a granule */
		granule = find_lock_granule(addr, (enum granule_state)state);

		/* Change the granule state */
		granule_set_state(granule, (enum granule_state)next_state);

		/* Check that the state is correct */
		CHECK_EQUAL(next_state, granule_get_state(granule));

		/* The granule must still be locked from find_lock_granule() */
		CHECK_EQUAL(1, granule->lock.val);
	}

	/*
	 * granule_{set, get}_state() implementation expects to always
	 * receive a valid granule and therefore it doesn't make any checks
	 * to ensure the correctness of the granule. Therefore, skip any tests
	 * with invalid granules.
	 *
	 * Likewise, it also expects that the next state belongs to
	 * enum granule_state, so it doesn't perform any checks on that either.
	 */
}

TEST(granule, granule_unlock_TC1)
{
	struct granule *granule;
	unsigned long addr;

	/***************************************************************
	 * TEST CASE 1:
	 *
	 * Find and lock a random granule, then unlock it.
	 * Iterate over all possible states, making sure it can be
	 * unlocked regardless of the state and that this doesn't change.
	 ***************************************************************/
	addr = get_rand_granule_addr();

	for (unsigned int state = GRANULE_STATE_NS;
	     state <= GRANULE_STATE_LAST;
	     state++) {

		/* Find and lock a granule */
		granule = find_lock_granule(addr, GRANULE_STATE_NS);

		/* Change the state of the granule */
		granule_set_state(granule, (enum granule_state)state);

		/* Unlock the granule */
		granule_unlock(granule);

		/* Check that the state is correct */
		CHECK_EQUAL(state, granule_get_state(granule));

		/* The granule must still be locked from find_lock_granule() */
		CHECK_EQUAL(0, granule->lock.val);

		/* Leave the granule in a known state for the next iteration */
		granule_set_state(granule, GRANULE_STATE_NS);
	}

	/*
	 * granule_unlock() implementation expects to always
	 * receive a valid granule and therefore it doesn't make any checks
	 * to ensure the correctness of the granule. Therefore, skip any tests
	 * with invalid granules.
	 */
}

TEST(granule, granule_unlock_transition_TC1)
{
	struct granule *granule;
	unsigned long addr;

	/***************************************************************
	 * TEST CASE 1:
	 *
	 * Find a random granule and transition it through all possible
	 * states.
	 ***************************************************************/
	addr = get_rand_granule_addr();

	for (unsigned int state = GRANULE_STATE_NS;
	     state <= GRANULE_STATE_LAST;
	     state++) {
		unsigned int next_state = (state + 1) %
					((int)GRANULE_STATE_LAST + 1);

		/* Find and lock a granule */
		granule = find_lock_granule(addr, (enum granule_state)state);

		/* Unlock the granule changing its state */
		granule_unlock_transition(granule,
					  (enum granule_state)next_state);

		/* Check that the state is correct */
		CHECK_EQUAL(next_state, granule_get_state(granule));
		CHECK_EQUAL(0, granule->lock.val);
	}

	/*
	 * granule_unlock_transition() implementation expects to always
	 * receive a valid granule and therefore it doesn't make any checks
	 * to ensure the correctness of the granule. Therefore, skip any tests
	 * with invalid granules.
	 *
	 * Likewise, it also expects that the next state belongs to
	 * enum granule_state, so it doesn't perform any checks on that either.
	 */
}

TEST(granule, granule_get_TC1)
{
	unsigned long address = get_rand_granule_addr();
	struct granule *granule = find_granule(address);

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Increase the refcount of a granule by invoking __granule_get().
	 * The refcount before the call is expected to be 0.
	 ******************************************************************/
	__granule_get(granule);

	CHECK_EQUAL(1UL, granule->refcount);

	/* Verify that not other parameters of the granule are altered */
	CHECK_EQUAL(0, granule->state);
	CHECK_EQUAL(0, granule->lock.val);

	/*
	 * __granule_get() doesn't make any check to validate the granule
	 * pointer passed, so skip the testcase for NULL pointer.
	 */
}

TEST(granule, granule_put_TC1)
{
	unsigned long address = get_rand_granule_addr();
	struct granule *granule = find_granule(address);

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Increase the refcount of a granule by invoking __granule_get(),
	 * then decrease it again with __granule_put().
	 *
	 * The refcount before the test starts is expected to be 0.
	 ******************************************************************/
	__granule_get(granule);
	__granule_put(granule);

	CHECK_EQUAL(0UL, granule->refcount);

	/* Verify that not other parameters of the granule are altered */
	CHECK_EQUAL(0, granule->state);
	CHECK_EQUAL(0, granule->lock.val);
}

TEST(granule, granule_put_TC2)
{
	unsigned long address = get_rand_granule_addr();
	struct granule *granule = find_granule(address);
	unsigned int get_count;

	/******************************************************************
	 * TEST CASE 2:
	 *
	 * Increase the refcount of a granule by invoking __granule_get()
	 * a random number of times, then decrease it again with
	 * __granule_put() only once.
	 *
	 * The refcount before the test starts is expected to be 0.
	 ******************************************************************/
	get_count = (unsigned int)get_rand_in_range(10, 1000);
	for (unsigned int i = 0; i < get_count; i++) {
		__granule_get(granule);
	}
	__granule_put(granule);

	LONGS_EQUAL((get_count - 1UL), granule->refcount);

	/* Verify that not other parameters of the granule are altered */
	CHECK_EQUAL(0, granule->state);
	CHECK_EQUAL(0, granule->lock.val);

	/*
	 * __granule_put() doesn't make any check to validate the granule
	 * pointer passed, so skip the testcase for NULL pointer.
	 */
}

TEST(granule, granule_refcount_inc_TC1)
{
	unsigned long address = get_rand_granule_addr();
	struct granule *granule = find_granule(address);
	unsigned long val = (unsigned long)get_rand_in_range(1, INT_MAX);

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Increase the refcount of a granule by invoking __granule_inc().
	 * The refcount before the call is expected to be 0.
	 ******************************************************************/
	__granule_refcount_inc(granule, val);

	CHECK_EQUAL(val, granule->refcount);

	/* Verify that not other parameters of the granule are altered */
	CHECK_EQUAL(0, granule->state);
	CHECK_EQUAL(0 ,granule->lock.val);

	/*
	 * __granule_refcount_inc() doesn't make any check to validate
	 * the granule pointer passed, so skip the testcase for NULL pointer.
	 */
}

TEST(granule, granule_refcount_dec_TC1)
{
	unsigned long address = get_rand_granule_addr();
	struct granule *granule = find_granule(address);
	unsigned long val = (unsigned long)get_rand_in_range(10, INT_MAX);

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Increase the refcount of a granule by invoking
	 * __granule_refcount_inc(), then decrease it again with
	 * __granule_refcount_dec().
	 *
	 * The refcount before the test starts is expected to be 0.
	 ******************************************************************/
	__granule_refcount_inc(granule, val);
	__granule_refcount_dec(granule, val);

	LONGS_EQUAL(0, granule->refcount);

	/* Verify that not other parameters of the granule are altered */
	CHECK_EQUAL(0, granule->state);
	CHECK_EQUAL(0, granule->lock.val);
}

TEST(granule, granule_refcount_dec_TC2)
{
	unsigned long address = get_rand_granule_addr();
	struct granule *granule = find_granule(address);
	unsigned long val = (unsigned long)get_rand_in_range(10, INT_MAX);

	/******************************************************************
	 * TEST CASE 2:
	 *
	 * Increase the refcount of a granule by invoking
	 * __granule_refcount_inc(), then decrease it again with
	 * __granule_refcount_dec() but using a lower value than the one
	 * used for inc.
	 *
	 * The refcount before the test starts is expected to be 0.
	 ******************************************************************/
	__granule_refcount_inc(granule, val);
	__granule_refcount_dec(granule, val - 1UL);

	LONGS_EQUAL(1, granule->refcount);

	/* Verify that not other parameters of the granule are altered */
	CHECK_EQUAL(0, granule->state);
	CHECK_EQUAL(0, granule->lock.val);

	/*
	 * __granule_refcount_dec() doesn't make any check to validate
	 * the granule pointer passed, so skip the testcase for NULL pointer.
	 *
	 * It also asserts in case the granule refcount is lower than the val
	 * passed, so skip this test too.
	 */
}

TEST(granule, atomic_granule_get_TC1)
{
	unsigned long address = get_rand_granule_addr();
	struct granule *granule = find_granule(address);

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Increase the refcount of a granule by invoking
	 * atomic_granule_get().
	 * The refcount before the call is expected to be 0.
	 ******************************************************************/
	atomic_granule_get(granule);

	LONGS_EQUAL(1, granule->refcount);

	/* Verify that not other parameters of the granule are altered */
	CHECK_EQUAL(0, granule->state);
	CHECK_EQUAL(0, granule->lock.val);

	/*
	 * atomic_granule_get doesn't make any check to validate the granule
	 * pointer passed, so skip the testcase for NULL pointer.
	 */
}

TEST(granule, atomic_granule_put_TC1)
{
	unsigned long address = get_rand_granule_addr();
	struct granule *granule = find_granule(address);

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Increase the refcount of a granule by invoking atomic_granule_get,
	 * then decrease it again with atomic_granule_put().
	 *
	 * The refcount before the test starts is expected to be 0.
	 ******************************************************************/
	atomic_granule_get(granule);
	atomic_granule_put(granule);

	LONGS_EQUAL(0, granule->refcount);

	/* Verify that not other parameters of the granule are altered */
	CHECK_EQUAL(0, granule->state);
	CHECK_EQUAL(0, granule->lock.val);
}

TEST(granule, atomic_granule_put_TC2)
{
	unsigned long address = get_rand_granule_addr();
	struct granule *granule = find_granule(address);
	unsigned int get_count;

	/******************************************************************
	 * TEST CASE 2:
	 *
	 * Increase the refcount of a granule by invoking atomic_granule_get()
	 * a random number of times, then decrease it again with
	 * atomic_granule_put() only once.
	 *
	 * The refcount before the test starts is expected to be 0.
	 ******************************************************************/
	get_count = (unsigned int)get_rand_in_range(10, 1000);
	for (unsigned int i = 0; i < get_count; i++) {
		atomic_granule_get(granule);
	}
	atomic_granule_put(granule);

	LONGS_EQUAL((get_count - 1UL), granule->refcount);

	/* Verify that not other parameters of the granule are altered */
	CHECK_EQUAL(0, granule->state);
	CHECK_EQUAL(0, granule->lock.val);

	/*
	 * atomic_granule_put() doesn't make any check to validate the granule
	 * pointer passed, so skip the testcase for NULL pointer.
	 */
}

TEST(granule, atomic_granule_put_release_TC1)
{
	unsigned long address = get_rand_granule_addr();
	struct granule *granule = find_granule(address);

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Increase the refcount of a granule by invoking atomic_granule_get,
	 * then decrease it again with atomic_granule_put_release().
	 *
	 * The refcount before the test starts is expected to be 0.
	 ******************************************************************/
	atomic_granule_get(granule);
	atomic_granule_put_release(granule);

	LONGS_EQUAL(0, granule->refcount);

	/* Verify that not other parameters of the granule are altered */
	CHECK_EQUAL(0, granule->state);
	CHECK_EQUAL(0, granule->lock.val);
}

TEST(granule, atomic_granule_put_release_TC2)
{
	unsigned long address = get_rand_granule_addr();
	struct granule *granule = find_granule(address);
	unsigned int get_count;

	/******************************************************************
	 * TEST CASE 2:
	 *
	 * Increase the refcount of a granule by invoking atomic_granule_get()
	 * a random number of times, then decrease it again
	 * with atomic_granule_put_releae() only once.
	 *
	 * The refcount before the test starts is expected to be 0.
	 ******************************************************************/
	get_count = (unsigned int)get_rand_in_range(10, 1000);
	for (unsigned int i = 0; i < get_count; i++) {
		atomic_granule_get(granule);
	}
	atomic_granule_put_release(granule);

	LONGS_EQUAL((get_count - 1UL), granule->refcount);

	/* Verify that not other parameters of the granule are altered */
	CHECK_EQUAL(0, granule->state);
	CHECK_EQUAL(0, granule->lock.val);

	/*
	 * atomic_granule_put_release() doesn't make any check to validate
	 * the granule pointer passed, so skip the testcase for NULL pointer.
	 *
	 * Also, if refcount reaches a value < 0, atomic_granule_put_release()
	 * will assert, so skip this test too.
	 */
}

TEST(granule, find_lock_unused_granule_TC1)
{
	struct granule *granule;
	unsigned long addr;

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Find and lock an unused random granule and verify that it is on
	 * the right state (granules should be in GRANULE_STATE_DELEGATED)
	 * by default, as well as refcount and lock status.
	 ******************************************************************/
	addr = get_rand_granule_addr();

	/* Find and lock the granule */
	granule = find_lock_granule(addr, GRANULE_STATE_NS);

	/* Change status to avoid assertions on invariants checks */
	granule->state = GRANULE_STATE_RD;

	granule = NULL;
	granule = find_lock_unused_granule(addr, GRANULE_STATE_RD);

	CHECK_FALSE(granule == NULL);
	CHECK_FALSE(granule == (struct granule *)status_ptr(RMI_ERROR_INPUT));
	CHECK_FALSE(granule == (struct granule *)status_ptr(RMI_ERROR_IN_USE));
	CHECK_FALSE(granule->lock.val == 0UL);
	LONGS_EQUAL(0, granule->refcount);
}

TEST(granule, find_lock_unused_granule_TC2)
{
	struct granule *granule;
	unsigned long addr;

	/***************************************************************
	 * TEST CASE 2:
	 *
	 * Try to find and lock an unused granule with the wrong
	 * expected state.
	 ***************************************************************/

	addr = get_rand_granule_addr();
	granule = find_granule(addr);

	/*
	 * Start the test with a granule in the same state as at the
	 * end of the previous test
	 */
	granule_set_state(granule, GRANULE_STATE_RD);

	for(unsigned int state = GRANULE_STATE_NS;
	    state <= GRANULE_STATE_LAST; state++)
	{
		if (state == GRANULE_STATE_RD) {
			/* Case already tested on TC1 */
			continue;
		}

		granule = find_lock_unused_granule(addr,
						   (enum granule_state)state);

		POINTERS_EQUAL(status_ptr(RMI_ERROR_INPUT), granule);
	}
}

TEST(granule, find_lock_unused_granule_TC3)
{
	struct granule *granule;
	unsigned long addr;

	/***************************************************************
	 * TEST CASE 3:
	 *
	 * Try to find and lock an used granule.
	 ***************************************************************/

	/*
	 * Increase the refcount of the current granule to mark it
	 * as used.
	 */
	addr = get_rand_granule_addr();
	granule = addr_to_granule(addr);
	granule->refcount = 10UL;
	granule_set_state(granule, GRANULE_STATE_RD);

	granule = find_lock_unused_granule(addr, GRANULE_STATE_RD);

	POINTERS_EQUAL(status_ptr(RMI_ERROR_IN_USE), granule);
}

TEST(granule, find_lock_unused_granule_TC4)
{
	struct granule *granule;
	unsigned long addr;

	/***************************************************************
	 * TEST CASE 4:
	 *
	 * Try to find and lock a granule for a misaligned address.
	 ***************************************************************/
	addr = get_rand_granule_addr();
	addr += get_rand_in_range(1, GRANULE_SIZE - 1);
	granule = find_lock_unused_granule(addr, GRANULE_STATE_NS);

	POINTERS_EQUAL(status_ptr(RMI_ERROR_INPUT), granule);
}

TEST(granule, find_lock_unused_granule_TC5)
{
	struct granule *granule;
	unsigned long addr;

	/***************************************************************
	 * TEST CASE 5:
	 *
	 * Try to find and lock a granule for an address outside the
	 * valid range.
	 ***************************************************************/
	addr = host_util_get_granule_base();
	addr += (unsigned long)((get_rand_in_range(
					test_get_platform_nr_granules(),
					test_get_platform_nr_granules() + 10) *
								GRANULE_SIZE));

	granule = find_lock_unused_granule(addr, GRANULE_STATE_NS);

	POINTERS_EQUAL(status_ptr(RMI_ERROR_INPUT), granule);
}

TEST(granule, granule_memzero_TC1)
{
	unsigned long addr = get_rand_granule_addr();
	struct granule *granule = addr_to_granule(addr);
	int *val = (int *)addr;

	/***************************************************************
	 * TEST CASE 1:
	 *
	 * Map a random granule to every possible slot type and memzero
	 * it. Verify then that the whole slot buffer is all 0.
	 * Repeat the operation on all possible CPUs.
	 *
	 * NOTE: granule_memzero() will fail with SLOT_NS, so skip that
	 * 	 testcase.
	 ***************************************************************/
	for (unsigned int i = 0U; i < MAX_CPUS; i++) {
		/* Configure the cpu id */
		host_set_cpuid(i);

		for (unsigned int j = 0; j < NR_CPU_SLOTS; j++) {
			if (j == SLOT_NS) {
				/* Not supported by granule_memzero */
				continue;
			}

			/* Initialize the granule with random data */
			memset((void *)addr, get_rand_in_range(1, INT_MAX),
								GRANULE_SIZE);
			granule_memzero(granule, (enum buffer_slot)j);

			for (unsigned int k = 0;
			     k < (GRANULE_SIZE / sizeof(int)); k++) {
				if (*(val + k) != 0) {
					FAIL_TEST("Memory not properly zeroed");
				}
			}
		}
	}

	/*
	 * granule_memzero() asserts if the granule is NULL, so skip this
	 * testcase.
	 */
}

TEST(granule, granule_memzero_mapped_TC1)
{
	/*
	 * Current implementation for granule_memzero_mapped()
	 * is a wrapper for memset, so skip this test for now.
	 */
}
