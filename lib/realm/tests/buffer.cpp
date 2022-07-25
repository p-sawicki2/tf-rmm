/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <CppUTest/CommandLineTestRunner.h>
#include <CppUTest/TestHarness.h>

extern "C" {
#include <buffer.h>	/* Interface to exercise */
#include <buffer_private.h>
#include <cpuid.h>
#include <granule.h>
#include <host_harness.h>
#include <host_utils.h>
#include <realm_test_utils.h>
#include <stdlib.h>
#include <string.h>
#include <test_helpers.h>
#include <time.h>
#include <xlat_tables.h>
}

/*
 * Function to get a random address within the granules range.
 * The address will be aligned to granule size.
 */
static inline uintptr_t get_rand_granule_addr(void) {
	uintptr_t addr;
	int random_granule = test_util_get_rand_in_range(0,
					test_helper_get_nr_granules() - 1);

	addr = (uintptr_t)(random_granule * GRANULE_SIZE)
					+ host_util_get_granule_base();

	return addr;
}

/*
 * Helper function to generate an array of random granule addresses
 * in which none of them repeat.
 */
static void get_rand_granule_array(uintptr_t *arr, unsigned int count)
{
	for (unsigned int i = 0U; i < count; i++) {
		arr[i] = get_rand_granule_addr();
		if (i > 0U) {
			while (arr[i - 1U] == arr[i]) {
				arr[i] = get_rand_granule_addr();
			}
		}
	}

}

TEST_GROUP(slot_buffer) {
	/*
	 * For this test, TEST_SETUP() initializes RMM which includes
	 * translation table and slot buffer mechanism initialization.
	 * Therefore, all the tests assume that the slot buffer mechanism
	 * has been properly initialized.
	 */
	TEST_SETUP()
	{
		static int random_seed = 0;

		/* Enable the platform with support for multiple PEs */
		test_helper_rmm_start(true);

		/* Make sure current cpu id is 0 (primary processor) */
		host_util_set_cpuid(0U);

		/* Initialize the random seed */
		while (random_seed == 0) {
			random_seed = (int)time(NULL);
			srand(random_seed);
		}
	}

	TEST_TEARDOWN()
	{}
};

TEST(slot_buffer, granule_map_buffer_unmap_TC1)
{
	uintptr_t slot_va, expected_va, granule_addr;
	struct granule *granule;

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * For all possible slot buffer types and all possible CPUs, try to
	 * map a random granule. Then unmap it.
	 ******************************************************************/
	granule_addr = get_rand_granule_addr();
	granule = addr_to_granule(granule_addr);

	for (unsigned int i = 0U; i < MAX_CPUS; i++) {
		host_util_set_cpuid(i);
		for (unsigned int j = 0U; j < NR_CPU_SLOTS; j++) {
			if (j == SLOT_NS) {
				/* Not supported. granule_map() would assert */
				continue;
			}
			slot_va = (uintptr_t)granule_map(granule,
							 (enum buffer_slot)j);
			expected_va = test_util_slot_to_expected_va((enum buffer_slot)j);

			/* Test the return value from granule_map() */
			POINTERS_EQUAL(granule_addr, slot_va);

			/*
			 * Test that the granule is actually mapped to the
			 * expected VA as per aarch64 build.
			 */
			POINTERS_EQUAL(expected_va,
				       test_util_get_slot_va_from_pa(slot_va, NULL));

			/* Unmap the buffer */
			buffer_unmap((void *)slot_va);

			/*
			 * test_util_get_slot_va_from_pa() return NULL if the address
			 * passed to it is not mapped to any slot buffer.
			 */
			POINTERS_EQUAL(NULL,
				       test_util_get_slot_va_from_pa(granule_addr, NULL));

		} /* For each slot type */
	} /* For each CPU */
}

TEST(slot_buffer, granule_map_buffer_unmap_TC2)
{
	uintptr_t mapped_pa;
	struct granule *granule;
	uintptr_t granules_per_cpu[MAX_CPUS];

	/******************************************************************
	 * TEST CASE 2:
	 *
	 * For each possible slot buffer type, map a different random
	 * granule to each one of the available CPUs. Then validate that
	 * the same PA is not mapped to two different CPUs.
	 ******************************************************************/
	get_rand_granule_array(granules_per_cpu, MAX_CPUS);
	for (unsigned int i = 0U; i < NR_CPU_SLOTS; i++) {
		if (i == SLOT_NS) {
			/* Not supported. granule_map() would assert */
			continue;
		}

		/* Map a granule on each CPU for the same slot */
		for (unsigned int j = 0U; j < MAX_CPUS; j++) {
			host_util_set_cpuid(j);
			granule = addr_to_granule(granules_per_cpu[j]);
			(void)granule_map(granule, (enum buffer_slot)i);
		}

		/*
		 * Iterate over all CPUs, ensuring that the granules are mapped
		 * into the slots for the right CPU.
		 */
		for (unsigned int j = 0U; j < MAX_CPUS; j++) {
			/*
			 * Get the PA mapped to the slot 'i' for CPU 'j'
			 */
			host_util_set_cpuid(j);
			mapped_pa = test_util_slot_to_pa((enum buffer_slot)i, NULL);

			/*
			 * Check that the PA mapped to slot 'i' for CPU 'j'
			 * is only mapped on the same slot for the same CPU.
			 * For the rest of CPUs, the PAs should not match.
			 */
			for (unsigned int k = 0U; k < MAX_CPUS; k++) {
				if (j == k) {
					POINTERS_EQUAL(granules_per_cpu[k],
						       mapped_pa);
				} else {
					CHECK_FALSE(granules_per_cpu[k] ==
						    mapped_pa);
				}
			}

		}

		/* Unmap the granules */
		for (unsigned int j = 0U; j < MAX_CPUS; j++) {
			host_util_set_cpuid(j);
			buffer_unmap((void *)granules_per_cpu[j]);
		}
	} /* NR_CPU_SLOTS */

	/*
	 * granule_map() asserts if the granule address is not aligned, so
	 * skip that test.
	 *
	 * buffer_unmap() exists gracefully if passed an incorrect granule
	 * address or an unmapped one, so skip that test too.
	 */
};

TEST(slot_buffer, ns_buffer_write_TC1)
{
	uintptr_t granule_addrs[4];
	struct granule *granule[2];
	unsigned int block;
	uintptr_t test_block;

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * For each CPU, map a random granule to NS_SLOT and copy random
	 * data into it with a random offset. Then verify that the data
	 * has been properly copied.
	 ******************************************************************/

	/*
	 * Get two random granules:
	 * granule_addrs[0]: To be used for write operations (SLOT_NS).
	 * granule_addrs[1]: will hold a copy of the data to transfer, so we
	 *		     can verify later.
	 */
	get_rand_granule_array(granule_addrs, 2U);

	/*
	 * Generate random data to copy
	 * We will only copy 1KB blocks. Clean the second 1KB block.
	 */
	for (unsigned int i = 0U; i < 1024U/sizeof(int); i++) {
		*((int *)granule_addrs[1] + i) = rand();
	}
	(void)memset((void *)(granule_addrs[1] + 1024U), 0, (size_t)1024);

	granule[0] = addr_to_granule(granule_addrs[0]);

	for (unsigned int i = 0U; i < MAX_CPUS; i++) {
		/* Clean the granule to test */
		(void)memset((void *)granule_addrs[0], 0, GRANULE_SIZE);

		host_util_set_cpuid(i);

		/*
		 * Select a random 1KB block within the granule and
		 * write data to it.
		 */
		block = (unsigned int)test_util_get_rand_in_range(0, 3);
		ns_buffer_write(SLOT_NS, granule[0], 1024U * block,
				1024U, (void*)granule_addrs[1]);

		/*
		 * Verify the data. We verify that we copied into the right
		 * random 1KB block and also that the rest of blocks in the
		 * granule were left untouched.
		 */
		for (unsigned int j = 0U; j < 4U; j++) {
			/*
			 * Select whether we check against the copied data
			 * or against a clean 1KB block
			 */
			test_block = granule_addrs[1];
			if (j != block) {
				/* Offset for a clean block to compare against */
				test_block += 1024U;
			}

			MEMCMP_EQUAL((void *)test_block,
				     (void *)(granule_addrs[0] + (1024U * j)),
				     (size_t)1024);
		}
	}
}

TEST(slot_buffer, ns_buffer_write_TC2)
{
	uintptr_t granule_addrs[4];
	struct granule *granule[2];
	unsigned int cpu[2];
	unsigned int pattern[2];
	unsigned int block;
	unsigned int val;

	/******************************************************************
	 * TEST CASE 2:
	 *
	 * for two random CPUs, map a random granule to their SLOT_NS, then
	 * copy different random data to it. Verify that the data from one
	 * CPU's SLOT_NS hasn't been leaked to the other's CPU SLOT_NS.
	 ******************************************************************/

	/*
	 * Get four random granules:
	 * [0, 1]: To be used for write operations (SLOT_NS).
	 * [2, 3]: Will hold a copy of the data to transfer, so we can
	 * 	   verify later.
	 */
	get_rand_granule_array(granule_addrs, 4U);

	/*
	 * Get two random CPUs where to run the tests.
	 */
	do {
		cpu[0] = test_util_get_rand_in_range(0, MAX_CPUS - 1U);
		cpu[1] = test_util_get_rand_in_range(0, MAX_CPUS - 1U);
	} while (cpu[0] == cpu[1]);

	/*
	 * Get two different patterns of data to copy.
	 */
	do {
		pattern[0] = rand();
		pattern[1] = rand();
	} while (pattern[0] == pattern[1]);

	/*
	 * Copy the patterns into the destination granules.
	 */
	for (unsigned int i = 0U; i < 2U; i++) {
		host_util_set_cpuid(cpu[i]);

		/*
		 * Fill the copy granule with the random pattern to use
		 * on the test.
		 */
		for (unsigned int j = 0U; j < GRANULE_SIZE/sizeof(int); j++) {
			*((int *)granule_addrs[i + 2U] + j) = pattern[i];
		}

		granule[i] = addr_to_granule(granule_addrs[i]);
		ns_buffer_write(SLOT_NS, granule[i], 0U, GRANULE_SIZE,
				(void*)granule_addrs[i + 2U]);
	}

	/*
	 * Verify that the granule for the first CPU doesn't contain the
	 * pattern for the second one. Do that by picking up a random
	 * integer address within the granule and comparing it with the
	 * pattern for both CPUs.
	 */
	block = test_util_get_rand_in_range(0, (GRANULE_SIZE/sizeof(int)) - 1U);
	val = *((int *)granule_addrs[0] + block);

	CHECK_FALSE(val == pattern[1]);
	CHECK(val == pattern[0]);

	/*
	 * Repeat the same operation, this time with the second CPU.
	 */
	block = test_util_get_rand_in_range(0, (GRANULE_SIZE/sizeof(int)) - 1U);
	val = *((int *)granule_addrs[1] + block);

	CHECK_FALSE(val == pattern[0]);
	CHECK(val == pattern[1]);

	/*
	 * ns_buffer_write() will assert if:
	 *	- The slot is not a non-secure one.
	 *	- The granule to read from is NULL.
	 *	- The size is not aligned to a byte size.
	 *	- The offset is not aligned to a byte size.
	 *	- The source is not aligned to a byte size.
	 *	- The offset + size overflows the granule size.
	 * So skip tests for these cases.
	 */
}

TEST(slot_buffer, ns_buffer_read_TC1)
{
	uintptr_t granule_addrs[4];
	struct granule *granule[2];
	unsigned int block;
	int val;

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * For each CPU, map a random granule to NS_SLOT and copy random
	 * data into it. Then verify that the data is properly read and
	 * that the source has not been altered.
	 ******************************************************************/

	/*
	 * Get three random granules:
	 * granule_addrs[0]: To be used for read operations (SLOT_NS).
	 * granule_addrs[1]: Will hold a copy of the data in the first
	 *		     granule so we can use it to compare and test.
	 * granule_addrs[2]: Will be the dst granule for the ns_buffer_read
	 *		     operation.
	 */
	get_rand_granule_array(granule_addrs, 3U);

	/*
	 * Generate random data.
	 */
	for (unsigned int i = 0U; i < GRANULE_SIZE/sizeof(int); i++) {
		val = rand();
		*((int *)granule_addrs[0] + i) = val;	/* To be mapped */
		*((int *)granule_addrs[1] + i) = val;	/* To validate */
	}

	granule[0] = addr_to_granule(granule_addrs[0]);

	for (unsigned int i = 0U; i < MAX_CPUS; i++) {
		host_util_set_cpuid(i);

		/* Clean the dest granule */
		(void)memset((void *)granule_addrs[2], 0, GRANULE_SIZE);

		/* Read a random 1KB block from the granule */
		block = (unsigned int)test_util_get_rand_in_range(0, 3);
		ns_buffer_read(SLOT_NS, granule[0], block * 1024U, 1024U,
			       (void*)granule_addrs[2]);

		/*
		 * Verify the integrity of the SLOT_NS granule.
		 */
		MEMCMP_EQUAL((void *)granule_addrs[0],
			     (void *)granule_addrs[1],
			     (size_t)GRANULE_SIZE);

		/*
		 * Verify that the block has been properly read.
		 */
		MEMCMP_EQUAL((void *)(granule_addrs[0] + (1024U * block)),
			     (void *)granule_addrs[2],
			     (size_t)1024);
	}
}

TEST(slot_buffer, ns_buffer_read_TC2)
{
	uintptr_t granule_addrs[4];
	struct granule *granule[2];
	unsigned int cpu[2];
	int fail;

	/******************************************************************
	 * TEST CASE 2:
	 *
	 * for two random CPUs, map a random granule with random data to
	 * their SLOT_NS, then read the SLOT_NS on each CPU and ensure that
	 * the destination buffers contain the data from their CPU SLOT_NS
	 * only and no leak from the other CPU has happened.
	 ******************************************************************/

	/*
	 * Get four random granules:
	 * [0, 1]: Will be used for read operations (SLOT_NS).
	 * [2, 3]: Will be the dst granule for the ns_buffer_read operation.
	 */
	get_rand_granule_array(granule_addrs, 4U);

	/*
	 * Get two random CPUs where to run the tests.
	 */
	do {
		cpu[0] = test_util_get_rand_in_range(0, MAX_CPUS - 1U);
		cpu[1] = test_util_get_rand_in_range(0, MAX_CPUS - 1U);
	} while (cpu[0] == cpu[1]);

	/*
	 * Generate two granules with different random data.
	 */
	for (unsigned int i = 0U; i < GRANULE_SIZE/sizeof(int); i++) {
		*((int *)granule_addrs[0] + i) = rand();
		*((int *)granule_addrs[1] + i) = rand();
	}

	/*
	 * Read the granules.
	 */
	for (unsigned int i = 0U; i < 2U; i++) {
		host_util_set_cpuid(cpu[i]);

		granule[i] = addr_to_granule(granule_addrs[i]);
		ns_buffer_read(SLOT_NS, granule[i], 0U, GRANULE_SIZE,
			       (void*)granule_addrs[i + 2U]);
	}

	/*
	 * Verify that the dest granule for the first CPU doesn't contain
	 * the pattern for the second one.
	 *	- granule_addrs[1]: SLOT_NS for CPU 1
	 *	- granule_addrs[2]: dest granule for copy from CPU 0
	 */
	fail = memcmp((void*)granule_addrs[1],
		      (void*)granule_addrs[2], GRANULE_SIZE);

	CHECK_TEXT(fail != 0, "SLOT_NS for CPU A leaked to SLOT_NS for CPU B");

	/*
	 * Repeat the same operation, this time with the second CPU.
	 *	- granule_addrs[0]: SLOT_NS for CPU 0
	 *	- granule_addrs[3]: dest granule for copy from CPU 1
	 */
	fail = memcmp((void*)granule_addrs[0],
		      (void*)granule_addrs[3], GRANULE_SIZE);

	CHECK_TEXT(fail != 0, "SLOT_NS for CPU B leaked to SLOT_NS for CPU A");

	/*
	 * ns_buffer_read() will assert if:
	 *	- The slot is not a non-secure one.
	 *	- The granule to read from is NULL.
	 *	- The size is not aligned to a byte size.
	 *	- The offset is not aligned to a byte size.
	 *	- The dest is not aligned to a byte size.
	 *	- The offset + size overflows the granule size.
	 * So skip tests for these cases.
	 */
}

TEST(slot_buffer, slot_buf_setup_xlat_TC1)
{
	/*
	 * slot_buf_setup_xlat() has already been used during initialization
	 * for all tests, so skip it.
	 */
}

TEST(slot_buffer, slot_buf_init_TC1)
{
	/*
	 * slot_buf_init() has already been used during initialization
	 * for all tests, so skip it.
	 */
}
