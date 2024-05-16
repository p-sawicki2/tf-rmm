/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch_helpers.h>
#include <assert.h>
#include <debug.h>
#include <host_defs.h>
#include <host_rmi_wrappers.h>
#include <host_utils.h>
#include <platform_api.h>
#include <rmm_el3_ifc.h>
#include <smc-rmi.h>
#include <smc-rsi.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <granule.h>
#include <unistd.h>

/* Add compiler assert as HOST_MEM_SIZE cannot be calculated in CMake */
COMPILER_ASSERT(HOST_MEM_SIZE == RMM_MAX_GRANULES * GRANULE_SIZE);

#define RMM_EL3_IFC_ABI_VERSION		\
	RMM_EL3_IFC_MAKE_VERSION(RMM_EL3_IFC_VERS_MAJOR, RMM_EL3_IFC_VERS_MINOR)
#define RMM_EL3_MAX_CPUS		(1U)
#define REALM_BUFFER_IPA		0x1000

void rmm_main(void);

void handle_ns_smc(unsigned long function_id,
		   unsigned long arg0,
		   unsigned long arg1,
		   unsigned long arg2,
		   unsigned long arg3,
		   unsigned long arg4,
		   unsigned long arg5,
		   struct smc_result *res);

/* Function to emulate the MMU enablement for the fake_host architecture. */
static void enable_fake_host_mmu(void)
{
	write_sctlr_el2(SCTLR_ELx_WXN_BIT | SCTLR_ELx_M_BIT);
}

void init() {
	host_util_set_cpuid(0U);

	host_util_setup_sysreg_and_boot_manifest();

	plat_setup(0UL,
		   RMM_EL3_IFC_ABI_VERSION,
		   RMM_EL3_MAX_CPUS,
		   (uintptr_t)host_util_get_el3_rmm_shared_buffer());

	/*
	 * Enable the MMU. This is needed as some initialization code
	 * called by rmm_main() asserts that the mmu is enabled.
	 */
	enable_fake_host_mmu();

	/* Start RMM */
	rmm_main();
}

/* Max sequence RMI calls */
#define FUZZ_COMMAND_COUNT 10
/* Registers X0 -- X6 */
#define FUZZ_REGISTER_COUNT 7
#define FUZZ_FID_BEGIN 0xC4000140
#define FUZZ_FID_END   0xC4000190

/* Internal data structure that fuzzing hooks in. */
extern struct granule granules[RMM_MAX_GRANULES];
extern unsigned char granules_buffer[HOST_MEM_SIZE] __aligned(GRANULE_SIZE);

void iteration_init(const uint8_t* const buffer) 
{
	memcpy(granules_buffer, buffer, HOST_MEM_SIZE * sizeof(unsigned char));
	memcpy(granules, buffer + HOST_MEM_SIZE * sizeof(unsigned char), RMM_MAX_GRANULES * sizeof(struct granule));
}

void execute(unsigned char* buffer)
{
	/* Initialise the RMM internal data structur. */
	iteration_init(buffer);

	VERBOSE("RMM: Beginning of Fake Host execution\n");

	/* Directly point to the buffer so save a `memcpy` call. */
	uint64_t (*call_invocation)[FUZZ_REGISTER_COUNT] = 
			(uint64_t (*)[FUZZ_REGISTER_COUNT])(
							buffer 
							+ HOST_MEM_SIZE * sizeof(unsigned char) 
							+ RMM_MAX_GRANULES * sizeof(struct granule));

	/* Call commands. */
	for(int i = 0; i < FUZZ_COMMAND_COUNT; ++i) {

		INFO("SMC ARGS: 0x%08X 0x%016lX 0x%016lX 0x%016lX 0x%016lX 0x%016lX 0x%016lX\n"
			, call_invocation[i][0]
			, call_invocation[i][1]
			, call_invocation[i][2]
			, call_invocation[i][3]
			, call_invocation[i][4]
			, call_invocation[i][5]
			, call_invocation[i][6]);

		struct smc_result result = { 0 };

		handle_ns_smc(call_invocation[i][0]
					 , call_invocation[i][1]
					 , call_invocation[i][2]
					 , call_invocation[i][3]
					 , call_invocation[i][4]
					 , call_invocation[i][5]
					 , call_invocation[i][6]
					 , &result);

	}

	VERBOSE("RMM: Fake Host execution completed\n");
}

#ifdef PERSISTENT_MODE
/* Adding AFL_FUZZ_INIT */
__AFL_FUZZ_INIT();

/* To ensure checks are not optimized out it is recommended to disable
   code optimization for the fuzzer harness main() */
#pragma clang optimize off
#pragma GCC            optimize("O0")
#endif

#define EXPECTED_LENGTH_FOR_FUZZ (HOST_MEM_SIZE * sizeof(unsigned char) \
			+ RMM_MAX_GRANULES * sizeof(struct granule) + \
			(sizeof(uint64_t) * FUZZ_REGISTER_COUNT) * FUZZ_COMMAND_COUNT)

int main(int argc, char *argv[])
{
	/* Global initialization for RMM */
	init();
#ifdef PERSISTENT_MODE
	/* Adding AFL_INIT and buf */
	__AFL_INIT();
	unsigned char* buffer = __AFL_FUZZ_TESTCASE_BUF;

	/* Starting AFL_LOOP */
	while (__AFL_LOOP(10000)) {
		int len = __AFL_FUZZ_TESTCASE_LEN;
		if(len != EXPECTED_LENGTH_FOR_FUZZ) continue;
		execute(buffer);
	}
#else
	if (argc < 2) return 1;

	/*
     * ALL pages, granule meta data, 
     * and a list of `FUZZ_COMMAND_COUNT` sequence calls. 
     */
	uint8_t buffer[EXPECTED_LENGTH_FOR_FUZZ] = { 0 };

	FILE *fp = fopen(argv[1], "rb");
	if (!fp) return 1;
	size_t read_res = fread(buffer, sizeof(uint8_t), sizeof(buffer), fp);
	fclose(fp);

	assert(read_res == sizeof(uint8_t) * sizeof(buffer));
	VERBOSE("Read bytes: %lu\n", read_res);

	execute(buffer);
#endif

	return 0;
}
