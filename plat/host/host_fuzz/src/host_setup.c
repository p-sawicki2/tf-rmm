/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch_helpers.h>
#include <assert.h>
#include <debug.h>
#include <granule.h>
#include <host_defs.h>
#include <host_rmi_wrappers.h>
#include <host_utils.h>
#include <platform_api.h>
#include <realm.h>
#include <rec.h>
#include <rmm_el3_ifc.h>
#include <smc-rmi.h>
#include <smc-rsi.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>
#include <xlat_tables.h>

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

void init(void)
{
	host_util_setup_sysreg_and_boot_manifest();

	host_util_set_cpuid(0U);

	/* Early setup the CpuId into tpidr_el2 */
	write_tpidr_el2(0U);

	plat_setup(0UL,
		   RMM_EL3_IFC_ABI_VERSION,
		   RMM_EL3_MAX_CPUS,
		   (uintptr_t)host_util_get_el3_rmm_shared_buffer());

	/*
	 * Enable the MMU. This is needed as some initialization code
	 * called by rmm_main() asserts that the mmu is enabled.
	 */
	xlat_enable_mmu_el2();

	/*
	 * rmm_main() finishhes the warmboot path.
	 *
	 * Note: It is expected that the attestation init will fail.
	 */
	rmm_main();
}

/* Max sequence RMI calls */
#define FUZZ_COMMAND_COUNT 10
/* Registers X0 -- X6 */
#define FUZZ_REGISTER_COUNT 7
#define FUZZ_FID_BEGIN 0xC4000150
#define FUZZ_FID_END   0xC4000190

unsigned long host_util_get_granule_meta_base();

void iteration_init(const uint8_t * const buffer)
{
	unsigned char * granules_buffer = (unsigned char *)host_util_get_granule_base();
	struct granule * granules = (struct granule *)host_util_get_granule_meta_base();
	memcpy(granules_buffer, buffer, HOST_MEM_SIZE * sizeof(unsigned char));
	memcpy(granules, buffer + HOST_MEM_SIZE * sizeof(unsigned char), RMM_MAX_GRANULES * sizeof(struct granule));
}

void parameter_transfer(uint64_t * parameters, size_t counts)
{
	uint64_t fid = parameters[0];
	for(size_t i = 1; i < counts; ++i) {
		/* skip the non-address parameters */
		if ( ( fid == 0xC4000153 && i == 5 )
		  || ( fid == 0xC4000170 && i == 2 ) 
		  || ( fid == 0xC4000172 && i == 3 ) 
		  || ( fid == 0xC400018D && i == 1 ) 
		  || ( fid == 0xC400017A && i == 2 ) 
		  || ( fid == 0xC400017B && ( i == 3 || i == 4 ) ) 
		  || ( fid == 0xC4000164 && i == 3 ) 
		  || ( fid == 0xC4000158 && i == 2 ) 
		  || ( fid == 0xC400017D && ( i == 4 || i == 5 ) ) 
		  || ( fid == 0xC400017E && ( i == 3 || i == 4 ) ) 
		  || ( fid == 0xC400017F && ( i == 3 || i == 4 ) ) 
		  || ( fid == 0xC4000180 && i == 3 ) 
		  || ( fid == 0xC4000181 && i == 3 ) 
		  || ( fid == 0xC4000182 && ( i == 3 || i == 4 ) ) 
		  || ( fid == 0xC4000183 && i == 3 ) 
		  || ( fid == 0xC4000184 && i == 3 ) 
		  || ( fid == 0xC400015D && i == 4 ) 
		  || ( fid == 0xC400015E && i == 3 ) 
		  || ( fid == 0xC4000166 && i == 3 ) 
		  || ( fid == 0xC400015F && ( i == 3 || i == 4 ) ) 
		  || ( fid == 0xC4000161 && i == 3 ) 
		  || ( fid == 0xC4000162 && i == 3 ) 
		  || ( fid == 0xC4000150 && i == 1 ) 
		  ) {
			continue;
		}
		/* The rest parameters are all relateive addresses to the base */
		parameters[i] += host_util_get_granule_base();
	}
}

bool valid_granule(void * g)
{
	void * granules_buffer = (unsigned char *)host_util_get_granule_base();
	return  g >= granules_buffer
		 && g < granules_buffer + HOST_MEM_SIZE
		 && (unsigned long)g % GRANULE_SIZE == 0;
}


bool valid_granule_meta(void * g)
{
	void * granules = (struct granule *)host_util_get_granule_meta_base();
	return g >= granules
		&& g < granules + (RMM_MAX_GRANULES * sizeof(struct rd)) 
		&& (unsigned long) g % sizeof(struct rd) == 0;
}
/* 
 * Early exit without calling the RMM handler.
 * NOTE: the lengths of arrays are defined in global macro.
 * */
bool valid_state(uint64_t (*call_invocation)[FUZZ_REGISTER_COUNT])
{

	unsigned char * granules_buffer = (unsigned char *)host_util_get_granule_base();
	struct granule * granules = (struct granule *)host_util_get_granule_meta_base();
	for (size_t i = 0; i < RMM_MAX_GRANULES; ++i) {
		struct granule * g = &(granules[i]);
		/* If the lock-bit is 1, i.e. locked */
		if (g->descriptor & GRN_LOCK_BIT) {
			INFO("Granule #%zu is locked.\n", i);
			return false;
		}

		/* rule out unexpected refcount state, `REFCOUNT(g)`,
		 * and then check invariant. */
		switch (STATE(g)) {
		case GRANULE_STATE_NS:
		case GRANULE_STATE_DELEGATED:
		case GRANULE_STATE_DATA:
		case GRANULE_STATE_REC_AUX:
			if (REFCOUNT(g) != 0U) {
				return false;
			}
			break;
		case GRANULE_STATE_REC: {
			if (REFCOUNT(g) > 1U) {
				return false;
			}
			struct rec * rec_ptr = (struct rec *)&granules_buffer[i * GRANULE_SIZE];
			struct granule * g_rd = (rec_ptr->realm_info).g_rd;
			if( !( valid_granule_meta(g_rd) ) ) {
				return false;
			}
			break;
		}
		case GRANULE_STATE_RTT:
			if (REFCOUNT(g) > RTT_REFCOUNT_MAX) {
				return false;
			}
			break;
		case GRANULE_STATE_RD: {
			struct rd * rd_ptr = (struct rd *)&granules_buffer[i * GRANULE_SIZE];
			int s2_starting_level = (rd_ptr->s2_ctx).s2_starting_level;
			unsigned int num_root_rtts = (rd_ptr->s2_ctx).num_root_rtts;
			void * g_rtt = (rd_ptr->s2_ctx).g_rtt;
			if ( !( s2_starting_level >= -1 
				 && s2_starting_level <= 3
				 && num_root_rtts <= 16
				 && valid_granule(g_rtt) ) ) {
				return false;
			}
			break;
		}
		default:
			break;
		}
	}

	/* Shrink the FID space */
	for (size_t i = 0; i < FUZZ_COMMAND_COUNT; ++i) {
		uint64_t fid = call_invocation[i][0];
		if ( !(fid >= FUZZ_FID_BEGIN && fid <= FUZZ_FID_END) ) {
			INFO("Call #%zu has unexpected fid %lx.\n", i, fid);
			return false;
		}
	}



	INFO("No early exit.\n");
	return true;
}

void execute(unsigned char *buffer)
{
	/* Initialise the RMM internal data structur. */
	iteration_init(buffer);

	INFO("RMM: Beginning of Fake Host execution\n");

	/* Directly point to the buffer so save a `memcpy` call. */
	uint64_t (*call_invocation)[FUZZ_REGISTER_COUNT] =
			(uint64_t (*)[FUZZ_REGISTER_COUNT])(
							buffer
							+ HOST_MEM_SIZE * sizeof(unsigned char)
							+ RMM_MAX_GRANULES * sizeof(struct granule));

	if (!valid_state(call_invocation)) {
		INFO("Early exist.\n");
		return;
	}

	/* Call commands. */
	for (int i = 0; i < FUZZ_COMMAND_COUNT; ++i) {

		parameter_transfer(call_invocation[i], FUZZ_REGISTER_COUNT);

		INFO("SMC ARGS: 0x%08lX 0x%016lX 0x%016lX 0x%016lX 0x%016lX 0x%016lX 0x%016lX\n"
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
	#ifdef __AFL_HAVE_MANUAL_CONTROL
	__AFL_INIT();
	#endif
	unsigned char *buffer = __AFL_FUZZ_TESTCASE_BUF;

	/* Starting AFL_LOOP */
	while (__AFL_LOOP(10000)) {
		int len = __AFL_FUZZ_TESTCASE_LEN;
		if (len != EXPECTED_LENGTH_FOR_FUZZ) {
			continue;
		}
		execute(buffer);
	}
#else
	if (argc < 2) {
		return 1;
	}

	/*
	 * ALL pages, granule meta data,
	 * and a list of `FUZZ_COMMAND_COUNT` sequence calls.
	 */
	uint8_t buffer[EXPECTED_LENGTH_FOR_FUZZ] = { 0 };

	FILE *fp = fopen(argv[1], "rb");
	if (!fp) {
		return 1;
	}
	size_t read_res = fread(buffer, sizeof(uint8_t), sizeof(buffer), fp);
	fclose(fp);

	assert(read_res == sizeof(uint8_t) * sizeof(buffer));
	VERBOSE("Read bytes: %lu\n", read_res);

	execute(buffer);
#endif

	return 0;
}
