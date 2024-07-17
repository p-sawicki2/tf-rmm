/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef REC_H
#define REC_H

#ifndef __ASSEMBLER__

#include <arch.h>
#include <attestation_token.h>
#include <gic.h>
#include <memory_alloc.h>
#include <pauth.h>
#include <pmu.h>
#include <ripas.h>
#include <s2tt.h>
#include <simd.h>
#include <sizes.h>
#include <smc-rmi.h>
#include <utils_def.h>

#ifndef CBMC
#define RMM_REC_SAVED_GEN_REG_COUNT	U(31)
#define STRUCT_TYPE			struct
#define REG_TYPE			unsigned long
#define RMM_REALM_TOKEN_BUF_SIZE	SZ_1K

/* MbedTLS needs 8K of heap for attestation usecases */
#define REC_HEAP_PAGES			2U
#define REC_HEAP_SIZE			(REC_HEAP_PAGES * SZ_4K)

/* Number of pages per REC for attestation buffer */
#define REC_ATTEST_TOKEN_BUF_SIZE	(RMM_CCA_TOKEN_BUFFER * SZ_4K)

#else /* CBMC */
/*
 * struct rec must fit in a single granule. CBMC has a smaller GRANULE_SIZE
 * defined than on a real target, and the full structure doesn't fit there. The
 * following definitions help making the structure smaller.
 */
/*
 * For CBMC it is not necessary to have a regs array that fits all the 31
 * general registers
 */
#define RMM_REC_SAVED_GEN_REG_COUNT	SMC_RESULT_REGS
/*
 * Some of the structures inside 'struct rec' don't influence the outcome of
 * the CBMC tests, so for CBMC build make these a union making their size being
 * of the largest field, instead of the sum of the fields' sizes.
 */
#define STRUCT_TYPE	                union
/* Reserve a single byte per saved register instead of 8. */
#define REG_TYPE			unsigned char
#define RMM_REALM_TOKEN_BUF_SIZE	4U

#define REC_HEAP_PAGES		2U
#define REC_HEAP_SIZE		(16)

/* Number of pages per REC for attestation buffer */
#define REC_ATTEST_TOKEN_BUF_SIZE	(16)

#endif /* CBMC */

#define PADDING_COUNT(type) \
	(round_up((long int)sizeof(type), (long int)GRANULE_SIZE) - (long_int)sizeof(type))

struct granule;

/*
 * System registers whose contents are specific to a REC.
 */
STRUCT_TYPE sysreg_state {
	unsigned long sp_el0;
	unsigned long sp_el1;
	unsigned long elr_el1;
	unsigned long spsr_el1;
	unsigned long pmcr_el0;
	unsigned long tpidrro_el0;
	unsigned long tpidr_el0;
	unsigned long csselr_el1;
	unsigned long sctlr_el1;
	unsigned long actlr_el1;
	unsigned long cpacr_el1;
	unsigned long zcr_el1;
	unsigned long ttbr0_el1;
	unsigned long ttbr1_el1;
	unsigned long tcr_el1;
	unsigned long esr_el1;
	unsigned long afsr0_el1;
	unsigned long afsr1_el1;
	unsigned long far_el1;
	unsigned long mair_el1;
	unsigned long vbar_el1;
	unsigned long contextidr_el1;
	unsigned long tpidr_el1;
	unsigned long amair_el1;
	unsigned long cntkctl_el1;
	unsigned long par_el1;
	unsigned long mdscr_el1;
	unsigned long mdccint_el1;
	unsigned long disr_el1;
	unsigned long mpam0_el1;

	/* Timer Registers */
	unsigned long cnthctl_el2;
	unsigned long cntvoff_el2;
	unsigned long cntpoff_el2;
	unsigned long cntp_ctl_el0;
	unsigned long cntp_cval_el0;
	unsigned long cntv_ctl_el0;
	unsigned long cntv_cval_el0;

	/* GIC Registers */
	struct gic_cpu_state gicstate;

	/* TODO MPAM */
	/* TODO Performance Monitor Registers */
	/* TODO Pointer Authentication Registers */

	unsigned long vmpidr_el2;	/* restored only */
	unsigned long hcr_el2;		/* restored only */

	unsigned long cptr_el2;		/* restored only */
};

/*
 * System registers whose contents are
 * common across all RECs in a Realm.
 */
STRUCT_TYPE common_sysreg_state {
	unsigned long vttbr_el2;
	unsigned long vtcr_el2;
	unsigned long hcr_el2;
	unsigned long mdcr_el2;
};

/*
 * This structure is aligned on cache line size to avoid cache line trashing
 * when allocated as an array for N CPUs.
 */
struct ns_state {
	STRUCT_TYPE sysreg_state sysregs;
	unsigned long sp_el0;
	unsigned long icc_sre_el2;
	struct pmu_state *pmu;
} __aligned(CACHE_WRITEBACK_GRANULE);

/*
 * Data used when handling attestation requests
 */
struct rec_attest_data {
	unsigned char rmm_realm_token_buf[RMM_REALM_TOKEN_BUF_SIZE];
	size_t rmm_realm_token_len;

	struct token_sign_cntxt token_sign_ctx;

	/* Buffer allocation info used for heap init and management */
	struct buffer_alloc_ctx alloc_ctx;
};
COMPILER_ASSERT(sizeof(struct rec_attest_data) <= GRANULE_SIZE);

/*
 * This structure contains pointers to data that are allocated
 * in auxilary granules for a REC.
 */
/* TODO: Is it really necessary to align members to page? */
struct rec_aux_data {
	/* Pointer to the heap buffer */
	uint8_t attest_heap_buf[REC_HEAP_SIZE];
	uint8_t padding1[(round_up((long int)REC_HEAP_SIZE, (long int)GRANULE_SIZE) - (long int)REC_HEAP_SIZE)];

	/* Pointer to PMU state */
	struct pmu_state pmu;
	uint8_t padding2[PADDING_COUNT(struct pmu_state)];

	/* SIMD context region */
	struct simd_context simd_ctx;
	uint8_t padding3[PADDING_COUNT(struct simd_context)];

	/* Pointer to attestation-related data */
	struct rec_attest_data attest_data;
	uint8_t padding4[PADDING_COUNT(struct rec_attest_data)];

	/* Address of the attestation token buffer */
	uint8_t cca_token_buf[REC_ATTEST_TOKEN_BUF_SIZE];
};
COMPILER_ASSERT(U(offsetof(struct rec_aux_data, pmu)) % GRANULE_SIZE == 0U);
COMPILER_ASSERT(U(offsetof(struct rec_aux_data, simd_ctx)) % GRANULE_SIZE == 0U);
COMPILER_ASSERT(U(offsetof(struct rec_aux_data, attest_data)) % GRANULE_SIZE == 0U);
COMPILER_ASSERT(U(offsetof(struct rec_aux_data, cca_token_buf)) % GRANULE_SIZE == 0U);

struct rec {
	struct granule *g_rec;	/* the granule in which this REC lives */
	unsigned long rec_idx;	/* which REC is this */
	bool runnable;

	REG_TYPE regs[RMM_REC_SAVED_GEN_REG_COUNT];
	REG_TYPE sp_el0;

#ifndef CBMC
	/*
	 * PAuth state of Realm.
	 * Note that we do not need to save NS state as EL3 will save this as part of world switch.
	 */
	struct pauth_state pauth;
#endif /* CBMC*/

	unsigned long pc;
	unsigned long pstate;

	STRUCT_TYPE sysreg_state sysregs;
	STRUCT_TYPE common_sysreg_state common_sysregs;

	/* Populated when the REC issues a RIPAS change request */
	struct {
		unsigned long base;
		unsigned long top;
		unsigned long addr;
		enum ripas ripas_val;
		enum ripas_change_destroyed change_destroyed;
		enum ripas_response response;
	} set_ripas;

	/*
	 * Common values across all RECs in a Realm.
	 */
	struct {
		struct granule *g_rd;
		bool pmu_enabled;
		unsigned int pmu_num_ctrs;
		enum hash_algo algorithm;
		struct simd_config simd_cfg;
		struct s2tt_context s2_ctx;
	} realm_info;

	STRUCT_TYPE {
		/*
		 * The contents of the *_EL2 system registers at the last time
		 * the REC exited to the host due to a synchronous exception.
		 * These are the unsanitized register values which may differ
		 * from the value returned to the host in rec_exit structure.
		 */
		unsigned long esr;
		unsigned long hpfar;
		unsigned long far;
	} last_run_info;

	/* Pointer to per-cpu non-secure state */
	struct ns_state *ns;

	struct {
		/*
		 * Set to 'true' when there is a pending PSCI
		 * command that must be resolved by the host.
		 * The command is encoded in rec->regs[0].
		 *
		 * A REC with pending PSCI is not schedulable.
		 */
		bool pending;
	} psci_info;

	/* Number of auxiliary granules */
	unsigned int num_rec_aux;

	/* Addresses of auxiliary granules */
	struct granule *g_aux[MAX_REC_AUX_GRANULES];
	struct rec_aux_data *aux_data;
	struct {
		unsigned long vsesr_el2;
		bool inject;
	} serror_info;

	/* True if host call is pending */
	bool host_call;

	/* The active SIMD context that is live in CPU registers */
	struct simd_context *active_simd_ctx;
};
COMPILER_ASSERT(sizeof(struct rec) <= GRANULE_SIZE);
/*
 * The `sp_el0` field must immediately follow `regs` field in `struct rec`.
 * This assumption is used by the assembly code saving and restoring realm
 * registers.
 */
COMPILER_ASSERT(U(offsetof(struct rec, sp_el0)) ==
	(U(offsetof(struct rec, regs)) + U(sizeof(REG_TYPE) * RMM_REC_SAVED_GEN_REG_COUNT)));

/*
 * Check that mpidr has a valid value with all fields except
 * Aff3[39:32]:Aff2[23:16]:Aff1[15:8]:Aff0[3:0] set to 0.
 */
static inline bool mpidr_is_valid(unsigned long mpidr)
{
	return (mpidr & ~(MASK(MPIDR_EL2_AFF0) |
			  MASK(MPIDR_EL2_AFF1) |
			  MASK(MPIDR_EL2_AFF2) |
			  MASK(MPIDR_EL2_AFF3))) == 0ULL;
}

/*
 * Calculate REC index from mpidr value.
 * index = Aff3[39:32]:Aff2[23:16]:Aff1[15:8]:Aff0[3:0]
 */
static inline unsigned long mpidr_to_rec_idx(unsigned long mpidr)
{
	return (MPIDR_EL2_AFF(0, mpidr) +
		MPIDR_EL2_AFF(1, mpidr) +
		MPIDR_EL2_AFF(2, mpidr) +
		MPIDR_EL2_AFF(3, mpidr));
}

void rec_run_loop(struct rec *rec, struct rmi_rec_exit *rec_exit);
void inject_serror(struct rec *rec, unsigned long vsesr);
void emulate_stage2_data_abort(struct rec *rec, struct rmi_rec_exit *rec_exit,
			       unsigned long rtt_level);

#endif /* __ASSEMBLER__ */
#endif /* REC_H */
