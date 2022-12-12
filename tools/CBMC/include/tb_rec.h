/*
 * Copyright (c) 2021-2022, Arm Limited. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

#ifndef TB_REC_H
#define TB_REC_H

#include "tb_granules.h"

#include "rec.h"
#include "gic.h"
#include "ripas.h"
#include "fpu_helpers.h"
#include <attestation_token.h>

//TODO
#define RMI_RUNNABLE true
#define RMI_NOT_RUNNABLE false
#define RUNNABLE true
#define NOT_RUNNABLE false
#define READY false
#define RUNNING true
#define NO_HOST_CALL_PENDING false
#define HOST_CALL_PENDING true
#define NO_ATTEST_IN_PROGRESS ATTEST_SIGN_NOT_STARTED
#define REC_AUX GRANULE_STATE_REC_AUX


struct rec nondet_rec(void);
void init_rec_page(struct granule *g_rd);

struct rmi_rec_params nondet_struct_rmi_rec_params(void);
void init_rec_param_page(void); 

struct rmi_rec_run nondet_struct_rmi_rec_run(void);
void init_rec_run_page(void);

struct Rec_Runnable {
        bool runnable;
};

struct rmi_rec_params_buffer {
	uint64_t pc;
	struct Rec_Runnable flags;
    uint64_t mpidr;
    struct granule * aux[MAX_REC_AUX_GRANULES];
    uint64_t num_aux;
	unsigned long gprs[32];
};

struct rmi_rec_params_buffer nondet_rmi_rec_params_buffer(void);
struct rmi_rec_params_buffer RecParams(unsigned long addr);

// In the spec, Rec predicate must return a concrete rec.
// We use a global fallback rec to by-pass this constraint.
// There is a mismatch in the type of `struct rec` against spec.
struct rmm_rec {
	unsigned long owner;
	struct granule **aux;
	struct Rec_Runnable flags;
	unsigned long mpidr;
	unsigned long pc;
	unsigned long gprs[32];
    enum attest_token_gen_state_t attest_state;
    unsigned long ripas_addr;
    unsigned long ripas_top;
    // Either `READY` or `RUNNING`
	bool state;
    bool host_call_pending;
};
struct rmm_rec nondet_struct_rmm_rec(void);
struct rmm_rec Rec(unsigned long addr);

struct rmi_rec_run_buffer {
	uint8_t exit_reason;
	uint64_t esr;
	uint64_t far;
	uint64_t hpfar;
	uint64_t emulated_write_val;
	unsigned char gprs [448];
	uint64_t dispose_base;
	uint64_t dispose_size;
	uint64_t gicv3_vmcr;
	uint64_t gicv3_misr;
	uint64_t cntv_ctl;
	uint64_t cntv_cval;
	uint64_t cntp_ctl;
	uint64_t cntp_cval;
	uint8_t is_emulated_mmio;
	uint64_t emulated_read_val;
	uint8_t dispose_response;
	unsigned char gicv3_lrs [1024];
	uint64_t gicv3_hcr;
};

struct rmi_rec_run_buffer nondet_rmi_rec_run_buffer(void);
struct rmi_rec_run_buffer RecRun(unsigned long addr);

uint64_t RecIndex(uint64_t mpidr);
bool RecAuxAligned(uint64_t aux, uint64_t num_aux);
bool RecAuxAlias(uint64_t rec, uint64_t aux, uint64_t num_aux);
bool RecAuxStateEqual(struct granule **rec_aux_addr, unsigned long rd_aux_count, enum granule_state state);
bool RecAuxEqual(struct granule **rec_aux_addr, struct granule **params_aux_addr, uint64_t aux_count);
unsigned long RecAuxCount(unsigned long rd_addr);
bool MpidrIsValid(unsigned long mpdir);
bool MpidrEqual(uint64_t rec_mpidr, uint64_t params_mpidr);
bool RmiRecParamsIsValid(unsigned long params_ptr);
uint64_t RimExtendRec(struct rmm_realm realm, struct rmi_rec_params_buffer params);

#endif  /* !TB_REC_H */
