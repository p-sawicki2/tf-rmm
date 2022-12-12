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


struct granule * init_rec_page(struct granule *g_rd);
void init_rec_param_page(void); 

//struct rmi_rec_run nondet_struct_rmi_rec_run(void);
//void init_rec_run_page(void);

struct Rec_Runnable {
    bool runnable;
};

// In the spec, Rec predicate must return a concrete rec.
// We use a global fallback rec to by-pass this constraint.
// There is a mismatch in the type of `struct rec` against spec.
struct rmm_rec {
	struct granule *aux[MAX_REC_AUX_GRANULES];
	struct Rec_Runnable flags;
	uint64_t gprs[RPV_SIZE];
	uint64_t mpidr;
	uint64_t owner;
	uint64_t pc;
    // Either `READY` or `RUNNING`
	bool state;
};

struct rmm_rec Rec(uint64_t addr);

struct spec_rec_params {
	struct Rec_Runnable flags;
    uint64_t mpidr;
	uint64_t pc;
	uint64_t gprs[8];
    uint64_t num_aux;
    struct granule * aux[MAX_REC_AUX_GRANULES];
};

struct spec_rec_param RecParams(uint64_t addr);

//struct rmi_rec_run_buffer {
	//uint8_t exit_reason;
	//uint64_t esr;
	//uint64_t far;
	//uint64_t hpfar;
	//uint64_t emulated_write_val;
	//unsigned char gprs [448];
	//uint64_t dispose_base;
	//uint64_t dispose_size;
	//uint64_t gicv3_vmcr;
	//uint64_t gicv3_misr;
	//uint64_t cntv_ctl;
	//uint64_t cntv_cval;
	//uint64_t cntp_ctl;
	//uint64_t cntp_cval;
	//uint8_t is_emulated_mmio;
	//uint64_t emulated_read_val;
	//uint8_t dispose_response;
	//unsigned char gicv3_lrs [1024];
	//uint64_t gicv3_hcr;
//};
//struct rmi_rec_run_buffer nondet_rmi_rec_run_buffer(void);
//struct rmi_rec_run_buffer RecRun(uint64_t addr);

uint64_t RecIndex(uint64_t mpidr);
bool RecAuxAligned(uint64_t aux, uint64_t num_aux);
bool RecAuxAlias(uint64_t rec, uint64_t aux, uint64_t num_aux);
bool RecAuxStateEqual(struct granule **rec_aux_addr, uint64_t rd_aux_count, enum granule_state state);
bool RecAuxEqual(struct granule **rec_aux_addr, struct granule **params_aux_addr, uint64_t aux_count);
bool MpidrIsValid(uint64_t mpdir);
bool MpidrEqual(uint64_t rec_mpidr, uint64_t params_mpidr);
bool RmiRecParamsIsValid(uint64_t params_ptr);
uint64_t RimExtendRec(struct rmm_realm realm, struct rmi_rec_params_buffer params);

#endif  /* !TB_REC_H */
