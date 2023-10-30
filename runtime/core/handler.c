/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch.h>
#include <arch_helpers.h>
#include <assert.h>
#include <buffer.h>
#include <debug.h>
#include <run.h>
#include <simd.h>
#include <smc-handler.h>
#include <smc-rmi.h>
#include <smc.h>
#include <status.h>
#include <utils_def.h>

/* Maximum number of supported arguments */
#define MAX_NUM_ARGS		5U

/* Maximum number of output values */
#define MAX_NUM_OUTPUT_VALS	4U

#define RMI_STATUS_STRING(_id)[RMI_##_id] = #_id

static const char * const rmi_status_string[] = {
	RMI_STATUS_STRING(SUCCESS),
	RMI_STATUS_STRING(ERROR_INPUT),
	RMI_STATUS_STRING(ERROR_REALM),
	RMI_STATUS_STRING(ERROR_REC),
	RMI_STATUS_STRING(ERROR_RTT)
};

COMPILER_ASSERT(ARRAY_LEN(rmi_status_string) == RMI_ERROR_COUNT);

/*
 * At this level (in handle_ns_smc) we distinguish the RMI calls only on:
 * - The number of input arguments [0..5], and whether
 * - The function returns up to three output values in addition
 *   to the return status code.
 * Hence, the naming syntax is:
 * - `*_[0..5]` when no output values are returned, and
 * - `*_[0..3]_o` when the function returns some output values.
 */
typedef unsigned long (*handler_0)(void);
typedef unsigned long (*handler_1)(unsigned long arg0);
typedef unsigned long (*handler_2)(unsigned long arg0, unsigned long arg1);
typedef unsigned long (*handler_3)(unsigned long arg0, unsigned long arg1,
				   unsigned long arg2);
typedef unsigned long (*handler_4)(unsigned long arg0, unsigned long arg1,
				   unsigned long arg2, unsigned long arg3);
typedef unsigned long (*handler_5)(unsigned long arg0, unsigned long arg1,
				   unsigned long arg2, unsigned long arg3,
				   unsigned long arg4);
typedef void (*handler_1_o)(unsigned long arg0, struct smc_result *res);
typedef void (*handler_2_o)(unsigned long arg0, unsigned long arg1,
			    struct smc_result *res);
typedef void (*handler_3_o)(unsigned long arg0, unsigned long arg1,
			    unsigned long arg2, struct smc_result *res);
typedef void (*handler_4_o)(unsigned long arg0, unsigned long arg1,
			    unsigned long arg2, unsigned long arg3,
			    struct smc_result *res);

/*
 * SMC RMI handler type encoding:
 * [0:7]  - number of arguments
 * [8:15] - number of output values
 */
#define RMI_TYPE(_in, _out)	((_in) | ((_out) << 8))
#define set_rmi_type(_in, _out)	rmi_type_##_in##_out = RMI_TYPE(_in, _out)

enum rmi_type {
	set_rmi_type(0, 0),	/* 0 arguments, 0 output values */
	set_rmi_type(1, 0),	/* 1 argument,  0 output values */
	set_rmi_type(2, 0),	/* 2 arguments, 0 output values */
	set_rmi_type(3, 0),	/* 3 arguments, 0 output values */
	set_rmi_type(4, 0),	/* 4 arguments, 0 output values */
	set_rmi_type(5, 0),	/* 5 arguments, 0 output values */
	set_rmi_type(1, 1),	/* 1 argument,  1 output value */
	set_rmi_type(1, 2),	/* 1 argument,  2 output values */
	set_rmi_type(2, 2),	/* 2 arguments, 2 output values */
	set_rmi_type(3, 1),	/* 3 arguments, 1 output value */
	set_rmi_type(3, 2),	/* 3 arguments, 2 output values */
	set_rmi_type(3, 4),	/* 3 arguments, 4 output values */
	set_rmi_type(4, 1)	/* 4 arguments, 1 output value */
};

struct smc_handler {
	const char	*fn_name;
	enum rmi_type	type;
	union {
		handler_0	f_00;
		handler_1	f_10;
		handler_2	f_20;
		handler_3	f_30;
		handler_4	f_40;
		handler_5	f_50;
		handler_1_o	f_11;
		handler_1_o	f_12;
		handler_2_o	f_22;
		handler_3_o	f_31;
		handler_3_o	f_32;
		handler_3_o	f_34;
		handler_4_o	f_41;
		void		*fn_dummy;
	};
	bool		log_exec;	/* print handler execution */
	bool		log_error;	/* print in case of error status */
};

/*
 * Get handler ID from FID
 * Precondition: FID is an RMI call
 */
#define RMI_HANDLER_ID(_id)	SMC64_FID_OFFSET_FROM_RANGE_MIN(RMI, _id)

#define HANDLER(_id, _in, _out, _fn, _exec, _error)[RMI_HANDLER_ID(SMC_RMM_##_id)] = { \
	.fn_name = (#_id),				\
	.type = (enum rmi_type)RMI_TYPE(_in, _out),	\
	.f_##_in##_out = (_fn),				\
	.log_exec = (_exec),				\
	.log_error = (_error)				\
}

/*
 * The 3rd value enables the execution log.
 * The 4th value enables the error log.
 */
static const struct smc_handler smc_handlers[] = {
	HANDLER(VERSION,		1, 2, smc_version,		 true,  true),
	HANDLER(FEATURES,		1, 1, smc_read_feature_register, true,  true),
	HANDLER(GRANULE_DELEGATE,	1, 0, smc_granule_delegate,	 false, true),
	HANDLER(GRANULE_UNDELEGATE,	1, 0, smc_granule_undelegate,	 false, true),
	HANDLER(REALM_CREATE,		2, 0, smc_realm_create,		 true,  true),
	HANDLER(REALM_DESTROY,		1, 0, smc_realm_destroy,	 true,  true),
	HANDLER(REALM_ACTIVATE,		1, 0, smc_realm_activate,	 true,  true),
	HANDLER(REC_CREATE,		3, 0, smc_rec_create,		 true,  true),
	HANDLER(REC_DESTROY,		1, 0, smc_rec_destroy,		 true,  true),
	HANDLER(REC_ENTER,		2, 0, smc_rec_enter,		 false, true),
	HANDLER(DATA_CREATE,		5, 0, smc_data_create,		 false, false),
	HANDLER(DATA_CREATE_UNKNOWN,	3, 0, smc_data_create_unknown,	 false, false),
	HANDLER(DATA_DESTROY,		2, 2, smc_data_destroy,		 false, true),
	HANDLER(RTT_CREATE,		4, 0, smc_rtt_create,		 false, true),
	HANDLER(RTT_DESTROY,		3, 2, smc_rtt_destroy,		 false, true),
	HANDLER(RTT_FOLD,		3, 1, smc_rtt_fold,		 false, true),
	HANDLER(RTT_MAP_UNPROTECTED,	4, 0, smc_rtt_map_unprotected,	 false, false),
	HANDLER(RTT_UNMAP_UNPROTECTED,	3, 1, smc_rtt_unmap_unprotected, false, false),
	HANDLER(RTT_READ_ENTRY,		3, 4, smc_rtt_read_entry,	 false, true),
	HANDLER(PSCI_COMPLETE,		3, 0, smc_psci_complete,	 true,  true),
	HANDLER(REC_AUX_COUNT,		1, 1, smc_rec_aux_count,	 true,  true),
	HANDLER(RTT_INIT_RIPAS,		3, 1, smc_rtt_init_ripas,	 false, true),
	HANDLER(RTT_SET_RIPAS,		4, 1, smc_rtt_set_ripas,	 false, true)
};

COMPILER_ASSERT(ARRAY_LEN(smc_handlers) == SMC64_NUM_FIDS_IN_RANGE(RMI));

static bool rmi_call_log_enabled = true;

static inline bool rmi_handler_needs_fpu(unsigned int id)
{
#ifdef RMM_FPU_USE_AT_REL2
	if (id == SMC_RMM_REALM_CREATE || id == SMC_RMM_DATA_CREATE ||
	    id == SMC_RMM_REC_CREATE || id == SMC_RMM_RTT_INIT_RIPAS) {
		return true;
	}
#else
	(void)id;
#endif
	return false;
}

static void rmi_log_on_exit(unsigned int handler_id,
			    unsigned long args[],
			    struct smc_result *res)
{
	const struct smc_handler *handler = &smc_handlers[handler_id];
	unsigned int function_id = SMC64_RMI_FID(handler_id);
	return_code_t rc;
	unsigned int num;

	if (!handler->log_exec && !handler->log_error) {
		return;
	}

	rc = unpack_return_code(res->x[0]);

	if ((handler->log_exec) ||
	    (handler->log_error && (rc.status != RMI_SUCCESS))) {
		/* Print function name */
		INFO("SMC_RMM_%-21s", handler->fn_name);

		/* Print arguments */
		num = (unsigned int)handler->type & 0xFFU;
		assert(num <= MAX_NUM_ARGS);

		for (unsigned int i = 0U; i < num; i++) {
			INFO(" %lx", args[i]);
		}

		/* Print status */
		if (rc.status >= RMI_ERROR_COUNT) {
			INFO(" > %lx", res->x[0]);
		} else {
			INFO(" > RMI_%s", rmi_status_string[rc.status]);
		}

		/* Check for index */
		if (((function_id == SMC_RMM_REC_ENTER) &&
		     (rc.status == RMI_ERROR_REALM)) ||
		     (rc.status == RMI_ERROR_RTT)) {
			INFO(" %x", rc.index);
		}

		if ((rc.status == RMI_SUCCESS) ||
		   ((rc.status == RMI_ERROR_RTT) &&
		   ((function_id == SMC_RMM_RTT_DESTROY) ||
		    (function_id == SMC_RMM_DATA_DESTROY)))) {
			/* Print output values */
			num = ((unsigned int)handler->type >> 8) & 0xFFU;
			assert(num <= MAX_NUM_OUTPUT_VALS);

			for (unsigned int i = 1U; i <= num; i++) {
				INFO(" %lx", res->x[i]);
			}
		}
		INFO("\n");
	}
}

/* coverity[misra_c_2012_rule_8_7_violation:SUPPRESS] */
void handle_ns_smc(unsigned int function_id,
		   unsigned long arg0,
		   unsigned long arg1,
		   unsigned long arg2,
		   unsigned long arg3,
		   unsigned long arg4,
		   unsigned long arg5,
		   struct smc_result *res)
{
	(void)arg5;
	unsigned int handler_id;
	const struct smc_handler *handler = NULL;
	bool restore_ns_simd_state = false;
	struct simd_context *ns_simd_ctx;
	bool sve_hint = false;

	/* Save the SVE hint bit and clear it from the function ID */
	if ((function_id & SMC_SVE_HINT) != 0U) {
		sve_hint = true;
		function_id &= ~SMC_SVE_HINT;
	}

	if (IS_SMC64_RMI_FID(function_id)) {
		handler_id = RMI_HANDLER_ID(function_id);
		if (handler_id < ARRAY_LEN(smc_handlers)) {
			handler = &smc_handlers[handler_id];
		}
	}

	/*
	 * Check if handler exists and 'fn_dummy' is not NULL
	 * for not implemented 'function_id' calls in SMC RMI range.
	 */
	if ((handler == NULL) || (handler->fn_dummy == NULL)) {
		VERBOSE("[%s] unknown function_id: %x\n",
			__func__, function_id);
		res->x[0] = SMC_UNKNOWN;
		return;
	}

	assert_cpu_slots_empty();

	/* Current CPU's SIMD state must not be saved when entering RMM */
	assert(simd_is_state_saved() == false);

	/* Get current CPU's NS SIMD context */
	ns_simd_ctx = get_cpu_ns_simd_context();

	/* Set or clear SVE hint bit in the NS SIMD context */
	simd_update_smc_sve_hint(ns_simd_ctx, sve_hint);

	/* If the handler needs FPU, actively save NS simd context. */
	if (rmi_handler_needs_fpu(function_id) == true) {
		simd_context_save(ns_simd_ctx);
		restore_ns_simd_state = true;
	}

	switch (handler->type) {
	case rmi_type_00:
		res->x[0] = handler->f_00();
		break;
	case rmi_type_10:
		res->x[0] = handler->f_10(arg0);
		break;
	case rmi_type_20:
		res->x[0] = handler->f_20(arg0, arg1);
		break;
	case rmi_type_30:
		res->x[0] = handler->f_30(arg0, arg1, arg2);
		break;
	case rmi_type_40:
		res->x[0] = handler->f_40(arg0, arg1, arg2, arg3);
		break;
	case rmi_type_50:
		res->x[0] = handler->f_50(arg0, arg1, arg2, arg3, arg4);
		break;
	case rmi_type_11:
		handler->f_11(arg0, res);
		break;
	case rmi_type_12:
		handler->f_12(arg0, res);
		break;
	case rmi_type_22:
		handler->f_22(arg0, arg1, res);
		break;
	case rmi_type_31:
		handler->f_31(arg0, arg1, arg2, res);
		break;
	case rmi_type_32:
		handler->f_32(arg0, arg1, arg2, res);
		break;
	case rmi_type_34:
		handler->f_34(arg0, arg1, arg2, res);
		break;
	case rmi_type_41:
		handler->f_41(arg0, arg1, arg2, arg3, res);
		break;
	default:
		assert(false);
	}

	if (rmi_call_log_enabled) {
		unsigned long args[] = {arg0, arg1, arg2, arg3, arg4};

		rmi_log_on_exit(handler_id, args, res);
	}

	/* If the handler uses FPU, restore the saved NS simd context. */
	if (restore_ns_simd_state) {
		simd_context_restore(ns_simd_ctx);
	}

	/* Current CPU's SIMD state must not be saved when exiting RMM */
	assert(simd_is_state_saved() == false);

	assert_cpu_slots_empty();
}

static void report_unexpected(uintptr_t regs)
{
	u_register_t lr;
	u_register_t sp = regs + (2U * sizeof(u_register_t));

	ERROR("----\n");
	ERROR("Unexpected exception:\n");

	for (unsigned int i = 0U; i < 30U; i++) {
		ERROR("X%u:\t\t0x%016lx\n", i++,
			*(u_register_t *)regs);
		ERROR("X%u:\t\t0x%016lx\n", i,
			*(u_register_t *)(regs + sizeof(u_register_t)));
		regs -= 2U * sizeof(u_register_t);
	}

	lr = *(u_register_t *)regs;

#if defined(__aarch64__)
	/* Demangle return address */
	asm volatile (
		"xpaci %0" : : "r" (lr)
	);
#endif
	ERROR("LR:\t\t0x%016lx\n", lr);
	ERROR("SP:\t\t0x%016lx\n", sp);

	ERROR("SPSR_EL2:\t0x%016lx\n", read_spsr_el2());
	ERROR("ESR_EL2:\t0x%016lx\n", read_esr_el2());
	ERROR("ELR_EL2:\t0x%016lx\n", read_elr_el2());
	ERROR("FAR_EL2:\t0x%016lx\n", read_far_el2());
	ERROR("----\n");
}

/*
 * Identifies an abort that the RMM may recover from.
 */
struct rmm_trap_element {
	/*
	 * The PC at the time of abort.
	 */
	unsigned long aborted_pc;
	/*
	 * New value of the PC.
	 */
	unsigned long new_pc;
};

#define RMM_TRAP_HANDLER(_aborted_pc, _new_pc) \
	{ .aborted_pc = (unsigned long)(&(_aborted_pc)), \
	  .new_pc = (unsigned long)(&(_new_pc)) }

/*
 * The registered locations of load/store instructions that access NS memory.
 */
extern void *ns_read;
extern void *ns_write;

/*
 * The new value of the PC when the GPF occurs on a registered location.
 */
extern void *ns_access_ret_0;

/* coverity[misra_c_2012_rule_8_9_violation:SUPPRESS] */
static struct rmm_trap_element rmm_trap_list[] = {
	RMM_TRAP_HANDLER(ns_read, ns_access_ret_0),
	RMM_TRAP_HANDLER(ns_write, ns_access_ret_0),
};
#define RMM_TRAP_LIST_SIZE (sizeof(rmm_trap_list)/sizeof(struct rmm_trap_element))

__dead2 static void fatal_abort(uintptr_t regs)
{
	report_unexpected(regs);

	while (true) {
		wfe();
	}
}

static bool is_el2_data_abort_gpf(unsigned long esr)
{
	if (((esr & MASK(ESR_EL2_EC)) == ESR_EL2_EC_DATA_ABORT_SEL) &&
	    ((esr & MASK(ESR_EL2_ABORT_FSC)) == ESR_EL2_ABORT_FSC_GPF)) {
		return true;
	}
	return false;
}

/*
 * Handles the RMM's aborts.
 * It compares the PC at the time of the abort with the registered addresses.
 * If it finds a match, it returns the new value of the PC that the RMM should
 * continue from. Other register values are preserved.
 * If no match is found, it aborts the RMM.
 */
/* coverity[misra_c_2012_rule_8_7_violation:SUPPRESS] */
unsigned long handle_rmm_trap(uintptr_t regs)
{
	unsigned long esr = read_esr_el2();
	unsigned long elr = read_elr_el2();

	/*
	 * Only the GPF data aborts are recoverable.
	 */
	if (!is_el2_data_abort_gpf(esr)) {
		fatal_abort(regs);
	}

	for (unsigned int i = 0U; i < RMM_TRAP_LIST_SIZE; i++) {
		if (rmm_trap_list[i].aborted_pc == elr) {
			return rmm_trap_list[i].new_pc;
		}
	}

	fatal_abort(regs);
	return 0UL;
}
