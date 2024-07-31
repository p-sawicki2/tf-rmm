/*
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch.h>
#include <arch_helpers.h>
#include <buffer.h>
#include <esr.h>
#include <exit.h>
#include <gic.h>
#include <granule.h>
#include <inject_exp.h>
#include <memory_alloc.h>
#include <planes.h>
#include <psci.h>
#include <realm.h>
#include <rec.h>
#include <run.h>
#include <rsi-handler.h>
#include <rsi-logger.h>
#include <s2tt.h>
#include <simd.h>
#include <smc-rmi.h>
#include <smc-rsi.h>
#include <status.h>
#include <sysreg_traps.h>

static void system_abort(void)
{
	/*
	 * TODO: report the abort to the EL3.
	 * We need to establish the exact EL3 API first.
	 */
	assert(false);
}

static bool fixup_aarch32_data_abort(struct rec *rec, unsigned long *esr)
{
	unsigned long spsr = read_spsr_el2();
	(void)rec;

	if ((spsr & SPSR_EL2_nRW_AARCH32) != 0UL) {
		/*
		 * mmio emulation of AArch32 reads/writes is not supported.
		 */
		*esr &= ~ESR_EL2_ABORT_ISV_BIT;
		return true;
	}
	return false;
}

static unsigned long get_dabt_write_value(struct rec *rec, unsigned long esr)
{
	unsigned int rt = esr_srt(esr);

	/* Handle xzr */
	if (rt == 31U) {
		return 0UL;
	}

	return rec_active_plane(rec)->regs[rt] & access_mask(esr);
}

/*
 * Returns 'true' if access from @rec to @addr is within the Protected IPA space.
 */
static bool access_in_rec_par(struct rec *rec, unsigned long addr)
{
	/*
	 * It is OK to check only the base address of the access because:
	 * - The Protected IPA space starts at address zero.
	 * - The IPA width is below 64 bits, therefore the access cannot
	 *   wrap around.
	 */
	return addr_in_rec_par(rec, addr);
}

/*
 * Returns 'true' if the @ipa is in PAR and its RIPAS is 'empty'.
 *
 * @ipa must be aligned to the granule size.
 */
static bool ipa_is_empty(unsigned long ipa, struct rec *rec)
{
	struct s2_walk_result s2_walk;
	enum s2_walk_status walk_status;

	assert(GRANULE_ALIGNED(ipa));

	walk_status = realm_ipa_to_pa(rec, ipa, &s2_walk);

	if (walk_status == WALK_SUCCESS) {
		granule_unlock(s2_walk.llt);
	}

	if ((walk_status != WALK_INVALID_PARAMS) &&
	    (s2_walk.ripas_val == RIPAS_EMPTY)) {
		return true;
	}
	return false;
}

static bool fsc_is_external_abort(unsigned long fsc)
{
	if (fsc == ESR_EL2_ABORT_FSC_SEA) {
		return true;
	}

	if ((fsc >= ESR_EL2_ABORT_FSC_SEA_TTW_START) &&
	    (fsc <= ESR_EL2_ABORT_FSC_SEA_TTW_END)) {
		return true;
	}

	return false;
}

static bool abort_is_permission_fault(unsigned long esr)
{
	unsigned long fsc = esr & MASK(ESR_EL2_ABORT_FSC);

	if ((fsc >= ESR_EL2_ABORT_FSC_PERM_FAULT_START) &&
	    (fsc <= ESR_EL2_ABORT_FSC_PERM_FAULT_END)) {
		return true;
	}

	return false;
}

/*
 * Handles Data/Instruction Aborts at a lower EL with External Abort fault
 * status code (D/IFSC).
 * Returns 'true' if the exception is the external abort and the `rec_exit`
 * structure is populated, 'false' otherwise.
 */
static bool handle_sync_external_abort(struct rec *rec,
				       struct rmi_rec_exit *rec_exit,
				       unsigned long esr)
{
	unsigned long fsc = esr & MASK(ESR_EL2_ABORT_FSC);
	unsigned long set = esr & MASK(ESR_EL2_ABORT_SET);
	(void)rec;

	if (!fsc_is_external_abort(fsc)) {
		return false;
	}

	switch (set) {
	case ESR_EL2_ABORT_SET_UER:
		/*
		 * The recoverable SEA.
		 * Inject the sync. abort into the Realm.
		 * Report the exception to the host.
		 */
		inject_sync_idabort(ESR_EL2_ABORT_FSC_SEA);
		/*
		 * Fall through.
		 */
	case ESR_EL2_ABORT_SET_UEO:
		/*
		 * The restartable SEA.
		 * Report the exception to the host.
		 * The REC restarts the same instruction.
		 */
		rec_exit->esr = esr & ESR_NONEMULATED_ABORT_MASK;

		/*
		 * The value of the HPFAR_EL2 is not provided to the host as
		 * it is undefined for external aborts.
		 *
		 * We also don't provide the content of FAR_EL2 because it
		 * has no practical value to the host without the HPFAR_EL2.
		 */
		break;
	case ESR_EL2_ABORT_SET_UC:
		/*
		 * The uncontainable SEA.
		 * Fatal to the system.
		 */
		system_abort();
		break;
	default:
		assert(false);
	}

	return true;
}

void emulate_stage2_data_abort(struct rec *rec,
			       struct rmi_rec_exit *rec_exit,
			       unsigned long rtt_level,
			       unsigned long ipa)
{
	assert(rtt_level <= (unsigned long)S2TT_PAGE_LEVEL);

	/*
	 * Setup Exception Syndrom Register to emulate a real data abort
	 * and return to NS host to handle it.
	 */
	rec_exit->esr = (ESR_EL2_EC_DATA_ABORT |
			(ESR_EL2_ABORT_FSC_TRANSLATION_FAULT_L0 + rtt_level));
	rec_exit->far = 0UL;
	rec_exit->hpfar = ipa >> HPFAR_EL2_FIPA_OFFSET;
	rec_exit->exit_reason = RMI_EXIT_SYNC;
}

/*
 * Returns 'true' if the abort is handled and the RMM should return to the Realm,
 * and returns 'false' if the exception should be reported to the HS host.
 */
static bool handle_data_abort(struct rec *rec, struct rmi_rec_exit *rec_exit,
			      unsigned long esr)
{
	unsigned long far = 0UL;
	unsigned long hpfar = read_hpfar_el2();
	unsigned long fipa = (hpfar & MASK(HPFAR_EL2_FIPA)) << HPFAR_EL2_FIPA_OFFSET;
	unsigned long write_val = 0UL;
	bool empty_ipa;

	if (handle_sync_external_abort(rec, rec_exit, esr)) {
		/*
		 * All external aborts are immediately reported to the host.
		 */
		return false;
	}

	empty_ipa = ipa_is_empty(fipa, rec);
	if (rec->active_plane_id != PRIMARY_PLANE_ID) {
		/*
		 * Data aborts from secondary plane to primary plane are
		 * reported when:
		 *	- There is a permission fault
		 *	- The fetch was from an 'empty' memory.
		 * Note that this may occur only if the abort is from PAR
		 */
		if (abort_is_permission_fault(esr) || empty_ipa) {
			assert(acces_is_rec_par(rec, fipa));
			return handle_secondary_plane_exit(rec, rec_exit,
							   ARM_EXCEPTION_SYNC_LEL);
		}
	} else {
		/*
		 * The SEA is injected back to primary plane if:
		 *	- The fetch was from 'empty' memory.
		 */
		if (empty_ipa) {
			inject_sync_idabort(ESR_EL2_ABORT_FSC_SEA);
			return true;
		}
	}

	/* The rest of data aborts are reported to the host */
	if (fipa >= rec_ipa_size(rec)) {
		inject_sync_idabort(ESR_EL2_ABORT_FSC_SEA);
		return true;
	}

	if (fixup_aarch32_data_abort(rec, &esr) ||
	    access_in_rec_par(rec, fipa)) {
		esr &= ESR_NONEMULATED_ABORT_MASK;
		goto end;
	}

	if (esr_is_write(esr)) {
		write_val = get_dabt_write_value(rec, esr);
	}

	far = read_far_el2() & ~GRANULE_MASK;
	esr &= ESR_EMULATED_ABORT_MASK;

end:
	rec_exit->esr = esr;
	rec_exit->far = far;
	rec_exit->hpfar = hpfar;
	rec_exit->gprs[0] = write_val;
	rec_exit->rtt_tree = (unsigned long)active_s2_context_idx(rec);

	return false;
}

/*
 * Returns 'true' if the abort is handled and the RMM should return to the Realm,
 * and returns 'false' if the exception should be reported to the NS host.
 */
static bool handle_instruction_abort(struct rec *rec, struct rmi_rec_exit *rec_exit,
				     unsigned long esr)
{
	unsigned long fsc = esr & MASK(ESR_EL2_ABORT_FSC);
	unsigned long fsc_type = fsc & ~MASK(ESR_EL2_ABORT_FSC_LEVEL);
	unsigned long hpfar = read_hpfar_el2();
	unsigned long fipa = (hpfar & MASK(HPFAR_EL2_FIPA)) << HPFAR_EL2_FIPA_OFFSET;
	bool empty_ipa, in_par;

	if (handle_sync_external_abort(rec, rec_exit, esr)) {
		/*
		 * All external aborts are immediately reported to the host.
		 */
		return false;
	}

	empty_ipa = ipa_is_empty(fipa, rec);
	in_par = access_in_rec_par(rec, fipa);
	if (rec->active_plane_id != PRIMARY_PLANE_ID) {
		/*
		 * Instruction aborts from secondary plane to primary plane are
		 * reported when:
		 *	- The fetch was from outside PAR
		 *	- There is a permission fault
		 *	- The fetch was from an 'empty' memory.
		 * Note that this may occur only if the abort is from PAR
		 */
		if (abort_is_permission_fault(esr) || empty_ipa || !in_par) {
			return handle_secondary_plane_exit(rec, rec_exit,
							   ARM_EXCEPTION_SYNC_LEL);
		}
	} else {
		/*
		 * The SEA is injected back to primary plane if:
		 *	- The fetch was from 'empty' memory
		 *	- The retch was from outside PAR
		 */
		if (empty_ipa || !in_par) {
			inject_sync_idabort(ESR_EL2_ABORT_FSC_SEA);
			return true;
		}
	}

	/* The rest of instruction aborts are reported to the host */
	if (fsc_type != ESR_EL2_ABORT_FSC_TRANSLATION_FAULT) {
		unsigned long far = read_far_el2();

		/*
		 * TODO: Should this ever happen, or is it an indication of an
		 * internal consistency failure in the RMM which should lead
		 * to a panic instead?
		 */

		ERROR("Unhandled instruction abort:\n");
		ERROR("    FSC: %12s0x%02lx\n", " ", fsc);
		ERROR("    FAR: %16lx\n", far);
		ERROR("  HPFAR: %16lx\n", hpfar);
		return false;
	}

	rec_exit->hpfar = hpfar;
	rec_exit->esr = esr & ESR_NONEMULATED_ABORT_MASK;
	rec_exit->rtt_tree = (unsigned long)active_s2_context_idx(rec);

	return false;
}

/*
 * Handle FPU or SVE exceptions.
 * Returns: true if the exception is handled.
 */
static bool handle_simd_exception(struct rec *rec, unsigned long esr)
{
	unsigned long esr_el2_ec = esr & MASK(ESR_EL2_EC);

	/*
	 * If the REC wants to use SVE and if SVE is not enabled for this REC
	 * then inject undefined abort. This can happen when CPU implements
	 * FEAT_SVE but the Realm didn't request this feature during creation.
	 */
	if ((esr_el2_ec == ESR_EL2_EC_SVE) && !rec->realm_info.simd_cfg.sve_en) {
		realm_inject_undef_abort();
		return true;
	}

	/*
	 * This is a special case where an SVE Realm accessing certain SVE or SME
	 * instructions will be reported as SME exception if RMM was REC entered
	 * with PSTATE.SM=1. RMM needs to distinguish between lazy save-restore
	 * for SVE and access to SME.
	 * Some cases:
	 * 1. If SVE is disabled for the realm, then RMM needs to inject UNDEF.
	 * 2. If SVE is enabled for the realm, RMM will restore SVE SIMD context
	 *    of the REC and will resume the Realm (this will get the CPU out of
	 *    streaming mode). While re-trying the faulting instruction if it
	 *    generates a SME exception, then RMM will inject undefined abort
	 *    since SME is not supported for Realm.
	 */
	if ((esr_el2_ec == ESR_EL2_EC_SME) &&
	    (!rec->realm_info.simd_cfg.sve_en ||
	     (rec->active_simd_ctx == rec->aux_data.simd_ctx))) {
		realm_inject_undef_abort();
		return true;
	}

	/*
	 * As REC uses lazy enablement, upon FPU/SVE exception the active SIMD
	 * context must not be the REC's context
	 */
	assert(rec->active_simd_ctx != rec->aux_data.simd_ctx);

	/* Save the NS SIMD context and restore REC's SIMD context */
	rec->active_simd_ctx = simd_context_switch(rec->active_simd_ctx,
						   rec->aux_data.simd_ctx);

	/*
	 * As the REC SIMD context is now restored, enable SIMD flags in REC's
	 * cptr based on REC's SIMD configuration.
	 */
	SIMD_ENABLE_CPTR_FLAGS(&rec->realm_info.simd_cfg, rec_active_plane(rec)->sysregs.cptr_el2);

	/*
	 * Return 'true' indicating that this exception has been handled and
	 * execution can continue.
	 */
	return true;
}

static void advance_pc(void)
{
	unsigned long pc = read_elr_el2();

	write_elr_el2(pc + 4UL);
}

static inline bool rsi_handler_needs_fpu(unsigned int id)
{
#ifdef RMM_FPU_USE_AT_REL2
	if ((id == SMC_RSI_ATTEST_TOKEN_CONTINUE) ||
	    (id == SMC_RSI_MEASUREMENT_EXTEND)) {
		return true;
	}
#else
	(void)id;
#endif
	return false;
}

/*
 * Return 'true' if execution should continue in the REC, otherwise return
 * 'false' to go back to the NS caller of REC.Enter.
 */
static bool handle_realm_rsi(struct rec *rec, struct rmi_rec_exit *rec_exit)
{
	struct rsi_result res = { 0 };
	struct rec_plane *plane = rec_active_plane(rec);
	unsigned int function_id = (unsigned int)plane->regs[0];
	bool restore_simd_ctx = false;
	unsigned int i;

	RSI_LOG_SET(plane->regs);

	/*
	 * According to SMCCCv1.1+ if SMC call doesn't return result
	 * in register starting from X4, it must preserve its value.
	 */
	for (i = 4U; i < SMC_RESULT_REGS; ++i) {
		res.smc_res.x[i] = plane->regs[i];
	}

	if (rec->active_plane_id != PRIMARY_PLANE_ID) {
		/* RSI API is only available to Primary plane */
		res.action = UPDATE_REC_RETURN_TO_REALM;
		res.smc_res.x[0] = SMC_NOT_SUPPORTED;
		goto out;
	}

	/* Ignore SVE hint bit, until RMM supports SVE hint bit */
	function_id &= ~SMC_SVE_HINT;

	if (rsi_handler_needs_fpu(function_id) == true) {
		simd_context_save(rec->active_simd_ctx);
		restore_simd_ctx = true;
	}

	switch (function_id) {
	case SMCCC_VERSION:
		res.action = UPDATE_REC_RETURN_TO_REALM;
		res.smc_res.x[0] = SMCCC_VERSION_NUMBER;
		break;
	case SMC32_PSCI_FID_MIN ... SMC32_PSCI_FID_MAX:
	case SMC64_PSCI_FID_MIN ... SMC64_PSCI_FID_MAX:
		handle_psci(rec, rec_exit, &res);
		break;
	case SMC_RSI_VERSION:
		handle_rsi_version(rec, &res);
		break;
	case SMC_RSI_FEATURES:
		handle_rsi_features(rec, &res);
		break;
	case SMC_RSI_ATTEST_TOKEN_INIT:
		handle_rsi_attest_token_init(rec, &res);
		break;
	case SMC_RSI_ATTEST_TOKEN_CONTINUE:
		handle_rsi_attest_token_continue(rec, rec_exit, &res);
		break;
	case SMC_RSI_MEASUREMENT_READ:
		handle_rsi_measurement_read(rec, &res);
		break;
	case SMC_RSI_MEASUREMENT_EXTEND:
		handle_rsi_measurement_extend(rec, &res);
		break;
	case SMC_RSI_REALM_CONFIG:
		handle_rsi_realm_config(rec, &res);
		break;
	case SMC_RSI_IPA_STATE_SET:
		handle_rsi_ipa_state_set(rec, rec_exit, &res);
		break;
	case SMC_RSI_IPA_STATE_GET:
		handle_rsi_ipa_state_get(rec, &res);
		break;
	case SMC_RSI_HOST_CALL:
		handle_rsi_host_call(rec, rec_exit, &res);
		break;
	case SMC_RSI_MEM_GET_PERM_VALUE:
		handle_rsi_mem_get_perm_value(rec, &res);
		break;
	case SMC_RSI_MEM_SET_PERM_INDEX:
		handle_rsi_mem_set_perm_index(rec, rec_exit, &res);
		break;
	case SMC_RSI_MEM_SET_PERM_VALUE:
		handle_rsi_mem_set_perm_value(rec, &res);
		break;
	default:
		res.action = UPDATE_REC_RETURN_TO_REALM;
		res.smc_res.x[0] = SMC_UNKNOWN;
		break;
	}

	if (restore_simd_ctx) {
		simd_context_restore(rec->active_simd_ctx);
	}

out:
	if (((unsigned int)res.action & FLAG_UPDATE_REC) != 0U) {
		for (i = 0U; i < SMC_RESULT_REGS; ++i) {
			plane->regs[i] = res.smc_res.x[i];
		}
	}

	if (((unsigned int)res.action & FLAG_STAGE_2_ABORT) != 0U) {
		/*
		 * The RSI call cannot progress because the IPA that was
		 * provided by the Realm has invalid mapping. Emulate the
		 * data abort gainst that IPA so that the host can bring
		 * the page in.
		 *
		 * @TODO: All RSI calls hold the IPA in X1. This may not be
		 * true in the future so further refactoring around data abort
		 * emulation might be required.
		 */
		unsigned long ipa = rec_active_plane(rec)->regs[1];

		emulate_stage2_data_abort(rec, rec_exit, res.rtt_level, ipa);
	} else {
		advance_pc();
	}

	/* Log RSI call */
	RSI_LOG_EXIT(function_id, plane->regs);

	return (((unsigned int)res.action & FLAG_EXIT_TO_HOST) == 0U);
}

/*
 * Return 'true' if the RMM handled the exception,
 * 'false' to return to the Non-secure host.
 */
static bool handle_exception_sync(struct rec *rec, struct rmi_rec_exit *rec_exit)
{
	const unsigned long esr = read_esr_el2();

	switch (esr & MASK(ESR_EL2_EC)) {
	case ESR_EL2_EC_WFX:
		rec_exit->esr = esr & (MASK(ESR_EL2_EC) | ESR_EL2_WFx_TI_BIT);
		advance_pc();
		return false;
	case ESR_EL2_EC_HVC:
		realm_inject_undef_abort();
		return true;
	case ESR_EL2_EC_SMC:
		return handle_realm_rsi(rec, rec_exit);
	case ESR_EL2_EC_SYSREG: {
		bool ret = handle_sysreg_access_trap(rec, rec_exit, esr);

		advance_pc();
		return ret;
	}
	case ESR_EL2_EC_INST_ABORT:
		return handle_instruction_abort(rec, rec_exit, esr);
	case ESR_EL2_EC_DATA_ABORT:
		return handle_data_abort(rec, rec_exit, esr);
	case ESR_EL2_EC_FPU:
	case ESR_EL2_EC_SVE:
	case ESR_EL2_EC_SME:
		return handle_simd_exception(rec, esr);
	default:
		/*
		 * TODO: Check if there are other exit reasons we could
		 * encounter here and handle them appropriately
		 */
		break;
	}

	VERBOSE("Unhandled sync exit ESR: %08lx (EC: %lx ISS: %lx)\n",
		esr, EXTRACT(ESR_EL2_EC, esr), EXTRACT(ESR_EL2_ISS, esr));

	/*
	 * Zero values in esr, far & hpfar of 'rec_exit' structure
	 * will be returned to the NS host.
	 * The only information that may leak is when there was
	 * some unhandled/unknown reason for the exception.
	 */
	return false;
}

/*
 * Return 'true' if the RMM handled the exception, 'false' to return to the
 * Non-secure host.
 */
static bool handle_exception_serror_lel(struct rec *rec, struct rmi_rec_exit *rec_exit)
{
	const unsigned long esr = read_esr_el2();

	if ((esr & ESR_EL2_SERROR_IDS_BIT) != 0UL) {
		/*
		 * Implementation defined content of the esr.
		 */
		system_abort();
	}

	if ((esr & MASK(ESR_EL2_SERROR_DFSC)) != ESR_EL2_SERROR_DFSC_ASYNC) {
		/*
		 * Either Uncategorized or Reserved fault status code.
		 */
		system_abort();
	}

	switch (esr & MASK(ESR_EL2_SERROR_AET)) {
	case ESR_EL2_SERROR_AET_UEU:	/* Unrecoverable RAS Error */
	case ESR_EL2_SERROR_AET_UER:	/* Recoverable RAS Error */
		/*
		 * The abort is fatal to the current S/W. Inject the SError into
		 * the Realm so it can e.g. shut down gracefully or localize the
		 * problem at the specific EL0 application.
		 *
		 * Note: Consider shutting down the Realm here to avoid
		 * the host's attack on unstable Realms.
		 */
		inject_serror(rec, esr);
		/*
		 * Fall through.
		 */
	case ESR_EL2_SERROR_AET_CE:	/* Corrected RAS Error */
	case ESR_EL2_SERROR_AET_UEO:	/* Restartable RAS Error */
		/*
		 * Report the exception to the host.
		 */
		rec_exit->esr = esr & ESR_SERROR_MASK;
		break;
	case ESR_EL2_SERROR_AET_UC:	/* Uncontainable RAS Error */
		system_abort();
		break;
	default:
		/*
		 * Unrecognized Asynchronous Error Type
		 */
		assert(false);
	}

	return false;
}

static bool handle_exception_irq_lel(struct rec *rec, struct rmi_rec_exit *rec_exit)
{
	(void)rec;

	rec_exit->exit_reason = RMI_EXIT_IRQ;

	/*
	 * With GIC all virtual interrupt programming
	 * must go via the NS hypervisor.
	 */
	return false;
}

/* Returns 'true' when returning to Realm (S) and false when to NS */
bool handle_realm_exit(struct rec *rec, struct rmi_rec_exit *rec_exit, int exception)
{
	struct rec_plane *plane = rec_active_plane(rec);

	switch (exception) {
	case ARM_EXCEPTION_SYNC_LEL: {
		bool ret;

		/*
		 * TODO: Sanitize ESR to ensure it doesn't leak sensitive
		 * information.
		 */
		rec_exit->exit_reason = RMI_EXIT_SYNC;
		ret = handle_exception_sync(rec, rec_exit);
		if (!ret) {
			plane->last_run_info.esr = read_esr_el2();
			plane->last_run_info.far = read_far_el2();
			plane->last_run_info.hpfar = read_hpfar_el2();
		}
		return ret;

		/*
		 * TODO: Much more detailed handling of exit reasons.
		 */
	}
	case ARM_EXCEPTION_IRQ_LEL:
		return handle_exception_irq_lel(rec, rec_exit);
	case ARM_EXCEPTION_FIQ_LEL:
		rec_exit->exit_reason = RMI_EXIT_FIQ;
		break;
	case ARM_EXCEPTION_SERROR_LEL: {
		const unsigned long esr = read_esr_el2();
		bool ret;

		/*
		 * TODO: Sanitize ESR to ensure it doesn't leak sensitive
		 * information.
		 */
		rec_exit->exit_reason = RMI_EXIT_SERROR;
		ret = handle_exception_serror_lel(rec, rec_exit);
		if (!ret) {
			plane->last_run_info.esr = esr;
			plane->last_run_info.far = read_far_el2();
			plane->last_run_info.hpfar = read_hpfar_el2();
		}
		return ret;
	}
	default:
		INFO("Unrecognized exit reason: %d\n", exception);
		break;
	}

	return false;
}

static void handle_plane_exit_sync(struct rec *rec,
				   struct rsi_plane_exit *exit)
{
	const unsigned long esr_el2 = read_esr_el2();
	const unsigned long elr_el2 = read_elr_el2();
	const unsigned long far_el2 = read_far_el2();
	const unsigned long hpfar_el2 = read_hpfar_el2();

	exit->exit_reason = RSI_EXIT_SYNC;

	/* TODO: need to do some sanitisation here */
	exit->elr_el2 = elr_el2;
	exit->esr_el2 = esr_el2;
	exit->far_el2 = far_el2;
	exit->hpfar_el2 = hpfar_el2;
}

static void do_handle_plane_exit(struct rec *rec, int exception,
				 struct rsi_plane_exit *exit)
{
	switch (exception) {
	case ARM_EXCEPTION_SYNC_LEL:
		handle_plane_exit_sync(rec, exit);
		break;
	default:
		ERROR("Unhandled Plane exit exception: 0x%x\n", exception);
	}
}

static void copy_el1_sysregs_to_plane_exit(struct sysreg_state *sysregs,
					   struct rsi_plane_el1_sysregs *exit)
{
	exit->sp_el0 = sysregs->sp_el0;
	exit->sp_el1 = sysregs->sp_el1;
	exit->elr_el1 = sysregs->elr_el1;
	exit->spsr_el1 = sysregs->spsr_el1;
	exit->pmcr_el0 = sysregs->pmcr_el0;
	exit->tpidrro_el0 = sysregs->tpidrro_el0;
	exit->tpidr_el0 = sysregs->tpidr_el0;
	exit->csselr_el1 = sysregs->csselr_el1;
	exit->sctlr_el1 = sysregs->sctlr_el1;
	exit->actlr_el1 = sysregs->actlr_el1;
	exit->cpacr_el1 = sysregs->cpacr_el1;
	exit->zcr_el1 = sysregs->zcr_el1;
	exit->ttbr0_el1 = sysregs->ttbr0_el1;
	exit->ttbr1_el1 = sysregs->ttbr1_el1;
	exit->tcr_el1 = sysregs->tcr_el1;
	exit->esr_el1 = sysregs->esr_el1;
	exit->afsr0_el1 = sysregs->afsr0_el1;
	exit->afsr1_el1 = sysregs->afsr1_el1;
	exit->far_el1 = sysregs->far_el1;
	exit->mair_el1 = sysregs->mair_el1;
	exit->vbar_el1 = sysregs->vbar_el1;
	exit->contextidr_el1 = sysregs->contextidr_el1;
	exit->tpidr_el1 = sysregs->tpidr_el1;
	exit->amair_el1 = sysregs->amair_el1;
	exit->cntkctl_el1 = sysregs->cntkctl_el1;
	exit->par_el1 = sysregs->par_el1;
	exit->mdscr_el1 = sysregs->mdscr_el1;
	exit->disr_el1 = sysregs->disr_el1;
	exit->mpam0_el1 = sysregs->mpam0_el1;
	exit->cntp_ctl_el0 = sysregs->cntp_ctl_el0;
	exit->cntp_cval_el0 = sysregs->cntp_cval_el0;
	exit->cntv_ctl_el0 = sysregs->cntv_ctl_el0;
	exit->cntv_cval_el0 = sysregs->cntv_cval_el0;
}

static void copy_gicstate_to_plane_exit(struct gic_cpu_state *gicstate,
					struct rsi_plane_exit *exit)
{
	/* TODO: need to do some sanitisation here */

	exit->gicv3_hcr = gicstate->ich_hcr_el2;

	for (int i = 0; i < RSI_PLANE_GIC_NUM_LRS; i++) {
		exit->gicv3_lrs[i] = gicstate->ich_lr_el2[i];
	}

	exit->gicv3_misr = gicstate->ich_misr_el2;
	exit->gicv3_vmcr = gicstate->ich_vmcr_el2;
}

static void copy_state_to_plane_exit(struct rec_plane *plane,
				     struct rsi_plane_exit *exit)
{
	for (int i = 0; i < RSI_PLANE_NR_GPRS; i++) {
		exit->gprs[i] = plane->regs[i];
	}

	copy_el1_sysregs_to_plane_exit(&plane->sysregs, &exit->el1_sysregs);
	copy_gicstate_to_plane_exit(&plane->sysregs.gicstate, exit);
}

/*
 * Handles the exit from secondary planes.
 *
 * It 'true' is returned:
 * - The Realm has switched to primary plane
 * - The Realm can continue running
 *
 * It 'false' is returned:
 * - The Realm has remained to primary plane because the stage 2 mapping of
 *   `rsi_plane_run` page is not valid.
 * - The data abort against the `rsi_plane_run` page is emulated.
 * - The RMM should returned to the host so that the host can fix the mapping.
 * - The caller must ensure that the secondary plane executes the same
 *   instruction the next time the Realm is scheduled.
 */
bool handle_secondary_plane_exit(struct rec *rec, struct rmi_rec_exit *rec_exit, int exception)
{
	enum s2_walk_status walk_status;
	struct s2_walk_result walk_res;
	struct rec_plane *primary_plane, *secondary_plane;
	unsigned long run_ipa, ret;
	struct granule *gr;
	struct rsi_plane_run *run;

	assert(rec->active_plane_id != 0);

	primary_plane = rec_primary_plane(rec);
	secondary_plane = rec_active_plane(rec);

	run_ipa = primary_plane->regs[2];

	/*
	 * Find the rsi_plane_run page, where we should report the secondary
	 * plane's exit to the primary one.
	 */
	walk_status = realm_ipa_to_pa(rec, run_ipa, &walk_res);

	/*
	 * Alignment and Protected IPA checks were done by
	 * handle_rsi_plane_enter
	 */
	assert(walk_status != WALK_INVALID_PARAMS);


	if (walk_res.ripas_val == RIPAS_EMPTY) {
		/*
		 * Primary plane has set the ripas of `rsi_plane_run` granule
		 * to "empty".
		 * Exit to the primary plane with error. The content of the
		 * secondary plane will be lost.
		 */
		ret = RSI_ERROR_INPUT;
		goto out_return_to_primary_plane;
	} else if ((walk_res.ripas_val == RIPAS_DESTROYED) ||
		  ((walk_res.ripas_val == RIPAS_RAM) && (walk_status == WALK_FAIL))) {
		/*
		 * `rsi_plane_run` page is either destroyed or unassigned_ram s2tte.
		 */
		emulate_stage2_data_abort(rec, rec_exit, walk_res.rtt_level, run_ipa);
		return false;
	}

	assert(walk_status == WALK_SUCCESS);

	ret = RSI_SUCCESS;

	/* Save target Plane state to REC */
	save_realm_state(secondary_plane);

	/* Map rsi_plane_run granule to RMM address space */
	gr = find_granule(walk_res.pa);
	run = (struct rsi_plane_run *)buffer_granule_map(gr, SLOT_RSI_CALL);

	/* Zero the exit structure */
	(void)memset(&run->exit, 0, sizeof(struct rsi_plane_exit));

	/* Copy target Plane state to exit structure */
	copy_state_to_plane_exit(secondary_plane, &run->exit);

	/* Populate other fields of exit structure */
	do_handle_plane_exit(rec, exception, &run->exit);

	/* Unmap rsi_plane_run granule */
	buffer_unmap(run);

	/* Unlock last level RTT */
	granule_unlock(walk_res.llt);

out_return_to_primary_plane:
	/* Return values to primary plane */
	primary_plane->regs[0] = ret;
	primary_plane->regs[1] = 0UL;
	primary_plane->regs[2] = 0UL;
	primary_plane->regs[3] = 0UL;

	/* Advance Plane 0 PC */
	primary_plane->pc = primary_plane->pc + 4UL;

	/* Restore Plane 0 state from REC */
	restore_realm_state(rec, primary_plane);

	/* Record that Plane 0 is active */
	rec->active_plane_id = PRIMARY_PLANE_ID;

	configure_realm_stage2(rec);

	return true;
}
