/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch_features.h>
#include <arch_helpers.h>
#include <assert.h>
#include <cpuid.h>
#include <simd.h>
#include <simd_private.h>

/*
 * Global variable to store the SVE max vq length supported by the CPU. We
 * expect all CPUs in the system to support the same max vq length.
 */
static int32_t g_sve_max_vq = -1;

/*
 * The default CPU SIMD type is set as FPU. During init time, if CPU supports
 * SVE (which encompasses FPU), this will be updated to SIMD_SVE. And if CPU
 * supports SME (which encompasses part of SVE), then this will be updated to
 * SIMD_SME.
 */
static simd_t g_cpu_simd_type = SIMD_FPU;

/*
 * This structure is used for storing NS world FPU or SVE or Streaming SVE
 * context.
 */
struct ns_simd_state {
	struct simd_state simd;
	uint64_t ns_zcr_el2;
	bool ssve_mode;		/* Is NS in Streaming SVE mode */
	bool saved;		/* Is NS SIMD state (FPU/SVE/SME) saved */
} __attribute__((aligned(CACHE_WRITEBACK_GRANULE)));

static struct ns_simd_state g_ns_simd[MAX_CPUS];

static bool g_simd_state_saved[MAX_CPUS];

typedef enum {
	SVE_SAVE,
	SVE_RESTORE
} sve_op_t;

typedef enum {
	NORMAL_SVE,
	STREAMING_SVE
} sve_mode_t;

/*
 * Returns 'true' if the current CPU's SIMD (FPU/SVE) live state is saved in
 * memory else 'false'.
 */
bool simd_is_state_saved(void)
{
	return g_simd_state_saved[my_cpuid()];
}

/*
 * Program the ZCR_EL2.LEN field from the VQ, if current ZCR_EL2.LEN is not same
 * as the passed in VQ.
 */
static void sve_config_vq(uint8_t vq)
{
	u_register_t zcr_val;

	zcr_val = read_zcr_el2();
	if (EXTRACT(ZCR_EL2_LEN, zcr_val) != vq) {
		zcr_val &= ~MASK(ZCR_EL2_LEN);
		zcr_val |= INPLACE(ZCR_EL2_LEN, vq);
		write_zcr_el2(zcr_val);
		isb();
	}
}

/*
 * Helper routine to handle saving or restoring either Normal or Streaming SVE
 * state. The caller must ensure that appropriate traps (SVE or SME) are
 * disabled.
 */
static void handle_sve_state(sve_op_t sve_op, sve_mode_t sve_mode,
			     struct simd_state *simd)
{
	bool include_ffr;
	bool include_zcr;

	if (sve_mode == NORMAL_SVE) {
		/*
		 * Configure zcr_el2 before saving the vector registers:
		 *  For NS state : max_vq restricted by EL3 (g_sve_max_vq)
		 *  For Realms   : max_vq of Realm
		 */
		sve_config_vq(simd->t.sve.vq);
		include_ffr = true;
		include_zcr = true;
	} else {
		/*
		 * Streaming SVE state is saved with the existing SVL in SMCR_EL2
		 * that was programmed by NS world. RMM doesn't modify
		 * SMCR_EL2.LEN bits.
		 */
		include_ffr = sme_feat_fa64_enabled();
		include_zcr = is_feat_sve_present();
	}

	/*
	 * Save SVE state registers Z0-Z31, P0-P15, FFR, ZCR_EL12 and FPU status
	 * register FPSR/FPCR.
	 *
	 * TODO: Handle SVE hint bit
	 */
	if (sve_op == SVE_SAVE) {
		sve_save_state((uint64_t)&simd->t.sve, include_ffr, include_zcr);
	} else {
		sve_restore_state((uint64_t)&simd->t.sve, include_ffr,
				  include_zcr);
	}
}

/*
 * Save FPU or SVE state from registers to memory. The caller must disable
 * traps for the corresponding 'type'. In case of SVE state, the vq from the
 * sve state is programmed to ZCR_EL2.LEN before saving the state. As this
 * function will modify ZCR_EL2, the caller needs to save the value of this
 * register if it needs to be preserved.
 */
void simd_save_state(simd_t type, struct simd_state *simd)
{
	assert(simd != NULL);
	assert(simd->simd_type == SIMD_NONE);

	switch (type) {
	case SIMD_FPU:
		assert(is_fpen_enabled());
		fpu_save_state((uint64_t)&simd->t.fpu);
		break;
	case SIMD_SVE:
		assert(is_feat_sve_present() == true);
		assert(is_zen_enabled() && is_fpen_enabled());

		handle_sve_state(SVE_SAVE, NORMAL_SVE, simd);
		break;
	case SIMD_SME:
		assert(is_feat_sme_present() == true);
		assert(is_smen_enabled() && is_zen_enabled() &&
		       is_fpen_enabled());

		if (is_feat_sve_present() && !is_sme_sm()) {
			handle_sve_state(SVE_SAVE, NORMAL_SVE, simd);
		} else if (is_sme_sm()) {
			handle_sve_state(SVE_SAVE, STREAMING_SVE, simd);
		} else {
			fpu_save_state((uint64_t)&simd->t.fpu);
		}
		break;
	default:
		assert(false);
	}
	simd->simd_type = type;
	g_simd_state_saved[my_cpuid()] = true;
}

/*
 * Restore FPU or SVE state from memory to registers. The caller must disable
 * traps for the corresponding 'type'. In case of SVE state, the vq from the
 * sve state is programmed to ZCR_EL2.LEN before restoring the state.
 */
void simd_restore_state(simd_t type, struct simd_state *simd)
{
	assert(simd != NULL);
	switch (type) {
	case SIMD_FPU:
		assert(is_fpen_enabled());
		assert(simd->simd_type == SIMD_FPU);
		fpu_restore_state((uint64_t)&simd->t.fpu);
		break;
	case SIMD_SVE:
		assert(is_feat_sve_present() == true);
		assert(is_zen_enabled() && is_fpen_enabled());
		assert(simd->simd_type == SIMD_SVE);

		handle_sve_state(SVE_RESTORE, NORMAL_SVE, simd);
		break;
	case SIMD_SME:
		assert(is_feat_sme_present() == true);
		assert(is_smen_enabled() && is_zen_enabled() &&
		       is_fpen_enabled());
		assert(simd->simd_type == SIMD_SME);

		if (is_feat_sve_present() && !is_sme_sm()) {
			handle_sve_state(SVE_RESTORE, NORMAL_SVE, simd);
		} else if (is_sme_sm()) {
			handle_sve_state(SVE_RESTORE, STREAMING_SVE, simd);
		} else {
			fpu_restore_state((uint64_t)&simd->t.fpu);
		}
		break;
	default:
		assert(false);
	}
	simd->simd_type = SIMD_NONE;
	g_simd_state_saved[my_cpuid()] = false;
}

/*
 * Save NS SIMD state based on CPU SIMD type. For SVE, save the current zcr_el2
 * and call simd_save_state() which will save the SVE state (Z, P, FFR) after
 * setting the zcr_el2 to max VQ
 */
void simd_save_ns_state(void)
{
	unsigned int cpu_id = my_cpuid();
	simd_t stype;

	assert(g_ns_simd[cpu_id].saved == false);
	stype = g_cpu_simd_type;

	simd_enable(stype);
	/*
	 * Save the NS zcr_el2 value since EL3 doesn't bank this. Note that the
	 * save of NS SVE context occurs with MAX_SVE_VL to prevent leakage.
	 *
	 * If CPU supports SME (which encompasses SVE), the NS_ZCR_EL2 is saved
	 * as Realms might use FPU or SVE.
	 */
	if (is_feat_sve_present()) {
		g_ns_simd[cpu_id].ns_zcr_el2 = read_zcr_el2();
	}

	/*
	 * As Realms do not support SME, the ZA state (for FEAT_SME) or ZT0
	 * (for FEAT_SME2) are not saved. The PSTATE.ZA is not accessed by RMM.
	 *
	 * As Realms support FPU/SVE, when the CPU is in Streaming SVE mode
	 * (PSTATE.SM is 1), the Streaming SVE state is saved.
	 *
	 * When SME is supported and the CPU not in Streaming SVE mode, then SVE
	 * state is saved.
	 */

	/* Set Streaming mode status flag in per-cpu data */
	if (stype == SIMD_SME) {
		g_ns_simd[cpu_id].ssve_mode = is_sme_sm();
	}

	simd_save_state(stype, &g_ns_simd[cpu_id].simd);

	/*
	 * After saving the state, exit Streaming SVE mode, if entered with
	 * Streaming SVE mode enabled. This makes FPU/SVE accessible by Realms.
	 *
	 * Exiting Streaming SVE mode doesn't have any impact on SME ZA storage
	 * or, if implemented, ZT0 storage.
	 */
	if ((stype == SIMD_SME) && g_ns_simd[cpu_id].ssve_mode) {
		sme_smstop();
	}

	simd_disable();
	g_ns_simd[cpu_id].saved = true;
}

/*
 * Restore NS SIMD state based on CPU SIMD type. For SVE, the
 * simd_restore_state() will set zcr_el2 to max VQ and restore the SVE state
 * (Z, P, FFR) registers.
 */
void simd_restore_ns_state(void)
{
	unsigned int cpu_id = my_cpuid();
	simd_t stype;

	assert(g_ns_simd[cpu_id].saved == true);
	stype = g_cpu_simd_type;

	simd_enable(stype);

	if (stype == SIMD_SME && g_ns_simd[cpu_id].ssve_mode) {
		/*
		 * Upon entering Streaming SVE mode each implemented bit
		 * of SVE registers Z0-Z31, P0-P15, and FFR in the new
		 * mode is set to zero. Even if Normal SVE implements a
		 * greater vector length than Streaming SVE, always the
		 * whole state is cleared.
		 *
		 * Entering Streaming SVE mode doesn't have any impact
		 * on SME ZA storage or, if implemented, ZT0 storage.
		 */
		sme_smstart();
	}

	simd_restore_state(stype, &g_ns_simd[cpu_id].simd);

	/*
	 * Note that the restore SVE state for NS state happens with
	 * MAX_SVE_VL to prevent leakage. RMM now needs to restore the NS zcr_el2
	 * value since EL3 is not saving this.
	 */
	if (is_feat_sve_present()) {
		write_zcr_el2(g_ns_simd[cpu_id].ns_zcr_el2);
		isb();
	}

	simd_disable();
	g_ns_simd[cpu_id].saved = false;
}

/* Return the SVE max vq discovered during init */
unsigned int simd_sve_get_max_vq(void)
{
	assert(is_feat_sve_present() == true);
	assert(g_sve_max_vq != -1);
	return g_sve_max_vq;
}

/*
 * Initializes simd_state. Set the 'type' in simd state and if 'type' is
 * SVE then set the 'sve_vq' in simd state. This interface is called by REC
 */
void simd_state_init(simd_t type, struct simd_state *simd, uint8_t sve_vq)
{
	assert(simd != NULL);
	assert((type == SIMD_FPU) || (type == SIMD_SVE));
	assert(simd->simd_type == SIMD_NONE);

	/*
	 * TODO: bzero simd state. Currently the simd context is assumed to be
	 * zeroed out but with FEAT_MEC enabled, the simd context in AUX granule
	 * might not be zeroed out.
	 */
	if (type == SIMD_SVE) {
		assert(sve_vq <= g_sve_max_vq);
		simd->t.sve.vq = sve_vq;
	}
	simd->simd_type = type;
}

/* Find the SVE max vector length restricted by EL3 */
static void sve_init_once(void)
{
	/*
	 * Called only once during cold boot. Check if 'g_sve_max_vq' is already
	 * initialized.
	 */
	if (g_sve_max_vq != -1) {
		return;
	}

	/*
	 * Write architecture max limit for vector length to ZCR_EL2.LEN and read
	 * back the SVE vector length reported by RDVL. This will give the vector
	 * length limit set by EL3 for its lower ELs. RMM will use this value as
	 * max limit for EL2 and lower ELs.
	 */
	simd_enable(SIMD_SVE);

	/*
	 * Configure ZCR.LEN to SVE_VQ_ARCH_MAX, the old zcr_el2 is not restored
	 * as this is called only once during cold boot.
	 */
	sve_config_vq(SVE_VQ_ARCH_MAX);
	g_sve_max_vq = SVE_VL_TO_VQ(sve_rdvl());
	g_cpu_simd_type = SIMD_SVE;

	simd_disable();
}

/* Find the architecturally permitted (Streaming Vector Length) SVL */
static void sme_init_once(void)
{
	static int32_t sme_svq_arch_max = -1;
	uint64_t smcr_val;

	/*
	 * Called only once during cold boot. Check if 'sme_svq_arch_max' is
	 * already initialized.
	 */
	if (sme_svq_arch_max != -1) {
		return;
	}

	simd_enable(SIMD_SME);

	/*
	 * Arm SME supplement recommends to request an out of range vector
	 * length of 8192 bytes by writing 0x1ff to SMCR_ELx[8:0]. Reading back
	 * the register will give the max architecturally permitted SVQ.
	 *
	 * The old smcr_el2 is not restored as this is called only once during
	 * cold boot.
	 */
	smcr_val = read_smcr_el2();
	smcr_val |= MASK(SMCR_EL2_RAZ_LEN);
	write_smcr_el2(smcr_val);
	isb();
	sme_svq_arch_max = EXTRACT(SMCR_EL2_RAZ_LEN, read_smcr_el2());

	/*
	 * Streaming SVE shares SVE register set Z/P/FFR. RMM will save and
	 * restore Streaming SVE state in 'sve_state', and 'sve_state' can hold
	 * vector registers for up to 2048 bits (vq: 15). If Streaming SVE mode
	 * reports a larger value than SVE_VQ_ARCH_MAX, then assert. Hopefully
	 * we won't hit this condition in the near future.
	 */
	assert(sme_svq_arch_max <= SVE_VQ_ARCH_MAX);

	g_cpu_simd_type = SIMD_SME;
	simd_disable();
}

/*
 * This function initializes the SIMD layer depending on SIMD capability of the
 * CPU (FPU/SVE/SME).
 */
void simd_init(void)
{
	unsigned int cpu_id = my_cpuid();

	if (is_feat_sve_present()) {
		sve_init_once();
		/* Set the max vq in NS simd state */
		g_ns_simd[cpu_id].simd.t.sve.vq = g_sve_max_vq;
	}

	if (is_feat_sme_present()) {
		sme_init_once();
	}
}
