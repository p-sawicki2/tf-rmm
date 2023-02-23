/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch_features.h>
#include <arch_helpers.h>
#include <assert.h>
#include <simd.h>

static bool sve_init_once;
static uint8_t g_sve_max_vq;

/* This structure is used for storing FPU or SVE context for NS world. */
struct ns_simd_state {
	struct simd_state simd;
	bool saved;
} __attribute__((aligned(CACHE_WRITEBACK_GRANULE)));
static struct ns_simd_state g_ns_simd[MAX_CPUS];

void simd_save_state(simd_t type, struct simd_state *simd)
{
	assert(simd != NULL);
	assert(simd->saved_state == SIMD_NONE);

	switch (type) {
	case SIMD_FPU:
		assert(is_fpen_enabled());
		fpu_save_state(&simd->t.fpu);
		break;
	case SIMD_SVE:
		assert(is_feat_sve_present() == true);
		assert(is_zen_enabled() && is_fpen_enabled());

		/*
		 * Before saving the SVE state, check if the current ZCR_EL2.LEN
		 * matches the context's SVE VQ
		 */
		assert(EXTRACT(ZCR_EL2_SVE_VL, read_zcr_el2()) ==
		       simd->t.sve.vq);

		/* Save SVE variable length registers Z */
		sve_save_z_state((uint8_t *)&simd->t.sve.z);
		/* Save SVE variable length registers P, FFR */
		sve_save_p_ffr_state((uint8_t *)&simd->t.sve.p);
		/* Save SVE ZCR_EL12 and FPU status register */
		sve_save_zcr_fpu_state((uint8_t *)&simd->t.sve.zcr_el12);
		break;
	default:
		assert(false);
	}
	simd->saved_state = type;
}

void simd_restore_state(simd_t type, struct simd_state *simd)
{
	assert(simd != NULL);
	switch (type) {
	case SIMD_FPU:
		assert(is_fpen_enabled());
		assert(simd->saved_state == SIMD_FPU);
		fpu_restore_state(&simd->t.fpu);
		break;
	case SIMD_SVE: {
		register_t zcr_val;

		assert(is_feat_sve_present() == true);
		assert(is_zen_enabled() && is_fpen_enabled());
		assert(simd->saved_state == SIMD_SVE);

		/*
		 * Before restoring vector registers, set ZCR_EL2.LEN to the
		 * context's VQ that needs to be restored.
		 */
		zcr_val = read_zcr_el2();
		if (EXTRACT(ZCR_EL2_SVE_VL, zcr_val) != simd->t.sve.vq) {
			zcr_val &= ~MASK(ZCR_EL2_SVE_VL);
			zcr_val |= INPLACE(ZCR_EL2_SVE_VL, simd->t.sve.vq);
			write_zcr_el2(zcr_val);
			isb();
		}

		/* Restore SVE variable length vectors register Z */
		sve_restore_z_state((uint8_t *)&simd->t.sve.z);
		/* Restore SVE variable length registers P, FFR */
		sve_restore_p_ffr_state((uint8_t *)&simd->t.sve.p);
		/* Restore SVE ZCR_EL12 and FPU status register */
		sve_restore_zcr_fpu_state((uint8_t *)&simd->t.sve.zcr_el12);
		break;
	}
	default:
		assert(false);
	}
	simd->saved_state = SIMD_NONE;
}

void simd_save_ns_state(void)
{
	struct ns_simd_state *ns_simd;
	unsigned int cpu_id = my_cpuid();
	simd_t stype;

	ns_simd = g_ns_simd + cpu_id;
	assert(ns_simd->saved == false);
	stype = cpu_simd_type();

	simd_traps_disable(stype);
	simd_save_state(stype, &ns_simd->simd);
	simd_traps_enable();
	ns_simd->saved = true;
}

void simd_restore_ns_state(void)
{
	struct ns_simd_state *ns_simd;
	unsigned int cpu_id = my_cpuid();
	simd_t stype;

	ns_simd = g_ns_simd + cpu_id;
	assert(ns_simd->saved == true);
	stype = cpu_simd_type();

	simd_traps_disable(stype);
	simd_restore_state(stype, &ns_simd->simd);
	simd_traps_enable();
	ns_simd->saved = false;
}

/*
 * These functions and macros will be renamed to simd_* once RMM supports
 * SIMD (FPU/SVE) at REL2
 */
#ifdef RMM_FPU_USE_AT_REL2
void fpu_save_my_state(void)
{
	/* todo */
	assert(false);
}

void fpu_restore_my_state(void)
{
	assert(false);
}

bool fpu_is_my_state_saved(unsigned int cpu_id)
{
	assert(false);
}
#else /* !RMM_FPU_USE_AT_REL2 */
void fpu_save_my_state(void) {}
void fpu_restore_my_state(void) {}
#endif /* RMM_FPU_USE_AT_REL */

void simd_sve_state_init(struct simd_state *simd, uint8_t vq)
{
	assert(simd != NULL);
	assert(is_feat_sve_present() == true);
	assert(vq <= g_sve_max_vq);
	simd->t.sve.vq = vq;
}

/*
 * Configure SVE vector length in ZCR_EL2.LEN.
 */
static void simd_sve_init(void)
{
	unsigned int vl_bits;
	register_t zcr_val;

	simd_traps_disable(SIMD_SVE);

	/*
	 * Write architecture max limit for vector length to ZCR_EL2.LEN and read
	 * back the sve vector length reported by rdvl. This will give the vector
	 * length limit set by EL3 for its lower ELs. RMM will use this value as
	 * max limit for EL2 and lower ELs.
	 */
	zcr_val = read_zcr_el2();
	if (!sve_init_once) {
		zcr_val |= INPLACE(ZCR_EL2_SVE_VL, 0xf);
		write_zcr_el2(zcr_val);
		isb();

		/* convert to bits */
		vl_bits = sve_rdvl() << 3;
		g_sve_max_vq = (vl_bits >> 7) - 1;

		sve_init_once = true;
	}

	/* Use the discovered sve_max_vq */
	zcr_val &= ~MASK(ZCR_EL2_SVE_VL);
	zcr_val |= INPLACE(ZCR_EL2_SVE_VL, g_sve_max_vq);
	write_zcr_el2(zcr_val);
	isb();

	simd_traps_enable();
}

static void simd_ns_state_init(void)
{
	struct ns_simd_state *ns_simd;
	unsigned int cpu_id = my_cpuid();

	/* Initialize NS simd state */
	ns_simd = g_ns_simd + cpu_id;
	ns_simd->saved = false;

	if (is_feat_sve_present()) {
		simd_sve_state_init(&ns_simd->simd, g_sve_max_vq);
	}
}

void simd_init(void)
{
	if (is_feat_sve_present()) {
		simd_sve_init();
	}
	simd_ns_state_init();
}
