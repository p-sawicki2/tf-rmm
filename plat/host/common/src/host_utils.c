/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch_helpers.h>
#include <assert.h>
#include <debug.h>
#include <errno.h>
#include <gic.h>
#include <host_defs.h>
#include <host_utils.h>
#include <plat_common.h>
#include <rmm_el3_ifc.h>
#include <string.h>
#include <utils_def.h>
#include <xlat_tables.h>

static struct sysreg_data sysregs[SYSREG_MAX_CBS];
static struct sysreg_data sysregs_snapshot[SYSREG_MAX_CBS];
static unsigned int installed_cb_idx;

static struct simd_vreg_data simd_vregs[NUM_Q_REGS];
static struct simd_vreg_cb simd_vreg_cbs;

static unsigned int current_cpuid;

/*
 * Allocate memory to emulate physical memory to initialize the
 * granule library.
 */
IF_NCBMC(static) unsigned char granules_buffer[HOST_MEM_SIZE] __aligned(GRANULE_SIZE);

/*
 * Define and set the Boot Interface arguments.
 */
static unsigned char el3_rmm_shared_buffer[PAGE_SIZE] __aligned(PAGE_SIZE);

/*
 * Create a basic boot manifest.
 */
static struct rmm_core_manifest *boot_manifest =
			(struct rmm_core_manifest *)el3_rmm_shared_buffer;

/*
 * Generic callback to access a sysreg for reading.
 */
static u_register_t sysreg_rd_cb(u_register_t *reg)
{
	return *reg;
}

/*
 * Generic callback to access a SIMD vreg for reading.
 */
static simd_vreg simd_vreg_rd_cb(simd_vreg *reg)
{
	return *reg;
}

/*
 * Generic callback to access a sysreg for writing.
 */
static void sysreg_wr_cb(u_register_t val, u_register_t *reg)
{
	*reg = val;
}

/*
 * Callback for writing specifically to an FPU Q vreg.
 */
static void fpu_vreg_wr_cb(simd_vreg val, simd_vreg *reg)
{
	*reg = val;
}

/*
 * Generic callback to access a SIMD vreg for writing.
 */
static void simd_vreg_wr_cb(enum simd_variant variant, simd_vreg val,
			    simd_vreg *reg)
{
	switch (variant) {
		case FPU:
			fpu_vreg_wr_cb(val, reg);
			break;
	}
}

struct sysreg_cb *host_util_get_sysreg_cb(char *name)
{
	for (unsigned int i = 0U; i < SYSREG_MAX_CBS; i++) {
		if (strncmp(name, &sysregs[i].name[0],
			    MAX_SYSREG_NAME_LEN) == 0) {

			/*
			 * Get a pointer to the register value for the
			 * current CPU.
			 */
			sysregs[i].callbacks.reg =
					&(sysregs[i].value[current_cpuid]);
			return &sysregs[i].callbacks;
		}
	}

	return (struct sysreg_cb *)NULL;
}

struct simd_vreg_cb *host_util_get_simd_vreg_cb(unsigned int idx)
{
	if (idx >= NUM_Q_REGS) {
		return (struct simd_vreg_cb *)NULL;
	}

	simd_vreg_cbs.reg = &(simd_vregs[idx].value[current_cpuid]);

	return &simd_vreg_cbs;
}

int host_util_set_sysreg_cb(char *name, rd_cb_t rd_cb, wr_cb_t wr_cb,
			    u_register_t init)
{
	if (installed_cb_idx < SYSREG_MAX_CBS) {
		sysregs[installed_cb_idx].callbacks.rd_cb = rd_cb;
		sysregs[installed_cb_idx].callbacks.wr_cb = wr_cb;
		sysregs[installed_cb_idx].callbacks.reg =
							(u_register_t *)NULL;

		for (unsigned int i = 0U; i < MAX_CPUS; i++) {
			sysregs[installed_cb_idx].value[i] = init;
		}

		(void)strncpy(&(sysregs[installed_cb_idx].name[0]),
			      &name[0], MAX_SYSREG_NAME_LEN);

		/*
		 * Add a string termination character in case the
		 * name were truncated.
		 */
		sysregs[installed_cb_idx].name[MAX_SYSREG_NAME_LEN] = '\0';

		++installed_cb_idx;

		return 0;
	}

	return -ENOMEM;
}

void host_util_set_simd_vreg_cb(simd_vreg_rd_cb_t rd_cb,
				simd_vreg_wr_cb_t wr_cb)
{
	/*
	 * We use the same read and write callbacks for each SIMD vreg because
	 * they are general-purpose registers.
	 */
	simd_vreg_cbs.rd_cb = rd_cb;
	simd_vreg_cbs.wr_cb = wr_cb;
	simd_vreg_cbs.reg = (simd_vreg *)NULL;
}

void host_util_take_sysreg_snapshot(void)
{
	memcpy((void *)&sysregs_snapshot[0], (void *)&sysregs[0],
		sizeof(struct sysreg_data) * SYSREG_MAX_CBS);
}

void host_util_restore_sysreg_snapshot(void)
{
	memcpy((void *)&sysregs[0], (void *)&sysregs_snapshot[0],
		sizeof(struct sysreg_data) * SYSREG_MAX_CBS);
}

void host_util_zero_sysregs_and_cbs(void)
{

	(void)memset((void *)sysregs, 0,
		     sizeof(struct sysreg_data) * SYSREG_MAX_CBS);

	installed_cb_idx = 0U;
}

void host_util_zero_simd_vregs(void)
{
	(void)memset((void *)simd_vregs, 0,
		     sizeof(struct simd_vreg_data) * NUM_Q_REGS);

}

int host_util_set_default_sysreg_cb(char *name, u_register_t init)
{
	return host_util_set_sysreg_cb(name, &sysreg_rd_cb,
				       &sysreg_wr_cb, init);
}

void host_util_set_default_simd_vreg_cb(void) {
	return host_util_set_simd_vreg_cb(&simd_vreg_rd_cb, &simd_vreg_wr_cb);
}

unsigned long host_util_get_granule_base(void)
{
	return (unsigned long)granules_buffer;
}

void host_util_set_cpuid(unsigned int cpuid)
{
	assert(cpuid < MAX_CPUS);

	current_cpuid = cpuid;
}

unsigned char *host_util_get_el3_rmm_shared_buffer(void)
{
	return el3_rmm_shared_buffer;
}

void host_util_setup_sysreg_and_boot_manifest(void)
{
	int ret;

	/*
	 * Initialize ID_AA64DFR0_EL1 with PMUVer field to PMUv3p7.
	 * (ID_AA64DFR0_EL1.PMUVer, bits [11:8] set to 7)
	 */
	ret = host_util_set_default_sysreg_cb("id_aa64dfr0_el1",
			INPLACE(ID_AA64DFR0_EL1_PMUVer, 7UL));

	/*
	 * Setup id_aa64mmfr0_el1 with a PA size of 48 bits
	 * and 4K granularity with LPA2 support for stages 1 and 2.
	 */
	ret = host_util_set_default_sysreg_cb("id_aa64mmfr0_el1",
				INPLACE(ID_AA64MMFR0_EL1_PARANGE, 5UL) |
				INPLACE(ID_AA64MMFR0_EL1_TGRAN4,
					ID_AA64MMFR0_EL1_TGRAN4_LPA2) |
				INPLACE(ID_AA64MMFR0_EL1_TGRAN4_2,
					ID_AA64MMFR0_EL1_TGRAN4_2_TGRAN4));

	/*
	 * Initialize ICH_VTR_EL2 with 6 preemption bits.
	 * (PREbits is equal number of preemption bits minus one)
	 */
	ret = host_util_set_default_sysreg_cb("ich_vtr_el2",
			INPLACE(ICH_VTR_EL2_PRE_BITS, 5UL));

	/* SCTLR_EL2 is reset to zero */
	ret = host_util_set_default_sysreg_cb("sctlr_el2", 0UL);

	/* HCR_EL2 is reset to zero */
	ret = host_util_set_default_sysreg_cb("hcr_el2", 0UL);

	/* TPIDR_EL2 is reset to zero */
	ret = host_util_set_default_sysreg_cb("tpidr_el2", 0UL);

	/* ID_AA64ISAR0.RNDR is reset to 1 */
	ret = host_util_set_default_sysreg_cb("id_aa64isar0_el1",
				INPLACE(ID_AA64ISAR0_EL1_RNDR, 1UL));

	/*
	 * Add callback to elr_el2 so that the realm entry point can be accessed
	 * by host_run_realm
	 */
	ret = host_util_set_default_sysreg_cb("elr_el2", 0UL);

	/*
	 * Add callback to esr_el2 so that the realm exceptions can be handled.
	 */
	ret = host_util_set_default_sysreg_cb("esr_el2", 0UL);

	/*
	 * Set number of event counters implemented to 31.
	 * (PMCR_EL0.N, bits [15:11] set to 31)
	 */
	ret = host_util_set_default_sysreg_cb("pmcr_el0",
			INPLACE(PMCR_EL0_N, 31UL));

	/* Set ISR_EL1 to 0 */
	ret = host_util_set_default_sysreg_cb("isr_el1", 0UL);

	/*
	 * Only check the return value of the last callback setup, to detect
	 * if we are out of callback slots.
	 */
	if (ret != 0) {
		panic();
	}

	/* Initialize the boot manifest */
	boot_manifest->version = RMM_EL3_MANIFEST_MAKE_VERSION(
						RMM_EL3_MANIFEST_VERS_MAJOR,
						RMM_EL3_MANIFEST_VERS_MINOR);
	boot_manifest->plat_data = (uintptr_t)NULL;
}

void host_util_setup_simd_reg(void)
{
	simd_vreg init = { .q = {0} };

	host_util_set_default_simd_vreg_cb();

	for (unsigned int vreg_idx = 0; vreg_idx < NUM_Q_REGS; vreg_idx++)
	{
		for (unsigned int cpu_idx = 0; cpu_idx < MAX_CPUS; cpu_idx++)
		{
			simd_vregs[vreg_idx].value[cpu_idx] = init;
		}

	}
}

int host_util_rec_run(unsigned long *regs)
{
	unsigned long pc = read_elr_el2();
	realm_entrypoint_t realm_ep = (void *)pc;

	write_esr_el2(0x0);
	return realm_ep(regs);
}

int host_util_rsi_helper(realm_entrypoint_t ep)
{
	/* Reduce the ep by 0x4 as RMM will advance_pc as part of handling RSI */
	write_elr_el2((u_register_t) ep - 0x4);
	write_esr_el2(ESR_EL2_EC_SMC);

	return ARM_EXCEPTION_SYNC_LEL;
}
