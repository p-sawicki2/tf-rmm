/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <debug.h>
#include <errno.h>
#include <gic.h>
#include <host_defs.h>
#include <host_utils.h>
#include <plat_common.h>
#include <rmm_el3_ifc.h>
#include <string.h>
#include <xlat_tables.h>

static struct sysreg_data sysregs[SYSREG_MAX_CBS];
static unsigned int installed_cb_idx;
static unsigned int current_cpuid;

/*
 * Allocate memory to emulate physical memory to initialize the
 * granule library.
 */
static unsigned char granules_buffer[HOST_MEM_SIZE] __aligned(GRANULE_SIZE);

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
 * Generic callback to access a sysreg for writing.
 */
static void sysreg_wr_cb(u_register_t val, u_register_t *reg)
{
	*reg = val;
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

void host_util_reset_all_sysreg_cb(void)
{

	(void)memset((void *)sysregs, 0,
		     sizeof(struct sysreg_data) * SYSREG_MAX_CBS);

	installed_cb_idx = 0U;
}

int host_util_set_default_sysreg_cb(char *name, u_register_t init,
				    bool readonly)
{
	rd_cb_t rd_cb = &sysreg_rd_cb;
	wr_cb_t wr_cb = readonly ? NULL : &sysreg_wr_cb;

	return host_util_set_sysreg_cb(name, rd_cb, wr_cb, init);
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
	 * Initialize ID_AA64MMFR0_EL1 with a physical address
	 * range of 48 bits (PARange bits set to 0b0101)
	 */
	ret = host_util_set_default_sysreg_cb("id_aa64mmfr0_el1",
			INPLACE(ID_AA64MMFR0_EL1_PARANGE, 5UL),
			true);

	/*
	 * Initialize ICH_VTR_EL2 with 6 preemption bits.
	 * (PREbits is equal number of preemption bits minus one)
	 */
	ret = host_util_set_default_sysreg_cb("ich_vtr_el2",
			INPLACE(ICH_VTR_EL2_PRE_BITS, 5UL),
			false);

	/* SCTLR_EL2 is reset to zero */
	ret = host_util_set_default_sysreg_cb("sctlr_el2", 0UL, false);

	/* TPIDR_EL2 is reset to zero */
	ret = host_util_set_default_sysreg_cb("tpidr_el2", 0UL, false);

	/* ID_AA64ISAR0.RNDR is reset to 1 */
	ret = host_util_set_default_sysreg_cb("id_aa64isar0_el1",
				INPLACE(ID_AA64ISAR0_EL1_RNDR, 1UL),
				true);

	/*
	 * Add callback to elr_el2 so that the realm entry point can be accessed
	 * by host_run_realm
	 */
	ret = host_util_set_default_sysreg_cb("elr_el2", 0UL, false);

	/*
	 * Only check the return value of the last callback setup, to detect
	 * if we are out of callback slots.
	 */
	if (ret != 0) {
		panic();
	}

	/* Initialize the boot manifest */
	boot_manifest->version = RMM_EL3_IFC_SUPPORTED_VERSION;
	boot_manifest->plat_data = (uintptr_t)NULL;
}
