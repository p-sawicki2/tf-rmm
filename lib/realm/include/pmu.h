/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef PMU_H
#define PMU_H

#include <arch_helpers.h>
#include <utils_def.h>

struct rmi_rec_exit;

struct pmev_regs {
	unsigned long pmevcntr_el0;
	unsigned long pmevtyper_el0;
};

/*
 * PMU context structure.
 * Align on cache writeback granule to minimise cache line
 * thashing when allocated as an array for use by each CPU.
 */
struct pmu_state {
	unsigned long pmcr_el0;
	unsigned long pmccfiltr_el0;
	unsigned long pmccntr_el0;
	unsigned long pmcntenset_el0;
	unsigned long pmcntenclr_el0;
	unsigned long pmintenset_el1;
	unsigned long pmintenclr_el1;
	unsigned long pmovsset_el0;
	unsigned long pmovsclr_el0;
	unsigned long pmselr_el0;
	unsigned long pmuserenr_el0;
	unsigned long pmxevcntr_el0;
	unsigned long pmxevtyper_el0;

	unsigned long pmecr_el1;	/* FEAT_PMUv3_SS / FEAT_EBEP */
	unsigned long pmsscr_el1;	/* FEAT_PMUv3_SS */
	unsigned long pmiar_el1;	/* FEAT_SEBEP */
	unsigned long pmicfiltr_el0;	/* FEAT_PMUv3_ICNTR */
	unsigned long pmicntr_el0;	/* FEAT_PMUv3_ICNTR */
	unsigned long pmuacr_el1;	/* FEAT_PMUv3p9 */

	struct pmev_regs pmev_regs[31];

} __aligned(CACHE_WRITEBACK_GRANULE);

void save_pmu_state(struct pmu_state *pmu, unsigned int num_cnts);
void restore_pmu_state(struct pmu_state *pmu, unsigned int num_cnts);
void pmu_copy_state_to_ns(struct rmi_rec_exit *rec_exit);

#endif /* PMU_H */
