/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef RUN_H
#define RUN_H

#ifdef CBMC
#include <tb_common.h>
#endif /* CBMC */

struct rec;
struct simd_context;

/*
 * Function to enter Realm with `regs` pointing to GP Regs to be
 * restored/saved when entering/exiting the Realm. This function
 * returns with the Realm exception code which is populated by
 * Realm_exit() on aarch64.
 */
int run_realm(unsigned long *regs);

/* Initialize the NS world SIMD context for all CPUs. */
#ifndef CBMC
void init_all_cpus_ns_simd_context(void);
#else /* CBMC */
static inline void init_all_cpus_ns_simd_context(void)
{
	ASSERT(false, "init_all_cpus_ns_simd_context");
}
#endif /* CBMC */

/* Returns current CPU's NS world SIMD context */
#ifndef CBMC
struct simd_context *get_cpu_ns_simd_context(void);
#else /* CBMC */
static inline struct simd_context *get_cpu_ns_simd_context(void)
{
	ASSERT(false, "get_cpu_ns_simd_context");
	return NULL;
}
#endif /* CBMC */

#endif /* RUN_H */
