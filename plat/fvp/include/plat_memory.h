/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef PLAT_MEMORY_H
#define PLAT_MEMORY_H

/* MbedTLS needs 8K of heap for attestation usecases */
#define REC_HEAP_PAGES		2
#define REC_HEAP_SIZE		(REC_HEAP_PAGES * SZ_4K)

/* Number of pages per REC for PMU state */
#define REC_PMU_PAGES		1
#define REC_PMU_SIZE		(REC_PMU_PAGES * SZ_4K)

/*
 * SIMD context that holds FPU/SVE registers. Space to save max arch supported
 * SVE vector length of 2048 bits.
 * Size of 32 Z registers (256 bytes each): 8192 bytes
 * Size of 16 P registers (32 bytes each) :  512 bytes
 * Size of 1 FFR register (32 bytes each) :   32 bytes
 * Size of other status registers         :   32 bytes
 * Total size is ~3 Pages (rounded up to page size).
 */
#define REC_SIMD_PAGES		3

/* Number of aux granules pages per REC to be used */
#define REC_NUM_PAGES		(REC_HEAP_PAGES + REC_PMU_PAGES + REC_SIMD_PAGES)

#endif /* PLAT_MEMORY_H */
