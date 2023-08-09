/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef REC_AUX_ALLOC_SIZE_H
#define REC_AUX_ALLOC_SIZE_H

#ifndef CBMC

/* MbedTLS needs 8K of heap for attestation usecases */
#define REC_HEAP_PAGES		2U
#define REC_HEAP_SIZE		(REC_HEAP_PAGES * SZ_4K)

/* Number of pages per REC for PMU state */
#define REC_PMU_PAGES		1U
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
#define REC_SIMD_PAGES		3U
#define REC_SIMD_SIZE		(REC_SIMD_PAGES * SZ_4K)

/* Number of pages per REC for 'rec_attest_data' structure */
#define REC_ATTEST_PAGES	1U
#define REC_ATTEST_SIZE		(REC_ATTEST_PAGES * SZ_4K)

/* Number of pages per REC to be allocated */
#define REC_NUM_PAGES		(REC_HEAP_PAGES	  + \
				 REC_PMU_PAGES	  + \
				 REC_SIMD_PAGES	  + \
				 REC_ATTEST_PAGES)


#else /* CBMC */

#define REC_HEAP_PAGES		2U
#define REC_HEAP_SIZE		(REC_HEAP_PAGES * SZ_4K)

#define REC_PMU_PAGES		0U
#define REC_PMU_SIZE		(REC_PMU_PAGES * SZ_4K)

#define REC_SIMD_PAGES		0U
#define REC_SIMD_SIZE		(REC_SIMD_PAGES * SZ_4K)

#define REC_ATTEST_PAGES	0U
#define REC_ATTEST_SIZE		(REC_ATTEST_PAGES * SZ_4K)

/* Number of aux granules pages per REC to be used */
#define REC_NUM_PAGES		(1U)

#endif /* CBMC */

#endif /* REC_AUX_ALLOC_SIZE_H */
