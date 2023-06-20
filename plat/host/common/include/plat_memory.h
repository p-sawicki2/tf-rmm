/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef PLAT_MEMORY_H
#define PLAT_MEMORY_H

#define REC_HEAP_PAGES		2
#define REC_HEAP_SIZE		(REC_HEAP_PAGES * SZ_4K)

#define REC_PMU_PAGES		0
#define REC_PMU_SIZE		(REC_PMU_PAGES * SZ_4K)

#define REC_SIMD_PAGES		0

/* Number of aux granules pages per REC to be used */
#define REC_NUM_PAGES		(1)

#endif /* PLAT_MEMORY_H */
