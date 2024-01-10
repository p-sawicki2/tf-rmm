/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef PLAT_COMMON_H
#define PLAT_COMMON_H

#ifdef CBMC
#include <tb_common.h>
#endif /* CBMC */

/* Forward declaration */
struct xlat_mmap_region;

#ifndef CBMC
int plat_cmn_setup(unsigned long x0, unsigned long x1,
		   unsigned long x2, unsigned long x3,
		   struct xlat_mmap_region *plat_regions,
		   unsigned int nregions);
int plat_cmn_warmboot_setup(void);
#else /* CBMC */
static inline int plat_cmn_setup(unsigned long x0, unsigned long x1,
				 unsigned long x2, unsigned long x3,
				 struct xlat_mmap_region *plat_regions,
				 unsigned int nregions)
{
	ASSERT(false, "plat_cmn_setup");
	return 0;
}
static inline int plat_cmn_warmboot_setup(void)
{
	ASSERT(false, "plat_cmn_warmboot_setup");
	return 0;
}
#endif /* CBMC */

#endif /* PLAT_COMMON_H */
