/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef HOST_DEFS_H
#define HOST_DEFS_H

#include <utils_def.h>

/*
 * Wrap the macro UL in another macro, so that HOST_MEM_SIZE_VALUE can be
 * substituted before being stringified.
 */
#define ULx(_x) UL(_x)

/* Total number of granules on the current platform */
#define HOST_NR_GRANULES		(HOST_MEM_SIZE/GRANULE_SIZE)

#endif /* HOST_DEFS_H */
