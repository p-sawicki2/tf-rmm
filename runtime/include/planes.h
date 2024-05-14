/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef PLANES_H
#define PLANES_H

/*
 * Maximum number of auxiliar planes supported. Note that this does not
 * take the primary plane into account.
 */
#ifndef CBMC
#define RMM_MAX_NUM_AUX_PLANES		(3U)
#else
#define RMM_MAX_NUM_AUX_PLANES		(0U)
#endif

/* Total number of planes supported, including the primary one */
#define RMM_MAX_TOTAL_PLANES		(RMM_MAX_NUM_AUX_PLANES + 1U)

/* Primary plane on a realm has always index '0' */
#define PRIMARY_PLANE_ID		(0U)

/* Index of the primary S2_CTX */
#define PRIMARY_S2_CTX_ID	(0U)

#endif /* PLANES_H */
