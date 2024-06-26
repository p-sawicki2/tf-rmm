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

/* Maximum number of Stage 2 Translation contexts needed per realm */
#define MAX_S2_CTXS			(RMM_MAX_TOTAL_PLANES)

/* Default Overlay Permission Index for Protected IPA */
#define DEFAULT_PROTECTED_OVERLAY_INDEX	(0U)

#endif /* PLANES_H */
