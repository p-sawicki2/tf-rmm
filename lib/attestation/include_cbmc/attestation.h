/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

/*
 *****************************************
 * This header is only for CBMC analysis *
 *****************************************
 */

#ifndef ATTESTATION_H
#define ATTESTATION_H

#include <stddef.h>

static int
attestation_heap_reinit_pe(unsigned char *buf, size_t buf_size)
{
	return 0;
}

#endif /* ATTESTATION_H */
