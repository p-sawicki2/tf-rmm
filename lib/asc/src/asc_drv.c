/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <smc.h>

unsigned long asc_mark_secure(unsigned long addr)
{
	return monitor_call(SMC_ASC_MARK_SECURE, addr,
				0UL, 0UL, 0UL, 0UL, 0UL);
}

unsigned long asc_mark_nonsecure(unsigned long addr)
{
	return monitor_call(SMC_ASC_MARK_NONSECURE, addr,
				0UL, 0UL, 0UL, 0UL, 0UL);
}

