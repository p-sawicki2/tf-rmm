/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */
#include <stdint.h>
#include <xlat_defs.h>

__attribute__ ((aligned (PAGE_SIZE)))
static char rmm_shared_buffer[PAGE_SIZE];

uintptr_t rmm_el3_ifc_get_shared_buf_pa_value(void)
{
	return (uintptr_t)rmm_shared_buffer;
}

void rmm_el3_ifc_set_shared_buf_pa_value(uintptr_t value)
{
	(void)value; /* Nothing to be done */
}

uintptr_t rmm_el3_ifc_get_shared_buf_va_value(void)
{
	return (uintptr_t)rmm_shared_buffer;
}
