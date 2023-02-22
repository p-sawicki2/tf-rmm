/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <stdint.h>

/* Platform parameter */
extern uintptr_t rmm_shared_buffer_start_va;

/* Boot Interface argument */
static uintptr_t rmm_shared_buffer_start_pa;

uintptr_t rmm_el3_ifc_get_shared_buf_pa_value(void)
{
	return rmm_shared_buffer_start_pa;
}

void rmm_el3_ifc_set_shared_buf_pa_value(uintptr_t value)
{
	rmm_shared_buffer_start_pa = value;
}

uintptr_t rmm_el3_ifc_get_shared_buf_va_value(void)
{
	return rmm_shared_buffer_start_va;
}
