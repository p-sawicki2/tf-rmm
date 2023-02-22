/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef RMM_EL3_IFC_PRIV_H
#define RMM_EL3_IFC_PRIV_H

/*
 * Function to process the boot manifest.
 *
 * Args:	None.
 * Return:	- This function does not return any value, but it will never
 *		  exit if there is an error.
 *
 * NOTE:	This function must be called with the MMU disabled.
 * NOTE2:	At return, the plat_data field of the manifest local copy
 *		will be pointing to the platform manifest in the shared area
 *		(if a platform manifest was loaded by EL3). Platform code is
 *		responsible for processing the platform manifest and keeping a
 *		local copy of it if needed at runtime.
 */
void rmm_el3_ifc_process_boot_manifest(void);

/*
 * Function to return the value of the shared buffer PA value.
 *
 * Args:	None.
 * Return:	- The address of the shared buffer
 */
uintptr_t rmm_el3_ifc_get_shared_buf_pa_value(void);

/*
 * Function to set the value of the shared buffer PA value.
 *
 * Args:	The value to set as PA value.
 * Return:	- None.
 */
void rmm_el3_ifc_set_shared_buf_pa_value(uintptr_t value);

/*
 * Function to return the value of the shared buffer VA value.
 *
 * Args:	None.
 * Return:	- The address of the shared buffer
 */
uintptr_t rmm_el3_ifc_get_shared_buf_va_value(void);


#endif /* RMM_EL3_IFC_PRIV_H */
