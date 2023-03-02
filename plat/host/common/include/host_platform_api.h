/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef HOST_PLATFORM_API_H
#define HOST_PLATFORM_API_H

/* Return the adderss of the EL3 RMM shared buffer */
unsigned char *plat_get_el3_rmm_shared_buffer(void);

/*
 * Performs some initialization needed before RMM can be run, such as
 * setting up callbacks for sysreg access.
 */
void plat_setup_sysreg_and_boot_manifest(void);

#endif /* HOST_PLATFORM_API_H */
