/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef XLAT_HIGH_VA_H
#define XLAT_HIGH_VA_H

/* Return a pointer to the High VA xlat context for the current CPU */
struct xlat_ctx *xlat_get_high_va_xlat_ctx(void);

/* Initialize the xlat context configuration for the current CPU */
int xlat_high_va_context_init(void);

/*
 * Initializes and enables the VMSA for the high va region.
 *
 * Create an empty translation context for the current PE.
 * If the context already exists (e.g. current PE was previously
 * turned on and therefore the context is already in memory),
 * nothing happens.
 */
void xlat_high_va_setup(void);

#endif /* XLAT_HIGH_VA_H */
