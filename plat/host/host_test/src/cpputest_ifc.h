/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef CPPUTEST_IFC_H
#define CPPUTEST_IFC_H

#ifdef __cplusplus
extern "C" {
#endif

void cpputest_ifc_fail_test(char *message);
void cpputest_ifc_pass_test(void);

#ifdef __cplusplus
}
#endif

#endif /* CPPUTEST_IFC_H */
