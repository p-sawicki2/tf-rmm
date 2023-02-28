/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef HOST_RMI_WRAPPERS_PRIVATE_H
#define HOST_RMI_WRAPPERS_PRIVATE_H

#include <smc-rmi.h>

void rmi_granule_delegate(void *granule_address, struct smc_result *ret);
void rmi_granule_undelegate(void *granule_address, struct smc_result *ret);
void rmi_realm_create(void *rd, void *params_ptr, struct smc_result *ret);
void rmi_realm_destroy(void *rd, struct smc_result *ret);
void rmi_rtt_create(void *rtt, void *rd, void *ipa, unsigned int level, struct smc_result *ret);
void rmi_rtt_destroy(void *rtt, void *rd, void *ipa, unsigned int level, struct smc_result *ret);
void rmi_rec_aux_count(void *rd, struct smc_result *ret);
void rmi_rec_create(void *rec, void *rd, void *params_ptr, struct smc_result *ret);
void rmi_rec_destroy(void *rec, struct smc_result *ret);
void rmi_realm_activate(void *rd, struct smc_result *ret);
void rmi_rec_enter(void *rec, void *run_ptr, struct smc_result *ret);

#endif /* HOST_RMI_WRAPPERS_PRIVATE_H */
