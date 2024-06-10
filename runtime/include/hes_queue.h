/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */
#ifndef HES_QUEUE_H
#define HES_QUEUE_H

#include <stddef.h>
#include <stdint.h>

int hes_attest_queue_init(void);
void hes_attest_pull_response_from_hes(void);
void hes_attest_push_request_to_hes(void);

#endif /* HES_QUEUE_H */
