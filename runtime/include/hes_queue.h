/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */
#ifndef HES_QUEUE_H
#define HES_QUEUE_H

#include <stddef.h>
#include <stdint.h>

/*
 * Initialize the HES attest queue. Perform checks to ensure that the queue is
 * properly initialized. Also initialize callbacks in the t_cose library.
 * The function returns 0 on success, and -EINVAL on failure.
 */
int hes_attest_queue_init(void);

/*
 * Pull responses to attestation signing requests from the HES via EL3. This
 * function also checks consistency of the response and writes the response to
 * the appropriate REC. Note that the REC is mapped at a different high-va slot
 * than it normally is, to ensure we dont overwrite the REC that may be
 * currently live when this function is called.
 */
void hes_attest_pull_response_from_hes(void);

/*
 * Push requests to the HES for attestation signing. This function pulls from
 * the HES queue and sends the request to EL3.
 */
void hes_attest_push_request_to_hes(void);

#endif /* HES_QUEUE_H */
