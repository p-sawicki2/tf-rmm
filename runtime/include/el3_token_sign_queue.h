/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */
#ifndef EL3_TOKEN_SIGN_H
#define EL3_TOKEN_SIGN_H

#include <rec.h>
#include <stddef.h>
#include <stdint.h>

/*
 * Initialize the EL3 token signing module. Also initialize callbacks
 * in the t_cose library. The function returns 0 on success, and -EINVAL
 * on failure.
 */
int el3_token_sign_queue_init(void);

/*
 * Pull responses to attestation signing requests from EL3. This function also
 * checks consistency of the response and writes the response to the
 * appropriate REC. Note that the REC is mapped at a different high-va slot
 * than it normally is, to ensure we dont overwrite the REC that may be
 * currently live when this function is called.
 */
void el3_token_sign_pull_response_from_el3(struct rec *curr_rec);

#endif /* EL3_TOKEN_SIGN_H */
