/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef CMA_SPDM_H
#define CMA_SPDM_H

#include <assert.h>
#include <da_interface.h>

#include <industry_standard/spdm.h>
#include <industry_standard/spdm_secured_message.h>
#include <library/spdm_requester_lib.h>
#include <library/spdm_secured_message_lib.h>


/*
 * Contains CMA SPDM related data and the transport handler for SPDM messages.
 */
struct cma_spdm_context {
	/*
	 * The libspdm context. Kept as the first field, so this can be used to
	 * retrieve transport ops during callbacks from libspdm
	 */
	void *spdm_context;
	uint32_t spdm_context_size;

	uint32_t session_id;
	uint8_t slot_id;

	/*
	 * Arch specific IO context to support async device communication through
	 * libspdm layer
	 */
	const struct dev_transport_ops *spdm_transport_ops;
};

#define LIBSPDM_CMD_INIT_CONNECTION	U(0x0)
#define LIBSPDM_CMD_DEINIT_CONNECTION	U(0x1)
#define LIBSPDM_CMD_GET_CERTIFICATE	U(0x2)

/* Minimum required SPDM version that DSM */
#define CMA_SPDM_VERSION_MIN		0x10

size_t cma_spdm_get_context_size(void);

int cma_spdm_context_init(struct cma_spdm_context *cma_spdm,
			  void *spdm_ctx);

int cma_spdm_connect(struct cma_spdm_context *cma_spdm);

int cma_spdm_terminate_session(struct cma_spdm_context *cma_spdm);

int cma_spdm_send_request(uint32_t cmd, struct cma_spdm_context *cma_spdm);

int cma_spdm_resume_cmd(struct cma_spdm_context *cma_spdm);

#endif /* CMA_SPDM_H */
