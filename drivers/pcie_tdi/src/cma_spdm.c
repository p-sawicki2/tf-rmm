/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <cma_spdm.h>
#include <da_interface.h>

static libspdm_return_t spdm_device_send_message(void *spdm_context,
						 size_t request_size,
						 const void *request,
						 uint64_t timeout)
{
	return LIBSPDM_STATUS_SUCCESS;
}

static libspdm_return_t spdm_device_receive_message(void *spdm_context,
						    size_t *response_size,
						    void **response,
						    uint64_t timeout)
{
	return LIBSPDM_STATUS_SUCCESS;
}

static libspdm_return_t
spdm_transport_encode_message(void *spdm_context, const uint32_t *session_id,
			      bool is_app_message, bool is_request_message,
			      size_t message_size, void *message,
			      size_t *transport_message_size,
			      void **transport_message)
{
	return LIBSPDM_STATUS_SUCCESS;
}

static libspdm_return_t
spdm_transport_decode_message(void *spdm_context, uint32_t **session_id,
			      bool *is_app_message, bool is_request_message,
			      size_t transport_message_size,
			      void *transport_message,
			      size_t *message_size, void **message)
{
	return LIBSPDM_STATUS_SUCCESS;
}

/* cma_spdm_connect */
int cma_spdm_connect(struct cma_spdm_context *cma_spdm)
{
	return 0;
}

/* cma_spdm_resume_cmd */
int cma_spdm_resume_cmd(struct cma_spdm_context *cma_spdm)
{
	return 0;
}


/*
 * Returns CMA SPDM context size. This include libspdm context and libspdm
 * secured message context size.
 */
size_t cma_spdm_get_context_size(void)
{
	return libspdm_get_context_size();
}

/* Inits SPDM context using libspdm helper routines */
int cma_spdm_context_init(struct cma_spdm_context *cma_spdm, void *spdm_context)
{
	cma_spdm->spdm_context = spdm_context;

	libspdm_init_context(cma_spdm->spdm_context);

	/* Register device send/recv handlers */
	libspdm_register_device_io_func(cma_spdm->spdm_context,
					spdm_device_send_message,
					spdm_device_receive_message);

	/* No transport encodings used as this is handled by NS host */
	libspdm_register_transport_layer_func(cma_spdm->spdm_context,
					      0x1200, 0, 0,
					      spdm_transport_encode_message,
					      spdm_transport_decode_message);

	return 0;
}
