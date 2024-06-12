/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <cma_spdm.h>
#include <cma_spdm_private.h>
#include <debug.h>
#include <library/spdm_crypt_lib.h>
#include <psa/crypto.h>
#include <psa/crypto_struct.h>
#include <string.h>

static libspdm_return_t cma_spdm_send_message(void *spdm_context,
					      size_t request_size,
					      const void *request,
					      uint64_t timeout)
{
	return LIBSPDM_STATUS_SUCCESS;
}

static libspdm_return_t cma_spdm_receive_message(void *spdm_context,
						 size_t *response_size,
						 void **response,
						 uint64_t timeout)
{
	return LIBSPDM_STATUS_SUCCESS;
}

static libspdm_return_t
cma_spdm_transport_encode_message(void *spdm_context, const uint32_t *session_id,
				  bool is_app_message, bool is_request_message,
				  size_t message_size, void *message,
				  size_t *transport_message_size,
				  void **transport_message)
{
	return LIBSPDM_STATUS_SUCCESS;
}

static libspdm_return_t
cma_spdm_transport_decode_message(void *spdm_context, uint32_t **session_id,
				  bool *is_app_message, bool is_request_message,
				  size_t transport_message_size,
				  void *transport_message,
				  size_t *message_size, void **message)
{
	return LIBSPDM_STATUS_SUCCESS;
}

static libspdm_return_t cma_spdm_acquire_sender_buffer(void *spdm_context,
						       void **msg_buf_ptr)
{
	struct cma_spdm_context *cma;

	cma = spdm_to_cma(spdm_context);
	*msg_buf_ptr = cma->send_recv_buffer;

	return LIBSPDM_STATUS_SUCCESS;
}

static void cma_spdm_release_sender_buffer(void *spdm_context,
					   const void *msg_buf_ptr)
{
	struct cma_spdm_context *cma __unused;

	cma = spdm_to_cma(spdm_context);
	assert(cma->send_recv_buffer == msg_buf_ptr);
}

static libspdm_return_t cma_spdm_acquire_receiver_buffer(void *spdm_context,
							 void **msg_buf_ptr)
{
	struct cma_spdm_context *cma;

	cma = spdm_to_cma(spdm_context);
	*msg_buf_ptr = cma->send_recv_buffer;

	return LIBSPDM_STATUS_SUCCESS;
}

static void cma_spdm_release_receiver_buffer(void *spdm_context,
					     const void *msg_buf_ptr)
{
	struct cma_spdm_context *cma __unused;

	cma = spdm_to_cma(spdm_context);
	assert(cma->send_recv_buffer == msg_buf_ptr);
}

/*
 * Returns CMA SPDM context size. This include libspdm context, libspdm
 * secured message context, libspdm send/recv buffer, libspdm scratch space and
 * libspdm stack.
 */
size_t cma_spdm_get_context_size(void)
{
	size_t total;

	/*
	 * As libspdm public headers do not export the type of libsdpm_context.
	 * RMM reserves 8192 bytes and check at runtime if the size is enough.
	 */
	assert(libspdm_get_context_size() <= LIBSPMD_CONTEXT_SIZE);

	total = sizeof(struct cma_spdm_context) + LIBSPMD_CONTEXT_SIZE +
		SEND_RECV_BUF_SIZE + LIBSPMD_SCRATCH_BUF_SIZE;
	total = round_up(total, 4096);

	return total;
}

/*
 * Assigns buffers to various objects as mentioned in the below mapping starting
 * from address 'cma_spdm_priv_data'.
 *
 *           --------------------------------
 *          |  | struct cma_spdm_context |   | sizeof(struct cma_spdm_context)
 *          |--|                         |---|
 *          |  |     libspdm_context     |   | 0x2000
 *          |--------------------------------|
 *          |      send_recv_buffer          | 0x1000
 *          |--------------------------------|
 *          |    libspdm scratch_buffer      | 0xC000
 *           --------------------------------
 *
 * Inits libspdm context using libspdm helper routines and registers send/recv
 * buffer acquire/release routines. Registers device send/recv callback handlers.
 */
int cma_spdm_context_init(void *cma_spdm_priv_data,
			  size_t cma_spdm_priv_data_size, dev_handle_t handle,
			  uint8_t cert_slot_id,
			  const struct dev_comm_ops *comm_ops)
{
	spdm_version_number_t cma_spdm_version;
	spdm_version_number_t cma_sspdm_version;
	libspdm_data_parameter_t parameter;
	struct cma_spdm_context *cma;
	libspdm_return_t status __unused;
	void *spdm_ctx;
	uint32_t data32;
	uint16_t data16;
	uint8_t data8;
	size_t sb_size;

	if (cma_spdm_priv_data_size != cma_spdm_get_context_size()) {
		return -1;
	}

	if (cert_slot_id >= SPDM_MAX_SLOT_COUNT) {
		return -1;
	}

	/* Assign the start of priv data to cma_spdm_context */
	cma = (struct cma_spdm_context *)cma_spdm_priv_data;

	cma->send_recv_buffer = cma_spdm_priv_data +
		sizeof(struct cma_spdm_context) + LIBSPMD_CONTEXT_SIZE;
	cma->scratch_buffer = cma->send_recv_buffer + SEND_RECV_BUF_SIZE;

	/* Initialize cma_spdm_context */
	cma->dev_handle = handle;
	cma->cert_slot_id = cert_slot_id;
	cma->comm_ops = comm_ops;

	/*
	 * Initialize SPDM and Secure SPDM context. 'spdm_ctx' is a combination
	 * of both SPDM context and secured message context.
	 */
	spdm_ctx = (void *)&cma->libspdm_context;
	libspdm_init_context(spdm_ctx);

	/* Register device send/recv handlers */
	libspdm_register_device_io_func(spdm_ctx, cma_spdm_send_message,
					cma_spdm_receive_message);

	/*
	 * No transport encodings used as this is handled by NS host. So the
	 * transport_header_size and transport_tail_size are passed as 0.
	 */
	libspdm_register_transport_layer_func(spdm_ctx, CMA_SPDM_MSG_SIZE_MAX,
					      0U, /* transport_header_size */
					      0U, /* transport_tail_size */
					      cma_spdm_transport_encode_message,
					      cma_spdm_transport_decode_message);

	/* Register send/recv buffer acquire/release functions */
	libspdm_register_device_buffer_func(spdm_ctx,
					    CMA_SPDM_SENDER_BUFFER_SIZE,
					    CMA_SPDM_RECEIVER_BUFFER_SIZE,
					    cma_spdm_acquire_sender_buffer,
					    cma_spdm_release_sender_buffer,
					    cma_spdm_acquire_receiver_buffer,
					    cma_spdm_release_receiver_buffer);

	/* Set scratch buffer size */
	sb_size = libspdm_get_sizeof_required_scratch_buffer(spdm_ctx);

	INFO("libspdm_context_size: 0x%lx\n", libspdm_get_context_size());
	INFO("libspdm_scratch_buffer_size: 0x%lx\n", sb_size);
	INFO("struct cma_spdm_context size: 0x%lx\n",
	     sizeof(struct cma_spdm_context));
	INFO("cma_spdm_get_context_size: 0x%lx\n", cma_spdm_get_context_size());

	/* todo: Find options to reduce scratch buffer size */
	assert(sb_size <= LIBSPMD_SCRATCH_BUF_SIZE);
	libspdm_set_scratch_buffer(spdm_ctx, cma->scratch_buffer, sb_size);

	/* Check libspdm context */
	if (!libspdm_check_context(spdm_ctx)) {
		assert(0);
	}

	/* Set SPDM version */
	memset(&parameter, 0, sizeof(parameter));
	parameter.location = LIBSPDM_DATA_LOCATION_LOCAL;
	cma_spdm_version = CMA_SPDM_VERSION << SPDM_VERSION_NUMBER_SHIFT_BIT;
	status = libspdm_set_data(spdm_ctx, LIBSPDM_DATA_SPDM_VERSION,
				  &parameter, &cma_spdm_version,
				  sizeof(cma_spdm_version));
	assert(status == LIBSPDM_STATUS_SUCCESS);

	/*
	 * todo: Skip setting SPDM and Secured message version and post init
	 * connection check if these version matches the minimal version
	 * remommended by PCIe CMA-SPDM
	 */

	/* Set secured message version */
	memset(&parameter, 0, sizeof(parameter));
	parameter.location = LIBSPDM_DATA_LOCATION_LOCAL;
	cma_sspdm_version = CMA_SECURED_SPDM_VERSION <<
		SPDM_VERSION_NUMBER_SHIFT_BIT;
	status = libspdm_set_data(spdm_ctx, LIBSPDM_DATA_SECURED_MESSAGE_VERSION,
				  &parameter, &cma_sspdm_version,
				  sizeof(cma_sspdm_version));
	assert(status == LIBSPDM_STATUS_SUCCESS);

	/*
	 * Set GET_CAPABILITY fields
	 * Note: DataTransferSize and MaxSPDMmsgSize is automatically set by
	 * libspdm during init connection based on CMA_SPDM_SENDER_BUFFER_SIZE
	 * and CMA_SPDM_MSG_SIZE_MAX respectivelky.
	 */
	memset(&parameter, 0, sizeof(parameter));
	parameter.location = LIBSPDM_DATA_LOCATION_LOCAL;
	data8 = CMA_SPDM_GET_CAPABILITY_CT_EXPONENT;
	status = libspdm_set_data(spdm_ctx, LIBSPDM_DATA_CAPABILITY_CT_EXPONENT,
				  &parameter, &data8, sizeof(data8));
	assert(status == LIBSPDM_STATUS_SUCCESS);

	data32 = CMA_SPDM_GET_CAPABILITIES_REQUEST_FLAGS;
	status = libspdm_set_data(spdm_ctx, LIBSPDM_DATA_CAPABILITY_FLAGS,
				  &parameter, &data32, sizeof(data32));
	assert(status == LIBSPDM_STATUS_SUCCESS);

	/* Set NEGOTIATE_ALGORITHMS fields */
	data8 = CMA_SPDM_ALGORITHMS_MEASUREMENT_SPEC;
	status = libspdm_set_data(spdm_ctx, LIBSPDM_DATA_MEASUREMENT_SPEC,
				  &parameter, &data8, sizeof(data8));
	assert(status == LIBSPDM_STATUS_SUCCESS);

	data8 = CMA_SPDM_ALGORITHMS_OTHER_PARAMS_SUPPORT;
	status = libspdm_set_data(spdm_ctx, LIBSPDM_DATA_OTHER_PARAMS_SUPPORT,
				  &parameter, &data8, sizeof(data8));
	assert(status == LIBSPDM_STATUS_SUCCESS);

	data32 = CMA_SPDM_ALGORITHMS_BASE_ASYM_ALGOS;
	status = libspdm_set_data(spdm_ctx, LIBSPDM_DATA_BASE_ASYM_ALGO,
				  &parameter, &data32, sizeof(data32));
	assert(status == LIBSPDM_STATUS_SUCCESS);

	data32 = CMA_SPDM_ALGORITHMS_BASE_HASH_ALGOS;
	status = libspdm_set_data(spdm_ctx, LIBSPDM_DATA_BASE_HASH_ALGO,
				  &parameter, &data32, sizeof(data32));
	assert(status == LIBSPDM_STATUS_SUCCESS);

	data16 = CMA_SPDM_ALGORITHMS_DHE_GROUPS;
	status = libspdm_set_data(spdm_ctx, LIBSPDM_DATA_DHE_NAME_GROUP,
				  &parameter, &data16, sizeof(data16));
	assert(status == LIBSPDM_STATUS_SUCCESS);

	data16 = CMA_SPDM_ALGORITHMS_AEAD_CIPHER_SUITES;
	status = libspdm_set_data(spdm_ctx, LIBSPDM_DATA_AEAD_CIPHER_SUITE,
				  &parameter, &data16, sizeof(data16));
	assert(status == LIBSPDM_STATUS_SUCCESS);

	data16 = CMA_SPDM_ALGORITHMS_KEY_SCHEDULE;
	status = libspdm_set_data(spdm_ctx, LIBSPDM_DATA_KEY_SCHEDULE,
				  &parameter, &data16, sizeof(data16));
	assert(status == LIBSPDM_STATUS_SUCCESS);

	data16 = CMA_SPDM_ALGORITHMS_REQ_BASE_ASYM_ALGOS;
	status = libspdm_set_data(spdm_ctx, LIBSPDM_DATA_REQ_BASE_ASYM_ALG,
				  &parameter, &data16, sizeof(data16));
	assert(status == LIBSPDM_STATUS_SUCCESS);

	return 0;
}