/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef CMA_SPDM_H
#define CMA_SPDM_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

typedef unsigned long dev_handle_t;

#define CMA_SPDM_STATUS_SUCCESS		0U
#define CMA_SPDM_STATUS_IO_WAIT		1U
#define CMA_SPDM_STATUS_ERROR		2U

#define SPDM_INIT_CONNECTION		0x10U
#define SPDM_DEINIT_CONNECTION		0x11U
#define SPDM_SECURE_SESSION		0x12U

#define CMA_SPDM_SIG_ECDSA_P256		0x1
#define CMA_SPDM_SIG_ECDSA_P384		0x2
#define CMA_SPDM_SIG_RSASSA_3072	0x3
#define CMA_SPDM_SIG_ALGO_INVALID	0xFF

/*
 * Device communication operations to send/recv management data to device (DSM).
 * NS host handles device communications. RMM reads/writes to NS buffer and does
 * an exit with RmiIoExit reason to host.
 */
struct dev_comm_ops {
	const char *name;
	int (*send)(dev_handle_t handle, const void *request,
		    size_t request_size, bool is_sspdm, uint64_t timeout);
	int (*recv)(dev_handle_t handle, void *response, size_t *response_size);
	int (*cache)(dev_handle_t handle, const void *cache_buf,
		     size_t cache_offset, size_t cache_len);
};

size_t cma_spdm_get_context_size(void);

int cma_spdm_context_init(void *cma_spdm_priv_data,
			  size_t cma_spdm_priv_data_size, dev_handle_t handle,
			  uint8_t cert_slot_id,
			  const struct dev_comm_ops *comm_ops);

int cma_spdm_cmd_dispatch(int cmd, void *cma_spdm_context);

int cma_spdm_cmd_resume(void *cma_spdm_context);

int cma_spdm_set_key(void *cma_spdm_context, uint8_t *key, size_t key_len,
		     uint8_t key_sig_algo);
#endif /* CMA_SPDM_H */
