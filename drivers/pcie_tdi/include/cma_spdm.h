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
#endif /* CMA_SPDM_H */
