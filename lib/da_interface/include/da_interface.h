/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef DA_INTERFACE_H
#define DA_INTERFACE_H

#include <stddef.h>
#include <stdint.h>

/* List of device types that RMM runtime supports TEE IO */
#define DEVICE_TYPE_PCIE_TDI		0U

/* Max size of device specific context in bytes */
#define DEV_CONTEXT_SIZE_MAX		1024U

#define DEV_STATUS_SUCCESS		0U
#define DEV_STATUS_IO_WAIT		1U
#define DEV_STATUS_ERROR		2U

typedef unsigned long dev_handle_t;

/* This parameters are specific to PCI TDI */
struct dev_params {
	unsigned long bdf;
	unsigned short segment_id;
	unsigned short root_id;
	unsigned long cert_id;
	unsigned long ide_sid;

	void *priv_data;
	size_t priv_data_sz;
};

/*
 * Transport operations to send/recv management data to device (DSM). NS host
 * handles device communications. RMM reads/writes to NS buffer and does an exit
 * with RmiIoExit reason to host.
 */
struct dev_transport_ops {
	const char *name;
	int (*send)(dev_handle_t handle, const void *request,
		    size_t request_size, uint64_t timeout);
	int (*recv)(dev_handle_t handle, void **response, size_t *response_size,
		    uint64_t timeout);
};

/*
 * Device that can support trusted IO registers device ops with DA interface
 * layer
 */
struct device_ops {
	const char *name;
	int (*init)(dev_handle_t handle, struct dev_params *params,
		    const struct dev_transport_ops *transport_ops);
	int (*connect)(dev_handle_t handle);
	int (*disconnect)(dev_handle_t handle);
	int (*ioresume)(dev_handle_t handle);
	int (*ioctl)(dev_handle_t handle, unsigned int cmd, unsigned long args);
};

int da_register_device(uint8_t dev_type, const struct device_ops *ops,
		       size_t dev_priv_data_size);

int da_get_registered_device(uint8_t dev_cls, const struct device_ops **ops,
			     size_t *dev_priv_data_size);

/* todo: This synbol comes from lib-allocator. Declare this in memory_alloc.h? */
void mbedtls_memory_buffer_alloc_init(unsigned char *buf, size_t len);

#endif /* DA_INTERFACE_H */
