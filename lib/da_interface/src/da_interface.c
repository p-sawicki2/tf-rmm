/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <da_interface.h>
#include <debug.h>
#include <smc-rmi.h>

/* Currently supports one device class type */
static const struct device_ops *pdev_cls_pcie_ops;
static size_t pdev_cls_pcie_priv_data_size;

/* Register the device with the interface layer */
int da_register_device(uint8_t dev_type, const struct device_ops *ops,
		       size_t dev_priv_data_size)
{
	assert(pdev_cls_pcie_ops == NULL);

	if (dev_type != DEVICE_TYPE_PCIE_TDI) {
		return -1;
	}

	if (ops == NULL) {
		return -1;
	}

	if (dev_priv_data_size > (PDEV_PARAM_AUX_GRANULES_MAX * GRANULE_SIZE)) {
		return -1;
	}

	pdev_cls_pcie_ops = ops;
	pdev_cls_pcie_priv_data_size = dev_priv_data_size;

	return 0;
}

/* Returns RMI_PDEV_CLASS_PCIE device ops */
int da_get_registered_device(uint8_t dev_cls, const struct device_ops **ops,
			     size_t *dev_priv_data_size)
{
	if (dev_cls != RMI_PDEV_CLASS_PCIE) {
		return -1;
	}

	if (pdev_cls_pcie_ops == NULL) {
		return -1;
	}

	*ops = pdev_cls_pcie_ops;
	*dev_priv_data_size = pdev_cls_pcie_priv_data_size;

	return 0;
}
