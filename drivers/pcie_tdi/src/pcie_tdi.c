/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <da_interface.h>
#include <pcie_tdi_private.h>
#include <stddef.h>

/* Returns device specific private data size in bytes */
static unsigned int get_private_data_size(void)
{
	size_t priv_data_size = 0U;

	/*
	 * Sum of below regions rounded to 4K
	 * IO context size
	 */
	priv_data_size = cma_spdm_get_context_size();
	return priv_data_size;
}

/* Verifies PCIE TDI specific parameters */
static int pcie_tdi_validate_params(struct pcie_tdi *tdi,
				    struct dev_params *params)
{
	size_t priv_data_sz;

	priv_data_sz = get_private_data_size();

	if (priv_data_sz && ((params->priv_data_sz < priv_data_sz) ||
			     (params->priv_data == NULL))) {
		return -1;
	}

	return 0;
}

/* Inits TDI struct, transport layer operaions to device */
int pcie_tdi_init(dev_handle_t handle, struct dev_params *params,
		  const struct dev_transport_ops *transport_ops)
{
	struct pcie_tdi *tdi;
	int rc;

	tdi = handle_to_tdi(handle);
	rc = pcie_tdi_validate_params(tdi, params);
	if (rc != 0U) {
		return -1;
	}

	/* Init CMA SPDM context */
	rc = cma_spdm_context_init(&tdi->cma_spdm, params->priv_data);

	return rc;
}

/*
 * Establishes a secure connection to the device. PCIE TDI uses SPDM to
 * establish connection to the device.
 */
int pcie_tdi_connect(dev_handle_t handle)
{
	struct pcie_tdi *tdi;
	int rc;

	tdi = handle_to_tdi(handle);

	/*
	 * Invokes sequence of SPDM commands to establish secure communication
	 * session to the device
	 */
	rc = cma_spdm_connect(&tdi->cma_spdm);

	return rc;
}

/*
 * Terminate the device connection and close the session. PCIE TDI uses CMA SPDM
 * to manage connection to the device.
 */
int pcie_tdi_disconnect(dev_handle_t handle)
{
	return 0;
}

/*
 * Resumes the IO operation was yielded due to response from device performed by
 * NS host.
 */
int pcie_tdi_ioresume(dev_handle_t handle)
{
	struct pcie_tdi *tdi;
	int rc;

	tdi = handle_to_tdi(handle);

	/*
	 * If IO command is related to CMA/IDE_KM/TDISP then pass the control to
	 * CMA SPDM layer.
	 */
	rc = cma_spdm_resume_cmd(&tdi->cma_spdm);

	return rc;
}

/*
 * Handles TDI management control related IO operations inside secure session
 * like SPDM:GET_MEASUREMENTS, IDE_KM messages, TDISP messages
 */
int pcie_tdi_ioctl(dev_handle_t handle, unsigned int cmd, unsigned long args)
{
	return 0;
}

static const struct device_ops pcie_tdi_ops = {
	.name = "pcie-tdi",
	.init = pcie_tdi_init,
	.connect = pcie_tdi_connect,
	.disconnect = pcie_tdi_disconnect,
	.ioresume = pcie_tdi_ioresume,
	.ioctl = pcie_tdi_ioctl,
};

/*
 * Called from RMM coldboot main
 * Handles below tasks:
 * - Calculates device specific private data size required
 * - Registers the device and device operations with DA interface layer
 */
int pcie_tdi_device_register(void)
{
	unsigned int priv_data_size;
	int rc;

	/* Init transport layer ops */
	priv_data_size = get_private_data_size();

	rc = da_register_device(DEVICE_TYPE_PCIE_TDI, &pcie_tdi_ops,
				priv_data_size);

	return rc;
}
