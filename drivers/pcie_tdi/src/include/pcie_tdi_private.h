/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef PCIE_TDI_PRIVATE_H
#define PCIE_TDI_PRIVATE_H

#include <cma_spdm.h>
#include <da_interface.h>
#include <stdint.h>
#include <utils_def.h>

#define handle_to_tdi(h)	((struct pcie_tdi *)h)

struct pcie_tdi {
	uint32_t status;

	uint64_t bdf;
	uint16_t segment_id;
	uint16_t root_id;
	uint64_t cert_id;
	uint64_t ide_sid;
	uint64_t rid_base;
	uint64_t rid_top;

	void *priv_data;
	size_t priv_data_sz;

	/* TDI io context */
	struct cma_spdm_context cma_spdm;
};
COMPILER_ASSERT(sizeof(struct pcie_tdi) <= DEV_CONTEXT_SIZE_MAX);

#endif /* PCIE_TDI_PRIVATE_H */
