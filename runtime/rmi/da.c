/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch.h>
#include <arch_features.h>
#include <buffer.h>
#include <cma_spdm.h>
#include <debug.h>
#include <granule.h>
#include <memory_alloc.h>
#include <sizes.h>
#include <smc-handler.h>
#include <smc-rmi.h>
#include <string.h>
#include <utils_def.h>

/*
 * Represents the state of communication between an RMM device object and a
 * device. The device object could be PDEV or VDEV.
 */
#define PDEV_IO_ACTIVE		0x0
#define PDEV_IO_ERROR		0x1
#define PDEV_IO_IDLE		0x2
#define PDEV_IO_PENDING		0x3

#define PDEV_HEAP_SIZE		(3U * SZ_4K)

#define pdev_to_devh(pd)	((dev_handle_t)((unsigned long)(pd)))
#define devh_to_pdev(dh)	((struct pdev *)((unsigned long)(dh)))

/* todo: This synbol comes from lib-allocator. Declare this in memory_alloc.h? */
void mbedtls_memory_buffer_alloc_init(unsigned char *buf, size_t len);

struct pcie_tdi {
	uint64_t bdf;
	uint16_t segment_id;
	uint16_t root_id;
	uint64_t cert_slot_id;
	uint64_t ide_sel_sid;
	uint64_t rid_base;
	uint64_t rid_top;

	/* CMA spdm context mapped in AUX granule */
	void *cma_spdm_priv_data;
	size_t cma_spdm_priv_data_size;
};

struct pdev {
	/* Pointer to this granule */
	struct granule *g_pdev;

	rmi_pdev_state_t rmi_state;
	uint32_t flags;
	uint32_t io_state;
	uint32_t num_vdevs;

	/* IO args passed from the RMM to the Host during device communication */
	rmi_io_exit_t io_exit_args;

	/* IO args passed from the Host to the RMM during device communication */
	rmi_io_enter_t io_enter_args;

	/* Number and addresses of PDEV auxiliary granules */
	struct granule *g_aux[PDEV_PARAM_AUX_GRANULES_MAX];
	unsigned int num_aux;

	/* PDEV Heap used by rmm-allocator mainly for mbedtls calls */
	struct buffer_alloc_ctx heap_ctx;
	void *heap;
	size_t heap_size;

	/* Algorithm used to generate device digests */
	uint8_t hash_algo;

	struct pcie_tdi dev;
};
COMPILER_ASSERT(sizeof(struct pdev) <= GRANULE_SIZE);

/* Copy out the IO request to NS buffer and fill in IoExit arguments */
static int rmi_pdev_comm_send(dev_handle_t handle, const void *request,
			      size_t request_size, bool is_sspdm,
			      uint64_t timeout)
{
	return 0;
}

/*
 * Receive response from device. RmiIoEnter with response from device and copy
 * data from NS buffer.
 */
static int rmi_pdev_comm_recv(dev_handle_t handle, void *response,
			      size_t *response_size)
{
	return 0;
}

/*
 * Set cache flags in IoExit.
 */
static int rmi_pdev_comm_cache(dev_handle_t handle, const void *cache_buf,
			       size_t cache_offset, size_t cache_len)
{
	return 0;
}

const struct dev_comm_ops pdev_comm_ops = {
	.name = "rmi_pdev_comm_ops",
	.send = rmi_pdev_comm_send,
	.recv = rmi_pdev_comm_recv,
	.cache = rmi_pdev_comm_cache,
};

/*
 * This function will only be invoked when the PDEV create fails or when PDEV is
 * being destroyed. Hence the PDEV will not be in use when this function is
 * called and therefore no lock is acquired before its invocation.
 */
static void pdev_restore_aux_granules_state(struct granule *pdev_aux[],
					    unsigned int cnt, bool scrub)
{
	for (unsigned int i = 0U; i < cnt; i++) {
		struct granule *g_pdev_aux = pdev_aux[i];

		granule_lock(g_pdev_aux, GRANULE_STATE_PDEV_AUX);
		if (scrub) {
			buffer_granule_memzero(g_pdev_aux,
			   (enum buffer_slot)((unsigned int)SLOT_PDEV_AUX0 + i));
		}
		granule_unlock_transition(g_pdev_aux, GRANULE_STATE_DELEGATED);
	}
}

/*
 * smc_pdev_create
 *
 * pdev_ptr		- PA of the PDEV
 * pdev_params_ptr	- PA of PDEV parameters
 */
unsigned long smc_pdev_create(unsigned long pdev_ptr,
			      unsigned long pdev_params_ptr)
{
	struct granule *g_pdev;
	struct granule *g_pdev_params;
	struct pdev *pd;
	struct rmi_pdev_params pdev_params; /* this consumes 4k of stack */
	struct granule *pdev_aux_granules[PDEV_PARAM_AUX_GRANULES_MAX];
	size_t pdev_aux_size;
	size_t pdev_aux_num;
	bool ns_access_ok;
	void *aux_mapped_addr;
	int rc;

	if (!GRANULE_ALIGNED(pdev_ptr) ||
	    !GRANULE_ALIGNED(pdev_params_ptr)) {
		return RMI_ERROR_INPUT;
	}

	/* Map and copy PDEV parameters */
	g_pdev_params = find_granule(pdev_params_ptr);
	if ((g_pdev_params == NULL ||
	     granule_unlocked_state(g_pdev_params) != GRANULE_STATE_NS)) {
		return RMI_ERROR_INPUT;
	}

	ns_access_ok = ns_buffer_read(SLOT_NS, g_pdev_params, 0U,
				      sizeof(struct rmi_pdev_params),
				      &pdev_params);
	if (!ns_access_ok) {
		return RMI_ERROR_INPUT;
	}

	/*
	 * Validate RmiPdevFlags. RMM supports PCIE off-chip device represented
	 * by flags RmiPdevFlags.SPDM = RMI_SPDM_TRUE and
	 * RmiPdevFlags.IDE = RMI_IDE_SEL
	 */
	if ((EXTRACT(RMI_PDEV_FLAGS_SPDM, pdev_params.flags) != RMI_SPDM_TRUE) ||
	    (EXTRACT(RMI_PDEV_FLAGS_IDE, pdev_params.flags) != RMI_IDE_SEL)) {
		return RMI_ERROR_NOT_SUPPORTED;
	}

	/* Validate PDEV parameters that are not specific to a device class. */
	if (pdev_params.num_aux > PDEV_PARAM_AUX_GRANULES_MAX ||
	    pdev_params.num_addr_range > PDEV_PARAM_ADDR_RANGE_MAX) {
		return RMI_ERROR_INPUT;
	}

	/* Validate hash algorithm */
	if (pdev_params.hash_algo != RMI_HASH_SHA_256 &&
	    pdev_params.hash_algo != RMI_HASH_SHA_512) {
		return RMI_ERROR_INPUT;
	}

	/* Loop through pdev_aux_granules and transit them */
	for (unsigned int i = 0U; i < pdev_params.num_aux; i++) {
		struct granule *g_pdev_aux;

		g_pdev_aux = find_lock_granule(pdev_params.aux[i],
					       GRANULE_STATE_DELEGATED);
		if (g_pdev_aux == NULL) {
			/* Unlock granules already locked before freeing them */
			for (unsigned int k = 0U; k < i; k++) {
				granule_unlock(pdev_aux_granules[k]);
			}
			pdev_restore_aux_granules_state(pdev_aux_granules, i,
							false);
			return RMI_ERROR_INPUT;
		}
		granule_unlock_transition(g_pdev_aux, GRANULE_STATE_PDEV_AUX);
		pdev_aux_granules[i] = g_pdev_aux;
	}

	/* Lock pdev granule and map it */
	g_pdev = find_lock_granule(pdev_ptr, GRANULE_STATE_DELEGATED);
	if (g_pdev == NULL) {
		rc = RMI_ERROR_INPUT;
		goto out_restore_pdev_aux_granule_state;
	}

	pd = buffer_granule_map(g_pdev, SLOT_PDEV);
	if (pd == NULL) {
		rc = RMI_ERROR_INPUT;
		granule_unlock_transition(g_pdev, GRANULE_STATE_DELEGATED);
		goto out_restore_pdev_aux_granule_state;
	}

	/* Copy all aux_granules entries to pdev */
	pd->g_pdev = g_pdev;
	pd->num_aux = pdev_params.num_aux;
	(void)memcpy(pd->g_aux, pdev_aux_granules, pdev_params.num_aux *
		     sizeof(struct granule *));

	/* Map all PDEV aux granules to slot starting SLOT_PDEV_AUX0 */
	aux_mapped_addr = buffer_pdev_aux_granules_map(pd->g_aux, pd->num_aux);
	if (aux_mapped_addr == NULL) {
		rc = RMI_ERROR_INPUT;
		goto out_unmap_pdev_slot_buffer;
	}

	/* Set CMA SPDM context size and PDEV heap size */
	pd->dev.cma_spdm_priv_data_size = cma_spdm_get_context_size();
	pd->heap_size = PDEV_HEAP_SIZE;

	/* Check if enough aux granules are allocated by NS Host for PDEV */
	pdev_aux_size = pd->dev.cma_spdm_priv_data_size + pd->heap_size;
	pdev_aux_num = round_up(pdev_aux_size, GRANULE_SIZE) >> GRANULE_SHIFT;
	if (pdev_params.num_aux < pdev_aux_num) {
		ERROR("ERROR: PDEV need %ld aux granules, host allocated %ld.\n",
		      pdev_aux_num, pdev_params.num_aux);
		rc = RMI_ERROR_INPUT;
		goto out_unmap_pdev_aux_slot_buffers;
	}

	/* Initialize PDEV aux map from the mapped region 'aux_mapped_addr' */
	pd->dev.cma_spdm_priv_data = (void *)aux_mapped_addr;
	pd->heap = (void *)(pd->dev.cma_spdm_priv_data +
			    pd->dev.cma_spdm_priv_data_size);

	/*
	 * If PDEV needs heap, assign the buffer alloc context to current CPU,
	 * so that the heap can be initialized for later PDEV communicate calls.
	 */
	rc = buffer_alloc_ctx_assign(&pd->heap_ctx);
	assert(rc == 0);

	/*
	 * This is not a mbedtls call, but to lib-allocator to initialize the
	 * heap
	 */
	mbedtls_memory_buffer_alloc_init(pd->heap, pd->heap_size);

	/*
	 * Unassign heap ctx from current CPU, as PDEV create SMC won't be
	 * making any calls that does memory allocation.
	 */
	buffer_alloc_ctx_unassign();

	/* Call init routine to initialize device class specific state */
	pd->dev.bdf = pdev_params.pdev_id;
	pd->dev.segment_id = pdev_params.segment_id;
	pd->dev.root_id = pdev_params.root_id;
	pd->dev.cert_slot_id = pdev_params.cert_id;
	pd->dev.ide_sel_sid = pdev_params.ide_sel_sid;

	rc = cma_spdm_context_init(pd->dev.cma_spdm_priv_data,
				   pd->dev.cma_spdm_priv_data_size,
				   pdev_to_devh(pd), pdev_params.cert_id,
				   &pdev_comm_ops);
	if (rc == 0) {
		pd->rmi_state = RMI_PDEV_STATE_NEW;
		pd->io_state = PDEV_IO_PENDING;
		pd->num_vdevs = 0;
		pd->hash_algo = pdev_params.hash_algo;

		rc = RMI_SUCCESS;
	} else {
		rc = RMI_ERROR_INPUT;
	}

 out_unmap_pdev_aux_slot_buffers:
	/* Unmap all PDEV aux granules */
	buffer_pdev_aux_unmap(aux_mapped_addr, pd->num_aux);

out_unmap_pdev_slot_buffer:
	/* unmap PDEV buffer from slot PDEV */
	buffer_unmap(pd);

	/*
	 * On success, unlock and transit the PDEV granule state to
	 * GRANULE_STATE_PDEV else unlock and retain the state at
	 * GRANULE_STATE_DELEGATED.
	 */
	if (rc == RMI_SUCCESS) {
		granule_unlock_transition(g_pdev, GRANULE_STATE_PDEV);
	} else {
		granule_unlock_transition(g_pdev, GRANULE_STATE_DELEGATED);
	}

out_restore_pdev_aux_granule_state:
	if (rc != RMI_SUCCESS) {
		/*
		 * Transit all PDEV AUX granule state back to
		 * GRANULE_STATE_DELEGATED
		 */
		pdev_restore_aux_granules_state(pdev_aux_granules,
						pdev_params.num_aux, false);
	}

	return rc;
}
