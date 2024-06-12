/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch.h>
#include <arch_features.h>
#include <buffer.h>
#include <da_interface.h>
#include <debug.h>
#include <granule.h>
#include <memory_alloc.h>
#include <smc-handler.h>
#include <smc-rmi.h>
#include <string.h>
#include <utils_def.h>

#define SET_MEMBER_PDEV			SET_MEMBER

/*
 * Represents the state of communication between an RMM device object and a
 * device. The device object could be PDEV or VDEV.
 */
#define PDEV_IO_ACTIVE		0x0
#define PDEV_IO_ERROR		0x1
#define PDEV_IO_IDLE		0x2
#define PDEV_IO_PENDING		0x3

#define pdev_to_devh(pd)	((dev_handle_t)((unsigned long)(pd) +		\
					offsetof(struct pdev, _dev_context)))

struct pdev {
	/* Pointer to this granule */
	struct granule *g_pdev;

	rmi_pdev_state_t rmi_state;
	rmi_pdev_class_t cls;
	uint32_t flags;
	uint32_t io_state;
	uint32_t num_vdevs;

	/* Device class specific handlers */
	const struct device_ops *ops;

	/* IO args passed from the RMM to the Host during device communication */
	rmi_io_exit_t io_send_args;

	/* IO args passed from the Host to the RMM during device communication */
	rmi_io_enter_t io_recv_args;

	/* Number and addresses of PDEV auxiliary granules */
	unsigned int num_aux;
	struct granule *g_aux[PDEV_PARAM_AUX_GRANULES_MAX];

	struct buffer_alloc_ctx heap_ctx;

	/* List of objects mapped in PDEV aux granules */
	struct {
		/* Device specific private data held in aux granules */
		void *priv_data;
		size_t priv_data_sz;

		/* Heap used by allocator for libspdm/mbedtls calls */
		void *heap;
		size_t heap_sz;
	} aux_map;

	/*
	 * The device that supports Trusted IO (TEE IO). Currently device class
	 * of type PCIE_TDI is supported.
	 */
	SET_MEMBER_PDEV(unsigned long _dev_context, 0x0, DEV_CONTEXT_SIZE_MAX);
};
COMPILER_ASSERT(sizeof(struct pdev) <= GRANULE_SIZE);

/*
 * Send request to device. Exit to host after copying data to NS buffer
 */
static int rmi_pdev_io_send(dev_handle_t handle, const void *request,
			    size_t request_size, uint64_t timeout)
{
	return 0;
}

/*
 * Receive response from device. RmiIoEnter with response from device and copy
 * data from NS buffer.
 */
static int rmi_pdev_io_recv(dev_handle_t handle, void **response,
			    size_t *response_size, uint64_t timeout)
{
	return 0;
}

const struct dev_transport_ops dev_transport_ops = {
	.name = "rmi_dev_interface",
	.send = rmi_pdev_io_send,
	.recv = rmi_pdev_io_recv,
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
	const struct device_ops *pdev_ops = NULL;
	size_t pdev_priv_data_size = 0;
	struct granule *g_pdev;
	struct granule *g_pdev_params;
	struct pdev *pd;
	struct rmi_pdev_params pdev_params; /* this consumes 4k of stack */
	struct dev_params dev_params;
	struct granule *pdev_aux_granules[PDEV_PARAM_AUX_GRANULES_MAX];
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

	/* Validate PDEV parameters that are not specific to a device class. */
	if (pdev_params.cls > RMI_PDEV_CLASS_LAST ||
	    pdev_params.num_aux > PDEV_PARAM_AUX_GRANULES_MAX ||
	    pdev_params.num_addr_range > PDEV_PARAM_ADDR_RANGE_MAX) {
		return RMI_ERROR_INPUT;
	}

	/*
	 * Check if the device class is registered for DA support and gets its
	 * device ops
	 */
	rc = da_get_registered_device(pdev_params.cls, &pdev_ops,
				      &pdev_priv_data_size);
	if (rc != 0) {
		return RMI_ERROR_INPUT;
	}

	assert(pdev_ops != NULL);
	if ((pdev_priv_data_size != 0U) &&
	    (pdev_params.num_aux <
	     ((pdev_priv_data_size >> GRANULE_SHIFT) + 1U))) {
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
	pd->ops = pdev_ops;
	pd->num_aux = pdev_params.num_aux;
	(void)memcpy(pd->g_aux, pdev_aux_granules, pdev_params.num_aux *
		     sizeof(struct granule *));

	/* Map all PDEV aux granules to slot starting SLOT_PDEV_AUX0 */
	aux_mapped_addr = buffer_pdev_aux_granules_map(pd->g_aux, pd->num_aux);
	if (aux_mapped_addr == NULL) {
		rc = RMI_ERROR_INPUT;
		goto out_unmap_pdev_slot_buffer;
	}

	/* Initialize PDEV aux map from the mapped region 'aux_mapped_addr' */
	pd->aux_map.priv_data = (void *)aux_mapped_addr;
	pd->aux_map.priv_data_sz = pdev_priv_data_size;

	pd->aux_map.heap = (void *)((unsigned long)pd->aux_map.priv_data +
				    pd->aux_map.priv_data_sz);
	pd->aux_map.heap_sz = 8096;

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
	mbedtls_memory_buffer_alloc_init(pd->aux_map.heap, pd->aux_map.heap_sz);

	/*
	 * Unassign heap ctx from current CPU, as PDEV create SMC won't be
	 * making any calls that does memory allocation.
	 */
	buffer_alloc_ctx_unassign();

	/* Call init routine to initialize device class specific state */
	dev_params.bdf = pdev_params.pdev_id;
	dev_params.segment_id = pdev_params.segment_id;
	dev_params.root_id = pdev_params.root_id;
	dev_params.cert_id = pdev_params.cert_id;
	dev_params.ide_sid = pdev_params.ide_sid;
	dev_params.priv_data = pd->aux_map.priv_data;
	dev_params.priv_data_sz = pd->aux_map.priv_data_sz;

	rc = pdev_ops->init(pdev_to_devh(pd), &dev_params, &dev_transport_ops);
	if (rc == 0) {
		rc = RMI_SUCCESS;
	} else {
		rc = RMI_ERROR_INPUT;
	}

	pd->rmi_state = RMI_PDEV_STATE_NEW;
	pd->io_state = PDEV_IO_PENDING;
	pd->num_vdevs = 0;

	/* Unmap all PDEV aux granules */
	buffer_pdev_aux_unmap(pd->g_aux, pd->num_aux);

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

/*
 * smc_pdev_communicate
 *
 * pdev_ptr	- PA of the PDEV
 * data_ptr	- PA of the communication data structure
 */
unsigned long smc_pdev_communicate(unsigned long pdev_ptr,
				   unsigned long io_data_ptr)
{
	return RMI_ERROR_NOT_SUPPORTED;
}

/*
 * smc_pdev_get_state
 *
 * Get state of a PDEV.
 *
 * pdev_ptr	- PA of the PDEV
 * res		- SMC result
 */
void smc_pdev_get_state(unsigned long pdev_ptr, struct smc_result *res)
{
	res->x[0] = RMI_ERROR_NOT_SUPPORTED;
}
