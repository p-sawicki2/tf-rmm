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
	struct pdev *pd;
	struct granule *g_req_addr;
	bool ns_access_ok;
	size_t request_size_min;

	pd = devh_to_pdev(handle);

	/* Copy the request to NS buffer passed during pdev_communicate */
	g_req_addr = find_granule(pd->io_enter_args.req_addr);
	if ((g_req_addr == NULL ||
	     granule_unlocked_state(g_req_addr) != GRANULE_STATE_NS)) {
		return -1;
	}

	request_size_min = round_up(request_size, 8);
	ns_access_ok = ns_buffer_write(SLOT_NS, g_req_addr, 0, request_size_min,
				       (void *)request);
	if (!ns_access_ok) {
		return -1;
	}

	pd->io_exit_args.flags |= INPLACE(RMI_IO_EXIT_FLAGS_SEND, 1UL);
	if (!is_sspdm) {
		pd->io_exit_args.req_type = RMI_IO_REQUEST_TYPE_SPDM;
	} else {
		pd->io_exit_args.req_type = RMI_IO_REQUEST_TYPE_SECURE_SPDM;
	}
	pd->io_exit_args.req_len = request_size;
	pd->io_exit_args.timeout = timeout;

	return 0;
}

/*
 * Receive response from device. RmiIoEnter with response from device and copy
 * data from NS buffer.
 */
static int rmi_pdev_comm_recv(dev_handle_t handle, void *response,
			      size_t *response_size)
{
	struct pdev *pd;
	struct granule *g_resp_addr;
	bool ns_access_ok;
	size_t resp_len;

	pd = devh_to_pdev(handle);

	/* Copy the response from NS buffer passed during pdev_communicate */
	g_resp_addr = find_granule(pd->io_enter_args.resp_addr);
	if ((g_resp_addr == NULL ||
	     granule_unlocked_state(g_resp_addr) != GRANULE_STATE_NS)) {
		return -1;
	}

	resp_len = round_up(pd->io_enter_args.resp_len, 8);
	ns_access_ok = ns_buffer_read(SLOT_NS, g_resp_addr, 0, resp_len,
				       (void *)response);
	if (!ns_access_ok) {
		return -1;
	}

	*response_size = pd->io_enter_args.resp_len;

	return 0;
}

/*
 * Set cache flags in IoExit.
 */
static int rmi_pdev_comm_cache(dev_handle_t handle, const void *cache_buf,
			       size_t cache_offset, size_t cache_len)
{
	struct pdev *pd;
	struct granule *g_resp_addr;
	bool ns_access_ok;

	pd = devh_to_pdev(handle);

	/*
	 * If 'cache_buf' is set then overwrite the NS response buffer with new
	 * data. Else use the existing content to be cached by the NS host.
	 */
	if (cache_buf != NULL) {
		size_t cache_len_rounded;

		assert(cache_offset == 0);

		g_resp_addr = find_granule(pd->io_enter_args.resp_addr);
		if ((g_resp_addr == NULL ||
		     granule_unlocked_state(g_resp_addr) != GRANULE_STATE_NS)) {
			return -1;
		}

		cache_len_rounded = round_up(cache_len, 8);
		ns_access_ok = ns_buffer_write(SLOT_NS, g_resp_addr, 0,
					       cache_len_rounded,
					       (void *)cache_buf);
		if (!ns_access_ok) {
			return -1;
		}
	}

	pd->io_exit_args.flags |= INPLACE(RMI_IO_EXIT_FLAGS_CACHE, 1UL);
	pd->io_exit_args.cache_offset = cache_offset;
	pd->io_exit_args.cache_len = cache_len;

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

/* Validate RmiIoData.RmiIoEnter argument passed by Host */
static unsigned long copyin_and_validate_io_enter(unsigned long io_data_ptr,
						  rmi_io_enter_t *io_enter_args)
{
	struct granule *g_io_data;
	bool ns_access_ok;

	g_io_data = find_granule(io_data_ptr);
	if ((g_io_data == NULL ||
	     granule_unlocked_state(g_io_data) != GRANULE_STATE_NS)) {
		return RMI_ERROR_INPUT;
	}

	ns_access_ok = ns_buffer_read(SLOT_NS, g_io_data, RMI_IO_ENTER_OFFSET,
				      sizeof(rmi_io_enter_t), io_enter_args);
	if (!ns_access_ok) {
		return RMI_ERROR_INPUT;
	}

	if (!GRANULE_ALIGNED(io_enter_args->req_addr) ||
	    !GRANULE_ALIGNED(io_enter_args->resp_addr) ||
	    (io_enter_args->resp_len > GRANULE_SIZE)) {
		return RMI_ERROR_INPUT;
	}

	/* Check if request and response buffers are in NS PAS */
	if ((granule_unlocked_state(find_granule(io_enter_args->req_addr)) !=
	     GRANULE_STATE_NS) ||
	    (granule_unlocked_state(find_granule(io_enter_args->resp_addr)) !=
	     GRANULE_STATE_NS)) {
		return RMI_ERROR_INPUT;
	}

	return RMI_SUCCESS;
}

/*
 * copyout IoExitArgs
 */
static unsigned long copyout_io_exit(unsigned long io_data_ptr,
				     rmi_io_exit_t *io_exit_args)
{
	struct granule *g_io_data;
	bool ns_access_ok;

	g_io_data = find_granule(io_data_ptr);
	if ((g_io_data == NULL ||
	     granule_unlocked_state(g_io_data) != GRANULE_STATE_NS)) {
		return RMI_ERROR_INPUT;
	}

	ns_access_ok = ns_buffer_write(SLOT_NS, g_io_data, RMI_IO_EXIT_OFFSET,
				      sizeof(rmi_io_exit_t), io_exit_args);
	if (!ns_access_ok) {
		return RMI_ERROR_INPUT;
	}

	return RMI_SUCCESS;
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
	struct granule *g_pdev;
	rmi_io_enter_t io_enter_args;
	struct pdev *pd;
	void *aux_mapped_addr __unused;
	int rc;
	int cma_rc;

	if (!GRANULE_ALIGNED(pdev_ptr) ||
	    !GRANULE_ALIGNED(io_data_ptr)) {
		return RMI_ERROR_INPUT;
	}

	/* Validate RmiIoEnter arguments in IoData */
	rc = copyin_and_validate_io_enter(io_data_ptr, &io_enter_args);
	if (rc != RMI_SUCCESS) {
		return rc;
	}

	/* Lock pdev granule and map it */
	g_pdev = find_lock_granule(pdev_ptr, GRANULE_STATE_PDEV);
	if (g_pdev == NULL) {
		return RMI_ERROR_INPUT;
	}

	pd = buffer_granule_map(g_pdev, SLOT_PDEV);
	if (pd == NULL) {
		granule_unlock(g_pdev);
		return RMI_ERROR_INPUT;
	}

	assert(pd->g_pdev == g_pdev);

	if (pd->io_state == PDEV_IO_IDLE || pd->io_state == PDEV_IO_ERROR) {
		rc = RMI_ERROR_DEVICE;
		goto out_pdev_buf_unmap;
	}

	/* todo: not mentioned in spec */
	/* IoEnter.status must be NONE when IO state is IO_PENDING */
	if ((pd->io_state == PDEV_IO_PENDING &&
	     io_enter_args.status != RMI_IO_ENTER_STATUS_NONE) ||
	    (pd->io_state == PDEV_IO_ACTIVE &&
	     (io_enter_args.status != RMI_IO_ENTER_STATUS_SUCCESS &&
	      io_enter_args.status != RMI_IO_ENTER_STATUS_ERROR))) {
		rc = RMI_ERROR_INPUT;
		goto out_pdev_buf_unmap;
	}

	/* Copy IoEnter args to PDEV and clear old IoExit args held in PDEV */
	memcpy(&pd->io_enter_args, &io_enter_args, sizeof(rmi_io_enter_t));
	memset(&pd->io_exit_args, 0, sizeof(rmi_io_exit_t));

	/* Map PDEV aux granules */
	aux_mapped_addr = buffer_pdev_aux_granules_map(pd->g_aux, pd->num_aux);
	assert(aux_mapped_addr != NULL);

	/* If PDEV needs heap, associate the heap context with current CPU */
	rc = buffer_alloc_ctx_assign(&pd->heap_ctx);
	assert(rc == 0);

	if (pd->io_state == PDEV_IO_ACTIVE) {
		cma_rc = cma_spdm_cmd_resume(pd->dev.cma_spdm_priv_data);
	} else {
		if (pd->rmi_state == RMI_PDEV_STATE_NEW) {
			cma_rc = cma_spdm_cmd_dispatch(SPDM_INIT_CONNECTION,
					       pd->dev.cma_spdm_priv_data);
		} else {
			cma_rc = CMA_SPDM_STATUS_ERROR;
			assert(false);
		}
	}

	if (cma_rc == CMA_SPDM_STATUS_ERROR) {
		pd->io_state = PDEV_IO_ERROR;
		pd->rmi_state = RMI_PDEV_STATE_ERROR;
		pd->io_exit_args.flags = 0;
	} else if (cma_rc == CMA_SPDM_STATUS_IO_WAIT) {
		pd->io_state = PDEV_IO_ACTIVE;
	} else {
		pd->io_state = PDEV_IO_IDLE;
		if (pd->rmi_state == RMI_PDEV_STATE_NEW) {
			pd->rmi_state = RMI_PDEV_STATE_NEEDS_KEY;
		} else {
			assert(false);
		}
	}

	rc = copyout_io_exit(io_data_ptr, &pd->io_exit_args);
	if (rc != RMI_SUCCESS) {
		/* todo: call cma_spdm cleanup? */
		rc = RMI_ERROR_INPUT;
		goto out_pdev_aux_unmap;
	}

out_pdev_aux_unmap:
	/* Unmap all PDEV aux granules */
	buffer_pdev_aux_unmap(aux_mapped_addr, pd->num_aux);

	buffer_alloc_ctx_unassign();

out_pdev_buf_unmap:
	buffer_unmap(pd);

	granule_unlock(g_pdev);

	return rc;
}
