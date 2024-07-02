/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch_helpers.h>
#include <assert.h>
#include <debug.h>
#include <host_crypto_utils.h>
#include <host_rmi_wrappers.h>
#include <host_spdm_rsp_ifc.h>
#include <host_utils.h>
#include <platform_api.h>
#include <rmm_el3_ifc.h>
#include <s2tt.h>
#include <smc-rmi.h>
#include <smc-rsi.h>
#include <stdlib.h>
#include <string.h>

#define IS_RMI_RESULT_SUCCESS(_r)	((_r).x[0] == RMI_SUCCESS)

#define HOST_DEV_CERT_LEN_MAX		(32 * 1024)

#define DEV_OBJ_CERT			0U
#define DEV_OBJ_MEASUREMENTS		2U
#define DEV_OBJ_INTERFACE_REPORT	3U

struct host_dev {
	/* PDEV related fields */
	void *pdev;
	rmi_pdev_flags_t pdev_flags;
	void *pdev_aux[PDEV_PARAM_AUX_GRANULES_MAX];
	uint32_t pdev_aux_num;
	struct rmi_io_data *io_data;

	/* Algorithm used to generate device digests */
	uint8_t hash_algo;

	/* Certificate, public key fields */
	uint8_t cert_slot_id;
	uint8_t *cert_chain;
	size_t cert_chain_len;
	void *public_key;
	size_t public_key_len;
	rmi_signature_algorithm_t public_key_sig_algo;

	/* SPDM responder_emu ID */
	int spdm_rsp_id;
};

void *allocate_granule(void);

static const char *pdev_state_str[] = {
	"PDEV_STATE_NEW",
	"PDEV_STATE_NEEDS_KEY",
	"PDEV_STATE_HAS_KEY",
	"PDEV_STATE_READY",
	"PDEV_STATE_COMMUNICATING",
	"PDEV_STATE_STOPPED",
	"RMI_PDEV_STATE_ERROR"
};

static int host_dev_pdev_get_state(struct host_dev *dev, rmi_pdev_state_t *state)
{
	struct smc_result result;

	host_rmi_pdev_get_state(dev->pdev, &result);
	if (result.x[0] != RMI_SUCCESS) {
		return -1;
	}

	*state = (rmi_pdev_state_t)result.x[1];

	return 0;
}

static bool is_host_dev_pdev_state(struct host_dev *dev,
				   rmi_pdev_state_t exp_state)
{
	rmi_pdev_state_t cur_state;

	if (host_dev_pdev_get_state(dev, &cur_state) != 0) {
		return false;
	}

	if (cur_state != exp_state) {
		return false;
	}

	return true;
}

static int host_dev_pdev_create(struct host_dev *dev)
{
	struct rmi_pdev_params *pdev_params;
	struct smc_result result;
	uint32_t i;

	pdev_params = allocate_granule();
	memset(pdev_params, 0, GRANULE_SIZE);

	pdev_params->flags = dev->pdev_flags;
	pdev_params->cert_id = dev->cert_slot_id;
	pdev_params->pdev_id = dev->spdm_rsp_id;
	pdev_params->num_aux = dev->pdev_aux_num;
	pdev_params->hash_algo = dev->hash_algo;
	for (i = 0; i < dev->pdev_aux_num; i++) {
		pdev_params->aux[i] = (uintptr_t)dev->pdev_aux[i];
	}

	host_rmi_pdev_create(dev->pdev, pdev_params, &result);
	if (!IS_RMI_RESULT_SUCCESS(result)) {
		return -1;
	}

	return 0;
}

static int host_dev_pdev_set_key(struct host_dev *dev)
{
	struct smc_result result;

	host_rmi_pdev_set_key(dev->pdev, dev->public_key, dev->public_key_len,
			      dev->public_key_sig_algo, &result);
	if (!IS_RMI_RESULT_SUCCESS(result)) {
		return -1;
	}

	return 0;
}

static int host_dev_cache_device_object(struct host_dev *dev, uint8_t obj_type,
					const uint8_t *obj_buf, size_t obj_len)
{
	INFO("%s: obj_type: %d, obj_offset: 0x%lx, cache_len: 0x%lx\n\n",
	     __func__, obj_type, dev->cert_chain_len, obj_len);

	if (obj_type == DEV_OBJ_CERT) {
		if ((dev->cert_chain_len + obj_len) > HOST_DEV_CERT_LEN_MAX) {
			return -1;
		}

		memcpy((void *)(dev->cert_chain + dev->cert_chain_len),
		       obj_buf, obj_len);
		dev->cert_chain_len += obj_len;
	}

	return 0;
}

/* Call RMI PDEV communicate until the target state is reached */
static int host_dev_pdev_communicate(struct host_dev *dev,
				     rmi_pdev_state_t target_state)
{
	int rc;
	rmi_pdev_state_t state;
	struct smc_result result;
	rmi_io_enter_t *io_enter = &dev->io_data->rmi_io_enter;
	rmi_io_exit_t *io_exit = &dev->io_data->rmi_io_exit;
	size_t resp_len;

	io_enter->status = RMI_IO_ENTER_STATUS_NONE;
	io_enter->resp_len = 0;

	if (host_dev_pdev_get_state(dev, &state) != 0) {
		return -1;
	}

	do {
		host_rmi_pdev_communicate(dev->pdev, dev->io_data, &result);
		if (result.x[0] != RMI_SUCCESS) {
			INFO("rmi_pdev_communicate failed\n");
			rc = -1;
			break;
		}

		/*
		 * If cache is set, then response buffer has the device object
		 * to be cached.
		 */
		if (EXTRACT(RMI_IO_EXIT_FLAGS_CACHE, io_exit->flags)) {
			uint8_t *obj_buf;
			uint8_t obj_type;

			if (io_exit->cache_len == 0 ||
			    (io_exit->cache_offset + io_exit->cache_len) >
			    GRANULE_SIZE) {
				INFO("Invalid cache offset/length\n");
				rc = -1;
				break;
			}

			if (state == RMI_PDEV_STATE_NEW) {
				obj_type = DEV_OBJ_CERT;
			} else {
				rc = -1;
				break;
			}

			obj_buf = (uint8_t *)io_enter->resp_addr +
				io_exit->cache_offset;
			rc = host_dev_cache_device_object(dev, obj_type, obj_buf,
							  io_exit->cache_len);
			if (rc != 0) {
				INFO("host_dev_cache_device_object failed\n");
				rc = -1;
				break;
			}
		}

		/* Send request to spdm responder */
		if (EXTRACT(RMI_IO_EXIT_FLAGS_SEND, io_exit->flags)) {
			bool is_sspdm;

			/* todo: validate IO exit flags */
			if (io_exit->req_type == RMI_IO_REQUEST_TYPE_SPDM) {
				is_sspdm = false;
			} else if (io_exit->req_type ==
				   RMI_IO_REQUEST_TYPE_SECURE_SPDM) {
				is_sspdm = true;
			} else {
				INFO("Invalid io_exit.req_type\n");
				rc = -1;
				break;
			}

			rc = host_spdm_rsp_communicate(dev->spdm_rsp_id,
						       (void *)
						       io_enter->req_addr,
						       io_exit->req_len,
						       (void *)
						       io_enter->resp_addr,
						       &resp_len,
						       is_sspdm);
			/*
			 * Set IoEnter args for next pdev_communicate. Upon
			 * success or error call pdev_communicate
			 */
			if (rc == 0) {
				io_enter->status = RMI_IO_ENTER_STATUS_SUCCESS;
				io_enter->resp_len = resp_len;
			} else {
				io_enter->status = RMI_IO_ENTER_STATUS_ERROR;
				io_enter->resp_len = 0;
			}
		}

		rc = host_dev_pdev_get_state(dev, &state);
		if (rc != 0) {
			break;
		}
	} while ((state != target_state) && (state != RMI_PDEV_STATE_ERROR));

	return rc;
}

/*
 * Invoke RMI handler to transition PDEV state to 'to_state'
 */
static int host_dev_pdev_transition(struct host_dev *dev,
				    rmi_pdev_state_t to_state)
{
	int rc;

	switch (to_state) {
	case RMI_PDEV_STATE_NEW:
		rc = host_dev_pdev_create(dev);
		break;
	case RMI_PDEV_STATE_NEEDS_KEY:
		rc = host_dev_pdev_communicate(dev, RMI_PDEV_STATE_NEEDS_KEY);
		break;
	case RMI_PDEV_STATE_HAS_KEY:
		rc = host_dev_pdev_set_key(dev);
		break;
	case RMI_PDEV_STATE_READY:
		rc = host_dev_pdev_communicate(dev, RMI_PDEV_STATE_READY);
		break;
	default:
		rc = -1;
	}

	if (rc != 0) {
		INFO("RMI command failed\n");
		return -1;
	}

	if (!is_host_dev_pdev_state(dev, to_state)) {
		ERROR("PDEV state not [%s]\n", pdev_state_str[to_state]);
		return -1;
	}

	return 0;
}

/* host_dev_setup */
static int host_dev_setup(struct host_dev *dev, uint32_t rmi_pdev_aux_num)
{
	struct smc_result result;
	int spdm_rsp_id;
	int i, rc;

	memset(dev, 0, sizeof(struct host_dev));

	/* Connect with SPDM responder emu */
	rc = host_spdm_rsp_init(SPDM_RSP_DEFAULT_HOST_ADDR, SPDM_RSP_EMU1_PORT,
				&spdm_rsp_id);
	if (rc != 0) {
		INFO("Connect to SPDM responder failed.\n");
		return -1;
	}

	/* Allocate granule for PDEV and delegate */
	dev->pdev = allocate_granule();
	memset(dev->pdev, 0, GRANULE_SIZE);
	host_rmi_granule_delegate(dev->pdev, &result);
	if (!IS_RMI_RESULT_SUCCESS(result)) {
		return -1;
	}

	dev->pdev_flags = (INPLACE(RMI_PDEV_FLAGS_SPDM, RMI_SPDM_TRUE) |
			   INPLACE(RMI_PDEV_FLAGS_IDE, RMI_IDE_SEL));
	dev->pdev_aux_num = rmi_pdev_aux_num;
	dev->spdm_rsp_id = spdm_rsp_id;

	/* Allocate aux granules for PDEV and delegate */
	INFO("PDEV create requires %u aux pages\n", rmi_pdev_aux_num);
	for (i = 0; i < rmi_pdev_aux_num; i++) {
		dev->pdev_aux[i] = allocate_granule();
		host_rmi_granule_delegate(dev->pdev_aux[i], &result);
		if (!IS_RMI_RESULT_SUCCESS(result)) {
			return -1;
		}
	}

	/* Allocate io_data and send/recv buffer for IO */
	dev->io_data = (struct rmi_io_data *)allocate_granule();
	memset(dev->io_data, 0, sizeof(struct rmi_io_data));
	dev->io_data->rmi_io_enter.req_addr = (unsigned long)allocate_granule();
	dev->io_data->rmi_io_enter.resp_addr = (unsigned long)allocate_granule();

	/* Allocate buffer to cache device certificate */
	dev->cert_slot_id = 0;
	dev->cert_chain = (uint8_t *)malloc(HOST_DEV_CERT_LEN_MAX);
	dev->cert_chain_len = 0;
	if (dev->cert_chain == NULL) {
		return -1;
	}

	/* Allocate buffer to store extracted public key */
	dev->public_key = (void *)allocate_granule();
	if (dev->public_key == NULL) {
		return -1;
	}

	/* Set algorithm to use for device digests */
	dev->hash_algo = RMI_HASH_SHA_512;

	return 0;
}

/* Invoke DA ABIs */
int host_rmi_feat_da(void)
{
	unsigned long feat_reg0;
	uint32_t rmi_pdev_aux_num;
	struct smc_result result;
	struct host_dev dev;
	uint8_t public_key_algo;
	int rc;

	/* Check if DA enabled in RMI features */
	host_rmi_read_feature_register(RMI_FEATURE_REGISTER_0_INDEX, &result);
	if (!IS_RMI_RESULT_SUCCESS(result)) {
		return -1;
	}
	feat_reg0 = result.x[1];

	if (EXTRACT(RMI_FEATURE_REGISTER_0_DA_EN, feat_reg0) ==
	    RMI_FEATURE_FALSE) {
		INFO("RMI FEAT DA not enabled. Skipping DA ABIs\n");
		return 0;
	}

	/* Get max aux granules required for PDEV */
	rmi_pdev_aux_num = EXTRACT(RMI_FEATURE_REGISTER_0_PDEV_NUM_AUX,
				   feat_reg0);
	/*
	 * RMM spec will be updated to use new RMI call for getting pdev_aux */
	rmi_pdev_aux_num = 22;

	/* Allocate granules. Skip DA ABIs if host_dev_setup fails */
	rc = host_dev_setup(&dev, rmi_pdev_aux_num);
	if (rc == -1) {
		INFO("host_dev_setup failed. skipping DA ABIs...\n");
		return 0;
	}

	/* Call rmi_pdev_create to transition PDEV to STATE_NEW */
	rc = host_dev_pdev_transition(&dev, RMI_PDEV_STATE_NEW);
	if (rc != 0) {
		ERROR("PDEV transition: NULL -> STATE_NEW failed\n");
		return -1;
	}

	/* Call rmi_pdev_communicate to transition PDEV to NEEDS_KEY */
	rc = host_dev_pdev_transition(&dev, RMI_PDEV_STATE_NEEDS_KEY);
	if (rc != 0) {
		ERROR("PDEV transition: PDEV_NEW -> PDEV_NEEDS_KEY failed\n");
		return -1;
	}

	/* Get public key. Verify cert_chain not done by host but by Realm? */
	rc = host_get_public_key_from_cert_chain(dev.cert_chain,
						 dev.cert_chain_len,
						 dev.public_key,
						 &dev.public_key_len,
						 &public_key_algo);
	if (rc != 0) {
		ERROR("Get public key failed\n");
		return -1;
	}

	if (public_key_algo == PUBLIC_KEY_ALGO_ECDSA_ECC_NIST_P256) {
		dev.public_key_sig_algo = RMI_SIGNATURE_ALGORITHM_ECDSA_P256;
	} else if (public_key_algo == PUBLIC_KEY_ALGO_ECDSA_ECC_NIST_P384) {
		dev.public_key_sig_algo = RMI_SIGNATURE_ALGORITHM_ECDSA_P384;
	} else {
		dev.public_key_sig_algo = RMI_SIGNATURE_ALGORITHM_RSASSA_3072;
	}
	INFO("DEV public key len/sig_algo: %ld/%d\n", dev.public_key_len,
	     dev.public_key_sig_algo);

	/* Call rmi_pdev_set_key transition PDEV to HAS_KEY */
	rc = host_dev_pdev_transition(&dev, RMI_PDEV_STATE_HAS_KEY);
	if (rc != 0) {
		INFO("PDEV transition: PDEV_NEEDS_KEY -> PDEV_HAS_KEY failed\n");
		return -1;
	}

	/* Call rmi_pdev_comminucate to transition PDEV to READY state */
	rc = host_dev_pdev_transition(&dev, RMI_PDEV_STATE_READY);
	if (rc != 0) {
		INFO("PDEV transition: PDEV_HAS_KEY -> PDEV_READY failed\n");
		return -1;
	}

	return rc;
}
