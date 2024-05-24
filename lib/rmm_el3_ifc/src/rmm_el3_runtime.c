/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <debug.h>
#include <rmm_el3_ifc.h>
#include <rmm_el3_ifc_priv.h>
#include <spinlock.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <xlat_defs.h>

/* Spinlock used to protect the EL3<->RMM shared area */
static spinlock_t shared_area_lock = {0U};

/*
 * Get and lock a pointer to the start of the RMM<->EL3 shared buffer.
 */
uintptr_t rmm_el3_ifc_get_shared_buf_locked(void)
{
	spinlock_acquire(&shared_area_lock);

	return rmm_shared_buffer_start_va;
}

/*
 * Release the RMM <-> EL3 buffer.
 */
void rmm_el3_ifc_release_shared_buf(void)
{
	spinlock_release(&shared_area_lock);
}

static unsigned long get_buffer_pa(uintptr_t buf, size_t buflen)
{
	unsigned long buffer_pa;
	unsigned long offset = buf - rmm_shared_buffer_start_va;

	assert((offset + buflen) <= rmm_el3_ifc_get_shared_buf_size());
	assert((buf & ~PAGE_SIZE_MASK) == rmm_shared_buffer_start_va);

	buffer_pa = (unsigned long)rmm_el3_ifc_get_shared_buf_pa() + offset;

	return buffer_pa;
}

static int rmm_el3_ifc_get_realm_attest_key_internal(uintptr_t buf,
						     size_t buflen, size_t *len,
						     unsigned int crv,
						     unsigned long id)
{
	struct smc_result smc_res;

	monitor_call_with_res(id,
			      get_buffer_pa(buf, buflen),
			      buflen,
			      crv, 0UL, 0UL, 0UL, &smc_res);

	/* coverity[uninit_use:SUPPRESS] */
	if (smc_res.x[0] != 0UL) {
		ERROR("Failed to get realm attestation key x0 = 0x%lx\n",
		      smc_res.x[0]);
		return (int)smc_res.x[0];
	}

	*len = smc_res.x[1];

	return 0;
}

/*
 * Get the realm attestation key to sign the realm attestation token. It is
 * expected that only the private key is retrieved in raw format.
 */
int rmm_el3_ifc_get_realm_attest_key(uintptr_t buf, size_t buflen, size_t *len,
				     unsigned int crv)
{
	return rmm_el3_ifc_get_realm_attest_key_internal(
		buf, buflen, len, crv, SMC_RMM_GET_REALM_ATTEST_KEY);
}

/*
 * Get the platform token from the EL3 firmware.
 * The caller must have already populated the public hash in `buf` which is an
 * input for platform token computation.
 */
int rmm_el3_ifc_get_platform_token(uintptr_t buf, size_t buflen,
					size_t *len, size_t hash_size)
{
	struct smc_result smc_res;
	/* Get the available space on the buffer after the offset */

	monitor_call_with_res(SMC_RMM_GET_PLAT_TOKEN,
			      get_buffer_pa(buf, buflen),
			      buflen,
			      hash_size,
			      0UL, 0UL, 0UL, &smc_res);

	/* coverity[uninit_use:SUPPRESS] */
	if (smc_res.x[0] != 0UL) {
		ERROR("Failed to get platform token x0 = 0x%lx\n",
				smc_res.x[0]);
		return (int)smc_res.x[0];
	}

	*len = smc_res.x[1];

	return 0;
}

/*
 * Push an attestation request to the HES.
 * The caller must have already populated the request in the shared buffer.
 * The push operation may fail if EL3 does not have enough queue space or if
 * the HES is not ready to accept the request.
 */
int rmm_el3_ifc_push_hes_request(uintptr_t buf, size_t buflen)
{
	struct smc_result smc_res;

	monitor_call_with_res(SMC_RMM_HES_PUSH_ATTEST_REQ,
			      get_buffer_pa(buf, buflen),
			      buflen,
			      0UL,
			      0UL, 0UL, 0UL, &smc_res);

	/* coverity[uninit_use:SUPPRESS] */
	if (smc_res.x[0] != 0UL) {
		VERBOSE("Failed to push attest req to HES x0 = 0x%lx\n",
		      smc_res.x[0]);
		return (int)smc_res.x[0];
	}

	return 0;
}

/*
 * Pull an attestation response from the HES. The pull operation may fail if
 * the HES has not yet provided a response.
 */
int rmm_el3_ifc_pull_hes_response(uintptr_t buf, size_t buflen,
					size_t *len)
{
	struct smc_result smc_res;

	monitor_call_with_res(SMC_RMM_HES_PULL_ATTEST_RESP,
			      get_buffer_pa(buf, buflen),
			      buflen,
			      0UL, 0UL, 0UL, 0UL, &smc_res);

	/* coverity[uninit_use:SUPPRESS] */
	if (smc_res.x[0] != 0UL) {
		VERBOSE("Failed to get attestation response x0 = 0x%lx\n",
		      smc_res.x[0]);
		return (int)smc_res.x[0];
	}

	*len = smc_res.x[1];

	return 0;
}

/*
 * Get the realm attestation key to sign the realm attestation token. It is
 * expected that only the private key is retrieved in raw format.
 */
int rmm_el3_ifc_get_realm_attest_pub_key_from_hes(uintptr_t buf, size_t buflen,
						  size_t *len, unsigned int crv)
{
	return rmm_el3_ifc_get_realm_attest_key_internal(
		buf, buflen, len, crv, SMC_RMM_GET_REALM_ATTEST_PUB_KEY_HES);
}
