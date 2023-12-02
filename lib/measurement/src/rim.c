/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <measurement.h>
#include <psa/crypto.h>
#include <string.h>

void measurement_data_granule_measure(unsigned char rim_measurement[],
				      enum hash_algo algorithm,
				      void *data,
				      unsigned long ipa,
				      unsigned long flags)
{
	struct measurement_desc_data measure_desc = {0};

	/* Initialize the measurement descriptior structure */
	measure_desc.desc_type = MEASURE_DESC_TYPE_DATA;
	measure_desc.len = sizeof(struct measurement_desc_data);
	measure_desc.ipa = ipa;
	measure_desc.flags = flags;
	(void)memcpy(measure_desc.rim, rim_measurement,
					measurement_get_size(algorithm));

	if (flags == RMI_MEASURE_CONTENT) {
		/*
		 * Hashing the data granules and store the result in the
		 * measurement descriptor structure.
		 */
		measurement_hash_compute(algorithm,
					data,
					GRANULE_SIZE,
					measure_desc.content);
	}

	/*
	 * Hashing the measurement descriptor structure; the result is the
	 * updated RIM.
	 */
	measurement_hash_compute(algorithm,
			       &measure_desc,
			       sizeof(measure_desc),
			       rim_measurement);
}

struct rim_measurement_context {
	psa_hash_operation_t operation;
	psa_algorithm_t psa_algorithm;
	void *next_location_to_update;
	void* structure_end;
};

#define MIN(x, y) ((x) < (y) ? (x) : (y))

static void hash_zeroes(psa_hash_operation_t *operation, size_t length) {
	/*
	 * This thing is now in the bss section. No need to be per-cpu as it is read only.
	 * But this can be created on the stack. Although in that case it needs to be
	 * initialised on every call.
	 * In an extreme case a reserved part of the measured structure could be passed
	 * to this function as a zero buffer. In this case	no extra allocation and memset is necessary.
	*/
	static unsigned char zero_buf[128] = {0};
	__unused psa_status_t ret;

	while (length) {
		size_t zeroes_to_hash =
			MIN(sizeof(zero_buf), length);
		ret = psa_hash_update(operation, zero_buf, zeroes_to_hash);
		length -= zeroes_to_hash;
		assert(ret == PSA_SUCCESS);
	}
}

static void start_measurement(struct rim_measurement_context *context,
			      enum hash_algo algorithm,
			      void* structure_address,
			      size_t structure_size) {
	psa_algorithm_t psa_algorithm = PSA_ALG_NONE;
	__unused psa_status_t ret;

	/* This should probably now be a utility function, already multiple times in measurement.c */
	switch (algorithm) {
	case HASH_SHA_256:
		psa_algorithm = PSA_ALG_SHA_256;
		break;
	case HASH_SHA_512:
		psa_algorithm = PSA_ALG_SHA_512;
		break;
	default:
		assert(false);
	};

	context->operation = psa_hash_operation_init();;
	context->next_location_to_update = structure_address;
	context->structure_end = structure_address + structure_size;
	context->psa_algorithm = psa_algorithm;

	ret = psa_hash_setup(&(context->operation), psa_algorithm);
	assert(ret == PSA_SUCCESS);
}


static void update_measurement(struct rim_measurement_context *context, void* member_address, size_t member_size) {
	size_t zeroes_to_hash;
	__unused psa_status_t ret;

	assert(member_address >= context->next_location_to_update);

	zeroes_to_hash = member_address - context->next_location_to_update;

	if (zeroes_to_hash > 0) {
		hash_zeroes(&(context->operation), zeroes_to_hash);
	}

	ret = psa_hash_update(&(context->operation),
			      (unsigned char *)member_address,
			      member_size);
	assert(ret == PSA_SUCCESS);
	context->next_location_to_update = member_address + member_size;
}

static void finish_measurement(struct rim_measurement_context *context,
			       unsigned char *out) {
	size_t zeroes_to_hash;
	size_t hash_size;
	__unused psa_status_t ret;
	assert(context->next_location_to_update <= context->structure_end);

	zeroes_to_hash = context->structure_end - context->next_location_to_update;

	if (zeroes_to_hash > 0) {
		hash_zeroes(&(context->operation), zeroes_to_hash);
	}

	ret = psa_hash_finish(&context->operation,
			      out,
			      (size_t)PSA_HASH_LENGTH(context->psa_algorithm),
			      &hash_size);
	assert(hash_size == (size_t)PSA_HASH_LENGTH(context->psa_algorithm));
	assert(ret == PSA_SUCCESS);
}


void measurement_realm_params_measure(unsigned char rim_measurement[],
				      enum hash_algo algorithm,
				      struct rmi_realm_params *realm_params)
{

	/* Calculate using hash_update */
	struct rim_measurement_context measurement_context;
	size_t i;

	/* Not necessary, only for easier comparing */
	memset(rim_measurement, 0, MAX_MEASUREMENT_SIZE);

	start_measurement(&measurement_context, algorithm, realm_params, sizeof(struct rmi_realm_params));
	update_measurement(&measurement_context, &realm_params->flags, sizeof(realm_params->flags));
	update_measurement(&measurement_context, &realm_params->s2sz, sizeof(realm_params->s2sz));
	update_measurement(&measurement_context, &realm_params->sve_vl, sizeof(realm_params->sve_vl));
	update_measurement(&measurement_context, &realm_params->num_bps, sizeof(realm_params->num_bps));
	update_measurement(&measurement_context, &realm_params->num_wps, sizeof(realm_params->num_wps));
	update_measurement(&measurement_context, &realm_params->pmu_num_ctrs, sizeof(realm_params->pmu_num_ctrs));
	update_measurement(&measurement_context, &realm_params->algorithm, sizeof(realm_params->algorithm));
	finish_measurement(&measurement_context, rim_measurement);

	/*
	 * The following attributes are used for calculation of the
	 * initial RIM value of the Realm:
 	 * - flags
	 * - s2sz
	 * - sve_vl
	 * - num_bps
	 * - num_wps
	 * - pmu_num_ctrs
	 * - hash_algo
	 *
	 * Clear non-relevant parts of the rmi_realm_params structure
	 * for calculation. Unused bits of the structure SBZ.
	 */

	/* Original code is here for checking regression*/
	unsigned char rim_measurement_check [MAX_MEASUREMENT_SIZE];
	/* Not necessary, only for easier comparing */
	memset(rim_measurement_check, 0, MAX_MEASUREMENT_SIZE);

	(void)memset(realm_params->rpv, 0, sizeof(realm_params->rpv));

	realm_params->vmid = 0U;
	realm_params->rtt_base = 0UL;
	realm_params->rtt_level_start = 0L;
	realm_params->rtt_num_start = 0U;

	/* Measure relevant Realm params, this will be the init value of RIM */
	measurement_hash_compute(algorithm,
				 realm_params,
				 sizeof(struct rmi_realm_params),
				 rim_measurement_check);

	for (i = 0; i < MAX_MEASUREMENT_SIZE; ++i) {
		assert(rim_measurement_check[i] == rim_measurement[i]);
	}
}

void measurement_rec_params_measure(unsigned char rim_measurement[],
				    enum hash_algo algorithm,
				    struct rmi_rec_params *rec_params)
{
	struct measurement_desc_rec measure_desc = {0};

	/*
	 * Clear non-relevant parts of the rmi_rec_params structure
	 * for initial measurement. Unused bits of the structure SBZ
	 * according to the Specification.
	 */
	rec_params->mpidr = 0UL;
	rec_params->num_aux = 0UL;
	(void)memset(rec_params->aux, 0, sizeof(rec_params->aux));

	/* Initialize the measurement descriptior structure */
	measure_desc.desc_type = MEASURE_DESC_TYPE_REC;
	measure_desc.len = sizeof(struct measurement_desc_rec);
	(void)memcpy(measure_desc.rim, rim_measurement,
					measurement_get_size(algorithm));
	/*
	 * Hash the REC params structure and store the result in the
	 * measurement descriptor structure.
	 */
	measurement_hash_compute(algorithm,
				rec_params,
				sizeof(struct rmi_rec_params),
				measure_desc.content);
	/*
	 * Hash the measurement descriptor structure; the result is the
	 * updated RIM.
	 */
	measurement_hash_compute(algorithm,
			       &measure_desc,
			       sizeof(measure_desc),
			       rim_measurement);
}

void measurement_init_ripas_measure(unsigned char rim_measurement[],
				    enum hash_algo algorithm,
				    unsigned long base,
				    unsigned long top)
{
	struct measurement_desc_ripas measure_desc = {0};

	/* Initialize the measurement descriptior structure */
	measure_desc.desc_type = MEASURE_DESC_TYPE_RIPAS;
	measure_desc.len = sizeof(struct measurement_desc_ripas);
	measure_desc.base = base;
	measure_desc.top = top;
	(void)memcpy(measure_desc.rim,
		     rim_measurement,
		     measurement_get_size(algorithm));

	/*
	 * Hashing the measurement descriptor structure; the result is the
	 * updated RIM.
	 */
	measurement_hash_compute(algorithm,
				 &measure_desc,
				 sizeof(measure_desc),
				 rim_measurement);
}
