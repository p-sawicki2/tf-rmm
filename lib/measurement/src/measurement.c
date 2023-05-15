/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <debug.h>
#include <measurement.h>
#include <psa/crypto.h>
#include <simd.h>
#include <stdbool.h>

#if LOG_LEVEL >= LOG_LEVEL_VERBOSE
static void measurement_print(unsigned char *measurement,
			      const enum hash_algo algorithm)
{
	unsigned int size = 0U;
	assert(measurement != NULL);

	VERBOSE("Measurement ");

	switch (algorithm) {
	case HASH_ALGO_SHA256:
		VERBOSE("(SHA256): 0x");
		size = SHA256_SIZE;
		break;
	case HASH_ALGO_SHA512:
		VERBOSE("(SHA512): 0x");
		size = SHA512_SIZE;
		break;
	default:
		/* Prevent static check and MISRA warnings */
		assert(false);
	}

	for (unsigned int i = 0U; i < size; ++i) {
		VERBOSE("%02x", *(measurement+i));
	}
	VERBOSE("\n");
}
#endif /* LOG_LEVEL */

static void do_hash(enum hash_algo hash_algo,
		    void *data,
		    size_t size,
		    unsigned char *out)
{
	__unused int ret;
	psa_algorithm_t psa_algorithm;
	size_t hash_size;

	assert(size <= GRANULE_SIZE);
	assert((data != NULL) && (out != NULL));


	if (hash_algo == HASH_ALGO_SHA256) {
		psa_algorithm = PSA_ALG_SHA_256;
	} else if (hash_algo == HASH_ALGO_SHA512) {
		psa_algorithm = PSA_ALG_SHA_512;
	} else {
		assert(false);
	}

	fpu_save_my_state();

	FPU_ALLOW(ret = psa_hash_compute(psa_algorithm,
			data,
			size,
			out,
			PSA_HASH_LENGTH(psa_algorithm),
			&hash_size));
	assert(hash_size == PSA_HASH_LENGTH(psa_algorithm));
	assert(ret == 0);

	fpu_restore_my_state();

#if LOG_LEVEL >= LOG_LEVEL_VERBOSE
	measurement_print(out, hash_algo);
#endif
}

void measurement_hash_compute(enum hash_algo hash_algo,
			      void *data,
			      size_t size,
			      unsigned char *out)
{
	do_hash(hash_algo, data, size, out);
}

static void do_extend(psa_algorithm_t psa_algorithm,
		      void *current_measurement,
		      void *extend_measurement,
		      size_t extend_measurement_size,
		      unsigned char *out)
{
	size_t hash_size;
	psa_status_t ret;
	psa_hash_operation_t operation = PSA_HASH_OPERATION_INIT;
	size_t current_measurement_size = PSA_HASH_LENGTH(psa_algorithm);

	ret = psa_hash_setup(&operation, psa_algorithm);
	assert(ret == PSA_SUCCESS);

	ret = psa_hash_update(&operation,
                              (unsigned char *)current_measurement,
			      current_measurement_size);
	assert(ret == PSA_SUCCESS);

	ret = psa_hash_update(&operation,
			      (unsigned char *)extend_measurement,
			      extend_measurement_size);
	assert(ret == PSA_SUCCESS);

	ret = psa_hash_finish(&operation,
			      out,
			      PSA_HASH_LENGTH(psa_algorithm),
			      &hash_size);
	assert(hash_size == PSA_HASH_LENGTH(psa_algorithm));
	assert(ret == PSA_SUCCESS);
}

void measurement_extend(enum hash_algo hash_algo,
			void *current_measurement,
			void *extend_measurement,
			size_t extend_measurement_size,
			unsigned char *out)
{
	psa_algorithm_t psa_algorithm;

	/* We limit the maximum size of the payload to be of GRANULE_SIZE */
	assert(current_measurement != NULL);
	assert(extend_measurement_size <= GRANULE_SIZE);
	assert(extend_measurement != NULL);
	assert(out != NULL);

	fpu_save_my_state();

	switch (hash_algo) {
	case HASH_ALGO_SHA256:
		psa_algorithm = PSA_ALG_SHA_256;
		break;
	case HASH_ALGO_SHA512:
		psa_algorithm = PSA_ALG_SHA_512;
		break;
	default:
		assert(false);
	}

	FPU_ALLOW(
		do_extend(psa_algorithm,
			  current_measurement,
			  extend_measurement,
			  extend_measurement_size,
			  out));

	fpu_restore_my_state();

#if LOG_LEVEL >= LOG_LEVEL_VERBOSE
	measurement_print(out, hash_algo);
#endif
}
