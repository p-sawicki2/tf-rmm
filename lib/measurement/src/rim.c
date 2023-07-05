/*
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <cpuid.h>
#include <measurement.h>
#include <sizes.h>
#include <string.h>

/*
 * Allocate a dummy rec_params for copying relevant parameters for measurement
 */
static struct rmi_rec_params rec_params_per_cpu[MAX_CPUS];

/*
 * Update the realm measurement with the realm parameters.
 */
void realm_params_measure(unsigned char rim_measurement[],
			  enum hash_algo algorithm,
			  struct rmi_realm_params *realm_params)
{
	/* By specification realm_params is 4KB */
	unsigned char buffer[SZ_4K] = {0};
	struct rmi_realm_params *realm_params_measured =
		(struct rmi_realm_params *)&buffer[0];

	realm_params_measured->hash_algo = realm_params->hash_algo;
	/* TODO: Add later */
	/* realm_params_measured->features_0 = realm_params->features_0; */

	/* Measure relevant realm params this will be the init value of RIM */
	measurement_hash_compute(algorithm,
			       buffer,
			       sizeof(buffer),
			       rim_measurement);
}

void measurement_rec_params_measure(unsigned char rim_measurement[],
				    enum hash_algo algorithm,
				    struct rmi_rec_params *rec_params)
{
	struct measurement_desc_rec measure_desc = {0};
	struct rmi_rec_params *rec_params_measured =
		&(rec_params_per_cpu[my_cpuid()]);

	memset(rec_params_measured, 0, sizeof(*rec_params_measured));

	/*
	 * Copy the relevant parts of the rmi_rec_params structure to be
	 * measured
	 */
	rec_params_measured->pc = rec_params->pc;
	rec_params_measured->flags = rec_params->flags;
	memcpy(rec_params_measured->gprs,
	       rec_params->gprs,
	       sizeof(rec_params->gprs));

	/* Initialize the measurement descriptior structure */
	measure_desc.desc_type = MEASURE_DESC_TYPE_REC;
	measure_desc.len = sizeof(struct measurement_desc_rec);
	memcpy(measure_desc.rim,
	       rim_measurement,
	       measurement_get_size(algorithm));

	/*
	 * Hashing the REC params structure and store the result in the
	 * measurement descriptor structure.
	 */
	measurement_hash_compute(algorithm,
				rec_params_measured,
				sizeof(*rec_params_measured),
				measure_desc.content);

	/*
	 * Hashing the measurement descriptor structure; the result is the
	 * updated RIM.
	 */
	measurement_hash_compute(algorithm,
			       &measure_desc,
			       sizeof(measure_desc),
			       rim_measurement);
}

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
	memcpy(measure_desc.rim,
	       rim_measurement,
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

void measurement_ripas_granule_measure(unsigned char rim_measurement[],
				       enum hash_algo algorithm,
				       unsigned long ipa,
				       unsigned long level)
{
	struct measurement_desc_ripas measure_desc = {0};

	/* Initialize the measurement descriptior structure */
	measure_desc.desc_type = MEASURE_DESC_TYPE_RIPAS;
	measure_desc.len = sizeof(struct measurement_desc_ripas);
	measure_desc.ipa = ipa;
	measure_desc.level = level;
	memcpy(measure_desc.rim,
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
