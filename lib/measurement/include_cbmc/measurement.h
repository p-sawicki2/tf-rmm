/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

/*
 *****************************************
 * This header is only for CBMC analysis *
 *****************************************
 */

#ifndef MEASUREMENT_H
#define MEASUREMENT_H

#include <smc-rmi.h>
#include <stdbool.h>
#include <stddef.h>

enum hash_algo {
	HASH_SHA_256 = RMI_HASH_SHA_256,
	HASH_SHA_512 = RMI_HASH_SHA_512,
};

#define RIM_MEASUREMENT_SLOT		(0U)
#define MEASUREMENT_SLOT_NR		(1U)
#define MAX_MEASUREMENT_SIZE		1

static void measurement_hash_compute(enum hash_algo hash_algo,
			      void *data,
			      size_t size, unsigned char *out)
{
	/* Write a single byte */
	*out = 42;
}

static void measurement_extend(enum hash_algo hash_algo,
			void *current_measurement,
			void *extend_measurement,
			size_t extend_measurement_size,
			unsigned char *out)
{}

static inline size_t measurement_get_size(const enum hash_algo algorithm)
{
	return 8UL;
}

static
void measurement_data_granule_measure(unsigned char rim_measurement[],
				      enum hash_algo algorithm,
				      void *data,
				      unsigned long ipa,
				      unsigned long flags)
{}

static
void measurement_realm_params_measure(unsigned char rim_measurement[],
			  enum hash_algo algorithm,
			  struct rmi_realm_params *realm_params)
{}

static
void measurement_rec_params_measure(unsigned char rim_measurement[],
				    enum hash_algo algorithm,
				    struct rmi_rec_params *rec_params)
{}

static
void measurement_ripas_granule_measure(unsigned char rim_measurement[],
				       enum hash_algo algorithm,
				       unsigned long ipa,
				       unsigned long level)
{}

#endif /* MEASUREMENT_H */
