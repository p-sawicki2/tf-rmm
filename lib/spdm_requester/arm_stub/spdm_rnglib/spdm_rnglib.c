/*
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <base.h>
#include <stdlib.h>

/*
 * Generates a 64-bit random number.
 *
 * if rand is NULL, then LIBSPDM_ASSERT().
 *
 * @param[out] rand_data     buffer pointer to store the 64-bit random value.
 *
 * @retval true         Random number generated successfully.
 * @retval false        Failed to generate the random number.
 *
 */
bool libspdm_get_random_number_64(uint64_t *rand_data)
{
	/* todo: implement libspdm_get_random_number_64 */
	return true;
}
