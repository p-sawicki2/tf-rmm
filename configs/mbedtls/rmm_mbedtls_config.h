/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

/*
 * Based on migration guide[1]:
 *
 * config.h was split into build_info.h and mbedtls_config.h. In code, use
 * #include <mbedtls/build_info.h>. Don't include mbedtls/config.h and don't
 * refer to MBEDTLS_CONFIG_FILE. And also the guide recommends, if you have a
 * custom configuration file don't define MBEDTLS_CONFIG_H anymore.
 *
 * [1] https://github.com/Mbed-TLS/mbedtls/blob/v3.6.0/docs/3.0-migration-guide.md
 */

/* This file is compatible with release 3.6.0 */
#define MBEDTLS_CONFIG_VERSION         0x03060000

/*
 * Configuration file to build mbed TLS with the required features for
 * RMM
 */
#define MBEDTLS_PLATFORM_MEMORY
#define MBEDTLS_PLATFORM_FREE_MACRO buffer_alloc_free
#define MBEDTLS_PLATFORM_CALLOC_MACRO buffer_alloc_calloc

#define MBEDTLS_PLATFORM_NO_STD_FUNCTIONS

#define MBEDTLS_CIPHER_C
#define MBEDTLS_PSA_CRYPTO_C

#define MBEDTLS_ECP_C
#define MBEDTLS_ECP_DP_SECP384R1_ENABLED
#define MBEDTLS_ECP_RESTARTABLE
#define MBEDTLS_ECDSA_C
#define MBEDTLS_ECDSA_DETERMINISTIC
#define MBEDTLS_ECP_WINDOW_SIZE		(2U)	/* Valid range = [2,7] */

#define MBEDTLS_PSA_CRYPTO_EXTERNAL_RNG

/*
 * This is enabled in RMM as PSA calls are made within the trust boundary.
 * Disabling this option causes mbedtls to create a local copy of input buffer
 * using buffer_alloc_calloc() during realm_create and we don't assign mbedtls
 * heap for RMI calls other than REC_ENTER.
 */
#define MBEDTLS_PSA_ASSUME_EXCLUSIVE_BUFFERS

#define MBEDTLS_ASN1_PARSE_C
#define MBEDTLS_ASN1_WRITE_C

#define MBEDTLS_PLATFORM_SNPRINTF_MACRO snprintf

#define MBEDTLS_BASE64_C
#define MBEDTLS_BIGNUM_C

#define MBEDTLS_ERROR_C

#define MBEDTLS_HKDF_C
#define MBEDTLS_HMAC_DRBG_C

#define MBEDTLS_MD_C

#define MBEDTLS_PLATFORM_C

#define MBEDTLS_SHA256_C
#define MBEDTLS_SHA224_C
#define MBEDTLS_SHA384_C
#define MBEDTLS_SHA512_C

#define MBEDTLS_VERSION_C

/*
 * Prevent the use of 128-bit division which
 * creates dependency on external libraries.
 */
#define MBEDTLS_NO_UDBL_DIVISION

/* Memory buffer allocator option */
#define MBEDTLS_MEMORY_ALIGN_MULTIPLE	8

/*
 * Enable acceleration of the SHA-256, SHA-224, SHA-512 and SHA-384
 * cryptographic hash algorithms with the ARMv8 cryptographic extensions, which
 * must be available at runtime or else an illegal instruction fault will occur.
 */
#ifdef RMM_FPU_USE_AT_REL2
#define MBEDTLS_SHA256_USE_A64_CRYPTO_ONLY
#define MBEDTLS_SHA512_USE_A64_CRYPTO_ONLY
#endif

/* This is needed for size_t used below */
#include <stddef.h>

/*
 * Declare memory allocation primitives to be used by MbedTLS
 */
void *buffer_alloc_calloc(size_t n, size_t size);
void buffer_alloc_free(void *ptr);
