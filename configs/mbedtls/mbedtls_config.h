/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */
#ifndef MBEDTLS_CONFIG_H
#define MBEDTLS_CONFIG_H

#include <limits.h>
/* This is needed for size_t */
#include <stddef.h>
/* For snprintf function declaration */
#include <stdio.h>

/* This file is compatible with release 3.1.0 */
#define MBEDTLS_CONFIG_VERSION         0x03010000

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
#define MBEDTLS_ECDH_LEGACY_CONTEXT
#define MBEDTLS_ECDSA_C
#define MBEDTLS_ECDSA_DETERMINISTIC
#define MBEDTLS_ECP_WINDOW_SIZE		(2U)	/* Valid range = [2,7] */

#define MBEDTLS_PSA_CRYPTO_EXTERNAL_RNG

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

/* Configs required by SPDM requester libs - start */
#define MBEDTLS_OID_C
#define MBEDTLS_RSA_C
#define MBEDTLS_PKCS1_V15
#define MBEDTLS_PKCS1_V21
#define MBEDTLS_ALLOW_PRIVATE_ACCESS
#define MBEDTLS_GENPRIME

#define MBEDTLS_X509_USE_C
#define MBEDTLS_X509_CRT_PARSE_C
#define MBEDTLS_X509_CRL_PARSE_C
#define MBEDTLS_X509_CSR_PARSE_C
#define MBEDTLS_X509_CREATE_C
#define MBEDTLS_X509_CSR_WRITE_C

#define MBEDTLS_AES_C
#define MBEDTLS_GCM_C

#define MBEDTLS_CHACHA20_C
#define MBEDTLS_POLY1305_C
#define MBEDTLS_CHACHAPOLY_C

#define MBEDTLS_ECDH_C
#define MBEDTLS_DHM_C

#define MBEDTLS_PK_C
#define MBEDTLS_PK_PARSE_C
#define MBEDTLS_PK_WRITE_C

#define MBEDTLS_ECP_DP_SECP256R1_ENABLED
#define MBEDTLS_ECP_DP_SECP384R1_ENABLED
#define MBEDTLS_ECP_DP_SECP521R1_ENABLED

/* todo: add #define MBEDTLS_PEM_PARSE_C */
/* Configs required by SPDM requester libs - end */

/*
 * Declare memory allocation primitives to be used by MbedTLS
 */
void *buffer_alloc_calloc(size_t n, size_t size);
void buffer_alloc_free(void *ptr);

#endif /* MBEDTLS_CONFIG_H */
