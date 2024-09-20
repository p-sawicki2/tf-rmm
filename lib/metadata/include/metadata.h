/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef METADATA_H
#define METADATA_H

#include <stddef.h>
#include <utils_def.h>
#include <measurement.h>

#define FMT_VERSION U(1)
#define REALM_ID_SIZE U(128)
#define P384_PUBLIC_KEY_SIZE U(96)
#define P384_SIGNATURE_SIZE P384_PUBLIC_KEY_SIZE
#define P384_SIGNATURE_POINT_SIZE U(P384_SIGNATURE_SIZE / 2)
#define SHA_384_HASH_SIZE U(48)

#define METADATA_HASH_SHA_256 U(0x01)
#define METADATA_HASH_SHA_512 U(0x02)

#define REALM_METADATA_HEADER_SIZE U(0x150)
#define REALM_METADATA_SIGNED_SIZE U(0x1B0)
#define REALM_METADATA_UNUSED_SIZE U(0xE50)

struct rmi_islet_realm_metadata {
	uint64_t fmt_version;
	uint8_t realm_id[REALM_ID_SIZE];
	uint8_t rim[MAX_MEASUREMENT_SIZE];
	uint64_t hash_algo;
	uint64_t svn;
	uint64_t version_major;
	uint64_t version_minor;
	uint64_t version_patch;
	uint8_t public_key[P384_PUBLIC_KEY_SIZE];
	uint8_t signature[P384_SIGNATURE_SIZE];
	uint8_t _unused[REALM_METADATA_UNUSED_SIZE];
};

COMPILER_ASSERT(sizeof(struct rmi_islet_realm_metadata) == GRANULE_SIZE);
COMPILER_ASSERT(sizeof(struct rmi_islet_realm_metadata) >= REALM_METADATA_SIGNED_SIZE);

COMPILER_ASSERT(U(offsetof(struct rmi_islet_realm_metadata, fmt_version)) == 0x0U);
COMPILER_ASSERT(U(offsetof(struct rmi_islet_realm_metadata, realm_id)) == 0x8U);
COMPILER_ASSERT(U(offsetof(struct rmi_islet_realm_metadata, rim)) == 0x88U);
COMPILER_ASSERT(U(offsetof(struct rmi_islet_realm_metadata, hash_algo)) == 0xC8U);
COMPILER_ASSERT(U(offsetof(struct rmi_islet_realm_metadata, svn)) == 0xd0U);
COMPILER_ASSERT(U(offsetof(struct rmi_islet_realm_metadata, version_major)) == 0xD8U);
COMPILER_ASSERT(U(offsetof(struct rmi_islet_realm_metadata, version_minor)) == 0xE0U);
COMPILER_ASSERT(U(offsetof(struct rmi_islet_realm_metadata, version_patch)) == 0xE8U);
COMPILER_ASSERT(U(offsetof(struct rmi_islet_realm_metadata, public_key)) == 0xF0U);
COMPILER_ASSERT(U(offsetof(struct rmi_islet_realm_metadata, signature)) == 0x150U);


bool verify_metadata_signature(struct rmi_islet_realm_metadata *realm_metadata);
bool validate_metadata_content(struct rmi_islet_realm_metadata *realm_metadata);
void copy_metadata(struct rmi_islet_realm_metadata *dst, struct rmi_islet_realm_metadata *src);
void dump_islet_realm_metadata(struct rmi_islet_realm_metadata *metadata);

#endif /* METADATA_H */
