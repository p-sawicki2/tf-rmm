/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <debug.h>
#include <errno.h>
#include <mbedtls/hkdf.h>
#include <rmm_el3_ifc.h>
#include <sealing.h>

/** Authority based VHUK */
static uint8_t vhuka[32] = {
  0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa,
  0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa,
  0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa
};

/** Measurement based VHUK */
static uint8_t vhukm[32] = {
  0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33,
  0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33,
  0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33
};

static uint8_t salt[32] = {
  0xd5, 0x77, 0x5f, 0x52, 0x4a, 0xce, 0x32, 0x21, 0xce, 0x77, 0x1e, 0xd2,
  0x74, 0xbb, 0x74, 0xa4, 0x60, 0xce, 0x3f, 0xb9, 0x74, 0x9c, 0xe3, 0x7d,
  0x0a, 0xe6, 0xd2, 0xe9, 0x07, 0xf8, 0xb5, 0x4b
};


int sealing_init()
{
	int ret;
	ret = rmm_el3_ifc_get_realm_vhuk_key(vhuka, sizeof(vhuka), 0x1);
	if (ret != 0) {
		WARN("Fetching VHUKA has failed!\n");
		return -EINVAL;
	}
	ret = rmm_el3_ifc_get_realm_vhuk_key(vhukm, sizeof(vhukm), 0x2);
	if (ret != 0) {
		WARN("Fetching VHUKM has failed!\n");
		return -EINVAL;
	}
	return 0;
}

void dump_key(const char *name, const unsigned char *key, size_t size)
{
	int i;
	rmm_log("%s: ", name);
	for (i = 0; i < size; i++) {
		rmm_log("%02x", key[i]);
	}
	rmm_log("\n");
}

void dump_info(const kdf_info_t *info)
{
	int idx;
	rmm_log("KDF info\n");
	rmm_log("public_key: ");
	for (idx = 0; idx < P384_PUBLIC_KEY_SIZE; idx++) {
		rmm_log("%02x", info->public_key[idx]);
	}
	rmm_log("\n");

	rmm_log("realm_id: ");
	for (idx = 0; idx < REALM_ID_SIZE && info->realm_id[idx] != 0; idx++) {
		rmm_log("%c", info->realm_id[idx]);
	}
	rmm_log("\n");

	rmm_log("rpv: ");
	for (idx = 0; idx < RPV_SIZE; idx++) {
		rmm_log("%02x", info->rpv[idx]);
	}
	rmm_log("\n");
	rmm_log("flags: %08lx\n", info->flags);

	rmm_log("rim: ");
	for (idx = 0; idx < MAX_MEASUREMENT_SIZE; idx++) {
		rmm_log("%02x", info->rim[idx]);
	}
	rmm_log("\n");
	rmm_log("hash_algo: %02x\n", info->hash_algo);
	rmm_log("svn: %08lx\n", info->svn);
}

int derive_sealing_key(const kdf_info_t *info, int vhuk_key_type, uint8_t *key, const size_t key_size)
{
	int ret;
	uint8_t *ikm = NULL;
	size_t ikm_size;

	switch (vhuk_key_type) {
		case VHUKA:
			ikm = vhuka;
			ikm_size = sizeof(vhuka);
			break;
		case VHUKM:
			ikm = vhukm;
			ikm_size = sizeof(vhukm);
			break;
		default:
			return -EINVAL;
	}

#if LOG_LEVEL >= LOG_LEVEL_INFO
	/** TODO: remove logs when everything is ready */
	dump_info(info);
	rmm_log("ikm type: %s\n", vhuk_key_type == VHUKA ? "VHUKA" : "VHUKM");
#endif

	ret = mbedtls_hkdf(mbedtls_md_info_from_type(MBEDTLS_MD_SHA256),
			salt, sizeof(salt),
			ikm, ikm_size,
			(unsigned char*)info, sizeof(*info),
			key, key_size);

	if (ret != 0)
		return -EINVAL;

	return 0;
}
