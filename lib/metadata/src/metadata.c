#include <debug.h>
#include <sizes.h>
#include <string.h>
#include <memory_alloc.h>

#include <metadata.h>

#include <mbedtls/ecdsa.h>
#include <mbedtls/ecp.h>
#include <mbedtls/error.h>
#include <mbedtls/hkdf.h>
#include <mbedtls/md.h>
#include <mbedtls/sha512.h>
#include <mbedtls/memory_buffer_alloc.h>

#define PRNG_INIT_HEAP_SIZE	((MAX_CPUS + 1UL) * 364UL)
#define INIT_HEAP_SIZE		(PRNG_INIT_HEAP_SIZE + SZ_4K)

static unsigned char mem_buf[INIT_HEAP_SIZE]
					__aligned(sizeof(unsigned long));

static struct buffer_alloc_ctx init_ctx;
static bool metadata_allocator_initialized = false;

bool verify_metadata_signature(struct rmi_islet_realm_metadata *realm_metadata)
{
	int ret;
	bool result = true;
	/* Public key used for verification */
	mbedtls_ecp_point Q;
	mbedtls_ecp_group grp;
	mbedtls_mpi r, s;
	/* One extra byte for Uncompressed buffer tag */
	unsigned char pubkey_buf[P384_PUBLIC_KEY_SIZE + 1];
	unsigned char hash[SHA_384_HASH_SIZE];
	const unsigned char *buffer = (const unsigned char *)realm_metadata;

	ret = buffer_alloc_ctx_assign(&init_ctx);
	if (ret != 0) {
		return ret;
	}

	if (!metadata_allocator_initialized) {
		mbedtls_memory_buffer_alloc_init(mem_buf,
								sizeof(mem_buf));
		metadata_allocator_initialized = true;
	}

	mbedtls_ecp_point_init(&Q);
	mbedtls_mpi_init(&r);
	mbedtls_mpi_init(&s);
	mbedtls_ecp_group_init(&grp);

	ret = mbedtls_ecp_group_load(&grp, MBEDTLS_ECP_DP_SECP384R1);
	if (ret != 0) {
		WARN("mbedtls_ecp_group_load failed: %s\n", mbedtls_high_level_strerr(ret));
		result = false;
		goto out_err;
	}

	memcpy(&pubkey_buf[1], realm_metadata->public_key, P384_PUBLIC_KEY_SIZE);
	pubkey_buf[0] = 0x04; /* Uncompressed buffer */

	ret = mbedtls_ecp_point_read_binary(&grp, &Q, pubkey_buf, sizeof(pubkey_buf));
	if (ret != 0) {
		WARN("Cannot read ecp_point binary data: %s\n", mbedtls_high_level_strerr(ret));
		result = false;
		goto out_err;
	}

	if ((ret = mbedtls_mpi_read_binary(&r, realm_metadata->signature, P385_SIGNATURE_POINT_SIZE)) != 0) {
		WARN("Cannot read R part of signature: %s\n", mbedtls_high_level_strerr(ret));
		result = false;
		goto out_err;
	}

	if ((ret = mbedtls_mpi_read_binary(&s, realm_metadata->signature + P385_SIGNATURE_POINT_SIZE,
			P385_SIGNATURE_POINT_SIZE)) != 0) {
		WARN("Cannot read S part of signature: %s\n",  mbedtls_high_level_strerr(ret));
		result = false;
		goto out_err;
	}

	ret = mbedtls_sha512(buffer, REALM_METADATA_HEADER_SIZE, hash, 1 /*SHA-384*/);
	if (ret != 0) {
		WARN("mbedtls_sha512 failed: %s\n",  mbedtls_high_level_strerr(ret));
		result = false;
		goto out_err;
	}

	if ((ret = mbedtls_ecdsa_verify(&grp, hash, SHA_384_HASH_SIZE, &Q, &r, &s)) != 0) {
		WARN("Signature verification error: %s\n",  mbedtls_high_level_strerr(ret));
		result = false;
	}

out_err:
	mbedtls_mpi_free(&s);
	mbedtls_mpi_free(&r);
	mbedtls_ecp_point_free(&Q);

	buffer_alloc_ctx_unassign();

	return result;
}

static bool is_printable_ascii(char c)
{
	return c >= ' ' && c <= '~';
}

bool validate_metadata_content(struct rmi_islet_realm_metadata *realm_metadata)
{
	int i;
	bool is_realm_id_valid = true;

	if (realm_metadata->fmt_version != FMT_VERSION) {
		WARN("Metadata format version %lu is not supported!\n", realm_metadata->fmt_version);
		return false;
	}

	if (realm_metadata->svn == 0) {
		WARN("SVN number should be greater than zero\n");
		return false;
	}

	if (realm_metadata->hash_algo != METADATA_HASH_SHA_256 && realm_metadata->hash_algo != METADATA_HASH_SHA_512) {
		WARN("Hash algorithm is invalid %lu\n", realm_metadata->hash_algo);
		return false;
	}

	/** Check the realm id format */
	for (i = 0; i < REALM_ID_SIZE && realm_metadata->realm_id[i] != '\0'; i++) {
		if (!is_printable_ascii(realm_metadata->realm_id[i])) {
			is_realm_id_valid = false;
			break;
		}
	}
	if (!is_realm_id_valid || i == 0) {
		WARN("Realm id is invalid\n");
		return false;
	}

	return true;
}

void copy_metadata(struct rmi_islet_realm_metadata *dst, struct rmi_islet_realm_metadata *src)
{
	memcpy(dst, src, REALM_METADATA_SIGNED_SIZE);
}

void dump_islet_realm_metadata(struct rmi_islet_realm_metadata *metadata)
{
	int idx;

	rmm_log("fmt_version:\t\t0x%08lx\n", metadata->fmt_version);

	rmm_log("realm_id:\t\t");
	for (idx = 0; idx < REALM_ID_SIZE && metadata->realm_id[idx] != 0; idx++)
		rmm_log("%c", metadata->realm_id[idx]);
	rmm_log("\n");

	rmm_log("rim:\t\t");
	for (idx = 0; idx < MAX_MEASUREMENT_SIZE; idx++)
		rmm_log("%02X", metadata->rim[idx]);
	rmm_log("\n");

	rmm_log("hash_algo = 0x%08lx\n", metadata->hash_algo);
	rmm_log("svn = 0x%08lx\n", metadata->svn);
	rmm_log("version_major = 0x%08lx\n", metadata->version_major);
	rmm_log("version_minor = 0x%08lx\n", metadata->version_minor);
	rmm_log("version_patch = 0x%08lx\n", metadata->version_patch);

	rmm_log("public_key:\t\t");
	for (idx = 0; idx < P384_PUBLIC_KEY_SIZE; idx++)
		rmm_log("%02X", metadata->public_key[idx]);
	rmm_log("\n");

	rmm_log("signature:\t\t");
	for (idx = 0; idx < P384_SIGNATURE_SIZE; idx++)
		rmm_log("%02X", metadata->signature[idx]);
	rmm_log("\n");
}
