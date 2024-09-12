#ifndef SEALING_H
#define SEALING_H

#include <stdint.h>
#include <measurement.h>
#include <metadata.h>
#include <smc-rsi.h>
#include <smc-rmi.h>

#define RSI_ISLET_USE_IKM_VHUK_M			(1U << 0)
#define RSI_ISLET_SLK_RIM			(1U << 1)
#define RSI_ISLET_SLK_REALM_ID			(1U << 2)
#define RSI_ISLET_SLK_SVN			(1U << 2)

#define SEALING_KEY_SIZE	U(32)
#define VHUKA 0x1
#define VHUKM 0x2

typedef struct  __attribute__((packed)) kdf_info {
	uint8_t public_key[P384_PUBLIC_KEY_SIZE];
	uint8_t realm_id[REALM_ID_SIZE];
	uint8_t rpv[RPV_SIZE];
	uint64_t flags;
	uint8_t rim[MAX_MEASUREMENT_SIZE];
	uint8_t hash_algo;
	uint64_t svn;
} kdf_info_t;

int sealing_init();
void dump_key(const char *name, const unsigned char *key, size_t size);
void dump_info(const kdf_info_t *info);
int derive_sealing_key(const kdf_info_t *info, int vhuk_key_type, uint8_t *key, const size_t key_size);

#endif /* SEALING_H */
