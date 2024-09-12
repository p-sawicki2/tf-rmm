/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <debug.h>
#include <granule.h>
#include <metadata.h>
#include <realm.h>
#include <rsi-handler.h>
#include <sealing.h>

void handle_rsi_islet_realm_sealing_key(struct rec *rec, struct rsi_result *res)
{
	int ret;
	struct rd *rd;
	struct rmi_islet_realm_metadata *metadata = NULL;
	union {
		unsigned char key[SEALING_KEY_SIZE];
		struct {
			uint64_t k0;
			uint64_t k1;
			uint64_t k2;
			uint64_t k3;
		} dw;
	} slk;
	kdf_info_t info;

	unsigned long flags = rec->regs[1];
	unsigned long svn = rec->regs[2];

	granule_lock(rec->realm_info.g_rd, GRANULE_STATE_RD);
	rd = granule_map(rec->realm_info.g_rd, SLOT_RD);
	assert(rd != NULL);

#if LOG_LEVEL >= LOG_LEVEL_INFO
	rmm_log("flags: %08lx, svn: %08lx\n", flags, svn);
#endif

	/** Populate the key material */
	memset(&info, 0, sizeof(info));
	memcpy(info.rpv, rd->rpv, sizeof(info.rpv));
	info.flags = flags;

	if (rd->g_metadata != NULL) {
		granule_lock(rd->g_metadata, GRANULE_STATE_METADATA);

		metadata = granule_map(rd->g_metadata, SLOT_METADATA);
		assert(metadata != NULL);

		if ((flags & RSI_ISLET_SLK_SVN) && metadata->svn < svn) {
			WARN("The SVN parameter is invalid!\n");

			buffer_unmap(metadata);
			granule_unlock(rd->g_metadata);
			buffer_unmap(rd);
			granule_unlock(rec->realm_info.g_rd);

			res->action = UPDATE_REC_RETURN_TO_REALM;
			res->smc_res.x[0] = RSI_ERROR_INPUT;
			return;
		}

		memcpy(info.public_key, metadata->public_key, sizeof(info.public_key));

		if (flags & RSI_ISLET_SLK_REALM_ID)
			memcpy(info.realm_id, metadata->realm_id, sizeof(info.realm_id));

		if (flags & RSI_ISLET_SLK_SVN)
			info.svn = svn;

		buffer_unmap(metadata);
		granule_unlock(rd->g_metadata);
	}

	/**
	 *  We allow realms not having a metadata block assigned
	 *  to derive sealing keys. In that case, the RIM of the realm
	 *  is always used as the key material.
	 */
	if ((flags & RSI_ISLET_SLK_RIM) || rd->g_metadata == NULL) {
		memcpy(info.rim, rd->measurement[RIM_MEASUREMENT_SLOT], sizeof(info.rim));
		info.hash_algo = (uint8_t)rd->algorithm;
	}

	buffer_unmap(rd);
	granule_unlock(rec->realm_info.g_rd);

	ret = derive_sealing_key(&info,
		(flags & RSI_ISLET_USE_IKM_VHUK_M) ? VHUKM : VHUKA,
		slk.key, sizeof(slk.key));

	/** Clear the input key material */
	memset(&info, 0, sizeof(info));

	if (ret != 0) {
		res->action = UPDATE_REC_RETURN_TO_REALM;
		res->smc_res.x[0] = RSI_ERROR_INPUT;
		return;
	}

	res->action = UPDATE_REC_RETURN_TO_REALM;
	res->smc_res.x[0] = RSI_SUCCESS;

	res->smc_res.x[1] = slk.dw.k0;
	res->smc_res.x[2] = slk.dw.k1;
	res->smc_res.x[3] = slk.dw.k2;
	res->smc_res.x[4] = slk.dw.k3;

	/** Clear the sealing key */
	(void)memset(slk.key, 0, sizeof(slk.key));
}
