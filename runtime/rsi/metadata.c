#include <granule.h>
#include <metadata.h>
#include <realm.h>
#include <rsi-handler.h>
#include <smc-rsi.h>

void handle_rsi_islet_realm_metadata(struct rec *rec, struct rsi_result *res)
{
	unsigned long ipa = rec->regs[1];
	enum s2_walk_status walk_status;
	struct s2_walk_result walk_res;
	struct granule *gr;
	struct rmi_islet_realm_metadata *dst_metadata;
	struct rmi_islet_realm_metadata *src_metadata;
	struct rd *rd;

	res->action = UPDATE_REC_RETURN_TO_REALM;

	if (!GRANULE_ALIGNED(ipa) || !addr_in_rec_par(rec, ipa)) {
		res->smc_res.x[0] = RSI_ERROR_INPUT;
		return;
	}

	walk_status = realm_ipa_to_pa(rec, ipa, &walk_res);

	if (walk_status == WALK_FAIL) {
		if (walk_res.ripas_val == RIPAS_EMPTY) {
			res->smc_res.x[0] = RSI_ERROR_INPUT;
		} else {
			res->action = STAGE_2_TRANSLATION_FAULT;
			res->rtt_level = walk_res.rtt_level;
		}
		return;
	}

	if (walk_status == WALK_INVALID_PARAMS) {
		res->smc_res.x[0] = RSI_ERROR_INPUT;
		return;
	}

	/* Map the Realm granule pointed by the ipa */
	gr = find_granule(walk_res.pa);
	dst_metadata = (struct rmi_islet_realm_metadata *)granule_map(gr, SLOT_RSI_CALL);
	assert(dst_metadata != NULL);

	/** Lock and map RD granule */
	granule_lock(rec->realm_info.g_rd, GRANULE_STATE_RD);
	rd = granule_map(rec->realm_info.g_rd, SLOT_RD);
	assert(rd != NULL);

	/** Lock and map RD's metadata granule */
	granule_lock(rd->g_metadata, GRANULE_STATE_METADATA);
	src_metadata = granule_map(rd->g_metadata, SLOT_METADATA);
	assert(src_metadata != NULL);

	/** Copy content of the metadata granule */
	memcpy(dst_metadata, src_metadata, sizeof(*dst_metadata));

	/** Unmap and unlock RD's metadata granule */
	buffer_unmap(src_metadata);
	granule_unlock(rd->g_metadata);

	/** Unmap and unlock the RD granule */
	buffer_unmap(rd);
	granule_unlock(rec->realm_info.g_rd);

	/* Unmap Realm data granule */
	buffer_unmap(dst_metadata);

	/* Unlock last level RTT */
	granule_unlock(walk_res.llt);

	/* Write output values */
	res->smc_res.x[0] = RSI_SUCCESS;
}
