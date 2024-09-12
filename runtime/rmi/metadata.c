#include <debug.h>
#include <granule.h>
#include <realm.h>

#include <metadata.h>

static bool get_metadata(struct rmi_islet_realm_metadata *realm_metadata,
				unsigned long realm_metadata_addr)
{
	bool ns_access_ok;
	struct granule *g_realm_metadata;

	g_realm_metadata = find_granule(realm_metadata_addr);
	if (g_realm_metadata == NULL) {
		WARN("g_realm_metadata == NULL\n");
		return false;
	}

	if (g_realm_metadata->state != GRANULE_STATE_NS) {
		WARN("g_realm_metadata->state (%d) != GRANULE_STATE_NS\n", g_realm_metadata->state);
		return false;
	}

	ns_access_ok = ns_buffer_read(SLOT_NS, g_realm_metadata, 0U,
				      sizeof(*realm_metadata), realm_metadata);

	return ns_access_ok;
}

unsigned long smc_islet_realm_set_metadata(unsigned long rd_addr,
		       unsigned long mdg_addr,
		       unsigned long metadata)
{
	struct granule *g_rd, *g_metadata;
	struct rd *rd;
	struct rmi_islet_realm_metadata realm_metadata;
	struct rmi_islet_realm_metadata *meta;
	unsigned long ret = RMI_SUCCESS;

	if (!get_metadata(&realm_metadata, metadata)) {
		return RMI_ERROR_INPUT;
	}

#if LOG_LEVEL >= LOG_LEVEL_INFO
	dump_islet_realm_metadata(&realm_metadata);
#endif

	if (!verify_metadata_signature(&realm_metadata)) {
		WARN("Verification of realm metadata signature has failed\n");
		return RMI_ERROR_INPUT;
	}

	if (!validate_metadata_content(&realm_metadata)) {
		WARN("The content of realm metadata is not valid\n");
		return RMI_ERROR_INPUT;
	}

	if (!find_lock_two_granules(mdg_addr,
				    GRANULE_STATE_DELEGATED,
				    &g_metadata,
				    rd_addr,
				    GRANULE_STATE_RD,
				    &g_rd)) {
		return RMI_ERROR_INPUT;
	}

	rd = granule_map(g_rd, SLOT_RD);
	assert(rd != NULL);

	meta = granule_map(g_metadata, SLOT_METADATA);
	assert(meta != NULL);

	if (get_rd_state_locked(rd) != REALM_NEW) {
		ret = RMI_ERROR_REALM;
		goto out_err;
	}

	/** Copy and assign the metadata granule to the realm descriptor */
	copy_metadata(meta, &realm_metadata);
	rd->g_metadata = g_metadata;
	granule_set_state(g_metadata, GRANULE_STATE_METADATA);

out_err:
	buffer_unmap(meta);
	buffer_unmap(rd);

	granule_unlock(g_metadata);
	granule_unlock(g_rd);

	return ret;
}
