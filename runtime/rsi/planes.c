/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <buffer.h>
#include <gic.h>
#include <granule.h>
#include <planes.h>
#include <realm.h>
#include <rec.h>
#include <rsi-handler.h>
#include <run.h>
#include <smc-rsi.h>
#include <utils_def.h>

static void copy_gicstate_from_plane_entry(struct gic_cpu_state *gicstate,
					   struct rsi_plane_enter *entry)
{
	/* TODO: need to do some sanitisation here */
	gicstate->ich_hcr_el2 = entry->gicv3_hcr;

	for (int i = 0; i < RSI_PLANE_GIC_NUM_LRS; i++) {
		gicstate->ich_lr_el2[i] = entry->gicv3_lrs[i];
	}
}

static void copy_state_from_plane_entry(struct rec_plane *plane,
					struct rsi_plane_enter *entry)
{
	for (int i = 0; i < RSI_PLANE_NR_GPRS; i++) {
		plane->regs[i] = entry->gprs[i];
	}

	plane->pc = entry->pc;
	copy_gicstate_from_plane_entry(&plane->sysregs.gicstate, entry);
}

void handle_rsi_plane_enter(struct rec *rec, struct rsi_result *res)
{
	struct rec_plane *primary_plane = rec_active_plane(rec);
	struct rec_plane *secondary_plane;
	unsigned long plane_idx = primary_plane->regs[1U];
	unsigned long run_ipa = primary_plane->regs[2U];
	enum s2_walk_status walk_status;
	struct s2_walk_result walk_res;
	struct granule *gr;
	struct rsi_plane_run *run;

	res->action = UPDATE_REC_RETURN_TO_REALM;

	/* This command can only be executed from Plane 0 */
	assert(rec->active_plane_id == PRIMARY_PLANE_ID);

	if (plane_idx == PRIMARY_PLANE_ID ||
				plane_idx > rec->realm_info.num_aux_planes) {
		res->smc_res.x[0U] = RSI_ERROR_INPUT;
		return;
	}

	walk_status = realm_ipa_to_pa(rec, run_ipa, &walk_res);

	if (walk_status == WALK_INVALID_PARAMS) {
		res->smc_res.x[0] = RSI_ERROR_INPUT;
		return;
	}

	if (walk_status == WALK_FAIL) {
		if (walk_res.ripas_val == RIPAS_EMPTY) {
			res->smc_res.x[0] = RSI_ERROR_INPUT;
		} else {
			res->action = STAGE_2_TRANSLATION_FAULT;
			res->rtt_level = walk_res.rtt_level;
		}
		return;
	}

	/* Save Primary plane state to REC */
	save_realm_state(primary_plane);

	/* Map Realm data granule to RMM address space */
	gr = find_granule(walk_res.pa);
	assert(gr != NULL);

	run = (struct rsi_plane_run *)buffer_granule_map(gr, SLOT_RSI_CALL);

	/* Copy target Plane state from entry structure to REC */
	secondary_plane = rec_plane_by_idx(rec, plane_idx);
	copy_state_from_plane_entry(secondary_plane, &run->enter);

	/* Initialize trap control bits */
	secondary_plane->sysregs.hcr_el2 = rec->common_sysregs.hcr_el2;

	if ((run->enter.flags & RSI_PLANE_ENTRY_FLAG_TRAP_WFI) != RSI_NO_TRAP) {
		secondary_plane->sysregs.hcr_el2 |= HCR_TWI;
	}

	if ((run->enter.flags & RSI_PLANE_ENTRY_FLAG_TRAP_WFE) != RSI_NO_TRAP) {
		secondary_plane->sysregs.hcr_el2 |= HCR_TWE;
	}

	secondary_plane->trap_hc =
		((run->enter.flags & RSI_PLANE_ENTRY_FLAG_TRAP_HC) != RSI_NO_TRAP);

	/* Restore target Plane from REC */
	restore_realm_state(rec, secondary_plane);

	/* Change active Plane */
	rec->active_plane_id = plane_idx;
	res->action = PLANE_CHANGED_RETURN_TO_REALM;

	/* Unmap Realm data granule */
	buffer_unmap(run);

	/* Unlock last level RTT */
	granule_unlock(walk_res.llt);
}
