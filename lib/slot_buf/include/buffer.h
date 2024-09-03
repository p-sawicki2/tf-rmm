/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef BUFFER_H
#define BUFFER_H

#include <granule.h>
#include <smc-rmi.h>
#include <stddef.h>
#include <utils_def.h>

enum buffer_slot {
	/*
	 * NS.
	 */
	SLOT_NS,

	/*
	 * RMM-private.
	 */
	SLOT_DELEGATED,
	SLOT_RD,
	SLOT_REC,
	SLOT_REC2,		/* Some commands access two REC granules at a time*/
	SLOT_REC_TARGET,	/* Target REC for interrupts */
	SLOT_REC_AUX0,		/* Reserve slots for max rec auxiliary granules
				 * so that all of them can be mapped at once.
				 * If the max aux granules is 0, no slots will
				 * be reserved.
				 */
	SLOT_RTT = U(SLOT_REC_AUX0) + MAX_REC_AUX_GRANULES,
	SLOT_RTT2,		/* Some commands access two RTT granules at a time*/
	SLOT_RSI_CALL,
	SLOT_EL3_SIGN_REC,	/* Slot for target REC during EL3 sign flow */
	SLOT_EL3_SIGN_AUX0,	/* Slots for AUX granules on target REC during EL3 sign flow */
	NR_CPU_SLOTS = U(SLOT_EL3_SIGN_AUX0) + MAX_REC_AUX_GRANULES
};

bool check_cpu_slots_empty(void);
void *buffer_granule_map(struct granule *g, enum buffer_slot slot);
void buffer_unmap(void *buf);

bool ns_buffer_read(enum buffer_slot slot,
		    struct granule *ns_gr,
		    unsigned int offset,
		    size_t size,
		    void *dest);

bool ns_buffer_write(enum buffer_slot slot,
		     struct granule *ns_gr,
		     unsigned int offset,
		     size_t size,
		     void *src);

/*
 * Finishes initializing the slot buffer mechanism.
 * This function should be called after the MMU is enabled, during the
 * warmboot path.
 */
void slot_buf_finish_warmboot_init(void);

/*
 * Maps the `num_aux` SLOT_REC_AUX granules.
 */
void *buffer_aux_granules_map(struct granule *g_rec_aux[], unsigned int num_aux);

/*
 * Maps the `num_aux` SLOT_EL3_SIGN_AUX0 granules.
 */
void *buffer_aux_granules_map_el3_sign_slot(struct granule *g_rec_aux[],
						   unsigned int num_aux);

/*
 * Unmaps the `num_aux` SLOT_REC_AUX or SLOT_EL3_SIGN_AUX0 buffers starting
 * with the one passed at the beginning of `rec_aux`.
 */
void buffer_aux_unmap(void *rec_aux, unsigned int num_aux);

/*
 * Map the granule 'g' to 'slot', zeroes its content and unmaps it.
 */
void buffer_granule_memzero(struct granule *g, enum buffer_slot slot);

/******************************************************************************
 * Internal APIs not meant to be invoked by generic RMM code.
 * These are exposed to facilitate testing.
 *****************************************************************************/

/*
 * Maps a given PA into the specified slot.
 *
 * On success, it returns the VA of the slot where the PA has been mapped to.
 * Otherwise, it will return NULL.
 */
void *buffer_map_internal(enum buffer_slot slot, unsigned long addr);

/*
 * Unmaps the slot buffer corresponding to the VA passed via `buf` argument.
 */
void buffer_unmap_internal(void *buf);

#endif /* BUFFER_H */
