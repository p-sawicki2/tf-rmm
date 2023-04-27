/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef RUN_H
#define RUN_H

struct granule;
struct rec_aux_data;

void init_rec_aux_data(struct rec_aux_data *aux_data, void *rec_aux,
		       unsigned long num_aux);
void *map_rec_aux(struct granule *rec_aux_pages[], unsigned long num_aux);
void unmap_rec_aux(void *rec_aux, unsigned long num_aux);

/*
 * Function to enter Realm with `regs` pointing to GP Regs to be
 * restored/saved when entering/exiting the Realm. This function
 * returns with the Realm exception code which is populated by
 * Realm_exit() on aarch64.
 */
int run_realm(unsigned long *regs);

#endif /* RUN_H */
