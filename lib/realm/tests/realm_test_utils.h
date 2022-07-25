/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef REALM_TEST_UTILS_H
#define REALM_TEST_UTILS_H

#include <buffer.h>

uintptr_t slot_to_expected_va(enum buffer_slot slot);
uintptr_t slot_to_arch_pa(enum buffer_slot slot, bool *ns);
uintptr_t host_pa_to_slot_va(uintptr_t pa, bool *ns);
int get_rand_in_range(int min, int max);

#endif /* REALM_TEST_UTILS_H */
