/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef REALM_TEST_UTILS_H
#define REALM_TEST_UTILS_H

#include <buffer.h>

uintptr_t test_util_slot_to_expected_va(enum buffer_slot slot);
uintptr_t test_util_slot_to_pa(enum buffer_slot slot, bool *ns);
uintptr_t test_util_get_slot_va_from_pa(uintptr_t pa, bool *ns);
int test_util_get_rand_in_range(int min, int max);

#endif /* REALM_TEST_UTILS_H */
