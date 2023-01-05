/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef REALM_TEST_UTILS_H
#define REALM_TEST_UTILS_H

#include <buffer.h>

uintptr_t realm_test_util_get_slot_va_from_pa(uintptr_t pa, bool *ns);

#endif /* REALM_TEST_UTILS_H */
