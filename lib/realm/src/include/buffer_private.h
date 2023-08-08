/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <buffer.h>
#include <xlat_tables.h>

struct xlat_llt_info *get_cached_llt_info(void);
uintptr_t slot_to_va(enum buffer_slot slot);
