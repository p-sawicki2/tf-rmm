/*
 * Copyright (c) 2021-2022, Arm Limited. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

#ifndef TB_LOCK_H
#define TB_LOCK_H

#include "granule.h"

#define MAX_LOCK_TRACE 10

struct lock_trace_entry {
    bool is_lock;
    bool has_parent;
    struct granule* granule_addr;
} lock_traces[MAX_LOCK_TRACE] = { 0 };

size_t next_lock_trace_entry = 0;

#define MAX_LOCK_RELATION 20

struct lock_relation_entry {
    struct granule* parent;
    struct granule* child;
} lock_relation[MAX_LOCK_RELATION];

size_t next_relation_entry = 0;

void add_lock_relation(struct granule * before, struct granule * after);

#endif /* !TB_LOCK_H */
