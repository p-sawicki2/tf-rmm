/*
 * Copyright (c) 2021-2022, Arm Limited. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

#ifndef TB_LOCK_H
#define TB_LOCK_H

#include "granule.h"

struct lock_trace_entry {
    bool is_lock;
    bool has_parent;
    struct granule* granule_addr;
};

#define MAX_LOCK_TRACE 10

struct lock_trace_entry lock_traces[MAX_LOCK_TRACE] = { 0 };
size_t next_lock_trace_entry = 0;

#define MAX_LOCK_RELATION 20

struct granule* lock_parents_granules[MAX_LOCK_RELATION] = { 0 };
struct granule* lock_children_granules[MAX_LOCK_RELATION] = { 0 };
size_t next_relation_entry = 0;

void add_lock_relation(struct granule * before, struct granule * after);

#endif /* !TB_LOCK_H */
