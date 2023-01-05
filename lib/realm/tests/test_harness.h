/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef TEST_HARNESS_H
#define TEST_HARNESS_H

#include <buffer.h>

void *test_buffer_map(enum buffer_slot slot, unsigned long addr);
void test_buffer_unmap(void *buf);

#endif /* TEST_HARNESS_H */
