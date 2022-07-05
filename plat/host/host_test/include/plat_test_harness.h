/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef PLAT_TEST_HARNESS_H
#define PLAT_TEST_HARNESS_H

#include <buffer.h>

void *test_buffer_map(enum buffer_slot slot,
		       unsigned long addr, bool ns);

void test_buffer_unmap(void *buf);

#endif /* PLAT_TEST_HARNESS */
