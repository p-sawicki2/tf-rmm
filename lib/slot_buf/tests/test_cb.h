/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef TEST_CB_H
#define TEST_CB_H

/*
 * Test specific host_harness functions which are dynamically
 * overridden during test execution.
 */

void *test_cb_buffer_map_access(unsigned int slot, unsigned long addr);
void test_cb_buffer_unmap_access(void *buf);

void *test_cb_buffer_map_aarch64_vmsa(unsigned int slot, unsigned long addr);
void test_cb_buffer_unmap_aarch64_vmsa(void *buf);

#endif /* TEST_HARNESS_H */
