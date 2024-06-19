/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <CppUTest/CommandLineTestRunner.h>
#include <CppUTest/TestHarness.h>

extern "C" {
#include <cpuid.h>
#include <host_harness.h>
#include <host_utils.h>
#include <queue.h>
#include <stdlib.h>
#include <string.h>
#include <test_harness.h>
#include <test_helpers.h>
#include <unistd.h>
#include <utils_def.h>
}

TEST_GROUP(queue) {

	TEST_SETUP()
	{
		test_helpers_init();

		/* Enable the platform with support for multiple PEs */
		test_helpers_rmm_start(true);

		/* Make sure current cpu id is 0 (primary processor) */
		host_util_set_cpuid(0U);

		test_helpers_expect_assert_fail(false);
	}

	TEST_TEARDOWN()
	{

	}
};

TEST(queue, queue_init_test)
{
	struct circular_q q;
	int ret;

	ret = q_init_check(NULL);
	CHECK_EQUAL(-EINVAL, ret);

	q.buffer = (void *)0x1000;
	q.capacity = 0x1000;
	q.element_size = 0x10;
	q.length = 0;
	q.read = 0;

	ret = q_init_check(&q);
	CHECK_EQUAL(0, ret);

	q.buffer = NULL;
	ret = q_init_check(&q);
	CHECK_EQUAL(-EINVAL, ret);

	q.buffer = (void *)0x1000;
	q.capacity = 0;
	ret = q_init_check(&q);
	CHECK_EQUAL(-EINVAL, ret);

	q.capacity = 0x1000;
	q.element_size = 0;
	ret = q_init_check(&q);
	CHECK_EQUAL(-EINVAL, ret);

	q.element_size = 0x10;
	q.capacity = 0x1001;
	ret = q_init_check(&q);
	CHECK_EQUAL(-EINVAL, ret);

	q.capacity = 0x1000;
	q.element_size = 0x10;
	q.buffer = (void *)0x1000;
	ret = q_init_check(&q);
	CHECK_EQUAL(0, ret);
}

TEST(queue, queue_push_pop_check)
{
	CIRCULAR_Q_DECLARE(q, 0x1000, 0x10);
	int ret;

	unsigned long data[2] = {0x1000, 0x2000};

	ret = q_init_check(&q);
	CHECK_EQUAL(0, ret);

	ret = q_push(&q, NULL, 0);
	CHECK_EQUAL(-EINVAL, ret);

	ret = q_push(&q, data, 0);
	CHECK_EQUAL(-EINVAL, ret);

	ret = q_push(&q, data, sizeof(data));
	CHECK_EQUAL(0, ret);

	CHECK_EQUAL(q_size(&q), 1);

	ret = q_pop(&q, data, sizeof(data));
	CHECK_EQUAL(0, ret);
	CHECK_EQUAL(0x1000, data[0]);
	CHECK_EQUAL(0x2000, data[1]);

	for (unsigned long i = 0; i < 0x1000; i++) {
		ret = q_push(&q, data, sizeof(data));
		CHECK_EQUAL(0, ret);
	}

	CHECK_EQUAL(q_size(&q), 0x1000);

	ret = q_push(&q, data, sizeof(data));
	CHECK_EQUAL(-EAGAIN, ret);

	CHECK_EQUAL(q_full(&q), true);

	for (unsigned long i = 0; i < 0x1000; i++) {
		ret = q_pop(&q, data, sizeof(data));
		CHECK_EQUAL(0, ret);
		CHECK_EQUAL(0x1000, data[0]);
		CHECK_EQUAL(0x2000, data[1]);
	}

	CHECK_EQUAL(q_size(&q), 0);
	CHECK_EQUAL(q_empty(&q), true);

	ret = q_pop(&q, data, sizeof(data));
	CHECK_EQUAL(-EAGAIN, ret);

	ret = q_pop(&q, data, 0);
	CHECK_EQUAL(-EINVAL, ret);

	ret = q_pop(&q, NULL, sizeof(data));
	CHECK_EQUAL(-EINVAL, ret);

	ret = q_pop(&q, data, sizeof(data) - 1);
	CHECK_EQUAL(-EINVAL, ret);
}

TEST(queue, queue_iterator_test)
{
	CIRCULAR_Q_DECLARE(q, 0x1000, sizeof(unsigned long));
	struct circular_q_iter iter;
	int ret;
	unsigned long *ptr;

	ret = q_init_check(&q);
	CHECK_EQUAL(0, ret);

	for (unsigned long i = 0; i < 0x1000; i++) {
		ret = q_push(&q, &i, sizeof(i));
		CHECK_EQUAL(0, ret);
	}

	ret = q_init_iterator(&q, &iter);
	CHECK_EQUAL(0, ret);

	for (unsigned long i = 0; i < 0x1000; i++) {
		ptr = (unsigned long *)q_iter_get_next(&iter);
		CHECK(ptr != NULL);
		CHECK_EQUAL(i, *ptr);
	}

	ptr = (unsigned long *)q_iter_get_next(&iter);
	CHECK(ptr == NULL);
}
