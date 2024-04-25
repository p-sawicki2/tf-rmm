/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <debug.h>
#include <errno.h>
#include <queue.h>
#include <stdbool.h>
#include <string.h>

int q_init_check(struct circular_q *q)
{
	if (q == NULL) {
		return -EINVAL;
	}

	q->initialized = false;

	if ((q->read != 0U) || (q->length != 0U) || (q->capacity == 0U) ||
	    (q->element_size == 0U) || (q->buffer == NULL)) {
		return -EINVAL;
	}

	if ((q->capacity & (q->capacity - 1U)) != 0U) {
		return -EINVAL;
	}

	q->initialized = true;
	return 0;
}

bool q_empty(struct circular_q *q)
{
	if ((q == NULL) || (q->initialized == false)) {
		panic();
	}

	return q->length == 0U;
}

bool q_full(struct circular_q *q)
{
	if ((q == NULL) || (q->initialized == false)) {
		panic();
	}

	assert(q->length <= q->capacity);
	return (q->length == q->capacity);
}

unsigned long q_size(struct circular_q *q)
{
	if ((q == NULL) || (q->initialized == false)) {
		panic();
	}

	return q->length;
}

int q_push(struct circular_q *q, void *data, unsigned long size)
{
	unsigned long index = 0;
	char *buffer = NULL;

	if ((q == NULL) || (q->initialized == false)) {
		panic();
	}

	if ((data == NULL) || (size == 0U) || (size > q->element_size)) {
		return -EINVAL;
	}

	if (q_full(q)) {
		return -EAGAIN;
	}

	index = (q->read + q->length) & (q->capacity - 1U);
	buffer = (char *)q->buffer;
	(void)memset(&buffer[index * q->element_size], 0, q->element_size);
	(void)memcpy(&buffer[index * q->element_size], data, size);
	q->length++;

	return 0;
}

int q_pop(struct circular_q *q, void *data, unsigned long size)
{
	char *buffer = NULL;

	if ((q == NULL) || (q->initialized == false)) {
		panic();
	}

	if ((data == NULL) || (size < q->element_size)) {
		return -EINVAL;
	}

	if (q_empty(q)) {
		return -EAGAIN;
	}

	buffer = (char *)q->buffer;
	(void)memcpy(data, &buffer[q->read * q->element_size], q->element_size);
	(void)memset(&buffer[q->read * q->element_size], 0, q->element_size);
	q->read = (q->read + 1U) & (q->capacity - 1U);
	q->length--;

	return 0;
}

/* When using the iterator, it is expected all queue modifications are restricted */
int q_init_iterator(struct circular_q *q, struct circular_q_iter *iter)
{
	if ((q == NULL) || (q->initialized == false) || (iter == NULL)) {
		return -EINVAL;
	}

	iter->q = q;
	iter->index = q->read;
	iter->remaining = q->length;

	return 0;
}

void *q_iter_get_next(struct circular_q_iter *iter)
{
	char *buffer = NULL;
	void *data = NULL;

	if ((iter == NULL) || (iter->q == NULL)) {
		return NULL;
	}

	if (iter->remaining == 0U) {
		return NULL;
	}

	buffer = (char *)iter->q->buffer;
	data = &buffer[iter->index * iter->q->element_size];
	iter->index = (iter->index + 1U) & (iter->q->capacity - 1U);
	iter->remaining--;

	return data;
}
