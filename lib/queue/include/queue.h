/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef QUEUE_H
#define QUEUE_H

#include <stdbool.h>

/**
 * This circular queue implementation provides a fixed-size buffer for storing
 * elements of any type. It supports operations like push, pop, check if the
 * queue is full or empty, and get the current size of the queue.
 *
 * Note: This implementation does not provide built-in thread safety. In a
 * multi-threaded environment, external locks should be used to ensure thread
 * safety.
 *
 * Note: This implementation is not optimized for high performance scenarios.
 *
 * See CIRCULAR_Q_DECLARE macro for declaring and initializing a circular queue.
 */

struct circular_q {
	bool initialized;
	unsigned long read;
	unsigned long length;
	unsigned long capacity;
	unsigned long element_size;
	unsigned long q_size_bytes;
	void *buffer;
};

struct circular_q_iter {
	struct circular_q *q;
	unsigned long index;
	unsigned long remaining;
};

#define CIRCULAR_Q_DECLARE(name, num_elements, element_size_in) \
		static char name##_buffer[(num_elements) * (element_size_in)];     \
		static struct circular_q name = { \
			.read = 0, \
			.length = 0, \
			.capacity = (num_elements), \
			.element_size = (element_size_in), \
			.q_size_bytes = (num_elements) * (element_size_in), \
			.buffer = (name##_buffer) \
		}

int q_init_check(struct circular_q *q);
int q_push(struct circular_q *q, void *data, unsigned long size);
int q_pop(struct circular_q *q, unsigned long *data, unsigned long size);
bool q_full(struct circular_q *q);
bool q_empty(struct circular_q *q);
unsigned long q_size(struct circular_q *q);
int q_init_iterator(struct circular_q *q, struct circular_q_iter *iter);
void *q_iter_get_next(struct circular_q_iter *iter);

#endif /* BUFFER_H */
