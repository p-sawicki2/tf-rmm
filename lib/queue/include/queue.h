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
 * The capacity of the queue is restricted to a power of 2 and the elements
 * are stored in fixed-size slots.
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
	void *buffer;
};

struct circular_q_iter {
	struct circular_q *q;
	unsigned long index;
	unsigned long remaining;
};

/* cppcheck-suppress [misra-c2012-20.7] */
#define CIRCULAR_Q_DECLARE(name, num_elements, element_size_in) \
		static char name##_buffer[(num_elements) * (element_size_in)];     \
		static struct circular_q name = { \
			.read = 0, \
			.length = 0, \
			.capacity = (num_elements), \
			.element_size = (element_size_in), \
			.buffer = (name##_buffer) \
		}

/*
 * Initialize the circular queue. Checks for common errors in the queue
 * such as invalid capacity, element size, or buffer pointer. The function
 * returns 0 on success, and -EINVAL on failure. It also sets the initialized
 * flag to true if the checks pass.
 */
int q_init_check(struct circular_q *q);

/*
 * Push an element into the queue. The function returns 0 on success, and
 * -EINVAL on failure such as when the queue is full or when the queue is not
 * initialized. It returns -ENOMEM if the queue is full.
 * Note that the function is not thread-safe and an external lock should be
 * used to ensure thread safety. The implementation also copies the data into
 * the queue buffer as opposed to storing a reference to the data. The size
 * parameter is used to ensure that the data pointer has enough space to store
 * the element.
 */
int q_push(struct circular_q *q, void *data, unsigned long size);

/*
 * Pop an element from the queue. The function returns 0 on success, and
 * -EINVAL on failure such as when the queue is empty or when the queue is not
 * initialized. It returns -ENOMEM if the queue is empty. The function also
 * copies the data from the queue buffer into the data pointer. The size
 * parameter is used to ensure that the data pointer has enough space to store
 * the element.
 * Note that the function is not thread-safe and an external lock should be
 * used to ensure thread safety.
 */
int q_pop(struct circular_q *q, void *data, unsigned long size);

/*
 * Check if the queue is full. The function returns true if the queue is full,
 * and false otherwise. It also checks if the queue is initialized before
 * performing the check.
 */
bool q_full(struct circular_q *q);

/*
 * Check if the queue is empty. The function returns true if the queue is empty,
 * and false otherwise. It also checks if the queue is initialized before
 * performing the check.
 */
bool q_empty(struct circular_q *q);

/*
 * Get the current size of the queue. The function returns the number of
 * elements in the queue. It also checks if the queue is initialized before
 * returning the size.
 */
unsigned long q_size(struct circular_q *q);

/*
 * Initialize an iterator for the queue. The function returns 0 on success, and
 * -EINVAL on failure such as when the queue is not initialized. The iterator
 * is used to iterate over the elements in the queue without modifying the
 * queue itself.
 * Note that the function is not thread-safe and an external lock should be
 * used to ensure thread safety.
 * When the iterator is used, it is expected that all queue modifications are
 * restricted. The iterator has no way to detect if a queue it points to have
 * changed. If q_iter_get_next is called on an iterator that iterates over a
 * queue that changed after q_init_iterator was called for that iterator, the
 * behavior of q_iter_get_next is undefined.
 */
int q_init_iterator(struct circular_q *q, struct circular_q_iter *iter);

/*
 * Get the next element from the queue using the iterator. The function returns
 * a pointer to the next element in the queue. It returns NULL if there are no
 * more elements in the queue. The iterator is used to keep track of the current
 * position in the queue.
 * Note that the function is not thread-safe and an external lock should be
 * used to ensure thread safety. The iterator has no way to detect if a queue
 * it points to have changed. If q_iter_get_next is called on an iterator that
 * iterates over a queue that changed after q_init_iterator was called for that
 * iterator, the behavior of q_iter_get_next is undefined.
 */
void *q_iter_get_next(struct circular_q_iter *iter);

#endif /* BUFFER_H */
