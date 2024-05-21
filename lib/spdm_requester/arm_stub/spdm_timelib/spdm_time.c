/*
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <base.h>

/*
 * Suspends the execution of the current SPDM request called through RMI/RSI
 * call until the time-out interval elapses.
 *
 * microseconds -  The time interval for which execution is to be suspended, in
 *                 microseconds.
 */
void libspdm_sleep(uint64_t microseconds)
{
	/*
	 * libspdm_sleep() is called from device IO communication path, when
	 * the device returns LIBSPDM_STATUS_BUSY_PEER. RMM needs to handle
	 * such libspdm_sleep by exit to NS host with RmiIoExit.timeout set?
	 * todo: For now define this function. Look at it when DA stack is run
	 * on aarch64 platform.
	 */
}
