/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef PLAT_PRIVATE_H
#define PLAT_PRIVATE_H

/**
 * FVP Platform Private Header
*/

/* Default number of CPUs per cluster */
#define PLAT_MAX_CPUS_PER_CLUSTER	4

/* Default number of threads per CPU */
#define PLAT_MAX_PE_PER_CPU			1

/* PL011 UART */
#define PLAT_UART_BAUDRATE			115200
#define PLAT_UART_CLK_IN_HZ			14745600

#endif /* PLAT_PRIVATE_H */
