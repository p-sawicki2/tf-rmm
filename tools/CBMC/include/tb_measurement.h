/*
 * Copyright (c) 2021-2022, Arm Limited. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

#ifndef TB_MEASUREMENT_H
#define TB_MEASUREMENT_H

#include "measurement.h"

enum hash_algo nondet_hash_algo(void);

bool valid_hash_algo(enum hash_algo value);
enum hash_algo init_hash_algo(void);

#endif /* !TB_MEASUREMENT_H */
