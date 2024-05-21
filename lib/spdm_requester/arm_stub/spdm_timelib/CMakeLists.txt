#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

cmake_minimum_required(VERSION 3.15.0)

set(src_spdm_timelib
    spdm_time.c)

add_library(spdm_timelib STATIC ${src_spdm_timelib})
target_include_directories(spdm_timelib PRIVATE
    ${LIBSPDM_DIR}/include
    ${LIBSPDM_DIR}/include/hal)
