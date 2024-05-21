#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

cmake_minimum_required(VERSION 3.15.0)

set(src_spdm_malloclib
    spdm_malloclib.c)

add_library(spdm_malloclib STATIC ${src_spdm_malloclib})
target_include_directories(spdm_malloclib PRIVATE
    ${LIBSPDM_DIR}/include
    ${LIBSPDM_DIR}/include/hal)
