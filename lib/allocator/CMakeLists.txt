#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_library(rmm-lib-allocator)

target_link_libraries(rmm-lib-allocator
  PRIVATE
    rmm-lib-arch
    rmm-lib-common
    rmm-lib-debug
    rmm-lib-libc
    rmm-lib-rmm_el3_ifc
    rmm-mbedtls)

set(MBEDTLS_SRC_DIR "${RMM_SOURCE_DIR}/ext/mbedtls")

target_include_directories(rmm-lib-allocator
    PUBLIC "include"
    "${RMM_SOURCE_DIR}/configs/mbedtls"
    "${MBEDTLS_SRC_DIR}/include")

target_sources(rmm-lib-allocator
    PRIVATE "src/memory_alloc.c")
