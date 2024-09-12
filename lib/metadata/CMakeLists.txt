#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_library(rmm-lib-metadata)

target_link_libraries(rmm-lib-metadata
    PUBLIC rmm-lib-allocator
           rmm-lib-attestation
           rmm-mbedtls
           rmm-lib-measurement
           rmm-lib-smc
    PRIVATE rmm-lib-arch
            rmm-lib-common
            rmm-lib-debug)

target_include_directories(rmm-lib-metadata
    PUBLIC "include"
    PRIVATE "src")

target_sources(rmm-lib-metadata
    PRIVATE
        "src/metadata.c")
