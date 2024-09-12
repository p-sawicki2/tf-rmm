#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_library(rmm-lib-sealing)

target_link_libraries(rmm-lib-sealing
    PUBLIC rmm-lib-metadata
            rmm-lib-measurement
    PRIVATE rmm-mbedtls
            rmm-lib-smc
            rmm-lib-rmm_el3_ifc
            rmm-lib-arch
            rmm-lib-common
            rmm-lib-debug)

target_include_directories(rmm-lib-sealing
    PUBLIC "include"
    PRIVATE "src")

target_sources(rmm-lib-sealing
    PRIVATE
        "src/sealing.c")
