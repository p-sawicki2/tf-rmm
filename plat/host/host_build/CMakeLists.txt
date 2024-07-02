#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_library(rmm-plat-host_build)

target_link_libraries(rmm-plat-host_build
    PRIVATE rmm-lib
            rmm-host-common)

target_include_directories(rmm-plat-host_build
    PRIVATE "src")

target_sources(rmm-plat-host_build
    PRIVATE "src/host_setup.c"
            "src/host_harness.c"
            "src/host_da.c"
            "src/host_spdm_rsp_ifc.c"
            "src/host_da_crypto_utils.c")

target_link_libraries(rmm-plat-host_build
    PUBLIC
        rmm-mbedtls)

 add_library(rmm-platform ALIAS rmm-plat-host_build)
