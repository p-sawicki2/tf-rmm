#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_library(rmm-lib-pauth)

target_link_libraries(rmm-lib-pauth
    PRIVATE rmm-lib-common
            rmm-lib-libc
            rmm-lib-arch
            rmm-lib-debug)

target_include_directories(rmm-lib-pauth
    PUBLIC "include"
    PRIVATE "src"
    PRIVATE "src/${RMM_ARCH}")

target_sources(rmm-lib-pauth
    PRIVATE "src/aarch64/pauth_core.c")
