#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_library(rmm-lib-pauth)

target_link_libraries(rmm-lib-pauth
    PRIVATE rmm-lib-common
            rmm-lib-libc
            rmm-lib-arch
            rmm-lib-debug
            rmm-lib-realm)

target_include_directories(rmm-lib-pauth
    PUBLIC "include")

target_include_directories(rmm-lib-pauth
    PRIVATE "src")

target_sources(rmm-lib-pauth
    PRIVATE "src/pauth_core.c")

if (NOT RMM_ARCH STREQUAL fake_host)
    target_sources(rmm-lib-pauth
	PRIVATE "src/aarch64/pauth_arch.S")
endif()
