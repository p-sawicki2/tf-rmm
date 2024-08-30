#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

if(NOT RMM_ARCH STREQUAL fake_host)
    add_library(rmm-lib-libc)

    target_link_libraries(rmm-lib-libc
    PUBLIC rmm-lib-arch
           rmm-lib-common
           rmm-lib-debug)

    target_include_directories(rmm-lib-libc SYSTEM
        PUBLIC "include"
               "include/${RMM_ARCH}"
        # The CMAKE_INCLUDE_PATH is included here for Yocto builds.  the
        # Yocto recipe will define this variable as part of the build.
        ${CMAKE_INCLUDE_PATH})

    target_sources(rmm-lib-libc
        PRIVATE "src/abort.c"
            "src/assert.c"
            "src/memcmp.c"
            "src/memcpy.c"
            "src/memmove.c"
            "src/printf.c"
            "src/strlen.c"
            "src/strcmp.c"
            "src/strlcpy.c"
            "src/strncmp.c"
            "src/strnlen.c"
            "src/strchr.c")

    target_sources(rmm-lib-libc
        PRIVATE
           "src/aarch64/memset.S"
           "src/aarch64/context_helpers.c"
           "src/aarch64/context.S")

target_compile_definitions(rmm-lib-libc
    PRIVATE "PRINTF_DISABLE_SUPPORT_FLOAT")
else()
    add_library(rmm-lib-libc INTERFACE)
    target_include_directories(rmm-lib-libc INTERFACE
        "include/${RMM_ARCH}")
endif()
