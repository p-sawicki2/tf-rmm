#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_library(rmm-plat-host_build)

target_link_libraries(rmm-plat-host_build
    PRIVATE rmm-lib
            rmm-host-common)

target_sources(rmm-plat-host_build
    PRIVATE "src/host_setup.c"
            "src/host_harness.c")

add_library(rmm-platform ALIAS rmm-plat-host_build)

add_custom_target(run-host-executable
    WORKING_DIRECTORY "${CMAKE_BINARY_DIR}"
    COMMAND ${CMAKE_BINARY_DIR}/$<CONFIG>/rmm.elf
)
add_dependencies(run-host-executable generate_rmm_elf)
