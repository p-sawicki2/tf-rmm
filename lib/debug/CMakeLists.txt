#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_library(rmm-lib-debug INTERFACE)

if(${CMAKE_BUILD_TYPE} STREQUAL "Release")
    arm_config_option(
        NAME LOG_LEVEL
        HELP "Log level to apply for RMM (0 - 50)"
        TYPE STRING
        DEFAULT 20)
else()
    arm_config_option(
        NAME LOG_LEVEL
        HELP "Log level to apply for RMM (0 - 50)"
        TYPE STRING
        DEFAULT 40)
endif()

target_compile_definitions(rmm-lib-debug
    INTERFACE "LOG_LEVEL=${LOG_LEVEL}")

target_include_directories(rmm-lib-debug
    INTERFACE "include")
