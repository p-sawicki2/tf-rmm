#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_library(rmm-plat-host_test)

target_link_libraries(rmm-plat-host_test
    PRIVATE rmm-lib
            CppUTest
    PUBLIC  rmm-host-common)

target_include_directories(rmm-plat-host_test
    PRIVATE "${PROJECT_BINARY_DIR}/plat/host/${RMM_HOST_VARIANT}/src"
            "../src")

target_include_directories(rmm-plat-host_test
    PUBLIC "include")

target_sources(rmm-plat-host_test
    PRIVATE "src/test_setup.cpp"
            "src/test_harness.c"
            "src/test_helpers.c")

add_library(rmm-platform ALIAS rmm-plat-host_test)
