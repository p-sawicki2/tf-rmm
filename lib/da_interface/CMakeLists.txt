#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_library(rmm-lib-da_interface)

message("RMM_SOURCE_DIR: ${RMM_SOURCE_DIR}")
target_include_directories(rmm-lib-da_interface
    PUBLIC "include"
           "${RMM_SOURCE_DIR}/lib/common/include"
           "${RMM_SOURCE_DIR}/lib/smc/include"
           "${RMM_SOURCE_DIR}/lib/debug/include")

target_sources(rmm-lib-da_interface
    PRIVATE "src/da_interface.c")
