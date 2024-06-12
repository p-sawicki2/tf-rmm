#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_library(rmm-driver-pcie_tdi)

set(LIBSPDM_SRC_DIR "${RMM_SOURCE_DIR}/ext/libspdm")
set(LIBSPDM_CONFIG "LIBSPDM_CONFIG=<rmm_libspdm_config.h>")

target_include_directories(rmm-driver-pcie_tdi
    PUBLIC  "include"
            "${RMM_SOURCE_DIR}/lib/common/include"
            "${RMM_SOURCE_DIR}/lib/debug/include"
            "${RMM_SOURCE_DIR}/configs/libspdm"
            "${LIBSPDM_SRC_DIR}/include"
    PRIVATE "src/include")

# todo: link with rmm-lib?
target_link_libraries(rmm-driver-pcie_tdi
    PRIVATE rmm-lib)

target_compile_definitions(rmm-driver-pcie_tdi
    PRIVATE ${LIBSPDM_CONFIG})

target_sources(rmm-driver-pcie_tdi
    PRIVATE "src/cma_spdm.c")
