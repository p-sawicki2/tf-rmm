#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_library(rmm-lib-rmm_el3_ifc)

#
# RMM_MAX_GRANULES. Maximum number of granules supported.
#
arm_config_option(
    NAME RMM_MAX_GRANULES
    HELP "Maximum number of granules supported"
    DEFAULT 0x0
    TYPE STRING)

if (RMM_MAX_GRANULES EQUAL 0x0)
    message (FATAL_ERROR "RMM_MAX_GRANULES not configured")
endif()

# Export RMM_MAX_GRANULES for use in `rmm-lib-rmm_el3_ifc` component.
target_compile_definitions(rmm-lib-rmm_el3_ifc
    PUBLIC "RMM_MAX_GRANULES=U(${RMM_MAX_GRANULES})")

target_include_directories(rmm-lib-rmm_el3_ifc
    PUBLIC "include"
    PRIVATE "src")

target_link_libraries(rmm-lib-rmm_el3_ifc
    PRIVATE
        rmm-lib-arch
        rmm-lib-common
        rmm-lib-debug
        rmm-lib-xlat
        rmm-lib-smc)

target_sources(rmm-lib-rmm_el3_ifc
    PRIVATE "src/rmm_el3_ifc.c"
            "src/rmm_el3_ifc_manifest.c"
            "src/rmm_el3_runtime.c")

if (NOT RMM_ARCH STREQUAL fake_host)
    target_sources(rmm-lib-rmm_el3_ifc
        PRIVATE "src/${RMM_ARCH}/rmm_el3_ifc_helpers.S")
endif()
