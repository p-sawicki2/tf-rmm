#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_library(rmm-plat-host_build)

#
# Maximum number of granules supported, enough to cover 2GB of DDR0.
#
arm_config_option_override(NAME RMM_MAX_GRANULES DEFAULT 0x80000)

target_link_libraries(rmm-plat-host_build
    PRIVATE rmm-lib
            rmm-host-common)

target_sources(rmm-plat-host_build
    PRIVATE "src/host_setup.c"
            "src/host_harness.c")

add_library(rmm-platform ALIAS rmm-plat-host_build)
