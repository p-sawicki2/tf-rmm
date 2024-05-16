#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_library(rmm-plat-host_fuzz)

# only need one CPU
arm_config_option_override(
    NAME MAX_CPUS
    FORCE 1)

# Maximum number of granules supported,
# so that fuzzing input has a reasonable size
arm_config_option_override(
    NAME RMM_MAX_GRANULES
    DEFAULT 0x80)

# the value of HOST_MEM_SIZE must equal to
# `RMM_MAX_GRANULES` * `GRANULE_SIZE`, where the value
# of `GRANULE_SIZE` is often 4k.
arm_config_option_override(
    NAME HOST_MEM_SIZE
    DEFAULT 0x80000)

target_link_libraries(rmm-plat-host_fuzz
    PRIVATE rmm-lib
            rmm-host-common)

target_sources(rmm-plat-host_fuzz
    PRIVATE "src/host_setup.c"
            "src/host_harness.c"
            "src/host_ns_access.c")

add_library(rmm-platform ALIAS rmm-plat-host_fuzz)
