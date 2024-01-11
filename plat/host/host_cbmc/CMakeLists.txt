#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_library(rmm-plat-host_cbmc)

arm_config_option(
    NAME RMM_CBMC_STATIC_ANALYSIS
    HELP "Enable CBMC static analysis."
    DEFAULT TRUE FORCE)

target_link_libraries(rmm-plat-host_cbmc
    PRIVATE rmm-lib
    PUBLIC rmm-host-common)

target_sources(rmm-plat-host_cbmc
    PRIVATE
        "src/host_harness.c"
        "src/tb_arch_features.c"
        "src/tb_attest.c"
        "src/tb_common.c"
        "src/tb_granules.c"
        "src/tb_measurement.c"
        "src/tb_ns_access.c"
        "src/tb_other.c"
        "src/tb_realm.c"
        "src/tb_rec.c"
        "src/tb_rim.c"
        "src/tb_rsi.c"
        "src/tb_rtt.c"
        "src/tb_simd.c"
        "src/tb_xlat.c"
        "src/tb.c"
        )

target_include_directories(rmm-plat-host_cbmc
    PUBLIC "include")

add_library(rmm-platform ALIAS rmm-plat-host_cbmc)
