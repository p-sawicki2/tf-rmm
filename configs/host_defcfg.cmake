#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

#
# Set the RMM_PLATFORM variable to Cmake cache.
#
set(RMM_PLATFORM "host" CACHE STRING "platform")

arm_config_option_override(NAME RMM_ARCH DEFAULT "fake_host")
arm_config_option_override(NAME RMM_TOOLCHAIN DEFAULT "gnu")

#
# Options specific to the test variant
#
arm_config_option(
    NAME COVERAGE_ENABLED
    HELP "Enable coverage tests"
    TYPE BOOL
    DEFAULT "OFF"
    DEPENDS (HOST_VARIANT STREQUAL host_test)
    ADVANCED)

arm_config_option(
    NAME HTML_COVERAGE_REPORT
    HELP "Enable html coverage report"
    TYPE BOOL
    DEFAULT "OFF"
    DEPENDS (HOST_VARIANT STREQUAL host_test)
    ADVANCED)

arm_config_option(
    NAME COVERAGE_REPORT_NAME
    HELP "Canonical name for the coverage report"
    TYPE STRING
    DEFAULT "tf-rmm_coverage"
    DEPENDS (HOST_VARIANT STREQUAL host_test)
    ADVANCED)

#
# Width of the virtual address space for the system.
#
arm_config_option_override(NAME VIRT_ADDR_SPACE_WIDTH DEFAULT 38)

#
# Set RMM_MAX_SIZE for this platform.
#
arm_config_option_override(NAME RMM_MAX_SIZE DEFAULT 0x01000000)

#
# Maximum number of translation tables allocated by the runtime context
# for the translation library.
#
arm_config_option_override(NAME PLAT_CMN_CTX_MAX_XLAT_TABLES DEFAULT 6)

#
# Maximum number of granules supported, enough to cover 2GB of DDR0.
#
arm_config_option_override(NAME RMM_MAX_GRANULES DEFAULT 0x80000)
