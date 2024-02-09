#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

#
# Set the RMM_PLATFORM variable to Cmake cache.
#
set(RMM_PLATFORM "rdfremont" CACHE STRING "platform")

arm_config_option_override(NAME RMM_TOOLCHAIN DEFAULT "gnu")

#
# Width of the virtual address space for the system.
#
arm_config_option_override(NAME VIRT_ADDR_SPACE_WIDTH DEFAULT 48)

#
# Set RMM_MAX_SIZE for this platform (36 MB)
#
arm_config_option_override(NAME RMM_MAX_SIZE DEFAULT 0x02400000)

#
# UART Base address. This must be dynamically discovered in future.
# Use UART3 on the FVP for RMM.
#
arm_config_option_override(NAME RMM_UART_ADDR DEFAULT 0x002A420000)

#
# Extra memory regions needed by this platform
#
arm_config_option_override(NAME PLAT_CMN_EXTRA_MMAP_REGIONS DEFAULT 1)

#
# Maximum number of translation tables allocated by the runtime context
# for the translation library.
#
arm_config_option_override(NAME PLAT_CMN_CTX_MAX_XLAT_TABLES DEFAULT 8)

#
# Disable FPU/SIMD usage in RMM. Enabling this option turns on
# DMBEDTLS_SHAXXX_USE_A64_CRYPTO_ONLY in Mbed TLS. To run RMM that was compiled
# this way requires Crypto.so plugin to be present for the FVP. This plugin is
# delivered separate to the FVP, and might not be present in all environments.
#
arm_config_option_override(NAME RMM_FPU_USE_AT_REL2 DEFAULT OFF)

#
# Maximum number of granules supported, enough to cover (2GB - 128MB) of DRAM0
# and 6GB DRAM1.
#
arm_config_option_override(NAME RMM_MAX_GRANULES DEFAULT 0x1FBA00)

#
# Maximum number of DRAM Banks allowed to be managed.
#
arm_config_option_override(NAME RMM_MAX_NUM_DRAM_BANKS DEFAULT 2)
