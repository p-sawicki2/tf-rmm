#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

#
# Set the RMM_PLATFORM variable to Cmake cache.
#
set(RMM_PLATFORM "arm" CACHE STRING "platform")
arm_config_option_override(NAME RMM_TOOLCHAIN DEFAULT "gnu")

#
# Maximum number of DRAM banks allowed to be managed
#
arm_config_option_override(NAME RMM_MAX_NUM_DRAM_BANKS DEFAULT 2)

#
# Set RMM_MAX_SIZE for this platform (24MB)
#
arm_config_option_override(NAME RMM_MAX_SIZE DEFAULT 0x01800000)

#
# Maximum number of granules supported, enough to cover
# (2GB - 64MB) of DRAM0 and 2GB of DRAM1. We overprovision
# for the case that DT has not catered for the 64 MB carveout.
#
arm_config_option_override(NAME RMM_MAX_GRANULES DEFAULT 0x100000)
