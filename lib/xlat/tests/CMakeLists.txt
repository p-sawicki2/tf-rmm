#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

target_include_directories(rmm-lib-xlat
    PRIVATE "tests")

# Add test functionality
rmm_build_unittest(NAME stage1_xlat
                   LIBRARIES rmm-platform
                   TARGET rmm-lib-xlat
                   SOURCES "tests/stage1_xlat.cpp"
                           "tests/st1_xlat_test_helpers.c"
                   ITERATIONS 10)
