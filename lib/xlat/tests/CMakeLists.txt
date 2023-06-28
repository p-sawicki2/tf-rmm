#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

target_include_directories(rmm-lib-xlat
    PRIVATE "tests")

# Add test functionality
rmm_build_unittest(NAME xlat_tests_LPA2
                   LIBRARIES rmm-platform
                   TARGET rmm-lib-xlat
                   SOURCES "tests/xlat_tests_lpa2.cpp"
                           "tests/xlat_tests_base.cpp"
                           "tests/xlat_test_helpers.c"
                   ITERATIONS 10)

rmm_build_unittest(NAME xlat_tests_no_LPA2
                   LIBRARIES rmm-platform
                   TARGET rmm-lib-xlat
                   SOURCES "tests/xlat_tests_no_lpa2.cpp"
                           "tests/xlat_tests_base.cpp"
                           "tests/xlat_test_helpers.c"
                   ITERATIONS 10)
