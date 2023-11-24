#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

target_include_directories(rmm-lib-s2tt
    PRIVATE "tests")

# Add test functionality
rmm_build_unittest(NAME s2tt_non_lpa2
		   TARGET rmm-lib-s2tt
		   SOURCES "tests/s2tt_test_helpers.c"
			   "tests/s2tt_tests_base.cpp"
			   "tests/s2tt_non_lpa2.cpp"
		   ITERATIONS 10)

rmm_build_unittest(NAME s2tt_lpa2
		   TARGET rmm-lib-s2tt
		   SOURCES "tests/s2tt_test_helpers.c"
			   "tests/s2tt_tests_base.cpp"
			   "tests/s2tt_lpa2.cpp"
		   ITERATIONS 10)

