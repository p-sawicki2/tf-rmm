#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

if(RMM_UNITTESTS)
    target_include_directories(rmm-lib-queue
        PRIVATE "tests")
endif()

# Add test functionality
rmm_build_unittest(NAME queue
                   TARGET rmm-lib-queue
                   LIBRARIES rmm-plat-host_test
                             rmm-lib-debug
                             rmm-lib-common
                             rmm-lib-slot_buf
                   SOURCES "tests/queue_tests.cpp")

