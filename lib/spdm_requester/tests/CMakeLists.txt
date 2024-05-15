#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

if(NOT RMM_UNITTESTS)
    return()
endif()

# As rmm-lib-spdm_requester is an interface library, we can't add sources to it
# like spdm_requester_tests.cpp so add a target named
# rmm-lib-spdm_requester_test.
add_library(rmm-lib-spdm_requester_test)
target_compile_definitions(rmm-lib-spdm_requester_test PRIVATE ${LIBSPDM_CONFIG})
target_include_directories(rmm-lib-spdm_requester_test
    PUBLIC "${RMM_SOURCE_DIR}/ext/mbedtls/include"
           "${RMM_SOURCE_DIR}/lib/common/include"
           "${RMM_SOURCE_DIR}/lib/allocator/include"
           "${RMM_SOURCE_DIR}/configs/libspdm")

# Add unit_test/test_crypt library
add_subdirectory("${LIBSPDM_DIR}/unit_test/test_crypt"
    "${LIBSPDM_BIN_DIR}/unit_test/test_crypt")
target_compile_definitions(test_crypt PRIVATE ${LIBSPDM_CONFIG})
target_include_directories(test_crypt PUBLIC
    PUBLIC "${RMM_SOURCE_DIR}/configs/libspdm")

# Add test group 'spdm_requester' to RMM unit test framwork.
rmm_build_unittest(NAME spdm_requester
    LIBRARIES test_crypt
    TARGET rmm-lib-spdm_requester_test
    SOURCES "tests/spdm_requester_tests.cpp"
    ITERATIONS 1)

# Copy all sample keys from libspdm source to build directory. These sample
# keys/certificates are used by test_crypt unit tests.
add_dependencies(rmm-lib-spdm_requester_test spdm_copy_sample_keys)
add_custom_target(spdm_copy_sample_keys ALL
    DEPENDS ${CMAKE_BINARY_DIR}/sample_key)
add_custom_command(COMMAND cp -r -f ${LIBSPDM_DIR}/unit_test/sample_key
    ${CMAKE_BINARY_DIR}/
    OUTPUT ${CMAKE_BINARY_DIR}/sample_key)
