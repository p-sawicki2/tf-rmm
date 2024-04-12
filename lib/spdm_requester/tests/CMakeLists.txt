#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

if(NOT RMM_ARCH STREQUAL fake_host)
    return()
endif()

#
# Import target test_crypt unit test in libspdm to RMM to verify RMM version of
# mbedtls used by libspdm for its cryptographic calls. This also verifies
# rmm-lib-allocator that manages mbedtls heap.
#
list(APPEND TEST_CRYPT_LIBS "debuglib")
list(APPEND TEST_CRYPT_LIBS "rnglib")
list(APPEND TEST_CRYPT_LIBS "malloclib")
list(APPEND TEST_CRYPT_LIBS "spdm_crypt_ext_lib")

foreach(TEST_CRYPT_LIB IN LISTS TEST_CRYPT_LIBS)
    add_subdirectory("${LIBSPDM_DIR}/os_stub/${TEST_CRYPT_LIB}"
        "${LIBSPDM_BIN_DIR}/os_stub/${TEST_CRYPT_LIB}")
    target_compile_definitions(${TEST_CRYPT_LIB} PRIVATE ${LIBSPDM_CONFIG})
endforeach()

# This variable CRYPTO is used by libspdm CMake file
set(CRYPTO "mbedtls")

add_subdirectory("${LIBSPDM_DIR}/unit_test/test_crypt"
    "${LIBSPDM_BIN_DIR}/unit_test/test_crypt")
target_compile_definitions(test_crypt PRIVATE ${LIBSPDM_CONFIG})
target_include_directories(test_crypt PRIVATE "${RMM_MBEDTLS_DIR}/include")

target_link_libraries(test_crypt
    rmm-lib-allocator
    rmm-plat-common
    rmm-lib-arch
    rmm-mbedtls)

# Copy all sample keys from libspdm source to build directory
# These sample keys/certificates are used by test_crypt
add_dependencies(test_crypt spdm_copy_sample_keys)
add_custom_target(spdm_copy_sample_keys ALL
    DEPENDS ${LIBSPDM_BIN_DIR}/unit_test/sample_key)

add_custom_command(
    OUTPUT ${LIBSPDM_BIN_DIR}/unit_test/sample_key
    COMMAND cp -r -f ${LIBSPDM_DIR}/unit_test/sample_key/*
        ${LIBSPDM_BIN_DIR}/unit_test/test_crypt/)
