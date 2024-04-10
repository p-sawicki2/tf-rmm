#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

find_package(Git)
list(APPEND CMAKE_MODULE_PATH "${CMAKE_SOURCE_DIR}/tools/common")
include(GitUtils)

# Skip rmm-lib-spdm_requester from CMBC analysis
if(RMM_CBMC_STATIC_ANALYSIS)
    add_library(rmm-lib-spdm_requester INTERFACE)
    return()
endif()

#
# This compiles libraries in ext/libspdm project to add SPDM requester protocol
# support in RMM. As part of recursive 'git clone', libspdm clones many dependent
# projects. But non of the projects are build by RMM including the mbedtls in
# libspdm. And also no header files in libspdm submodule are referred by RMM.
#
add_library(rmm-lib-spdm_requester INTERFACE)

# Set LIBSPDM_DIR. Note: This variable is used by libspdm CMake.
set(LIBSPDM_DIR "${RMM_SOURCE_DIR}/ext/libspdm")
set(LIBSPDM_BIN_DIR "${CMAKE_BINARY_DIR}/ext/libspdm")
set(RMM_MBEDTLS_DIR "${RMM_SOURCE_DIR}/ext/mbedtls")

# Only one session per device is supported by RMM Specification
list(APPEND LIBSPDM_CONFIG "LIBSPDM_MAX_SESSION_COUNT=1")

#
# libspdm enables all capabilities by default. This disables the SPMD requester
# capabilities that are not required for RMM DA.
#
list(APPEND LIBSPDM_CONFIG "LIBSPDM_ENABLE_CAPABILITY_PSK_CAP=0")
list(APPEND LIBSPDM_CONFIG "LIBSPDM_ENABLE_CAPABILITY_HBEAT_CAP=0")
list(APPEND LIBSPDM_CONFIG "LIBSPDM_ENABLE_CAPABILITY_MUT_AUTH_CAP=0")
list(APPEND LIBSPDM_CONFIG "LIBSPDM_ENABLE_CAPABILITY_ENCAP_CAP=0")
list(APPEND LIBSPDM_CONFIG "LIBSPDM_ENABLE_CAPABILITY_CSR_CAP_EX=0")
list(APPEND LIBSPDM_CONFIG "LIBSPDM_ENABLE_CAPABILITY_SET_CERT_CAP=0")
list(APPEND LIBSPDM_CONFIG "LIBSPDM_ENABLE_CAPABILITY_EVENT_CAP=0")
list(APPEND LIBSPDM_CONFIG "LIBSPDM_EVENT_RECIPIENT_SUPPORT=0")

#
# libspdm enables all cryptography configuration by default.
# todo: Disable more cryptography configuration in SPDM that are not required
# by RMM.
#
list(APPEND LIBSPDM_CONFIG "LIBSPDM_SHA3_256_SUPPORT=0")
list(APPEND LIBSPDM_CONFIG "LIBSPDM_SHA3_384_SUPPORT=0")
list(APPEND LIBSPDM_CONFIG "LIBSPDM_SHA3_512_SUPPORT=0")
list(APPEND LIBSPDM_CONFIG "LIBSPDM_SM3_256_SUPPORT=0")
list(APPEND LIBSPDM_CONFIG "LIBSPDM_EDDSA_ED25519_SUPPORT=0")
list(APPEND LIBSPDM_CONFIG "LIBSPDM_EDDSA_ED448_SUPPORT=0")
list(APPEND LIBSPDM_CONFIG "LIBSPDM_SM2_DSA_P256_SUPPORT=0")
list(APPEND LIBSPDM_CONFIG "LIBSPDM_SM2_KEY_EXCHANGE_P256_SUPPORT=0")
list(APPEND LIBSPDM_CONFIG "LIBSPDM_AEAD_SM4_128_GCM_SUPPORT=0")

# Based on RMM build type, set libspdm DEBUG flag
if (CMAKE_BUILD_TYPE STREQUAL Debug)
    list(APPEND LIBSPDM_CONFIG "LIBSPDM_DEBUG_ENABLE=1")
else()
    list(APPEND LIBSPDM_CONFIG "LIBSPDM_DEBUG_ENABLE=0")
endif()

# Below are the list of core SPDM libraries required for requester side protocol.
list(APPEND LIBSPDM_CORE_LIBS "spdm_common_lib")
list(APPEND LIBSPDM_CORE_LIBS "spdm_crypt_lib")
list(APPEND LIBSPDM_CORE_LIBS "spdm_requester_lib")
list(APPEND LIBSPDM_CORE_LIBS "spdm_secured_message_lib")

foreach(LIBSPDM_CORE_LIB IN LISTS LIBSPDM_CORE_LIBS)
    add_subdirectory("${LIBSPDM_DIR}/library/${LIBSPDM_CORE_LIB}"
        "${LIBSPDM_BIN_DIR}/library/${LIBSPDM_CORE_LIB}")
    target_compile_definitions(${LIBSPDM_CORE_LIB} PRIVATE ${LIBSPDM_CONFIG})
    target_link_libraries(rmm-lib-spdm_requester INTERFACE "${LIBSPDM_CORE_LIB}")
endforeach()

#
# Below are the list of os_stub libraries in libspdm that LIBSPDM_CORE_LIBS
# depends on.
#
list(APPEND LIBSPDM_STUB_LIBS "cryptlib_mbedtls")
list(APPEND LIBSPDM_STUB_LIBS "memlib")

foreach(LIBSPDM_STUB_LIB IN LISTS LIBSPDM_STUB_LIBS)
    add_subdirectory("${LIBSPDM_DIR}/os_stub/${LIBSPDM_STUB_LIB}"
        "${LIBSPDM_BIN_DIR}/os_stub/${LIBSPDM_STUB_LIB}")
    target_compile_definitions(${LIBSPDM_STUB_LIB} PRIVATE ${LIBSPDM_CONFIG})

    # For cryptlib_mbedtls include headers and config from RMM MbedTLS directory
    if (LIBSPDM_STUB_LIB STREQUAL cryptlib_mbedtls)
        target_include_directories(${LIBSPDM_STUB_LIB} PRIVATE
            "${RMM_SOURCE_DIR}/configs/mbedtls"
            "${RMM_MBEDTLS_DIR}/include")
        target_compile_definitions(${LIBSPDM_STUB_LIB} PUBLIC
            "-DMBEDTLS_CONFIG_FILE=<mbedtls_config.h>")
    endif()
    target_link_libraries(rmm-lib-spdm_requester INTERFACE "${LIBSPDM_STUB_LIB}")
endforeach()

# Patch support
set(LIBSPDM_PATCH_DIR "${RMM_SOURCE_DIR}/configs/libspdm")
list(APPEND LIBSPDM_PATCH_FILES
    "${LIBSPDM_PATCH_DIR}/0001-cryptlib_mbedtls-use-external-Mbed-TLS.patch")
list(APPEND LIBSPDM_PATCH_FILES
    "${LIBSPDM_PATCH_DIR}/0002-cryptlib_mbedtls-use-mbedtls-3.4.0.patch")

Git_Apply_Patches(${LIBSPDM_DIR} "${LIBSPDM_PATCH_FILES}")
