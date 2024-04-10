#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

find_package(Git)
list(APPEND CMAKE_MODULE_PATH "${CMAKE_SOURCE_DIR}/tools/common")
include(GitUtils)
include(FetchContent)

# Skip rmm-lib-spdm_requester from CMBC analysis
if(RMM_CBMC_STATIC_ANALYSIS)
    add_library(rmm-lib-spdm_requester INTERFACE)
    return()
endif()

#
# Git clone libspdm. We manually clone instead of adding this as a submodule
# because adding libspdm as a submodule causes recursive clone to fetch all
# dependency projects by libspdm. This causes projects that not required by RMM
# in RMM source path and also causes timeouts in CI. For RMM we only need
# libspdm source and not the submodules that libspdm refers.
#
# LIBSPDM_SHA points to v3.3.0 + mbedtls 3.6.0
#
set(LIBSPDM_URL "https://github.com/DMTF/libspdm.git")
set(LIBSPDM_SHA "e5eb4484705fb3fb5cd25e773477c456096bd837")
FetchContent_Declare(libspdm
    GIT_REPOSITORY	${LIBSPDM_URL}
    GIT_TAG		${LIBSPDM_SHA}
    GIT_SUBMODULES	""
    GIT_PROGRESS	1)

FetchContent_GetProperties(libspdm)
if(NOT libspdm_POPULATED)
    message("Fetching: ${LIBSPDM_URL} SHA: ${LIBSPDM_SHA}")
    FetchContent_Populate(libspdm)
    message("libspdm SRC: ${libspdm_SOURCE_DIR}")
endif()

# Set LIBSPDM_DIR. Note: This variable is used by libspdm CMake.
# libspdm_SOURCE_DIR will be set by FetchContent_Populate() call.
set(LIBSPDM_DIR ${libspdm_SOURCE_DIR})
set(LIBSPDM_BIN_DIR "${CMAKE_BINARY_DIR}/ext/libspdm")
set(MBEDTLS_SRC_DIR "${RMM_SOURCE_DIR}/ext/mbedtls")

# Apply RMM specific patches to libspdm once cloned.
set(LIBSPDM_PATCH_DIR "${RMM_SOURCE_DIR}/configs/libspdm")
set(LIBSPDM_PATCH_FILES
    "${LIBSPDM_PATCH_DIR}/0001-cryptlib_mbedtls-use-external-Mbed-TLS.patch"
    )
Git_Apply_Patches(${LIBSPDM_DIR} "${LIBSPDM_PATCH_FILES}")

#
# This compiles libraries in ext/libspdm project to add SPDM requester protocol
# support in RMM.
#
add_library(rmm-lib-spdm_requester INTERFACE)

# Set libspdm config file
set(LIBSPDM_CONFIG "LIBSPDM_CONFIG=<rmm_libspdm_config.h>")

# Below are the list of core SPDM libraries required for requester side protocol.
set(LIBSPDM_CORE_LIBS
    spdm_common_lib
    spdm_crypt_lib
    spdm_requester_lib
    spdm_secured_message_lib)

foreach(LIBSPDM_CORE_LIB IN LISTS LIBSPDM_CORE_LIBS)
    add_subdirectory("${LIBSPDM_DIR}/library/${LIBSPDM_CORE_LIB}"
        "${LIBSPDM_BIN_DIR}/library/${LIBSPDM_CORE_LIB}")
    target_include_directories(${LIBSPDM_CORE_LIB} PRIVATE
        "${RMM_SOURCE_DIR}/configs/libspdm")
    target_compile_definitions(${LIBSPDM_CORE_LIB} PRIVATE ${LIBSPDM_CONFIG})
    target_link_libraries(rmm-lib-spdm_requester INTERFACE "${LIBSPDM_CORE_LIB}")
endforeach()

#
# Below are the list of os_stub libraries in libspdm that LIBSPDM_CORE_LIBS
# depends on.
#
set(LIBSPDM_STUB_LIBS
    cryptlib_mbedtls
    memlib)

foreach(LIBSPDM_STUB_LIB IN LISTS LIBSPDM_STUB_LIBS)
    add_subdirectory("${LIBSPDM_DIR}/os_stub/${LIBSPDM_STUB_LIB}"
        "${LIBSPDM_BIN_DIR}/os_stub/${LIBSPDM_STUB_LIB}")
    target_include_directories(${LIBSPDM_STUB_LIB} PRIVATE
        "${RMM_SOURCE_DIR}/configs/libspdm")
    target_compile_definitions(${LIBSPDM_STUB_LIB} PRIVATE ${LIBSPDM_CONFIG})

    # For cryptlib_mbedtls include headers and config from RMM MbedTLS directory
    if (LIBSPDM_STUB_LIB STREQUAL cryptlib_mbedtls)
        target_include_directories(${LIBSPDM_STUB_LIB} PRIVATE
            "${RMM_SOURCE_DIR}/configs/mbedtls"
            "${MBEDTLS_SRC_DIR}/include")
        target_compile_definitions(${LIBSPDM_STUB_LIB} PUBLIC
            "-DMBEDTLS_CONFIG_FILE=<rmm_mbedtls_config.h>")
        target_compile_options(${LIBSPDM_STUB_LIB} PRIVATE
            "-Wno-incompatible-pointer-types")
    endif()
    target_link_libraries(rmm-lib-spdm_requester INTERFACE "${LIBSPDM_STUB_LIB}")
endforeach()
