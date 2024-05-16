#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

include_guard()

include(${CMAKE_CURRENT_LIST_DIR}/common_fake_host.cmake)

# When running fuzzing, use the afl custom compiler.
if(HOST_VARIANT STREQUAL "host_fuzz")
# Try to find the afl-clang-lto, 
# which has to the best fuzzing performance
find_program(CMAKE_C_COMPILER
    NAMES "afl-clang-lto"
    DOC "Path to afl-clang-lto if exists.")
    if(${CMAKE_C_COMPILER})
    # find alf-clang-lto, then also need to set linker
    find_program(CMAKE_LINKER
        NAMES "afl-ld-lto"
        DOC "Path to afl-ld-lto if exists."
        REQUIRED)
    else()
    #cannot find afl-clang-lto, full back to afl-clang-fast
    find_program(CMAKE_C_COMPILER
        NAMES "afl-clang-fast"
        DOC "Path to afl-clang-lto if exists."
        REQUIRED)
    endif()
else()
find_program(CMAKE_C_COMPILER
    NAMES "clang"
    DOC "Path to clang."
    REQUIRED)
endif()


find_program(CMAKE_CXX_COMPILER
    NAMES "clang++"
    DOC "Path to clang++."
    REQUIRED)

set(CMAKE_ASM_COMPILER ${CMAKE_C_COMPILER})

foreach(language IN ITEMS ASM C CXX)
    string(APPEND CMAKE_${language}_FLAGS_INIT "-Wno-unknown-warning-option ")
    string(APPEND CMAKE_${language}_FLAGS_INIT "-Wno-unused-function ")
    string(APPEND CMAKE_${language}_FLAGS_INIT "-fPIC ")
endforeach()

string(APPEND CMAKE_EXE_LINKER_FLAGS_INIT "-Wl,--build-id=none ")
string(APPEND CMAKE_EXE_LINKER_FLAGS_INIT "-fuse-ld=lld ")
