#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

include_guard()

include(${CMAKE_CURRENT_LIST_DIR}/../common.cmake)

find_program(CMAKE_C_COMPILER
    NAMES "gcc"
    DOC "Path to gcc."
    REQUIRED)

#
# Needed to build CppUTest for unit tests
#
find_program(CMAKE_CXX_COMPILER
    NAMES "g++"
    DOC "Path to g++."
    REQUIRED)

foreach(language IN ITEMS ASM C CXX)
    string(APPEND CMAKE+${language}_FLAGS_INIT "-fPIC ")
endforeach()

set(CMAKE_ASM_COMPILER ${CMAKE_C_COMPILER})

#
# Flags needed to enable coverage testing
#

if (COVERAGE_ENABLED STREQUAL "ON")
    foreach(language in ITEMS C CXX)
        string(APPEND CMAKE_${language}_FLAGS_INIT "--coverage ")
    endforeach()
endif()

string(APPEND CMAKE_EXE_LINKER_FLAGS_INIT "-Wl,--build-id=none")
