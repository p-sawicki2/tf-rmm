#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_subdirectory("ext/cpputest")

unset(cpputest_CXX_FLAGS)

if(CMAKE_VERBOSE_MAKEFILE)
    list(APPEND cpputest_CXX_FLAGS -D "CMAKE_VERBOSE_MAKEFILE=1")
endif()

string(APPEND cpputest_CXX_FLAGS "-Wno-c++98-compat-pedantic")

target_compile_options(CppUTest
    PRIVATE
        ${cpputest_CXX_FLAGS}
)
