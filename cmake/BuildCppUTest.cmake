#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_subdirectory("ext/cpputest")

unset(cpputest_CXX_FLAGS)

if(CMAKE_VERBOSE_MAKEFILE)
    string(APPEND cpputest_CXX_FLAGS "-DCMAKE_VERBOSE_MAKEFILE=1 ")
endif()

string(APPEND cpputest_CXX_FLAGS "-Wno-c++98-compat-pedantic ")
string(APPEND cpputest_CXX_FLAGS "-Wno-c++98-compat ")
string(APPEND cpputest_CXX_FLAGS "-Wno-old-style-cast ")
string(APPEND cpputest_CXX_FLAGS "-Wno-padded ")
string(APPEND cpputest_CXX_FLAGS "-Wno-disabled-macro-expansion ")
string(APPEND cpputest_CXX_FLAGS "-Wno-exit-time-destructors ")
string(APPEND cpputest_CXX_FLAGS "-Wno-weak-vtables ")

string(REPLACE " " ";" cpputest_CXX_FLAGS ${cpputest_CXX_FLAGS})

target_compile_options(CppUTest
    PRIVATE
        ${cpputest_CXX_FLAGS}
)
