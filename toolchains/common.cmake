#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

include_guard()

set(CMAKE_FIND_ROOT_PATH_MODE_PROGRAM NEVER)
set(CMAKE_FIND_ROOT_PATH_MODE_LIBRARY ONLY)
set(CMAKE_FIND_ROOT_PATH_MODE_INCLUDE ONLY)
set(CMAKE_FIND_ROOT_PATH_MODE_PACKAGE ONLY)

foreach(language IN ITEMS ASM C CXX)
    string(APPEND CMAKE_${language}_FLAGS_INIT "-fno-common ")
    string(APPEND CMAKE_${language}_FLAGS_INIT "-ffunction-sections ")
    string(APPEND CMAKE_${language}_FLAGS_INIT "-fdata-sections ")
    string(APPEND CMAKE_${language}_FLAGS_INIT "-Wall -Werror ")
    string(APPEND CMAKE_${language}_FLAGS_INIT "-gdwarf-4 ")
    string(APPEND CMAKE_${language}_FLAGS_DEBUG_INIT "-Og ")
    string(APPEND CMAKE_${language}_FLAGS_RELEASE_INIT "-g ")
endforeach()

string(APPEND CMAKE_EXE_LINKER_FLAGS_INIT "-Wl,--gc-sections -g ")

#
# Using <LINK_FLAGS> filers flags related to linking stage and avoids compile
# time flags passed to linker. By grouping libraries between
# --start-group/--end-group the specified archives are searched repeatedly
# until no new undefined references are created.
#
foreach(language IN ITEMS C CXX)
    set(CMAKE_${language}_LINK_EXECUTABLE "<CMAKE_${language}_COMPILER> \
<LINK_FLAGS> <OBJECTS> -o <TARGET> -Wl,--start-group <LINK_LIBRARIES> \
-Wl,--end-group")
endforeach()
