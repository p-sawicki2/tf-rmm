#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_library(rmm-lib-queue)

target_include_directories(rmm-lib-queue
    PUBLIC "include")

target_link_libraries(rmm-lib-queue
    PRIVATE
      rmm-lib-debug
      rmm-lib-common
)

target_sources(rmm-lib-queue
    PRIVATE "src/queue.c")
