#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#


# only need one CPU
arm_config_option_override(
    NAME MAX_CPUS
    FORCE 1)

add_library(rmm-plat-host_fuzz)

arm_config_option(
    NAME GRANULE_SIZE
    HELP "The size of the size."
    TYPE STRING
    DEFAULT 4096)

arm_config_option(
    NAME GRANULE_META_SIZE
    HELP "The size of the metadata of granule, i.e., `struct granule`."
    TYPE STRING
    DEFAULT 4)

arm_config_option(
    NAME FUZZING_COMMAND_COUNT
    HELP "The number of arbitrary RMI commands to be executed in the fuzzing."
    TYPE STRING
    DEFAULT 10)

arm_config_option(
    NAME FUZZING_REGISTER_COUNT
    HELP "The size of register."
    TYPE STRING
    DEFAULT 7)

arm_config_option(
    NAME REGISTER_SIZE
    HELP "The size of register."
    TYPE STRING
    DEFAULT 8)

arm_config_option(
    NAME FUZZING_FID_BEGIN
    HELP "The opcode lower bound."
    TYPE STRING
    DEFAULT 0xC4000150)

arm_config_option(
    NAME FUZZING_FID_END
    HELP "The opcode upper bound."
    TYPE STRING
    DEFAULT 0xC4000190)

set(ENV{GRANULE_SIZE} ${GRANULE_SIZE})
set(ENV{GRANULE_META_SIZE} ${GRANULE_META_SIZE})
set(ENV{FUZZING_COMMAND_COUNT} ${FUZZING_COMMAND_COUNT})
set(ENV{FUZZING_REGISTER_COUNT} ${FUZZING_REGISTER_COUNT})
set(ENV{REGISTER_SIZE} ${REGISTER_SIZE})
set(ENV{FUZZING_FID_BEGIN} ${FUZZING_FID_BEGIN})
set(ENV{FUZZING_FID_END} ${FUZZING_FID_END})
set(ENV{RMM_MAX_GRANULES} ${RMM_MAX_GRANULES})

target_link_libraries(rmm-plat-host_fuzz
    PRIVATE rmm-lib
            rmm-host-common)

target_sources(rmm-plat-host_fuzz
    PRIVATE "src/host_setup.c"
            "src/host_harness.c")

configure_file(${CMAKE_CURRENT_SOURCE_DIR}/python/mutate.py ${CMAKE_BINARY_DIR}/mutate.py COPYONLY)
configure_file(${CMAKE_CURRENT_SOURCE_DIR}/python/parser.py ${CMAKE_BINARY_DIR}/parser.py COPYONLY)
configure_file(${CMAKE_CURRENT_SOURCE_DIR}/python/data_type.py ${CMAKE_BINARY_DIR}/data_type.py COPYONLY)

add_library(rmm-platform ALIAS rmm-plat-host_fuzz)

math(EXPR HOST_MEM_SIZE "${RMM_MAX_GRANULES} * ${GRANULE_SIZE}")
arm_config_option_override(
    NAME HOST_MEM_SIZE
    FORCE ${HOST_MEM_SIZE})


# SMC corpus
add_custom_command(OUTPUT "${CMAKE_BINARY_DIR}/smc_corpus"
    COMMAND python3 ${CMAKE_CURRENT_SOURCE_DIR}/python/generate_corpus.py ${CMAKE_BINARY_DIR}/smc_corpus/default.bin ${GRANULE_SIZE} ${GRANULE_META_SIZE} ${RMM_MAX_GRANULES} ${FUZZING_COMMAND_COUNT} ${FUZZING_FID_BEGIN} ${FUZZING_FID_END} ${FUZZING_REGISTER_COUNT} ${REGISTER_SIZE}
    COMMENT "Generate default test as SMC corpus"
)

add_custom_target(smc-corpus ALL
    DEPENDS "${CMAKE_BINARY_DIR}/smc_corpus"
)

add_dependencies(rmm-plat-host_fuzz smc-corpus)

math(EXPR FUZZING_BUFF_SIZE "${HOST_MEM_SIZE} + ${RMM_MAX_GRANULES} * ${GRANULE_META_SIZE} + ${REGISTER_SIZE} * ${FUZZING_REGISTER_COUNT} * ${FUZZING_COMMAND_COUNT}")

# Run AFL target
add_custom_target(run-fuzzer
    COMMAND AFL_AUTORESUME=1 PYTHONPATH=${CMAKE_BINARY_DIR} AFL_PYTHON_MODULE=mutate afl-fuzz -i "${CMAKE_BINARY_DIR}/smc_corpus" -o "${CMAKE_BINARY_DIR}/afl_out" -g ${FUZZING_BUFF_SIZE} -G ${FUZZING_BUFF_SIZE} -a binary -P exploit -- ${CMAKE_BINARY_DIR}/$<CONFIG>/rmm.elf @@
    COMMENT "Run fuzzer"
    DEPENDS rmm
)
