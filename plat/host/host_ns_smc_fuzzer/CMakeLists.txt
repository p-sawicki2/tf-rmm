#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#


# only need one CPU 
set(MAX_CPUS 1)

add_library(rmm-plat-host_ns_smc_fuzzer)

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
    NAME FUZING_REGISTER_COUNT
    HELP "The size of register."
    TYPE STRING
    DEFAULT 7)

arm_config_option(
    NAME REGISTER_SIZE
    HELP "The size of register."
    TYPE STRING
    DEFAULT 8)

target_link_libraries(rmm-plat-host_ns_smc_fuzzer
    PRIVATE rmm-lib
            rmm-host-common)

target_sources(rmm-plat-host_ns_smc_fuzzer
    PRIVATE "src/host_setup.c"
            "src/host_harness.c")

configure_file(${CMAKE_CURRENT_SOURCE_DIR}/python/mutate.py ${CMAKE_BINARY_DIR}/mutate.py COPYONLY)

add_library(rmm-platform ALIAS rmm-plat-host_ns_smc_fuzzer)

math(EXPR MACHINE_STATE_BYTES "${HOST_MEM_SIZE} + ${RMM_MAX_GRANULES} * ${GRANULE_META_SIZE}")

# SMC corpus
add_custom_command(OUTPUT "${CMAKE_BINARY_DIR}/smc_corpus"
    COMMAND python3 ${CMAKE_CURRENT_SOURCE_DIR}/python/generate_default_test.py ${CMAKE_BINARY_DIR}/smc_corpus/default.bin ${MACHINE_STATE_BYTES} ${FUZZING_COMMAND_COUNT} ${FUZING_REGISTER_COUNT} ${REGISTER_SIZE}
    COMMENT "Generate default test as SMC corpus"
)

add_custom_target(smc-corpus ALL
    DEPENDS "${CMAKE_BINARY_DIR}/smc_corpus"
)

add_dependencies(rmm-plat-host_ns_smc_fuzzer smc-corpus)

math(EXPR FUZZING_BUFF_SIZE "${HOST_MEM_SIZE} + ${RMM_MAX_GRANULES} * ${GRANULE_META_SIZE} + ${REGISTER_SIZE} * ${FUZING_REGISTER_COUNT} * ${FUZZING_COMMAND_COUNT}")

# Run AFL target
add_custom_target(run-fuzzer
    COMMAND AFL_AUTORESUME=1 PYTHONPATH=${CMAKE_BINARY_DIR} AFL_PYTHON_MODULE=mutate afl-fuzz -i "${CMAKE_BINARY_DIR}/smc_corpus" -o "${CMAKE_BINARY_DIR}/afl_out" -g ${FUZZING_BUFF_SIZE} -G ${FUZZING_BUFF_SIZE} -a binary -P exploit -- ${CMAKE_BINARY_DIR}/$<CONFIG>/rmm.elf @@
    COMMENT "Run fuzzer"
    DEPENDS rmm
)
