#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

if(HOST_VARIANT STREQUAL "host_fuzz")

arm_config_option(
    NAME FUZZ_GRANULE_META_SIZE
    HELP "The size of the metadata of granule, i.e., `struct granule`."
    TYPE STRING
    DEFAULT 2)

arm_config_option(
    NAME FUZZ_COMMAND_COUNT
    HELP "The number of arbitrary RMI commands to be executed in the fuzzing."
    TYPE STRING
    DEFAULT 10)

arm_config_option(
    NAME FUZZ_REGISTER_COUNT
    HELP "The size of register."
    TYPE STRING
    DEFAULT 7)

arm_config_option(
    NAME FUZZ_REGISTER_SIZE
    HELP "The size of register."
    TYPE STRING
    DEFAULT 8)

arm_config_option(
    NAME FUZZ_FID_BEGIN
    HELP "The opcode lower bound."
    TYPE STRING
    DEFAULT 0xC4000150)

arm_config_option(
    NAME FUZZ_FID_END
    HELP "The opcode upper bound."
    TYPE STRING
    DEFAULT 0xC4000190)

math(EXPR GRANULE_SIZE "1 << ${GRANULE_SHIFT}" OUTPUT_FORMAT DECIMAL)

set(ENV{GRANULE_SIZE} ${GRANULE_SIZE})
set(ENV{FUZZ_GRANULE_META_SIZE} ${FUZZ_GRANULE_META_SIZE})
set(ENV{FUZZ_COMMAND_COUNT} ${FUZZ_COMMAND_COUNT})
set(ENV{FUZZ_REGISTER_COUNT} ${FUZZ_REGISTER_COUNT})
set(ENV{FUZZ_REGISTER_SIZE} ${FUZZ_REGISTER_SIZE})
set(ENV{FUZZ_FID_BEGIN} ${FUZZ_FID_BEGIN})
set(ENV{FUZZ_FID_END} ${FUZZ_FID_END})
set(ENV{RMM_MAX_GRANULES} ${RMM_MAX_GRANULES})

configure_file(${CMAKE_CURRENT_SOURCE_DIR}/python/mutate.py ${CMAKE_BINARY_DIR}/mutate.py COPYONLY)
configure_file(${CMAKE_CURRENT_SOURCE_DIR}/python/parser.py ${CMAKE_BINARY_DIR}/parser.py COPYONLY)
configure_file(${CMAKE_CURRENT_SOURCE_DIR}/python/data_type.py ${CMAKE_BINARY_DIR}/data_type.py COPYONLY)

# SMC corpus
add_custom_command(OUTPUT "${CMAKE_BINARY_DIR}/smc_corpus"
    COMMAND python3 ${CMAKE_CURRENT_SOURCE_DIR}/python/generate_corpus.py
        ${CMAKE_BINARY_DIR}/smc_corpus/default.bin
        ${GRANULE_SIZE}
        ${FUZZ_GRANULE_META_SIZE}
        ${RMM_MAX_GRANULES}
        ${FUZZ_COMMAND_COUNT}
        ${FUZZ_FID_BEGIN}
        ${FUZZ_FID_END}
        ${FUZZ_REGISTER_COUNT}
        ${FUZZ_REGISTER_SIZE}
    COMMENT "Generate default test as SMC corpus"
)

add_custom_target(smc-corpus ALL
    DEPENDS "${CMAKE_BINARY_DIR}/smc_corpus"
)

add_dependencies(rmm-plat-host_fuzz smc-corpus)

math(EXPR FUZZ_BUFF_SIZE "${HOST_MEM_SIZE} + ${RMM_MAX_GRANULES} * ${FUZZ_GRANULE_META_SIZE} + ${FUZZ_REGISTER_SIZE} * ${FUZZ_REGISTER_COUNT} * ${FUZZ_COMMAND_COUNT}")

# Run AFL target
add_custom_target(run-fuzzer
    COMMAND AFL_AUTORESUME=1 PYTHONPATH=${CMAKE_BINARY_DIR} AFL_PYTHON_MODULE=mutate afl-fuzz -i "${CMAKE_BINARY_DIR}/smc_corpus" -o "${CMAKE_BINARY_DIR}/afl_out" -g ${FUZZ_BUFF_SIZE} -G ${FUZZ_BUFF_SIZE} -a binary -P exploit -- ${CMAKE_BINARY_DIR}/$<CONFIG>/rmm.elf @@
    COMMENT "Run fuzzer"
    DEPENDS rmm
)

endif() # HOST_VARIANT STREQUAL "host_fuzz"
