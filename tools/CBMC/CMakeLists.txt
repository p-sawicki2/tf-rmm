#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

include(FetchContent)

if(RMM_STATIC_ANALYSIS)
    find_program(RMM_CBMC_PATH "cbmc"
        DOC "Path to cbmc.")
endif()

if(EXISTS "${RMM_CBMC_STATIC_ANALYSIS}")
    mark_as_advanced(FORCE RMM_CBMC_PATH)
else()
    mark_as_advanced(CLEAR RMM_CBMC_PATH)
endif()

arm_config_option(
    NAME RMM_CBMC_STATIC_ANALYSIS
    HELP "Enable CBMC static analysis."
    DEFAULT FALSE
    DEPENDS (RMM_STATIC_ANALYSIS))

arm_config_option(
    NAME RMM_CBMC_CONFIGURATION
    HELP "The configuration in witch to use CBMC"
    STRINGS "COVER" "ASSERT" "ANALYSIS"
    DEFAULT "COVER"
    DEPENDS RMM_CBMC_STATIC_ANALYSIS)

arm_config_option(
    NAME RMM_TESTBENCH_DIR
    HELP "RMM testbench folder"
    TYPE STRING
    DEFAULT "${CMAKE_CURRENT_SOURCE_DIR}/testbenches"
    DEPENDS RMM_CBMC_STATIC_ANALYSIS
    ADVANCED)

arm_config_option(
    NAME RMM_TESTBENCH_RESULT_DIR
    HELP "RMM testbench result folder"
    TYPE STRING
    DEFAULT "${CMAKE_CURRENT_BINARY_DIR}/testbenches_results"
    DEPENDS RMM_CBMC_STATIC_ANALYSIS
    ADVANCED)

if("${RMM_CBMC_CONFIGURATION}" STREQUAL "COVER")
  set(CBMC_RESULT_FILE_SUFFIX "coverage")
  set(CBMC_SUMMARY_HEADER "COVERAGE")
  set(CBMC_SUMMARY_PATTERN "covered")
elseif("${RMM_CBMC_CONFIGURATION}" STREQUAL "ASSERT")
  set(CBMC_RESULT_FILE_SUFFIX "assert")
  set(CBMC_SUMMARY_HEADER "ASSERT")
  set(CBMC_SUMMARY_PATTERN "failed")
elseif("${RMM_CBMC_CONFIGURATION}" STREQUAL "ANALYSIS")
  set(CBMC_RESULT_FILE_SUFFIX "verification")
  set(CBMC_SUMMARY_HEADER "VERIFICATION")
  set(CBMC_SUMMARY_PATTERN "failed")
else()
  message(FATAL_ERROR "Invalid RMM_CBMC_CONFIGURATION '${RMM_CBMC_CONFIGURATION}'")
endif()

set(SUMMARY_FILE "SUMMARY.${CBMC_RESULT_FILE_SUFFIX}")
set(RMM_CBMC_SUMMARY_FIELD_WIDTH 38)

#
# Functions for extracting sources and includes from targets
#

function(add_include_from_target target_name)
  get_target_property(target_type ${target_name} TYPE)
  if(${target_type} STREQUAL "INTERFACE_LIBRARY")
    get_target_property(target_includes_dir ${target_name} INTERFACE_INCLUDE_DIRECTORIES)
  else()
    get_target_property(target_includes_dir ${target_name} INCLUDE_DIRECTORIES)
  endif()
  if(NOT "${target_includes_dir}" STREQUAL "target_includes_dir-NOTFOUND")
    foreach(target_includes_dir ${target_includes_dir})
      list(APPEND rmm_implementation_includes "-I${target_includes_dir}")
    endforeach()
    set (rmm_implementation_includes ${rmm_implementation_includes} PARENT_SCOPE)
  endif()
endfunction()

function(add_source_and_include_from_target target_name target_src_patterns)
  get_target_property(target_srcs ${target_name} SOURCES)
  get_target_property(target_srcs_dir ${target_name} SOURCE_DIR)
  foreach(target_src ${target_srcs})
    foreach(pattern ${target_src_patterns})
      if(target_src MATCHES ${pattern})
        set(src_full_path "${target_srcs_dir}/${target_src}")
        list(APPEND rmm_implementation_srcs "${src_full_path}")
        break()
      endif()
    endforeach()
  endforeach()
  add_include_from_target(${target_name})
  set (rmm_implementation_srcs ${rmm_implementation_srcs} PARENT_SCOPE)
  set (rmm_implementation_includes ${rmm_implementation_includes} PARENT_SCOPE)
  endfunction()

#
# Helper functions for formatting the summary file
#

function(rmm_cbmc_align_to_middle field_width padding_character text)
  set (pad_pool "")
  foreach(i RANGE ${field_width})
    string(APPEND pad_pool ${padding_character})
  endforeach()
  string(LENGTH ${text} text_len)
  math(EXPR leading_space "(${field_width} - ${text_len}) / 2")
  math(EXPR trailing_space "${field_width} - ${text_len} - ${leading_space}")

  string (SUBSTRING ${pad_pool} 0 ${leading_space} leading_spaces)
  string (SUBSTRING ${pad_pool} 0 ${trailing_space} trailing_spaces)

  set(aligned_text "")
  string (APPEND aligned_text "${leading_spaces}" "${text}" "${trailing_spaces}")
  set(aligned_text "${aligned_text}" PARENT_SCOPE)
endfunction()

function(rmm_cbmc_append_separator)
  rmm_cbmc_align_to_middle(${RMM_CBMC_SUMMARY_FIELD_WIDTH} "-" "-")
  set(separator_line "")
  string(APPEND separator_line "+" "${aligned_text}" "+" "${aligned_text}" "+\n")
  file(APPEND ${RMM_TESTBENCH_RESULT_DIR}/${SUMMARY_FILE} ${separator_line})
endfunction()

function(rmm_cbmc_write_summary_header)
  file(MAKE_DIRECTORY ${RMM_TESTBENCH_RESULT_DIR})
  file(WRITE ${RMM_TESTBENCH_RESULT_DIR}/${SUMMARY_FILE} "")
  rmm_cbmc_append_separator()
  rmm_cbmc_align_to_middle(${RMM_CBMC_SUMMARY_FIELD_WIDTH} " " "FILENAME")
  set(field1 "${aligned_text}")
  rmm_cbmc_align_to_middle(${RMM_CBMC_SUMMARY_FIELD_WIDTH} " " "${CBMC_SUMMARY_HEADER}")
  set(field2 "${aligned_text}")
  set(header "")
  string(APPEND header "|" "${field1}" "|" "${field2}" "|\n")
  file(APPEND ${RMM_TESTBENCH_RESULT_DIR}/${SUMMARY_FILE} ${header})
  rmm_cbmc_append_separator()
endfunction()

function(rmm_cbmc_append_summary testbench_filename output_file)
  rmm_cbmc_align_to_middle(${RMM_CBMC_SUMMARY_FIELD_WIDTH} " " ${testbench_filename})
  set(testbench_filename "${aligned_text}")

  execute_process(COMMAND grep -E "${CBMC_SUMMARY_PATTERN}" ${output_file} OUTPUT_VARIABLE testbench_result)

  if("${testbench_result}" STREQUAL "")
    rmm_cbmc_align_to_middle(${RMM_CBMC_SUMMARY_FIELD_WIDTH} " " "N/A")
    set(testbench_result "${aligned_text}")
  endif()

  string(REPLACE "\n" "" testbench_result "${testbench_result}")
  string(REGEX REPLACE "[^\\*]*\\*\\*[\\s]*" "" testbench_result "${testbench_result}")

  rmm_cbmc_align_to_middle(${RMM_CBMC_SUMMARY_FIELD_WIDTH} " " ${testbench_result})
  set(testbench_result "${aligned_text}")

  string(APPEND summary_data "|${testbench_filename}|${testbench_result}|\n")
  file(APPEND ${RMM_TESTBENCH_RESULT_DIR}/${SUMMARY_FILE} ${summary_data})
  rmm_cbmc_append_separator()
endfunction()

#
# Configure and execute CBMC
#

if(RMM_CBMC_STATIC_ANALYSIS)
  if(NOT (EXISTS "${RMM_CBMC_PATH}"))
    message(FATAL_ERROR "cbmc executable not found. (${RMM_CBMC_PATH})")
  endif()

  if (NOT (${HOST_VARIANT} STREQUAL "host_cbmc"))
    message(FATAL_ERROR "cbmc analysis requires host variant `host_cbmc`. (Add `-DHOST_VARIANT=host_cbmc`)")
  endif()

  # Configurations for shrinking the search space
  set(MEASUREMENT_SLOT_NR "1U")
  set(MAX_MEASUREMENT_SIZE "1")
  set(RPV_SIZE "1")
  # Configurations for the initial state.
  set(GRANULE_SIZE_SHIFT "7")
  math(EXPR GRANULE_SIZE "1 << ${GRANULE_SIZE_SHIFT}" OUTPUT_FORMAT DECIMAL)
  set(MAX_NUM_OF_GRANULE "8")
  set(ATTEST_CHALLENGE_SIZE "1")

  set(MAX_RTT_UNWIND "6")
  set(MAX_AUX_REC "2")
  set(MAX_ROOT_RTT "3")
  set(MAX_UNWIND_FLAGS "")

  # retrieve the testbench source files
  aux_source_directory(${RMM_TESTBENCH_DIR} testbench_files)

  #
  # Create the list of source files and include directories that are to be
  # included in the analysis.
  #

  set(rmm_implementation_srcs)
  set(rmm_implementation_includes)

  set(all_c_files_pattern ".+\\.c")
  set(rmm_platform_pattern ".+host_harness\\.c")
  set(rmm_lib_arch_pattern ".*src\\/[^\\/]+\\.c")
  set(rmm_runtime_pattern
    ".*rmi\\/[^\\/]+\\.c"
    ".*core\\/fake_host\\/.+\\.c"
    ".*core\\/vmid\\.c")

  add_include_from_target("rmm-lib-allocator")
  add_include_from_target("rmm-lib-rmm_el3_ifc")
  add_include_from_target("t_cose")
  add_include_from_target("rmm-lib-attestation")
  add_include_from_target("rmm-lib-measurement")
  add_include_from_target("rmm-lib-xlat")
  add_include_from_target("rmm-lib-timers")
  add_include_from_target("qcbor")
  add_include_from_target("rmm-lib-debug")
  add_include_from_target("rmm-lib-common")
  add_include_from_target("rmm-mbedtls")
  add_include_from_target("rmm-plat-common")
  add_source_and_include_from_target("rmm-host-common" "${all_c_files_pattern}")
  add_source_and_include_from_target("rmm-lib-gic"     "${all_c_files_pattern}")
  add_source_and_include_from_target("rmm-lib-realm"   "${all_c_files_pattern}")
  add_source_and_include_from_target("rmm-lib-smc"     "${all_c_files_pattern}")
  add_source_and_include_from_target("rmm-platform"    "${rmm_platform_pattern}")
  add_source_and_include_from_target("rmm-lib-arch"    "${rmm_lib_arch_pattern}")
  add_source_and_include_from_target("rmm-runtime"     "${rmm_runtime_pattern}")

  list(APPEND rmm_implementation_srcs
    "${CMAKE_CURRENT_SOURCE_DIR}/src/tb_rtt.c"
    "${CMAKE_CURRENT_SOURCE_DIR}/src/tb_realm.c"
    "${CMAKE_CURRENT_SOURCE_DIR}/src/tb.c"
    "${CMAKE_CURRENT_SOURCE_DIR}/src/tb_common.c"
    "${CMAKE_CURRENT_SOURCE_DIR}/src/tb_granules.c"
    "${CMAKE_CURRENT_SOURCE_DIR}/src/tb_measurement.c")

  list(APPEND rmm_implementation_includes
    "-I${CMAKE_CURRENT_SOURCE_DIR}/include"
    "-I${CMAKE_CURRENT_SOURCE_DIR}/testbenches"
    "-I${CMAKE_SOURCE_DIR}/ext/mbedtls/include")

  list(REMOVE_DUPLICATES rmm_implementation_includes)
  list(REMOVE_DUPLICATES rmm_implementation_srcs)

  list(FILTER rmm_implementation_srcs EXCLUDE REGEX ".*rmi\\/run\\.c")

  #
  # Set up cbmc command line
  #

  set(cbmc_unwinds_list
    "--unwindset;find_lock_rd_granules.0:${MAX_RTT_UNWIND}"
    "--unwindset;find_lock_rd_granules.1:${MAX_RTT_UNWIND}"
    "--unwindset;smc_realm_create.0:${MAX_RTT_UNWIND}"
    "--unwindset;total_root_rtt_refcount.0:${MAX_RTT_UNWIND}"
    "--unwindset;free_sl_rtts.0:${MAX_RTT_UNWIND}"
    "--unwindset;rtt_walk_lock_unlock.0:${MAX_RTT_UNWIND}"
    "--unwindset;RttWalk.0:${MAX_RTT_UNWIND}"
    "--unwindset;init_walk_path.0:${MAX_RTT_UNWIND}"
    "--unwindset;smc_rec_create.0:${MAX_AUX_REC}"
    "--unwindset;free_rec_aux_granules.0:${MAX_AUX_REC}"
    "--unwindset;find_lock_granules.3:${MAX_ROOT_RTT}"
    "--unwindset;RealmIsLive.0:${MAX_ROOT_RTT}"
    "--unwindset;init_rtt_root_page.0:${MAX_ROOT_RTT}"
    "--unwindset;init_rec.0:${MAX_AUX_REC}"
  )

  set(cbmc_defines_list
    "-DCBMC"
    "-DDISABLE_COMPILER_ASSERT"
    "-DDISABLE_SET_MEMBER"
    "-DGRANULE_SHIFT=${GRANULE_SIZE_SHIFT}"
    "-DXLAT_GRANULARITY_SIZE_SHIFT=${GRANULE_SIZE_SHIFT}"
    "-DGRANULE_SIZE=${GRANULE_SIZE}"
    "-DRMM_MAX_GRANULES=${MAX_NUM_OF_GRANULE}"
    "-DMAX_CPUS=1"
    "-DMAX_RTT_LEVEL=${MAX_RTT_UNWIND}"
    "-DMEASUREMENT_SLOT_NR=${MEASUREMENT_SLOT_NR}"
    "-DMAX_MEASUREMENT_SIZE=${MAX_MEASUREMENT_SIZE}"
    "-DRPV_SIZE=${RPV_SIZE}"
    "-DATTEST_CHALLENGE_SIZE=${ATTEST_CHALLENGE_SIZE}"
  )

  # CBMC flags for memory safety analysis and undefined behaviour analysis.
  set(cbmc_analysis_flags_list
    "--bounds-check"
    "--pointer-check"
    "--div-by-zero-check"
    "--signed-overflow-check"
    "--unsigned-overflow-check"
    "--pointer-overflow-check"
    "--conversion-check"
    "--undefined-shift-check"
    "--float-overflow-check"
    "--nan-check"
    "--enum-range-check"
    "--pointer-primitive-check"
    "--memory-leak-check")

  set(cbmc_flags_list
    "--c11"
    "--timestamp;wall"
    "--verbosity;9"
    # Optimisation flags:
    "--drop-unused-functions"
    "--reachability-slice"
    )

  if("${RMM_CBMC_CONFIGURATION}" STREQUAL "COVER")
    list(APPEND cbmc_flags_list
      "--cover;cover"
      "--no-assertions")
  elseif("${RMM_CBMC_CONFIGURATION}" STREQUAL "ASSERT")
    list(APPEND cbmc_flags_list
      "--unwinding-assertions"
      "--trace"
      "--trace-show-function-calls")
  elseif("${RMM_CBMC_CONFIGURATION}" STREQUAL "ANALYSIS")
    list(APPEND cbmc_flags_list
      "--unwinding-assertions"
      "${cbmc_analysis_flags_list}")
  else()
    message(FATAL_ERROR "Invalid RMM_CBMC_CONFIGURATION '${RMM_CBMC_CONFIGURATION}'")
  endif()

  #
  # Execute CBMC on the testbench files
  #

  rmm_cbmc_write_summary_header()

  foreach(testbench_file ${testbench_files})

    string(REPLACE ${RMM_TESTBENCH_DIR}/ "" testbench_filename ${testbench_file})
    string(REGEX REPLACE "\\.[^\\.]*$" "" entry_point "${testbench_filename}")

    set(cmd
      ${RMM_CBMC_PATH}
      ${cbmc_flags_list}
      ${cbmc_analysis_flags_list}
      "--function;${entry_point}"
      ${rmm_implementation_includes}
      ${cbmc_unwinds_list}
      ${cbmc_defines_list}
      ${rmm_implementation_srcs}
      ${testbench_file})

    # Set the names of output files
    string(REPLACE ${RMM_TESTBENCH_DIR} ${RMM_TESTBENCH_RESULT_DIR} output_file ${testbench_file})
    set(error_file ${output_file})
    set(cmd_file ${output_file})
    string(APPEND output_file ".${CBMC_RESULT_FILE_SUFFIX}" ".output")
    string(APPEND error_file ".${CBMC_RESULT_FILE_SUFFIX}" ".error")
    string(APPEND cmd_file ".${CBMC_RESULT_FILE_SUFFIX}" ".cmd")

    # remove the absolute path making it relative
    string (REPLACE "${CMAKE_SOURCE_DIR}/" "" cmd "${cmd}")
    # replace the ; with space
    string (REPLACE ";" " " CMD_STR "${cmd}")
    # add double quotes
    string (REPLACE "\"" "\\\"" CMD_STR "${CMD_STR}")
    # escape parentheses
    string (REPLACE "(" "\"(" CMD_STR "${CMD_STR}")
    string (REPLACE ")" ")\"" CMD_STR "${CMD_STR}")
    file(WRITE ${cmd_file} "${CMD_STR}")

    execute_process(COMMAND ${CMAKE_COMMAND} -E echo_append "CBMC: ${testbench_file}... ")
    execute_process(
		    COMMAND ${cmd}
		    RESULT_VARIABLE res_var
		    OUTPUT_FILE ${output_file}
		    ERROR_FILE ${error_file}
		    )

    execute_process(COMMAND ${CMAKE_COMMAND} -E echo "DONE")

    rmm_cbmc_append_summary("${testbench_filename}" "${output_file}")

  endforeach()
  message(STATUS "Result in ${RMM_TESTBENCH_RESULT_DIR}")

endif() # RMM_CBMC_STATIC_ANALYSIS
