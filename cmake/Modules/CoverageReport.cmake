#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

macro(check_and_append_c_coverage_flags)
  # Store a copy of CMAKE_C_FLAGS
  set(CMAKE_C_FLAGS_BACKUP "${CMAKE_C_FLAGS}")

  foreach(flag ${ARGN})
    string(REPLACE "-" "_" flag_no_hyphen ${flag})
    check_c_compiler_flag("-${flag}" COVERAGE_C_FLAG_${flag_no_hyphen})
      if (COVERAGE_C_FLAG_${flag_no_hyphen})
      set(COVERAGE_SUPPORTED BOOL "1")

      # Some of the coverage flags depend on the previous ones being
      # enabled, so add them to the C Flags now for the next check.
      string(APPEND CMAKE_C_FLAGS " -${flag}")
      string(APPEND COVERAGE_C_FLAGS " -${flag}")
    endif (COVERAGE_C_FLAG_${flag_no_hyphen})
  endforeach(flag)

  # Restore CMAKE_C_FLAGS
  set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS_BACKUP}")
endmacro(check_and_append_c_coverage_flags)

macro(check_and_append_cxx_coverage_flags)
  # Store a copy of CMAKE_CXX_FLAGS
  set(CMAKE_CXX_FLAGS_BACKUP "${CMAKE_CXX_FLAGS}")

  foreach(flag ${ARGN})
    string(REPLACE "-" "_" flag_no_hyphen ${flag})
    check_cxx_compiler_flag("-${flag}" COVERAGE_CXX_FLAG_${flag_no_hyphen})
    if (COVERAGE_CXX_FLAG_${flag_no_hyphen})

      # Some of the coverage flags depend on the previous ones being
      # enabled, so add them to the CXX Flags now for the next check.
      string(APPEND CMAKE_CXX_FLAGS " -${flag}")
      string(APPEND COVERAGE_CXX_FLAGS " -${flag}")
    endif (COVERAGE_CXX_FLAG_${flag_no_hyphen})
  endforeach(flag)

  # Restore CMAKE_CXX_FLAGS
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS_BACKUP}")
endmacro(check_and_append_cxx_coverage_flags)

if((${RMM_COVERAGE} STREQUAL "ON" OR
    ${RMM_COVERAGE} STREQUAL "TRUE") AND
    RMM_UNITTESTS)

  find_program(GCOVR_EXECUTABLE "gcovr" DOC "Path to gcovr")

  if(${GCOVR_EXECUTABLE} STREQUAL "GCOVR_EXECUTABLE-NOTFOUND")
      message (WARNING "gcovr executable not found. Coverage tests disabled")
  else()
    include(CheckCCompilerFlag)
    include(CheckCXXCompilerFlag)

    # List of coverage flags to test on the toolchain
    set(COVERAGE_FLAGS
        -coverage
        ftest-coverage
        fprofile-instr-generate
        fprofile-arcs
        fcoverage-mapping)

    check_and_append_c_coverage_flags(${COVERAGE_FLAGS})
    check_and_append_cxx_coverage_flags(${COVERAGE_FLAGS})

    # If coverage is not supported by the C compiler, or the C and C++
    # compilers do not support the same set of coverage flags (which can
    # lead to link problems), abort.
    if (COVERAGE_SUPPORTED AND (COVERAGE_C_FLAGS STREQUAL COVERAGE_CXX_FLAGS))
      # Setup flags for coverage
      foreach(language in ITEMS C CXX)
        string(APPEND CMAKE_${language}_FLAGS " ${COVERAGE_${language}_FLAGS} ")
      endforeach()

      # Create a directory for the coverage results,
      # if it doesn't exist yet.
      set(COVERAGE_DIRECTORY "${CMAKE_BINARY_DIR}/Testing/${CMAKE_BUILD_TYPE}/coverage")
      file(MAKE_DIRECTORY "${COVERAGE_DIRECTORY}")

      set(COVERAGE_OUTPUT "${COVERAGE_DIRECTORY}/${COVERAGE_REPORT_NAME}")

      if(${RMM_HTML_COV_REPORT} STREQUAL "ON" OR
          ${RMM_HTML_COV_REPORT} STREQUAL "TRUE")
          set(HTML_REPORT --html-details ${COVERAGE_OUTPUT}.html)
      endif()

      #
      # Rules for coverage tests
      #
      add_custom_target(coverage-report
                        COMMAND ${GCOVR_EXECUTABLE}
                                ${GCOV_EXECUTABLE}
                                --exclude "'((.+)ext(.+))|((.+)CMakeFiles(.+)\..)|((.+)\.cpp)|((.+)test(.+))'"
                                -r ${CMAKE_SOURCE_DIR}
                                -x ${COVERAGE_OUTPUT}.xml
                                ${HTML_REPORT}
                                ${CMAKE_BINARY_DIR}
                        DEPENDS run-unittests)
    else()
      message(WARNING "Toolchain does not support Coverage analysis")
    endif() # COVERAGE_SUPPORTED
  endif() # GCOVR_EXECUTABLE
endif() # RMM_COVERAGE
