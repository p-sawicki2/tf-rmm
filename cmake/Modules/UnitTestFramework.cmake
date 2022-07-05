#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

#[=======================================================================[.rst:
rmm_build_unittest
------------------

.. default-domain:: unit tests

.. command:: rmm_build_unittest

Build a unit test group for a given target

.. code:: cmake

    rmm_build_unittest(NAME <name> TARGET <target> SOURCES <sources>
                       [FORCED]
                       [RUN_ISOLATED_TESTS <LIST of tests to run>]
                       [LIBRARIES <libraries_to_link>]
                       [ITERATIONS <iterations>])

This helper function simplifies the mechanics to setup and enable an unit test.

Basics
^^^^^^

Every unit test configuration has the following parameters (defined as
strings):

- ``NAME`` Name of the test. It must match the name of the CppUtest test group.
- ``TARGET`` Target where the tests will be linked against.
- ``SOURCES`` Source files for the tests. This is usually a single C++ file.
- ``FORCED`` Ignore the RMM_SKIP_UNITTESTS flag and adds the unittest into the
             list of runnable unittests. This parameter must only be used
             during the development of a new feature and/or its companion
             unittest in combination with RMM_SKIP_UNITTESTS build flag
             so run-unittests target will only run forced tests by default
             rather than every unittest. This allows to get a coverage report
             focused only on specific tests and therefore its output will not
             be biased by unrelated tests. Hence this parameter helps on ensure
             that a test group effectively exercises its target API.
             This option must be disabled on production.
- ``RUN_ISOLATED_TESTS`` Optional parameter that specifies a list of tests
                         implemented within ``SOURCES`` to be run. When this
                         list is specified, the binary is re-spawned for each
                         test and only executed once (``ITERATIONS`` is
                         ignored). Any test not included on the list will be
                         ignored.
                         If this parameter is not used, all the tests included
                         in the group will be run automatically by CppUTest,
                         the number of times specified by ``ITERATIONS``
- ``LIBRARIES`` Optional parameter to define libraries to link against
                the tests.
- ``ITERATIONS`` Optional parameter that defines how many times the test will
                 run. By default it is 1 times.
                 This option is ignored when using ``RUN_ISOLATED_TESTS``

#]=======================================================================]

include("${CMAKE_SOURCE_DIR}/cmake/BuildCppUTest.cmake")

# Flag variable to notify that the unit tests are enabled
SET(RMM_UNITTESTS "ON" CACHE INTERNAL "RMM_UNITTESTS")

# Clean ${IMPORT_TEST_GROUPS}, used to generate test_groups.h later.
SET(IMPORT_TEST_GROUPS "" CACHE INTERNAL "IMPORT_TEST_GROUP List")

enable_testing()

#
# Custom target to run the unit tests
#
add_custom_target(run-unittests
    WORKING_DIRECTORY "${CMAKE_BINARY_DIR}"
    COMMAND ctest
)

function(rmm_build_unittest)

    set(_options "FORCED")
    set(_multi_args "SOURCES;LIBRARIES;RUN_ISOLATED_TESTS")
    set(_single_args "NAME;TARGET;ITERATIONS")

    cmake_parse_arguments(
        arg "${_options}" "${_single_args}" "${_multi_args}" ${ARGN})

    if("NAME" IN_LIST arg_KEYWORDS_MISSING_VALUES OR
        NOT DEFINED arg_NAME)
        message(FATAL_ERROR "Missing unit test name")
    endif()

    if("TARGET" IN_LIST arg_KEYWORDS_MISSING_VALUES OR
        NOT DEFINED arg_TARGET)
        message(FATAL_ERROR "Missing test target")
    endif()

    if("SOURCES" IN_LIST arg_KEYWORDS_MISSING_VALUES OR
        NOT DEFINED arg_SOURCES)
        message(FATAL_ERROR "Missing test sources")
    endif()

    if("ITERATIONS" IN_LIST arg_KEYWORDS_MISSING_VALUES OR
        NOT DEFINED arg_ITERATIONS)
        set(arg_ITERATIONS "1")
    endif()

    if(${arg_FORCED} STREQUAL "TRUE")
        message(WARNING "FORCE mode enabled for test ${arg_NAME} must be disabled on production")
    endif()

    target_sources("${arg_TARGET}"
        PRIVATE ${arg_SOURCES})

    target_link_libraries("${arg_TARGET}"
        PRIVATE CppUTest ${arg_LIBRARIES})

    # Add the test to the CMake test builder, so we can automate
    # the test run process.
    if (${RMM_SKIP_UNITTESTS} STREQUAL "OFF" OR
        ${RMM_SKIP_UNITTESTS} STREQUAL "FALSE" OR
        ${arg_FORCED} STREQUAL "TRUE")
        if("RUN_ISOLATED_TESTS" IN_LIST arg_KEYWORDS_MISSING_VALUES OR
            NOT DEFINED arg_RUN_ISOLATED_TESTS)
            # Run all tests at once
            add_test(NAME "${arg_NAME}"
                    COMMAND ${CMAKE_BINARY_DIR}/rmm.elf
                            -g${arg_NAME}
                            -r${arg_ITERATIONS})
        else()
            # Register a test for each test case, so each one on them can
            # run on isolation.
            foreach(TEST IN LISTS arg_RUN_ISOLATED_TESTS)
                add_test(NAME "${arg_NAME}::${TEST}"
                         COMMAND ${CMAKE_BINARY_DIR}/rmm.elf
                                 -sg${arg_NAME}
                                 -sn${TEST})
            endforeach()
        endif()
    endif()

    # Use CppUtest IMPORT_TEST_GROUP macro to explicitly include the new test
    # group. This is needed as otherwise the linker will ignore the test code.
    SET(IMPORT_TEST_GROUPS "${IMPORT_TEST_GROUPS} IMPORT_TEST_GROUP(${arg_NAME});"
        CACHE INTERNAL "IMPORT_TEST_GROUP List")
    configure_file(${CMAKE_SOURCE_DIR}/plat/host/host_test/src/test_groups.h.in
                   ${CMAKE_BINARY_DIR}/plat/host/host_test/src/test_groups.h
                   @ONLY)

endfunction()
