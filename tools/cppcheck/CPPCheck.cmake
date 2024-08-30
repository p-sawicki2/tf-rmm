#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

find_program(RMM_CPPCHECK_EXE "cppcheck" DOC "Path to Cppcheck")

if(NOT RMM_CPPCHECK_EXE)
  message(FATAL_ERROR "Could not find cppcheck executable.")
else()
  message(cppcheck_path: "${RMM_CPPCHECK_EXE}")
  execute_process(COMMAND ${RMM_CPPCHECK_EXE} --version
			OUTPUT_VARIABLE CPPCHECK_VERSION)
  message(cppcheck_version: "${CPPCHECK_VERSION}")
  set(CPPCHECK_MIN "2.14")
endif()

#
# Set up checkers.
#
set(cppcheck-flags)

list(APPEND cppcheck-flags "--enable=all")
list(APPEND cppcheck-flags "--xml")
list(APPEND cppcheck-flags "--xml-version=2")
list(APPEND cppcheck-flags "--template=gcc")
list(APPEND cppcheck-flags "--check-level=exhaustive")

if(CPPCHECK_MISRA)
    list(APPEND cppcheck-flags "--addon=${SOURCE_DIR}/tools/cppcheck/misra.json")
    set(CPPCHECK_OUTPUT "${BUILD_DIR}/tools/cppcheck/cppcheck_misra.xml")
    set(CPPCHECK_BUILD_DIR "${BUILD_DIR}/tools/cppcheck/dump_misra")
else()
    set(CPPCHECK_OUTPUT "${BUILD_DIR}/tools/cppcheck/cppcheck.xml")
    set(CPPCHECK_BUILD_DIR "${BUILD_DIR}/tools/cppcheck/dump")
endif()

list(APPEND cppcheck-flags "--output-file=${CPPCHECK_OUTPUT}")
list(APPEND cppcheck-flags "--cppcheck-build-dir=${CPPCHECK_BUILD_DIR}")

#
# Exclude files or directories we don't want to receive warnings about.
#
list(APPEND cppcheck-flags "-i${SOURCE_DIR}/ext/")
list(APPEND cppcheck-flags "-i${SOURCE_DIR}/lib/libc")

#
# If you want to suppress specific files without using an inline suppression,
# do it in `suppressions.txt`.
#
list(APPEND cppcheck-flags
    "--inline-suppr" # Allow inline suppressions
    "--suppressions-list=${SOURCE_DIR}/tools/cppcheck/suppressions.txt")

#
# Configure the platform file. This communicates certain implementation details to
# Cppcheck and avoid false positives.
#
set(toolchain-xml
    "${SOURCE_DIR}/tools/cppcheck-aarch64-platform.xml")

list(APPEND cppcheck-flags "--platform=${toolchain-xml}")
set(COMPILE_COMMANDS_FILE "${BUILD_DIR}/compile_commands.json")
if(NOT EXISTS "${COMPILE_COMMANDS_FILE}")
    message(FATAL_ERROR "Please configure with -DCMAKE_EXPORT_COMPILE_COMMANDS=ON.")
endif()

find_package(Python3 REQUIRED)
find_program(CPPCHECK_XML_EXEC "parse_cppcheck_xml.py"
  PATHS ${SOURCE_DIR}
  PATH_SUFFIXES tools/cppcheck
  DOC "Path to parse_cppcheck_xml.py"
)

#
# Create the output directory
#
file(MAKE_DIRECTORY "${CPPCHECK_BUILD_DIR}")

set(EXE_CPPCHECK_TWICE)

#
# Workaround for "internal errors" reported for cppcheck-misra.
# Run CPPCheck 2nd time if the output file is not created.
#
if(CPPCHECK_MISRA AND (NOT EXISTS "${CPPCHECK_OUTPUT}"))
    set(EXE_CPPCHECK_TWICE 1)
endif()

execute_process(
    WORKING_DIRECTORY ${SOURCE_DIR}
    COMMAND ${RMM_CPPCHECK_EXE}
      --project=${COMPILE_COMMANDS_FILE} ${cppcheck-flags}
    )

if(EXE_CPPCHECK_TWICE)
    execute_process(
        WORKING_DIRECTORY ${SOURCE_DIR}
        COMMAND ${RMM_CPPCHECK_EXE}
          --project=${COMPILE_COMMANDS_FILE} ${cppcheck-flags}
    )
endif()

execute_process(
    WORKING_DIRECTORY ${SOURCE_DIR}
    COMMAND  ${Python3_EXECUTABLE} ${CPPCHECK_XML_EXEC} ${CPPCHECK_OUTPUT} ${CPPCHECK_BUILD_DIR}
    OUTPUT_VARIABLE cppcheck_errors
    RESULT_VARIABLE cppcheck_version
)

if(${cppcheck_version} GREATER 0)
  message(FATAL_ERROR "Cppcheck failed with error count: ${cppcheck_errors}")
else()
  message(WARNING "cppcheck version installed is : ${CPPCHECK_VERSION}, but minimum required version is ${CPPCHECK_MIN}")
endif()

