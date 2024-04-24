.. SPDX-License-Identifier: BSD-3-Clause
.. SPDX-FileCopyrightText: Copyright TF-RMM Contributors.

********
CPPCheck
********

CppCheck is an open source static analysis tool for C/C++.

It also has an addon to verify compliance with MISRA C 2012.

CppCheck can be run standalone or along with MISRA addon. Please refer `CPPCheck Project Page`_ for details.

TF-RMM codebase aims to have 0 outstanding CPPCheck errors with the recommended version mentioned :ref:`here<tool_dependencies>`. 

Installing CPPCheck
===================

Please refer to `CPPCheck GitHub`_ for downloading recommended version and build guidelines.

Add CPPCheck and CPPCheck-htmlreport to PATH.

htmlreport converts XML output into user friendly html report.

.. code-block:: bash

        export PATH=$cppcheck_root/build/bin:$cppcheck_root/htmlreport:$PATH
        cppcheck --version

Invoking cppcheck rule within TF-RMM build system
=================================================

Build instructions for running CPPCheck on TF-RMM using cmake.

If you have misra.rules file copy in $rmm_root/tools/cppcheck/misra.rules
to get error messages.

.. code-block:: bash

        cd $rmm_root        
        cmake -DRMM_CONFIG=fvp_defcfg -S . -B build  -DCMAKE_EXPORT_COMPILE_COMMANDS=ON
        cmake --build build -- cppcheck

This will generate cppcheck.xml in build/tools/cppcheck folder

Build instructions for running CPPCheck with MISRA on TF-RMM using cmake

.. code-block:: bash

        cd $rmm_root
        cmake -DRMM_CONFIG=fvp_defcfg -S . -B build  -DCMAKE_EXPORT_COMPILE_COMMANDS=ON
        cmake --build build -- cppcheck-misra

This will generate cppcheck_misra.xml in build/tools/cppcheck folder

Running CPPCheck-htmlreport
===========================

Generate html report in current directory.

.. code-block:: bash

        cppcheck-htmlreport --file=./build/tools/cppcheck/cppcheck_misra.xml --report-dir=test --source-dir=.

See ./test/index.html for report

CPPCheck Error Suppressions
===========================

In case if errors are false positive, it can be suppressed using one of below method.

suppression.txt
---------------

Add to Suppression.txt in tools/cppcheckeck directory

.. code-block:: bash

        [error id]:[filename]:[line]
        [Uninitvar, arrayIndexOutOfBounds]:*/file.c:10
        *:*/ext/*  ;exclude folder

Inline Suppression
------------------

Suppression can be added directly to code.

.. code-block:: bash

        /* cppcheck-suppress uninitvar */
        /* cppcheck-suppress [arrayIndexOutOfBounds, uninitvar] */
        /* cppcheck-suppress-begin uninitvar*/
        /* cppcheck-suppress-end uninitvar*/

.. _CPPCheck Project Page: https://cppcheck.sourceforge.io/
.. _CPPCheck GitHub: https://github.com/danmar/cppcheck
