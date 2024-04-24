.. SPDX-License-Identifier: BSD-3-Clause
.. SPDX-FileCopyrightText: Copyright TF-RMM Contributors.

********
CPPCheck
********

CppCheck is an open source static analysis tool for C/C++

It also has an addon to verify compliance with MISRA C 2012

Installing CPPCheck
===================

Recommended CPPCheck version for RMM is 2.13.4

.. code-block:: bash

        git clone https://github.com/danmar/cppcheck.git -b 2.13.x
        mkdir build
        cd build
        cmake ..
        cmake --build .
        export PATH=$cppcheck_root/build/bin:$cppcheck_root/htmlreport:$PATH
        cppcheck --version

Running CPPCheck
================

.. code-block:: bash

        cmake -DRMM_CONFIG=fvp_defcfg -S . -B build  -DCMAKE_EXPORT_COMPILE_COMMANDS=ON
        cmake --build build -- cppcheck-misra

This will generate cppcheck_misra.xml in build/tools/cppcheck folder

Running CPPCheck-htmlreport
===========================

.. code-block:: bash

        cppcheck-htmlreport --file=./build/tools/cppcheck/cppcheck_misra.xml --report-dir=test --source-dir=.

See test/index.html for report
