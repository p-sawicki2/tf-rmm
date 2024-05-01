.. SPDX-License-Identifier: BSD-3-Clause
.. SPDX-FileCopyrightText: Copyright TF-RMM Contributors.

Using Shrinkwrap with RMM
*************************

This document explains how to build and run |RMM| in |FVP|, including all
necessary firmware images, by using `Shrinkwrap`_.

Introduction
____________

`Shrinkwrap`_ is a tool that helps to simplify the process of building and
running firmware on Arm |FVP| by providing an intuitive command line interface
frontend and (by default) a container-based backend.

Shrinkwrap works by using *Configs*, which are defined in YAML and can be easily
extended using a built-in layering system.

For further information on Shrinkwrap, you can refer to the `Quick Start Guide`_
for instructions on how to get the tool up and running. In particular, for |RMM|
development, please refer to the `3 word configuration`_.

Configs
_______

|RMM| provides a number of Shrinkwrap Configs. These configs can be found in
``<RMM_ROOT_DIR>/tools/shrinkwrap/configs``.

The available Configs are described in the following subsections.

rmm-tftf.yaml
~~~~~~~~~~~~~

This Config Brings together a software stack to test CCA using Arm RME extension
utilizing `TF-A-Tests`_. The main Test payload in TF-A-Tests is the |TFTF|
binary. in this config, |TF-A| is in Root World, |RMM| is in Realm EL2 and
|TFTF| is in Normal World.

The Config pulls |TF-A| and |TFTF| repositories on the Shrinkwrap working
directory (defined through the environment variable ``${SHRINKWRAP_BUILD}``)
whilst using the local |RMM| repository to build, so this can be used for |RMM|
development.

By default, it is expected that the |RMM| source code is located inside the
``<RMM_ROOT_DIR>`` directory. Also, although Shrinkwrap can be called from
anywhere in the filesystem (provided that ``${SHRINKWRAP_CONFIG}`` variable is
properly configured), the following subsections  will assume that it is always
called from ``<RMM_ROOT_DIR>``.

Build-Time Variables
====================

.. csv-table::
   :header: "`btvar`_", "Default", "Description", "Notes"
   :widths: 2 3 4 4

   RMM_LOG_LEVEL,``40``,Determines the TF-RMM log level,Inherited from *rmm.yaml* layer overlay
   TFA_REVISION,``master``,TF-A Branch/SHA to pull on build,Inherited from *tftf.yaml* layer overlay
   TFTF_REVISION,``master``,TFTF Branch/SHA to pull on build,Interited from *tftf.yaml* layer overlay

Run-Time Variables
====================

.. csv-table::
   :header: "`rtvar`_", "Default", "Description", "Notes"
   :widths: 2 3 4 4

   BL1,``${artifact:BL1}``,Path to the BL1 image to load on the model,Inherited from *tftf.yaml* layer overlay
   FIP,``${artifact:FIP}``,Path to the FIP image to load on the model,Inherited from *tftf.yaml* layer overlay

Usage
=====

Setup
-----

In order to use this Config, the ``SHRINKWRAP_BUILD``, ``SHRINKWRAP_PACKAGE``
and ``SHRINKWRAP_CONFIG`` environment variables must be set. |RMM| source code
is expected to be stored in ``${SHRINKWRAP_BUILD}``. Assuming you have not yet
downloaded |RMM|, you can proceed as shown on the example below:

    .. code-block:: bash

      export WORKSPACE=${HOME}/workspace
      export SHRINKWRAP_BUILD=${WORKSPACE}
      export SHRINKWRAP_PACKAGE=${SHRINKWRAP_BUILD}/package
      export SHRINKWRAP_CONFIG=${WORKSPACE}/tf-rmm/tools/shrinkwrap/configs

      mkdir -p ${SHRINKWRAP_BUILD}
      cd ${SHRINKWRAP_BUILD}

Then you can download |RMM| as explained on :ref:`getting_started_get_source`

Note that in the case you build and run natively on the development machine
(thus build and run without using Shrinkwrap containers), you also need to
manually setup your toolchain as well as |FVP|, including any needed plugin.
See :ref:`getting_started_toolchain` for more information.

Basic build
-----------

The following example shows how to run a basic build with the default settings
natively on the host machine (without containers). The example will download
all the necessary repositories (|TF-A| and |TFTF|) whilst keeping the |RMM|
sources intact.

    .. code-block:: bash

      shrinkwrap --runtime=null build rmm-tftf.yaml --no-sync=rmm

.. note::

    At the time of writing this document, the default behaviour of shrinkwrap
    when using the ``build`` command is to reset all the repositories to
    the branch/SHA configured by default on the Config. This will cause that any
    change made on the respositories will be lost unless the *--no-sync* option
    is passed on the command line. For more information on the use of
    *--no-sync* and *--no-sync-all* options, you can run ``shrinkwrap build --help``
    or check the `Shrinkwrap`_ documentation.

.. note::
    It is recommended that the first time you build you use the above command
    in order to pull all the necessary repositories. On subsequent builds, and
    specially if you made changes to any of the repositories, you will need to
    ensure that you don't re-sync the repos and loose all the changes by the use
    of the ``no-sync-all`` option as described above.

When invoking the ``build`` command, Shrinkwrap stores the external repositores
inside the ``${SHRINKWRAP_BUILD}/source/<CONFIG_NAME>`` directory.

Specifying ``LOG_LEVEL`` on RMM
-------------------------------

This is an example on how to setup a ``btvar`` available on the Config.
RMM LOG_LEVEL is controlled by ``RMM_LOG_LEVEL`` btbar.

    .. code-block:: bash

      shrinkwrap --runtime=null build rmm-tftf.yaml --btvar=RMM_LOG_LEVEL=50 --no-sync-all

Run the model
-------------

    .. code-block:: bash

      shrinkwrap --runtime=null run rmm-tftf.yaml

In order to stop the model, you need to press ``ctrl + ]``

Clean the build
---------------

This action is recommended when rebuilding after adding changes to any repository
or when trying different configurations, including run configurations.

    .. code-block:: bash

      shrinkwrap --runtime=null clean rmm-tftf.yaml

.. note::

    Shrinkwrap supports incremental build, however when trying different
    configurations (for instance, using different values for ``${RMM_LOG_LEVEL}``
    or even using different run overlays for the model), it is recommended that
    we clean and rebuild to avoid errors.

Overlays
________

Overlays can be used to extend the functionality of a Config by overwriting both
build and runtime settings. They can be used on any Config and they can be combined
in any way needed.

In order to use an overlay, they need to be specified on the command line, through
the ``--overalay`` keyworkd, as follows:

    .. code-block:: bash

      shrinkwrap --runtime=null build rmm-tftf.yaml --overlay=<PATH_TO_OVERLAY> --no-sync-all

.. note::

    When working with Overlays, you will need to specify the same overlays during
    the run phase as well as during the build phase.

The path to the overlay can be relative to where Shrinwrap is called from and you
can use as many ``--overlay`` statements as needed.

Overlays are stored in the ``<RMM_ROOT_DIR>/tools/shrinkwrap/common/layers`` directory.

The available Overlays are listed in the next subsections.

``model-enable-cache.yaml``
~~~~~~~~~~~~~~~~~~~~~~~~~~~

Overlay used to enable Cache Modeling on the |FVP| model at run time.

Build-Time Variables
====================

None

Run-Time Variables
==================

None

``model-enable-lpa2.yaml``
~~~~~~~~~~~~~~~~~~~~~~~~~~

Overlay used to enable ``FEAT_LPA2`` on the |FVP| model at run time. In addition,
this overlay also sets the ``PA_SIZE`` on the model to 52 bits.

Build-Time Variables
====================

None

Run-Time Variables
==================

None

``model-wait-debugger.yaml``
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Overlay to configure the |FVP| model to listen for Iris connections on port 7100
and make it wait until a debugger is connected before starting the execution.

Build-Time Variables
====================

None

Run-Time Variables
==================

None

``rmm-debug.yaml``
~~~~~~~~~~~~~~~~~~

Overlay to build |RMM| in Debug mode.

Build-Time Variables
====================

None

Run-Time Variables
==================

None

-----

.. _Shrinkwrap: https://shrinkwrap.docs.arm.com
.. _Quick Start Guide: https://shrinkwrap.docs.arm.com/en/latest/userguide/quickstart.html#quick-start-guide
.. _3 word configuration: https://shrinkwrap.docs.arm.com/en/latest/userguide/configstore/cca-3world.html
.. _TF-A-Tests: https://trustedfirmware-a-tests.readthedocs.io/en/latest/index.html
.. _btvar: https://shrinkwrap.docs.arm.com/en/latest/userguide/configmodel.html#defined-macros
.. _rtvar: https://shrinkwrap.docs.arm.com/en/latest/userguide/configmodel.html#defined-macros
