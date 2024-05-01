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
for instructions on how to get the tool up and running. In particular, for
development with RME enabling Linux in Normal World, please refer to the
`3 world configuration`_. In case that the Secure World also needs to be
included, please refer to the `4 world configuration`_

Setup
_____

In order to use the configurations defined in |RMM|, it is essential to
configure the ``${SHRINKWRAP_CONFIG}`` environment variable to point to the
absolute path for ``<RMM_ROOT>/tools/shrinkwrap/configs`` directory so the tool
can locate the config yaml files.

    .. code-block:: shell

      export SHRINKWRAP_CONFIG=${RMM_ROOT_DIR}/tools/shrinkwrap/configs

It is also recommended to override the default ``${SHRINKWRAP_BUILD}`` and
``${SRHINKWRAP_PACKAGE}`` environment variables to a known workspace directory,
as shown below:

    .. code-block:: shell

      export WORKSPACE=${HOME}/workspace
      export SHRINKWRAP_BUILD=${WORKSPACE}
      export SHRINKWRAP_PACKAGE=${SHRINKWRAP_BUILD}/package

When building, Shrinkwrap will store the sources inside
``${SHRINKWRAP_BUILD}/source/<CONFIG_NAME>`` and the build artifacts and
packages will be stored inside ``${SHRINKWRAP_BUILD}/build/<CONFIG_NAME>`` and
``${SHRINKWRAP_PACKAGE}`` directories respectively.

.. note::

      By default, if ${SHRINKWRAP_BUILD} and ${SRHINKWRAP_PACKAGE} are not
      specified, Shrinkwrap will use the ``${HOME}/.shrinkwrap`` as default
      value for ${SHRINKWRAP_BUILD}. It is only necessary to overwrite the
      environment variables in the case it is needed to build in a different
      location.

.. _3_world_testing:

3-World testing
_______________

|RMM| provides a number of overlays that can be used in conjunction with some
of the configurations provided by default by Shrinkwrap. One of the overlays,
specifically ``rmm.yaml``, can be used along with the ``cca-3world.yaml`` to
build a 3 World demonstrator using the ``master`` branch on |TF-A| and the
local |RMM| repository.

As an example, the following command line would build the 3-World demonstrator.
It assumes that Shrinkwrap is called from within the ``<RMM_ROOT>`` directory:

    .. code-block:: shell

       shrinkwrap build cca-3world.yaml --overlay=buildroot.yaml --overlay=./tools/shrinkwrap/common/layers/rmm.yaml --btvar=GUEST_ROOTFS='${artifact:BUILDROOT}' --btvar=RMM_SRC=${PWD} --no-sync=rmm

To run the demonstrator, use the following command:

    .. code-block:: shell

       shrinkwrap build cca-3world.yaml -rtvar=ROOTFS=${SHRINKWRAP_PACKAGE}/cca-3world/rootfs.ext2

You can find further instructions on how to use this configuration on the
`3 world configuration`_ documentation.

Testing RMM with |TFTF|
_______________________

|RMM| provides a configuration that brings together a software stack to test CCA
using Arm RME extension and utilizing `TF-A-Tests`_. The main Test payload in
TF-A-Tests is the |TFTF| binary. In this config, |TF-A| is in Root World, |RMM|
is in Realm EL2 and |TFTF| is in Normal World.

For further documentation about this configuration, you can check the docs through

    .. code-block:: shell

      shrinkwrap inspect rmm-tftf.yaml

The build and run commands can also be found in the documentation of the config
yaml file. When invoking the ``build`` command, Shrinkwrap will store the
external repositories inside the ``${SHRINKWRAP_BUILD}/sources/<CONFIG_NAME>``
directory.

Overlays
________

Overlays can be used to extend the functionality of a configuration by
overwriting both build and runtime settings. They can be used on any configuration
and they can be combined in any way needed.

In order to use an overlay, they need to be specified on the command line, through
the ``--overlay`` keyword, as follows:

    .. code-block:: shell

      shrinkwrap --runtime=null build rmm-tftf.yaml --btvar=RMM_SRC=${PWD} --overlay=<PATH_TO_OVERLAY> --no-sync-all

The path to the overlay can be relative to where Shrinwrap is called from and you
can use as many ``--overlay`` statements as needed.

Overlays are stored in the ``<RMM_ROOT_DIR>/tools/shrinkwrap/common/layers`` directory.

The available Overlays are sumarized in the next table

.. csv-table::
   :header: "Overlay", "Description"
   :widths: 2 8

   model-enable-lpa2.yaml,Overlay used to enable ``FEAT_LPA2`` on the |FVP| model at run time. In addition this overlay also sets the ``PA_SIZE`` on the model to 52
   model-wait-debugger.yaml,Overlay to configure the |FVP| model to listen for Iris connections on port 7100 and make it wait until a debugger is connected before starting execution
   rmm-debug.yaml,Overlay to build |RMM| (as well as |TF-A|) in debug mode
   clean.yaml,Overlay used to avoid an exception with ``Shrinkwrap clean`` in which a path with a valid format needs to be specified for |RMM|

Example of use
~~~~~~~~~~~~~~

Below is an example on how to use use one of the available overlays with the
existing configuration. The example uses the native toolchain (without the
Docker container) to build the artifacts and prevent Shrinkwrap from updating/cleaning
the repositories:

    .. code-block:: shell

       shrinkwrap --runtime=null build rmm-tftf.yaml --overlay=./tools/shrinkwrap/common/layers/model-enable-lpa2.yaml --btvar=RMM_SRC=${PWD} --no-sync-all

Then you run your tests with

    .. code-block:: shell

       shrinkwrap --runtime=null run rmm-tftf.yaml

-----

.. _Shrinkwrap: https://shrinkwrap.docs.arm.com
.. _Quick Start Guide: https://shrinkwrap.docs.arm.com/en/latest/userguide/quickstart.html#quick-start-guide
.. _3 world configuration: https://shrinkwrap.docs.arm.com/en/latest/userguide/configstore/cca-3world.html
.. _4 world configuration: https://shrinkwrap.docs.arm.com/en/latest/userguide/configstore/cca-4world.html
.. _TF-A-Tests: https://trustedfirmware-a-tests.readthedocs.io/en/latest/index.html
.. _btvar: https://shrinkwrap.docs.arm.com/en/latest/userguide/configmodel.html#defined-macros
.. _rtvar: https://shrinkwrap.docs.arm.com/en/latest/userguide/configmodel.html#defined-macros
