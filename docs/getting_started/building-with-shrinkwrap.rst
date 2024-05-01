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
development, please refer to the `3 world configuration`_.

Configs
_______

|RMM| provides a number of Shrinkwrap Configs to aid development and verification
utilizing different software stacks. The below configs assume that |RMM| source
code is located inside ``<RMM_ROOT_DIR>`` and the configs can be found in
``<RMM_ROOT_DIR>/tools/shrinkwrap/configs``.

The available configs are described in the following subsections.

rmm-tftf.yaml
~~~~~~~~~~~~~

This config brings together a software stack to test CCA using Arm RME extension
utilizing `TF-A-Tests`_. The main Test payload in TF-A-Tests is the |TFTF|
binary. In this config, |TF-A| is in Root World, |RMM| is in Realm EL2 and
|TFTF| is in Normal World.

For further documentation about this Config, you can check the docs through

    .. code-block:: bash

      shrinkwrap inspect rmm-tftf.yaml

.. note::

    For the above command to work, you might need to configure the env variable
    ``${SHRINKWRAP_CONFIG}`` to point to ``<RMM_ROOT>/tools/shrinkwrap/configs``
    directory so the tool can locate the config yaml files.

Overlays
________

Overlays can be used to extend the functionality of a Config by overwriting both
build and runtime settings. They can be used on any Config and they can be combined
in any way needed.

In order to use an overlay, they need to be specified on the command line, through
the ``--overalay`` keyworkd, as follows:

    .. code-block:: bash

      shrinkwrap --runtime=null build rmm-tftf.yaml --btvar=RMM_SRC=${PWD} --overlay=<PATH_TO_OVERLAY> --no-sync-all

.. note::

    When working with Overlays, you will need to specify the same overlays during
    the run phase as well as during the build phase.

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

-----

.. _Shrinkwrap: https://shrinkwrap.docs.arm.com
.. _Quick Start Guide: https://shrinkwrap.docs.arm.com/en/latest/userguide/quickstart.html#quick-start-guide
.. _3 world configuration: https://shrinkwrap.docs.arm.com/en/latest/userguide/configstore/cca-3world.html
.. _TF-A-Tests: https://trustedfirmware-a-tests.readthedocs.io/en/latest/index.html
.. _btvar: https://shrinkwrap.docs.arm.com/en/latest/userguide/configmodel.html#defined-macros
.. _rtvar: https://shrinkwrap.docs.arm.com/en/latest/userguide/configmodel.html#defined-macros
