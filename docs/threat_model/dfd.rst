.. SPDX-License-Identifier: BSD-3-Clause
.. SPDX-FileCopyrightText: Copyright TF-RMM Contributors.

Data Flow Diagram
=================

This section describes the Data Flow Diagram for RMM.

********************
Target of Evaluation
********************

In this threat model, the target of evaluation is the Realm Manager Monitor
(RMM) for A-Class Processors, as shown on Figure 1. Everything else on Figure 1
is outside of the scope of the evaluation.

RMM can be configured in various ways. In this threat model we consider
only the most basic configuration. To that end we make the following
assumptions:

- RMM images is run from either ROM or on-chip trusted SRAM. Any memory shared
  with EL-3 Firmware is located in on-chip trusted SRAM as well. This means
  that RMM (or at least its runtime) is not vulnerable to an attacker that can
  probe or tamper with off-chip memory.

- No experimental features are enabled. We do not consider threats that may come
  from them.

*****************
Data Flow Diagram
*****************

Figure 1 shows a high-level data flow diagram for RMM. The diagram
shows a model of the different components of a RMM system and
their interactions with other FW/SW components. A description of each
diagram element is given on Table 1. On the diagram, the red broken lines
indicate trust boundaries. Components outside of the broken lines
are considered untrusted by RMM.

.. uml:: ./diagrams/rmm_dfd.puml
  :caption: Figure 1: RMM Data Flow Diagram

.. table:: Table 1: RMM Data Flow Diagram Description

  +-----------------+--------------------------------------------------------+
  | Diagram Element | Description                                            |
  +=================+========================================================+
  |       DF1       | | At boot time, EL-3 Firmware configures RMM through   |
  |                 |   paramaters sent through register x0 to x3. It also   |
  |                 | | passes a Boot Manifest using secure shared memory.   |
  |                 |   The first CPU executes the cold-boot path, whereas   |
  |                 | | the rest of the CPUs execute the warm-boot path.     |
  |                 |   Both cold and warm boots receive parameters from     |
  |                 | | EL-3 Firmware, including a boot manifest.            |
  +-----------------+--------------------------------------------------------+
  |       DF2       | | RMM log system framework outputs debug messages      |
  |                 |   over a UART interface.                               |
  +-----------------+--------------------------------------------------------+
  |       DF3       | | Debug and trace IP on a platform can allow access    |
  |                 |   to registers and memory of RMM.                      |
  +-----------------+--------------------------------------------------------+
  |       DF4       | | EL-3 Firmware uses RMI (Realm Management Interface)  |
  |                 |   to communicate with RMM. It can invoke services rom  |
  |                 | | RMM on its own as well as forward request from the   |
  |                 |   Non-Secure World (e.g. from the Rich OS).            |
  |                 | | Under some circumstances, such us during cold-boot,  |
  |                 |   RMM can start a request to EL-3 through the RMI      |
  |                 | | interface.                                           |
  +-----------------+--------------------------------------------------------+
  |       DF5       | | Realm software can interact with RMM to request      |
  |                 |   services through the RSI (Ream Service Interface).   |
  +-----------------+--------------------------------------------------------+
  |       DF6       | | Realm software needs to interact with off-chip       |
  |                 |   dynamic RAM in order to store large data structures. |
  +-----------------+--------------------------------------------------------+
  |       DF7       | | This path represents the interaction between RMM and |
  |                 |   various hardware IPs such as MMU controller and GIC. |
  |                 | | At boot time RMM configures/initializes the IPs and  |
  |                 |   IPs and interacts with them at runtime through       |
  |                 | | interrupts and registers.                            |
  +-----------------+--------------------------------------------------------+
