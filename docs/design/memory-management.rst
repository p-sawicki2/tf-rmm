.. SPDX-License-Identifier: BSD-3-Clause
.. SPDX-FileCopyrightText: Copyright TF-RMM Contributors.

Memory management
=================

This document describes how memory, used by the |RMM| and by Realms, is
managed by the |RMM| implementation.

Categories of memory
--------------------

Memory accessed by the |RMM| and by Realms can be categorised as follows:

- Static Mappings common for all PEs

   -  |RMM| code

   -  |RMM| RO

   -  |RMM| RW data

      -  Granule state tracking (see `Granule state tracking`_)
      -  |RMM| stage 1 translation tables (see `RMM stage 1 translation
         regime`_)
      - Per-CPU stacks

   -  Shared page for EL3-RMM communications

   -  Realm data

      -  Memory that can be used for code and data by the Realm and which
         is mapped into the IPA space of a Realm via RTTs inside the Protected
         Address Range (PAR). NS Memory can also be mapped into IPA space in
         which case it will be the unprotected range of the IPA space.

- Dynamic mappings which are private to a PE

   -  Realm metadata correspondig to the specific Realm and Realm Execution
      context scheduled on the PE

      -  Realm Descriptors (RDs)
      -  Realm Execution Contexts (RECs)
      -  REC lists
      -  Realm Translation Tables (RTTs) (see `Realm stage 2 translation
         regime`_)

   -  NS data

      -  Parameters passed by the Host to |RMM| commands, which are too large
         to be passed via GPRs
      -  Data provided by the Host, for copying by the |RMM| into Realm data
         memory
      -  The *RmiRecRun* data structure, used to communicate between the Host
         and the |RMM| on Realm entry and on Realm exit
      -  Non-secure memory which is mapped into the IPA space of a Realm,
         outside the PAR

The following sections describe how the physical memory in each of these
categories is provided to the |RMM|, and how the |RMM| manages translation
table mappings to this memory.

Physical Address Space
----------------------

The Realm Management Extension (RME) defines four Physical Address
Spaces (PAS):

-  Non-secure
-  Secure
-  Realm
-  Root

|RMM| code and |RMM| data are in Realm PAS memory, allocated to the |RMM| at
boot by the EL3 Firware. This is a static allocation, so this memory is never
accessible to the Host.

The size of the |RMM| data is fixed at boot. The majority of this is the
granule array (see `Granule state tracking`_ below), whose size is configurable
and proportional to the maximum amount of DRAM supported by the system.

Realm data and Realm metadata are in Realm PAS memory, delegated to the
|RMM| by the Host at runtime. The |RMM| ABI ensures that this memory cannot
be returned to Non-secure PAS ("undelegated") while it is in use by the
|RMM| or by a Realm.

NS data is in Non-secure PAS memory. The Host is able to change the PAS
of this memory (in particular, to either Secure PAS or Root PAS) while
it is being accessed by the |RMM|. Consequently, the |RMM| must be able to
handle a Granule Protection Fault (GPF) while accessing NS data.
Similarly, a Realm must be able to handle a GPF when accessing memory
outside the PAR.

.. _granule state tracking:

Granule state tracking
----------------------

The |RMM| manages a data structure called the granule array, which is
stored in |RMM| data memory.

The granule array contains one entry for every Granule of physical
memory which was in Non-secure PAS at |RMM| boot.

Each entry in the granule array contains a field which records the
*state* of the Granule:

-  NS: Not Realm PAS (i.e. Non-secure PAS, Root PAS or Secure PAS)
-  Delegated: Realm PAS, but not yet assigned a purpose as either Realm
   data or Realm metadata
-  RD
-  REC
-  REC aux
-  Data: Realm data
-  RTT

For further details, see:

-  ``enum granule_state``
-  ``struct granule``

.. _RMM stage 1 translation regime:

RMM stage 1 translation regime
------------------------------

The |RMM| stage 1 translation regime is taken care of by the xlat library. This
library, which is able to support up to 52-bit addresses and 4 levels of
translation (when ``FEAT_LPA2`` is enabled) is configured by |RMM| to use

-  Up to 38 bits of VA space (256G) per address region (modifiable through
   ``VIRT_ADDR_SPACE_WIDTH`` build option)
-  3 levels of translation tables (L1 to L3)

In order to keep the bootstrap of Stage 2 MMU simple, VHE is used by the xlat
library to split the 64-bit VA space into two address spaces:

-  The lower range: it expands from VA 0x0 up to the maximum VA size configured
   for the region (with a maximum VA size of 48 bits or 52 bits if ``FEAT_LPA2``
   is supported). This is used to map the |RMM| Runtime (code and data) using
   `Static mappings`_
-  The upper range: It expands from VA 0xFFFF_FFFF_FFFF_FFFF all the way down
   to a space equal to the maximum VA size configured for the region.
   This region is used by the `Dynamic Mappings`_ as well as the per-CPU
   stacks.

For further details, see ``lib/xlat``.

Static mappings
~~~~~~~~~~~~~~~

The |RMM| is loaded as an ELF binary with various sections. The loader of
the |RMM| allocates memory for each section available in the |RMM| binary.

The size of the sections in the |RMM| binary as well as the placing of
|RMM| code and data into appropriate sections is controlled by the linker
script.

Platform initialization code takes care of importing the linker symbols
that define the boundaries of the different sections and creates static
memory mapping representations that are then passed to the xlat library to
generate flat static mappings. In addition, as |RMM| is compiled as a
Position Independed Execution (PIE) application at offset 0x0, the Global
Offset Table (GOT) and other data structures provided by the linker are
updated with the right offsets.

For I/O devices such as the UART, the addresses are defined as per-platform
build options or through the Boot Manifest.

All the CPUs in the system share the same translation context for the static
mappings.

The diagram below, corresponding to the full VA space of the system, shows the
memory layout for the lower range region region, where the static mappings are
allocated. The Per-CPU stacks, which are also statically allocated, are mapped
to the high region at boot time, as in this case we cannot use flat-mappings
(the stack start PA is different for each CPU whereas the VA is the same).

[TODO: Update the diagram with the per-CPU stacks]

|full va space|

For further details, see:

-  ``runtime/linker.lds``
-  ``plat/common/src/plat_common_init.c``
-  ``plat/fvp/src/fvp_setup.c``

Dynamic mappings
~~~~~~~~~~~~~~~~

Memory which is mapped into the |RMM| VA space and unmapped dynamically at
runtime is referred to as *buffers*.

The |RMM| has a fixed number of *buffer slots* per CPU. These are used to
create dynamic mappings of buffers used by the |RMM|. These dynamic mappings
are marked by the xlat library as *TRANSIENT*, to distinguish their Translation
Table Entries from invalid ones, as they can be temporarly invalid but
eventually will be used to map a buffer.

Each buffer slot is used to map memory of a particular category. The |RMM|
validates that the target physical granule is of the expected category
using the tag value in the tag-lock for that granule.

This avoids the need for generic allocation of VA space. This is only
possible due to the simple nature of the |RMM| design - in particular, the
fact that it is possible to statically determine the types of objects
which need to be mapped into the |RMM|'s address space, and the maximum
number of objects of a given type which need to be mapped at any point
in time.

Buffer slots include:

-  ``SLOT_NS``: used to access NS data during execution of RMI handlers
-  ``SLOT_DELEGATED``: used to access a granule in Delegated state
-  A slot for each type of Realm metadata granule

During Realm entry and Realm exit, the RD is mapped in the "RD" buffer
slot. Once Realm entry or Realm exit is complete, this mapping is
removed. The RD is not mapped during Realm execution.

The REC and the *RmiRecRun* data structures are both mapped during Realm
execution.

The tag-lock is held while a dynamic mapping exists, for all memory
categories except for the *RmiRecRun* data structure. In this case, access
to this data structure is protected by holding a reference count
during execution of RMI.REC.Run.

Buffer slots are mapped in the upper address range. The VA space for this area
is fixed at build time and it depends on the the number of buffer slots
descriptors defined in ``enum granule_state``.

Each CPU in the system has its own translation context for the slot buffers,
which means that a particular slot buffer descriptor will always be mapped to
the same VA, regardless of the CPU or if other CPUs have the same slot buffer
descriptor in use. The slot buffer implementation includes some optimizations,
such as internal caches for the translation table entries, which allows to
improve the efficiency of mapping and unmapping operations. This also allows
the migration of vCPUs accross different CPUs if an operation is interrupted,
for instance while the Realm attestation is ongoing in RMM.

The diagram below shows the memory layout for the upper range region region.
This layout includes the per-CPU stacks mentioned on the previous section.

|upper range memory|

As an alternative to using dynamic buffer slots, the approach of
maintaining static mappings for all physical memory (similar to the
linear map in the Linux kernel) was considered, but rejected on the
grounds that this could permit arbitrary memory access for an attacker
who is able to subvert |RMM| execution.

For further details, see:

-  ``enum buffer_slot``
-  ``lib/realm/src/buffer.c``
-  ``struct granule``

.. _Realm stage 2 translation regime:

Realm stage 2 translation regime
--------------------------------

The Realm stage 2 translation regime is configured to use

-  48 bits of IPA space
-  4 levels of translation tables (L0 to L3)

Realm stage 2 translation tables are referred to as Realm Translation
Tables (RTTs) to distinguish them from the |RMM| stage 1 translation
tables.

The L0 RTT is allocated at Realm creation time. The address of the L0
RTT is stored in the RD. On entry to a Realm, VTTBR_EL2 is set to point
to the L0 RTT.

L1 to L3 RTTs are delegated to the |RMM| by the Host.

For further details, see:

-  ``struct rd``

Glossary
--------

-  GPF: Granule Protection Fault
-  IPA: Intermediate Physical Address
-  PA: Physical Address
-  PAR: Protected Address Range
-  PAS: Physical Address Space
-  RMM: Realm Management Monitor
-  RTT: Realm Translation Table
-  VHE: Virtualization Host Extensions

References
----------

.. |full va space| image:: ./diagrams/full_va_space_diagram.png
   :height: 600

.. |upper range memory| image:: ./diagrams/upper_memory_diagram.png
   :height: 450

