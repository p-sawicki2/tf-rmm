.. SPDX-License-Identifier: BSD-3-Clause
.. SPDX-FileCopyrightText: Copyright TF-RMM Contributors.

Memory management
=================

This document describes how memory, used by the |RMM| and by Realms, is
managed by the |RMM| implementation.

Categories of memory
--------------------

Memory accessed by the |RMM| and by Realms can be categorised as follows:

-  |RMM| code

-  |RMM| data

   -  Granule state tracking (see "Granule state tracking")
   -  |RMM| stage 1 translation tables (see "|RMM| stage 1 translation
      regime")

-  Realm data

   -  Memory that can be used for code and data by the Realm and which
      is mapped into the IPA space of a Realm, inside the Protected
      Address Range (PAR)

-  Realm metadata

   -  Realm Descriptors (RDs)
   -  Realm Execution Contexts (RECs)
   -  REC lists
   -  Realm Translation Tables (RTTs) (see "Realm stage 2 translation
      regime")

-  NS data

   -  Parameters passed by the Host to |RMM| commands, which are too large
      to be passed via GPRs
   -  Data provided by the Host, for copying by the |RMM| into Realm data
      memory
   -  The *REC run* data structure, used to communicate between the Host
      and the |RMM| on Realm entry and on Realm exit
   -  Non-secure memory which is mapped into the IPA space of a Realm,
      outside the PAR

The following sections describe how the physical memory in each of these
categories is provided to the |RMM|, and how the |RMM| manages translation
table mappings to this memory.

Physical Address Space
----------------------

Tormore (TORMORE\_ARCH) defines four Physical Address Spaces (PASs):

-  Non-secure
-  Secure
-  Realm
-  Root

|RMM| code and |RMM| data are in Realm PAS memory, allocated to the |RMM| at
boot. This is a static allocation, so this memory is never accessible to
the Host.

The size of the |RMM| data is fixed at boot. The majority of this is the
granule array (see "Granule state tracking" below), whose size is
proportional to the amount of DRAM in the system.

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

Granule state tracking
----------------------

The |RMM| manages a data structure called the granule array, which is
stored in |RMM| data memory.

The granule array contains one entry for every Granule of physical
memory which was in Non-secure PAS at |RMM| boot. It therefore describes
all memory in categories except for |RMM| code and |RMM| data.

Each entry in the granule array contains a field which records the
*state* of the Granule:

-  NS: Not Realm PAS (i.e. Non-secure PAS, Root PAS or Secure PAS)
-  Delegated: Realm PAS, but not yet assigned a purpose as either Realm
   data or Realm metadata
-  RD
-  REC
-  REC list
-  RTT
-  Data: Realm data

For further details, see:

-  ``enum granule_state``
-  ``struct granule``

|RMM| stage 1 translation regime
---------------------------------

The |RMM| stage 1 translation regime is configured to use

-  36 bits of VA space (64G)
-  3 levels of translation tables (L1 to L3)

Each entry in the L1 table maps a 1G block of VA space as follows:

::

    TTBR1_EL2 --> L1 table
                  --------
                  entry 0  --> static mappings for RMM code and RMM data
                  entry 1      invalid
                  ...          invalid
                  entry 61     invalid
                  entry 62 --> dynamic mappings
                  entry 63 --> static mappings for I/O devices

|RMM| stage 1 translation tables are shared by all PEs in the system.

The base of the |RMM| VA range is defined as ``RMM_VIRT``.

Static mappings
~~~~~~~~~~~~~~~

The |RMM| is loaded as an ELF binary with various sections. The loader of
the |RMM| allocates memory for each section in the |RMM| binary.

The size of the sections in the |RMM| binary and placing of |RMM| code and
data into appropriate sections is controlled by the linker script.

I/O devices such as the UART are allocated from the top of the
TTBR1\_EL2 range.

For further details, see:

-  ``src/linker.lds``
-  ``src/core/mmu.S``

Dynamic mappings
~~~~~~~~~~~~~~~~

Memory which is mapped into the |RMM| VA space and unmapped dynamically at
runtime is referred to as *buffers*.

The |RMM| has a fixed number of *buffer slots* per CPU. These are used to
create transient mappings of buffers used by the |RMM|.

Buffer slots are statically allocated in the |RMM| stage 1 translation
tables as shown in the following diagram.

::

    TTBR1_EL2 --> L1 table
                  --------
                  ...
                  entry 62 --> L2 table
                  ...          --------
                               entry 0  --> L3 table
                                            --------
                                            CPU 0 slot 0
                                            ...
                                            CPU 0 slot N
                                            CPU 1 slot 0
                                            ...
                                            CPU 1 slot N
                                            ...
                                            CPU M slot 0
                                            ...
                                            CPU M slot N

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

The REC and the *REC run* data structure are both mapped during Realm
execution.

The tag-lock is held while a dynamic mapping exists, for all memory
categories except for the REC run data structure. In this case, access
to the REC run data structure is protected by holding a reference count
during execution of RMI.REC.Run.

As an alternative to using dynamic buffer slots, the approach of
maintaining static mappings for all physical memory (similar to the
linear map in the Linux kernel) was considered, but rejected on the
grounds that this could permit arbitrary memory access for an attacker
who is able to subvert |RMM| execution.

For further details, see:

-  ``enum buffer_slot``
-  ``src/core/buffer.c``
-  ``src/core/mmu.S``
-  ``struct granule``

Realm stage 2 translation regime
--------------------------------

The Realm stage 2 translation regime is configured to use

-  48 bits of IPA space
-  4 levels of translation tables (L0 to L3)

Realm stage 2 translation tables are referred to as Realm Translation
Tables (RTTs) to distinguish them from the |RMM| stage 1 translation
tables.

The L0 RTT is allocated at Realm creation time. The address of the L0
RTT is stored in the RD. On entry to a Realm, VTTBR\_EL2 is set to point
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

References
----------

-  TORMORE\_ARCH: Tormore architecture specification (ARM AES 0014)

