.. SPDX-License-Identifier: BSD-3-Clause
.. SPDX-FileCopyrightText: Copyright TF-RMM Contributors.

Threat Assessment
=================

The following threats were identified by applying STRIDE analysis on
each diagram element of the data flow diagram. The threats are related to
software and implementation specific to TF-RMM.

For each threat, we strive to indicate whether the mitigations are currently
implemented or not. However, the answer to this question is not always straight
forward. Some mitigations are partially implemented in the generic code but also
rely on the platform code to implement some bits of it. This threat model aims
to be platform-independent and it is important to keep in mind that such threats
only get mitigated if the platform properly fulfills its responsibilities.

Also, some mitigations might require enabling specific features, which must be
explicitly turned on via a build flag.

The ``Pending actions?`` box highlights any action that needs to be done in
order to implement the mitigations.

+------------------------+---------------------------------------------------+
| ID                     | 01                                                |
+========================+===================================================+
| Threat                 | | Information leak via UART logs.                 |
|                        |                                                   |
|                        | | During the development stages of software it is |
|                        |   common to print all sorts of information on the |
|                        | | console, including sensitive or confidential    |
|                        |   information such as crash reports with detailed |
|                        | | information of the CPU state, current registers |
|                        |   values, privilege level or stack dumps.         |
|                        |                                                   |
|                        | | This information is useful when debugging       |
|                        |   problems before releasing the production        |
|                        | | version but it could be used by an adversary    |
|                        |   to develop a working exploit if left enabled in |
|                        | | the production version.                         |
|                        |                                                   |
|                        | | This happens when directly logging sensitive    |
|                        |   information and more subtly when logging based  |
|                        | | on sensitive data that can be used as a         |
|                        |   side-channel information by an adversary.       |
+------------------------+---------------------------------------------------+
| Diagram Elements       | DF2                                               |
+------------------------+---------------------------------------------------+
| Assets                 | Sensitive Data                                    |
+------------------------+---------------------------------------------------+
| Threat Agent           | AppDebug                                          |
+------------------------+---------------------------------------------------+
| Threat Type            | Information Disclosure                            |
+------------------------+---------------------------------------------------+
| Impact                 | Informational (1)                                 |
+------------------------+---------------------------------------------------+
| Likelihood             | Informational (1)                                 |
+------------------------+---------------------------------------------------+
| Total Risk Rating      | Informational (1)                                 |
+------------------------+---------------------------------------------------+
| Mitigations            | | For production releases:                        |
|                        |                                                   |
|                        | | 1) Remove sensitive information logging.        |
|                        | | 2) Do not conditionally log based on            |
|                        |   sensitive data.                                 |
|                        | | 3) Do not log high precision timing information.|
+------------------------+---------------------------------------------------+
| Mitigations            | | Yes.                                            |
| implemented?           |   Requires the right build options to be used.    |
|                        |                                                   |
|                        | | Crash reporting is not implemented on RMM at    |
|                        |   the time.                                       |
|                        |                                                   |
|                        | | The log level can be tuned at build time, from  |
|                        |   very verbose to no output at all. See           |
|                        | | ``LOG_LEVEL`` build option. By default, release |
|                        |   builds are a lot less verbose than debug ones   |
|                        | | but still produce some output.                  |
|                        |                                                   |
|                        | | Messages produced by the platform code should   |
|                        |   use the appropriate level of verbosity so as    |
|                        | | not to leak sensitive information in production |
|                        |   builds.                                         |
+------------------------+---------------------------------------------------+
| Pending actions?       | | Ensure the right verbosity level is used for    |
|                        |   the type of information that it is logged.      |
+------------------------+---------------------------------------------------+

+------------------------+------------------------------------------------------+
| ID                     | 02                                                   |
+========================+======================================================+
| Threat                 | | An adversary can perform a denial-of-service       |
|                        |   attack on the system by causing the Realm world/RMM|
|                        | | to deadlock or enter into an unknown state.        |
|                        |                                                      |
|                        | | Malicious Host or Realm code can attempt to place  |
|                        |   the RMM into an inconsistent state by calling      |
|                        | | unimplemented SMC calls or by passing invalid      |
|                        |   arguments.                                         |
+------------------------+------------------------------------------------------+
| Diagram Elements       | DF4, DF5, DF7                                        |
+------------------------+------------------------------------------------------+
| Assets                 | Availability                                         |
+------------------------+------------------------------------------------------+
| Threat Agent           | RootCode, RealmCode, HostSoftware                    |
+------------------------+------------------------------------------------------+
| Threat Type            | Denial of Service                                    |
+------------------------+------------------------------------------------------+
| Impact                 | Medium (3)                                           |
+------------------------+------------------------------------------------------+
| Likelihood             | High (4)                                             |
+------------------------+------------------------------------------------------+
| Total Risk Rating      | High (12)                                            |
+------------------------+------------------------------------------------------+
| Mitigations            | | Validate SMC function IDs and arguments before     |
|                        |   using them.                                        |
|                        |                                                      |
|                        | | Follow locking discipline when acquiring locks in  |
|                        |   RMM.                                               |
|                        |                                                      |
|                        | | Upon an unrecoverable/catastrophic condition, RMM  |
|                        |   should issue a panic(). This call would return     |
|                        | | to EL3 software, keeping the availability of the   |
|                        |   overall system. It would be EL3 responsibility to  |
|                        | | to decide how to proceed (e.g. by disabling the    |
|                        |   whole Realm world).                                |
|                        |                                                      |
|                        | | State transitions should be designed and           |
|                        |   implemented to avoid RMM entering into invalid     |
|                        | | states. RMM specification mandates varius failure  |
|                        |   conditions for input arguments. These need to be   |
|                        | | enforced. Tooling CBMC will help to enforce these  |
|                        |   rules and validate that RMM can enter into invalid |
|                        | | state. Fuzz testing can also be implemented to     |
|                        |   ensure implementation is robust.                   |
+------------------------+------------------------------------------------------+
| Mitigations            | | Yes, except for panic() management.                |
| implemented?           |                                                      |
|                        | | For RMI and RSI services, all input is validated.  |
|                        |                                                      |
|                        | | The pre-conditions for RMI and RSI services are    |
|                        |   validated through CBMC.                            |
+------------------------+------------------------------------------------------+
| Pending actions?       | | Add fuzz testing to RMM ABI.                       |
|                        |                                                      |
|                        | | Implement proper panic() management as, at the     |
|                        |   moment, the call just halts the current PE.        |
+------------------------+------------------------------------------------------+

+------------------------+------------------------------------------------------+
| ID                     | 03                                                   |
+========================+======================================================+
| Threat                 | | An adversary can try stealing information by       |
|                        |   using RMM ABI.                                     |
|                        |                                                      |
|                        | | NS Host as well as Realm clients access RMM        |
|                        |   through RMM ABI. Malicious code can attempt to     |
|                        | | invoke services that would result in disclosing    |
|                        |   private information or secrets.                    |
|                        |                                                      |
|                        | | A realm can claim to be another Realm. NS Host can |
|                        |   associate the PA of one Realm to another Realm.    |
+------------------------+------------------------------------------------------+
| Diagram Elements       | DF4, DF5, DF7                                        |
+------------------------+------------------------------------------------------+
| Assets                 | Sensitive Data                                       |
+------------------------+------------------------------------------------------+
| Threat Agent           | RootCode, RealmCode, HostSoftware                    |
+------------------------+------------------------------------------------------+
| Threat Type            | Spoofing, Information disclosure                     |
+-------------------------------------------------------------------------------+
| Impact                 | Critical (5)                                         |
+------------------------+------------------------------------------------------+
| Likelihood             | High (4)                                             |
+------------------------+------------------------------------------------------+
| Total Risk Rating      | Critical (20)                                        |
+------------------------+------------------------------------------------------+
| Mitigations            | | 1) Ensure that RMM protects the Realm memory by    |
|                        |   using GPT and appropriate Stage 2 protections. CPU |
|                        | | registers and system registers should not leak any |
|                        |   Realm details to NS host other than what is        |
|                        | | allowed by the RMM ABI. NS Host must not be able   |
|                        |   to change or access the memory and CPU registers   |
|                        | | other than what is allowed by the RMM ABI. RMM     |
|                        |   should perform proper context switching of CPU     |
|                        | | registers when entering and exiting Realms.        |
|                        |   using them.                                        |
|                        | | 2) The RME Architecture provides memory isolation  |
|                        |   to the Realm world. RMM relies on RootCode for     |
|                        | | correct RME setup. But when delegating memory to   |
|                        |   the Realm world, RMM needs to ensure that suitable |
|                        | | memory scrubbing is implemented. Also, RMM should  |
|                        |   ensure any any architectural caches and memory is  |
|                        | | invalidated before returning back to NS Host.      |
|                        | | 3) SMC call from realm is always associated to the |
|                        |   Realm Descriptor (RD) and the RMM ABI does not     |
|                        | | allow spoofing of RD. NS Host always has to send   |
|                        |   the valid RD to make requests to the corresponding |
|                        | | Realm. RMM maintains a global granule array and    |
|                        |   every granule linked to a Realm has a specific     |
|                        | | State and reference count associated with it.      |
|                        |   Hence, the NS Host cannot associate a granule to   |
|                        | | another Realm. This mechanism is part of the RMM   |
|                        |   ABI.                                               |
+------------------------+------------------------------------------------------+
| Mitigations            | | 1) Yes.                                            |
| implemented?           | | 2) Yes.                                            |
|                        | | 3) Yes.                                            |
+------------------------+------------------------------------------------------+
| Pending actions?       | | None.                                              |
+------------------------+------------------------------------------------------+

+------------------------+------------------------------------------------------+
| ID                     | 04                                                   |
+========================+======================================================+
| Threat                 | | Memory corruption due to memory overflows and      |
|                        |   lack of boundary checks when accessing resources   |
|                        | | could allow an adversary to execute arbitrary code,|
|                        |   modify some state variable to change the normal    |
|                        | | flow of the program or leak sensitive              |
|                        |   information.                                       |
|                        |                                                      |
|                        | | Like in other software, RMM has multiple points    |
|                        |   where memory corruption security errors can arise. |
|                        |                                                      |
|                        | | Some of the errors include integer overflow,       |
|                        |   buffer overflow, incorrect array boundary checks,  |
|                        | | and incorrect error management.                    |
|                        |   Improper use of asserts instead of proper input    |
|                        | | validations might also result in these kinds of    |
|                        |   errors in release builds.                          |
+------------------------+------------------------------------------------------+
| Diagram Elements       | DF4, DF5, DF7                                        |
+------------------------+------------------------------------------------------+
| Assets                 | Code Execution, Sensitive Data, Availability         |
+------------------------+------------------------------------------------------+
| Threat Agent           | RootCode, RealmCode, HostSoftware                    |
+------------------------+------------------------------------------------------+
| Threat Type            | Tampering, Information Disclosure,                   |
|                        | Elevation of Privilege                               |
+-------------------------------------------------------------------------------+
| Impact                 | Critical (5)                                         |
+------------------------+------------------------------------------------------+
| Likelihood             | Medium (3)                                           |
+------------------------+------------------------------------------------------+
| Total Risk Rating      | High (15)                                            |
+------------------------+------------------------------------------------------+
| Mitigations            | | 1) Use proper input validation.                    |
|                        | | 2) Code reviews, testing.                          |
|                        | | 3) Static checks.                                  |
|                        | | 4) Memory loop and bound validation.               |
+------------------------+------------------------------------------------------+
| Mitigations            | | 1) Yes to all the mitigations.                     |
| implemented?           |                                                      |
|                        | | Data received from NS Host, forwarded through EL3  |
|                        |   Firmware, such as addresses and sizes identifying  |
|                        | | memory regions, are sanitized before being used.   |
|                        |   These security checks make sure that no software   |
|                        | | can access memory beyond its limit.                |
|                        |                                                      |
|                        | | Hardware protection mechanisms, such as GPT or     |
|                        |   memory encryption, are set in place to protect     |
|                        | | realms (and RMM) memory from unauthorized access.  |
|                        |                                                      |
|                        | | Memory shared with normal world (as well as other  |
|                        |   regions when it applies) is scrubbed by RMM after  |
|                        | | use before being released.                         |
|                        |                                                      |
|                        | | By default, *asserts* are only used to check for   |
|                        |   programming errors in debug builds. Other types of |
|                        | | errors are handled through condition checks that   |
|                        |   remain enabled in release builds. There is support |
|                        | | to ``panic`` RMM, halting it upon catastrophic     |
|                        |   errors. See :ref:`asserts and panic`.              |
|                        |                                                      |
|                        | | RMM uses a combination of manual code reviews      |
|                        |   and automated program analysis and testing to      |
|                        | | detect and fix memory corruption bugs. RMM makes   |
|                        |   use of various static analysis tools and other     |
|                        | | model checkers like CBMC to ensure that bugs in    |
|                        |   code are caught and fixed. RMM also uses MISRA     |
|                        | | coding guidelines to remove some of the issues     |
|                        |   which is considered safer for implementations      |
|                        | | using C language.                                  |
+------------------------+------------------------------------------------------+
| Pending actions?       | Incorporate new static analyzers into RMM.           |
+------------------------+------------------------------------------------------+

+------------------------+-----------------------------------------------------+
| ID                     | 05                                                  |
+========================+=====================================================+
| Threat                 | | SMC calls can leak sensitive information from     |
|                        |   RMM memory via microarchitectural side channels.  |
|                        |                                                     |
|                        | | Microarchitectural side-channel attacks such as   |
|                        |   `Spectre`_ can be used to leak data across        |
|                        | | security boundaries. An adversary might attempt to|
|                        |   use this kind of attack to leak sensitive         |
|                        | | data from RMM memory.                             |
|                        |                                                     |
|                        | | Also, some SMC calls, such as the ones involving  |
|                        |   encryption when applicable, might take different  |
|                        | | amount of time to complete depending upon the     |
|                        |   parameters. An adversary might attempt to use     |
|                        | | that information in order to infer secrets or to  |
|                        |   leak sensitive information.                       |
+------------------------+-----------------------------------------------------+
| Diagram Elements       | DF1, DF4, DF5, DF7                                  |
+------------------------+-----------------------------------------------------+
| Assets                 | Sensitive Data                                      |
+------------------------+-----------------------------------------------------+
| Threat Agent           | RootCode, RealmCode, HostSoftware                   |
+------------------------+-----------------------------------------------------+
| Threat Type            | Information Disclosure                              |
+------------------------+-----------------------------------------------------+
| Impact                 | High (4)                                            |
+------------------------+-----------------------------------------------------+
| Likelihood             | Medium (3)                                          |
+------------------------+-----------------------------------------------------+
| Total Risk Rating      | High (12)                                           |
+------------------------+-----------------------------------------------------+
| Mitigations            | | Enable appropriate side-channel protections as    |
|                        |   recommended by the Architecture.                  |
|                        |                                                     |
|                        | | Enable appropriate timing side-channel            |
|                        |   protections.                                      |
|                        |                                                     |
|                        | | Ensure the software components dealing with       |
|                        |   sensitive data use Data Independent algorithms.   |
|                        |                                                     |
|                        | | Ensure that only required memory is mapped when   |
|                        |   executing a Realm or doing operations in RMM so   |
|                        | | as to minimize effects of CPU speculation.        |
+------------------------+-----------------------------------------------------+
| Mitigations            | | Partially. RMM Enables some mitigations as        |
| implemented?           |   mandated by the Architecture.                     |
|                        |                                                     |
|                        | | RMM relies on MbedTLS library to use algorithms   |
|                        |   which are data independent when handling          |
|                        | | sensitive data.                                   |
|                        |                                                     |
|                        | | FEAT_DIT should be enabled.                       |
+------------------------+-----------------------------------------------------+
| Pending actions?       | | Review speculation vulnerabilities and ensure RMM |
|                        |   implements the minitagions.                       |
|                        |                                                     |
|                        | | Enable FEAT_DIT.                                  |
+------------------------+-----------------------------------------------------+

+------------------------+-----------------------------------------------------+
| ID                     | 6                                                   |
+========================+=====================================================+
| Threat                 | | Unexpected boot arguments (including boot         |
|                        |   manifest) from EL3 firmware or different format   |
|                        | | of boot manifest can cause RMM to crash or        |
|                        |   panic().                                          |
|                        |                                                     |
|                        | | If ``panic()`` is invoked as part of the RMM boot |
|                        |   process, either during cold or warm boot paths,   |
|                        | | the PE might get halted/stalled thus causing      |
|                        |   Denial of service to other worlds in the system.  |
+------------------------+-----------------------------------------------------+
| Diagram Elements       | DF1                                                 |
+------------------------+-----------------------------------------------------+
| Assets                 | Availability                                        |
+------------------------+-----------------------------------------------------+
| Threat Agent           | RootCode                                            |
+------------------------+-----------------------------------------------------+
| Threat Type            | Denial of Service                                   |
+------------------------+-----------------------------------------------------+
| Impact                 | Critical (5)                                        |
+------------------------+-----------------------------------------------------+
| Likelihood             | High (4)                                            |
+------------------------+-----------------------------------------------------+
| Total Risk Rating      | Critical (20)                                       |
+------------------------+-----------------------------------------------------+
| Mitigations            | | 1) Enforce a strict version control of the Boot   |
|                        |   interface between RMM and EL3 Firmware. Any       |
|                        | | mismatch or incompatible change is caught out by  |
|                        |   the version change and will cause RMM to fail.    |
|                        | | Validate Boot Arguments.                          |
|                        |                                                     |
|                        | | 2) Any boot failure is signaled to RootCoude      |
|                        |   suitably using an SMC which then can take         |
|                        | | appropriate action (e.g. disable the Realm world  |
|                        |   or reboot the system).                            |
+------------------------+-----------------------------------------------------+
| Mitigations            | | 1) Yes/Platform specific.                         |
| implemented?           |   The `RMM Boot Interface specification`_ defines   |
|                        | | the checks done at boot time and all the possible |
|                        |   error codes returned to EL3 Firmware. It also     |
|                        | | specifies the action to take by EL3 upon failure. |
|                        |   Platform specific part of the boot protocol needs |
|                        | | platform specific mitigation.                     |
|                        |                                                     |
|                        | | 2) Partially.                                     |
+------------------------+-----------------------------------------------------+
| Pending actions?       | | 2) Review the current use of ``panic()`` during   |
|                        |   the boot stages.                                  |
+------------------------+-----------------------------------------------------+

+------------------------+----------------------------------------------------+
| ID                     | 7                                                  |
+========================+====================================================+
| Threat                 | | Misconfiguration of the S1 and S2 MMU tables may |
|                        |   allow Realms to access sensitive data belonging  |
|                        | | to other Realms.                                 |
|                        |                                                    |
|                        | | A misconfiguration of the MMU could lead to an   |
|                        |   open door for a Realm to access other Realms or  |
|                        | | even HS Host memory.                             |
+------------------------+----------------------------------------------------+
| Diagram Elements       | DF1                                                |
+------------------------+----------------------------------------------------+
| Assets                 | Sensitive Data, Code execution                     |
+------------------------+----------------------------------------------------+
| Threat Agent           | RootCode                                           |
+------------------------+----------------------------------------------------+
| Threat Type            | Information Disclosure, Elevation of Privilege     |
+------------------------+----------------------------------------------------+
| Impact                 | Critical (5)                                       |
+------------------------+----------------------------------------------------+
| Likelihood             | High (4)                                           |
+------------------------+----------------------------------------------------+
| Total Risk Rating      | Critical (20)                                      |
+------------------------+----------------------------------------------------+
| Mitigations            | | The RMM specification mandates the rules for     |
|                        |   assigning memory to a Realm and hence the S1 and |
|                        | | S2 checks to be performed. Also, the access      |
|                        |   permissions are mandated by the RMM              |
|                        | | specification.                                   |
|                        |                                                    |
|                        | | Ensure that RMM verified that any PA to be mapped|
|                        |   in S2 belongs to the Realm. If the PA is NS, then|
|                        | | the request for mapping the PA must have been    |
|                        |   by NS Host.                                      |
+------------------------+----------------------------------------------------+
| Mitigations            | | Yes                                              |
| implemented?           |                                                    |
+------------------------+----------------------------------------------------+
| Pending actions?       | None                                               |
+------------------------+----------------------------------------------------+

+------------------------+-----------------------------------------------------+
| ID                     | 8                                                   |
+========================+=====================================================+
| Threat                 | | Realm code flow diversion through REC manipulation|
|                        |   from Host Software.                               |
|                        |                                                     |
|                        | | An adversary with access to a Realm's REC could   |
|                        |   tamper with the structure content and affect the  |
|                        | | Realm's execution flow.                           |
+------------------------+-----------------------------------------------------+
| Diagram Elements       | DF7                                                 |
+------------------------+-----------------------------------------------------+
| Assets                 | Availability , Code Execution                       |
+------------------------+-----------------------------------------------------+
| Threat Agent           | HostSoftware                                        |
+------------------------+-----------------------------------------------------+
| Threat Type            | Denial of Service, Tampering                        |
+------------------------+-----------------------------------------------------+
| Impact                 | Critical (5)                                        |
+------------------------+-----------------------------------------------------+
| Likelihood             | High (4)                                            |
+------------------------+-----------------------------------------------------+
| Total Risk Rating      | Critical (20)                                       |
+------------------------+-----------------------------------------------------+
| Mitigations            | | Store sensitive data structures in Realm PAS      |
|                        |   memory.                                           |
|                        |                                                     |
|                        | | Do not allow NS Host to manipulate REC contents   |
|                        |   via RMI once a Realm is activated.                |
+------------------------+-----------------------------------------------------+
| Mitigations            | | Yes                                               |
| implemented?           |                                                     |
+------------------------+-----------------------------------------------------+
| Pending actions?       | None                                                |
+------------------------+-----------------------------------------------------+

+------------------------+-----------------------------------------------------+
| ID                     | 9                                                   |
+========================+=====================================================+
| Threat                 | | Exploit unmeasured RMI operations to control Realm|
|                        |   memory content.                                   |
|                        |                                                     |
|                        | | Some RMI operations are not measured. An adversary|
|                        |   could use those to (partially) control the        |
|                        | | contents of the IPA space of a Realm, which may   |
|                        |   become a useful primitive for further attacks.    |
+------------------------+-----------------------------------------------------+
| Diagram Elements       | DF4                                                 |
+------------------------+-----------------------------------------------------+
| Assets                 | Availability , Code Execution                       |
+------------------------+-----------------------------------------------------+
| Threat Agent           | RootCode, HostSoftware                              |
+------------------------+-----------------------------------------------------+
| Threat Type            | Denial of Service, Tampering                        |
+------------------------+-----------------------------------------------------+
| Impact                 | Critical (5)                                        |
+------------------------+-----------------------------------------------------+
| Likelihood             | High (4)                                            |
+------------------------+-----------------------------------------------------+
| Total Risk Rating      | Critical (20)                                       |
+------------------------+-----------------------------------------------------+
| Mitigations            | | Scrub granules on transitioning them between      |
|                        |   security domains.                                 |
+------------------------+-----------------------------------------------------+
| Mitigations            | | Yes                                               |
| implemented?           |                                                     |
+------------------------+-----------------------------------------------------+
| Pending actions?       | None                                                |
+------------------------+-----------------------------------------------------+

+------------------------+-----------------------------------------------------+
| ID                     | 10                                                  |
+========================+=====================================================+
| Threat                 | | Use of PMU and MPAM statistics to increase the    |
|                        |   the accuracy of side channel attacks.             |
+------------------------+-----------------------------------------------------+
| Diagram Elements       | DF7                                                 |
+------------------------+-----------------------------------------------------+
| Assets                 | Sensitive Data                                      |
+------------------------+-----------------------------------------------------+
| Threat Agent           | HostSoftware                                        |
+------------------------+-----------------------------------------------------+
| Threat Type            | Information Disclosure                              |
+------------------------+-----------------------------------------------------+
| Impact                 | Critical (5)                                        |
+------------------------+-----------------------------------------------------+
| Likelihood             | High (4)                                            |
+------------------------+-----------------------------------------------------+
| Total Risk Rating      | Critical (20)                                       |
+------------------------+-----------------------------------------------------+
| Mitigations            | | Save/Restore performance counters on transitions  |
|                        |   between security domains or between Realms.       |
|                        |                                                     |
|                        | | Configure MPAM so that is either disabled or set  |
|                        |   to default values for Realm world.                |
+------------------------+-----------------------------------------------------+
| Mitigations            | | PMU is saved and restored.                        |
| implemented?           |                                                     |
|                        | | MPAM is not enabled for Realm world.              |
+------------------------+-----------------------------------------------------+
| Pending actions?       | None.                                               |
+------------------------+-----------------------------------------------------+

+------------------------+------------------------------------------------------------+
| ID                     | 11                                                         |
+========================+============================================================+
| Threat                 | | Misconfiguration of the hardware IPs and registers       |
|                        |   may lead to data leaks or incorrect behaviour.           |
|                        |                                                            |
|                        | | RMM needs to interact with several hardware IPs          |
|                        |   as well as system registers for which it uses            |
|                        | | its own libraries and/or drivers. Misconfiguration       |
|                        |   of such elements could cause data leaks and/or           |
|                        | | system malfunction.                                      |
+------------------------+------------------------------------------------------------+
| Diagram Elements       | DF8                                                        |
+------------------------+------------------------------------------------------------+
| Assets                 | Sensitive Data, Availability                               |
+------------------------+------------------------------------------------------------+
| Threat Agent           | RMMCode                                                    |
+------------------------+------------------------------------------------------------+
| Threat Type            | Information Disclosure, Denial of Service                  |
+------------------------+------------------------------------------------------------+
| Impact                 |  Critical (5)                                              |
+------------------------+------------------------------------------------------------+
| Likelihood             |  Informational (1)                                         |
+------------------------+------------------------------------------------------------+
| Total Risk Rating      |  Low (5)                                                   |
+------------------------+------------------------------------------------------------+
| Mitigations            | | 1) Code reviews, testing.                                |
|                        | | 2) Static checks.                                        |
+------------------------+------------------------------------------------------------+
| Mitigations            | | 1), 2) Yes/Platform specific.                            |
| implemented?           |   RMM uses a combination of manual code reviews            |
|                        | | and automated program analysis and testing to            |
|                        |   detect and fix bugs as well as to test various security  |
|                        | | properties.                                              |
+------------------------+------------------------------------------------------------+
| Pending actions?       | None                                                       |
+------------------------+------------------------------------------------------------+

--------------

.. _RMM-EL3 world switch register save restore convention: https://trustedfirmware-a.readthedocs.io/en/latest/components/rmm-el3-comms-spec.html#rmm-el3-world-switch-register-save-restore-convention
.. _DEN0034: https://developer.arm.com/documentation/den0034/latest
.. _Armv8.5-A and Armv9 Updates: https://developer.arm.com/documentation/102822/
.. _RMM Boot Interface specification: https://trustedfirmware-a.readthedocs.io/en/latest/components/rmm-el3-comms-spec.html#rmm-boot-interface
.. _Spectre: https://developer.arm.com/support/arm-security-updates/speculative-processor-vulnerability
.. _ASLR: https://lwn.net/Articles/569635/
