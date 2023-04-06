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
| Threat Agent           | AppDebug, Faulty code at Root Level               |
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
|                        |   attack by using a broken SMC call that causes the  |
|                        | | system to reboot or enter into unknown state.      |
|                        |                                                      |
|                        | | EL-3 Firmware as well as Realm clients access RMM  |
|                        |   through SMC calls. Malicious code can attempt to   |
|                        | | place the RMM into an inconsistent state by calling|
|                        |   unimplemented SMC calls or by passing invalid      |
|                        | | arguments.                                         |
+------------------------+------------------------------------------------------+
| Diagram Elements       | DF4, DF5                                             |
+------------------------+------------------------------------------------------+
| Assets                 | Availability                                         |
+------------------------+------------------------------------------------------+
| Threat Agent           | Faulty code at Root Level, RealmCode                 |
+------------------------+------------------------------------------------------+
| Threat Type            | Denial of Service                                    |
+------------------------+------------------------------------------------------+
| Impact                 | Medium (3)                                           |
+------------------------+------------------------------------------------------+
| Likelihood             | High (4)                                             |
+------------------------+------------------------------------------------------+
| Total Risk Rating      | High (12)                                            |
+------------------------+------------------------------------------------------+
| Mitigations            | Validate SMC function IDs and arguments before using |
|                        | them.                                                |
+------------------------+------------------------------------------------------+
| Mitigations            | | Yes.                                               |
| implemented?           |                                                      |
|                        | | For RMI and RSI services, all input is validated.  |
+------------------------+------------------------------------------------------+
| Pending actions?       | None                                                 |
+------------------------+------------------------------------------------------+

+------------------------+------------------------------------------------------+
| ID                     | 03                                                   |
+========================+======================================================+
| Threat                 | | An adversary can try stealing information by       |
|                        |   using SMC calls.                                   |
|                        |                                                      |
|                        | | EL-3 Firmware as well as Realm clients access RMM  |
|                        |   through SMC calls. Malicious code can attempt to   |
|                        | | invoke services that would result in disclosing    |
|                        |   private information or secrets.                    |
+------------------------+------------------------------------------------------+
| Diagram Elements       | DF4, DF5                                             |
+------------------------+------------------------------------------------------+
| Assets                 | Sensitive Data                                       |
+------------------------+------------------------------------------------------+
| Threat Agent           | Faulty code at Root Level, RealmCode                 |
+------------------------+------------------------------------------------------+
| Threat Type            | Spoofing, Information disclosure                     |
+-------------------------------------------------------------------------------+
| Impact                 | Critical (5)                                         |
+------------------------+------------------------------------------------------+
| Likelihood             | High (4)                                             |
+------------------------+------------------------------------------------------+
| Total Risk Rating      | Critical (20)                                        |
+------------------------+------------------------------------------------------+
| Mitigations            | | 1) Validate SMC function IDs and arguments before  |
|                        |   using them.                                        |
|                        | | 2) Implement a mechanism to validate the identity  |
|                        |   of the service requester.                          |
+------------------------+------------------------------------------------------+
| Mitigations            | | 1) Yes.                                            |
| implemented?           |   For RMI and RSI services, all input is validated.  |
|                        | | 2) No.                                             |
|                        |   There is no mechanism in place to validate the     |
|                        |   identity of the SMC issuer.                        |
+------------------------+------------------------------------------------------+
| Pending actions?       | | Study the feasibility of introducing a mechanism   |
|                        |   to validate the identity of the SMC issuer, such   |
|                        | | as using an encrypted caller-id. This could be     |
|                        |   implemented as a build option.                     |
+------------------------+------------------------------------------------------+

+------------------------+------------------------------------------------------+
| ID                     | 04                                                   |
+========================+======================================================+
| Threat                 | | Memory corruption due to memory overflows and      |
|                        |   lack of boundary checks when accessing resources   |
|                        | | could allow an adversary to execute arbitrary code,|
|                        |   modify some state variable to change the normal    |
|                        | | flow of the program, or leak sensitive             |
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
| Diagram Elements       | DF4, DF5                                             |
+------------------------+------------------------------------------------------+
| Assets                 | Code Execution, Sensitive Data, Availability         |
+------------------------+------------------------------------------------------+
| Threat Agent           | Faulty code at Root Level, RealmCode                 |
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
+------------------------+------------------------------------------------------+
| Mitigations            | | 1) Yes.                                            |
| implemented?           |   Data received from normal world, forwarded through |
|                        |   EL-3 Firmware, such as addresses and sizes         |
|                        | | identifying memory regions, are sanitized          |
|                        |   before being used. These security checks make      |
|                        | | sure that no software can access memory beyond its |
|                        |   limit.                                             |
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
|                        | | 2), 3) Yes.                                        |
|                        |   RMM uses a combination of manual code reviews      |
|                        |   and automated program analysis and testing to      |
|                        | | detect and fix memory corruption bugs. All RMM     |
|                        |   code including platform code goes through manual   |
|                        | | code reviews. Additionally, static code analysis   |
|                        |   is performed on all RMM code. The code is also     |
|                        | | tested on FVP platforms.                           |
+------------------------+------------------------------------------------------+
| Pending actions?       | None                                                 |
+------------------------+------------------------------------------------------+

+------------------------+------------------------------------------------------+
| ID                     | 05                                                   |
+========================+======================================================+
| Threat                 | | Improperly handled SMC calls can leak register     |
|                        |   contents.                                          |
|                        |                                                      |
|                        | | When switching between worlds, or between realms,  |
|                        |   RMM can leak the content of some registers to      |
|                        | | different contexts.                                |
+------------------------+------------------------------------------------------+
| Diagram Elements       | DF4, DF5                                             |
+------------------------+------------------------------------------------------+
| Assets                 | Sensitive Data                                       |
+------------------------+------------------------------------------------------+
| Threat Agent           | Faulty code at Root Level, RealmCode                 |
+------------------------+------------------------------------------------------+
| Threat Type            | Information Disclosure                               |
+------------------------+------------------------------------------------------+
| Impact                 | Critical (5)                                         |
+------------------------+------------------------------------------------------+
| Likelihood             | High (4)                                             |
+------------------------+------------------------------------------------------+
| Total Risk Rating      | Critical (20)                                        |
+------------------------+------------------------------------------------------+
| Mitigations            | Save and restore registers when switching contexts.  |
+------------------------+------------------------------------------------------+
| Mitigations            | | Yes.                                               |
| implemented?           |   This is the default behaviour in RMM, documented in|
|                        | | `RMM-EL3 world switch register save restore        |
|                        |    convention`_                                      |
+------------------------+------------------------------------------------------+
| Pending actions?       | None                                                 |
+------------------------+------------------------------------------------------+

+------------------------+-----------------------------------------------------+
| ID                     | 06                                                  |
+========================+=====================================================+
| Threat                 | | SMC calls can leak sensitive information from     |
|                        |   RMM memory via microarchitectural side channels.  |
|                        |                                                     |
|                        | | Microarchitectural side-channel attacks such as   |
|                        |   `Spectre`_ can be used to leak data across        |
|                        | | security boundaries. An adversary might attempt to|
|                        |   use this kind of attack to leak sensitive         |
|                        | | data from RMM memory.                             |
+------------------------+-----------------------------------------------------+
| Diagram Elements       | DF1, DF4, DF5                                       |
+------------------------+-----------------------------------------------------+
| Assets                 | Sensitive Data                                      |
+------------------------+-----------------------------------------------------+
| Threat Agent           | Faulty code at Root Level, RealmCode                |
+------------------------+-----------------------------------------------------+
| Threat Type            | Information Disclosure                              |
+------------------------+-----------------------------------------------------+
| Impact                 | Medium (3)                                          |
+------------------------+-----------------------------------------------------+
| Likelihood             | Medium (3)                                          |
+------------------------+-----------------------------------------------------+
| Total Risk Rating      | Medium (9)                                          |
+------------------------+-----------------------------------------------------+
| Mitigations            | Enable appropriate side-channel protections.        |
+------------------------+-----------------------------------------------------+
| Mitigations            | | No.                                               |
| implemented?           |                                                     |
|                        | | RMM does not implement specific software          |
|                        |   mitigations for Spectre type attacks as           |
|                        | | recommended by `Armv8.5-A and Armv9 Updates`_ for |
|                        |   the generic code.                                 |
|                        |                                                     |
|                        | | SiPs should implement similar mitigations as      |
|                        |   explained on `Armv8.5-A and Armv9 Updates`_ on    |
|                        | | code that is deemed to be vulnerable to such      |
|                        |   attacks.                                          |
|                        |                                                     |
|                        | | RMM needs to enable the architectural mitigations |
|                        |   for vulnerabilities. It also needs to ensure that |
|                        | | only required memory is mapped when executing     |
|                        |   a Realm or doing operatoins in RMM so as to       |
|                        | | minimize effects of CPU speculation.              |
+------------------------+-----------------------------------------------------+
| Pending actions?       | | Implement specific software mitigations as        |
|                        |   recommended by `Armv8.5-A and Armv9 Updates`_ for |
|                        | | the generic code.                                 |
+------------------------+-----------------------------------------------------+

+------------------------+-----------------------------------------------------+
| ID                     | 07                                                  |
+========================+=====================================================+
| Threat                 | | SMC calls can leak sensitive information from     |
|                        |   RMM memory via time side channel attacks.         |
|                        |                                                     |
|                        | | Some SMC calls, such as the ones involving        |
|                        |   encryption when applicable, might take different  |
|                        | | amount of time to complete depending upon the     |
|                        |   call parameters. An adversary might attempt to use|
|                        | | that information in order to infer secrets or to  |
|                        |   leak sensitive information.                       |
|                        |                                                     |
|                        | | This could also be applicable to the arguments    |
|                        |   used by EL-3 Firmware during RMM initialization.  |
+------------------------+-----------------------------------------------------+
| Diagram Elements       | DF1, DF4, DF5                                       |
+------------------------+-----------------------------------------------------+
| Assets                 | Sensitive Data                                      |
+------------------------+-----------------------------------------------------+
| Threat Agent           | Faulty code at Root Level, RealmCode                |
+------------------------+-----------------------------------------------------+
| Threat Type            | Information Disclosure                              |
+------------------------+-----------------------------------------------------+
| Impact                 | Hihg (4)                                            |
+------------------------+-----------------------------------------------------+
| Likelihood             | Low (2)                                             |
+------------------------+-----------------------------------------------------+
| Total Risk Rating      | Medium (8)                                          |
+------------------------+-----------------------------------------------------+
| Mitigations            | | Enable appropriate timing side-channel            |
|                        |   protections.                                      |
|                        |                                                     |
|                        | | Ensure the software components dealing with       |
|                        |   sensitive data use Data Independent algorithms.   |
+------------------------+-----------------------------------------------------+
| Mitigations            | | RMM relies on MbedTLS library to use algorithms   |
|                        |   which are data independent when handling          |
|                        | | sensitive data.                                   |
+------------------------+-----------------------------------------------------+
| Pending actions?       | | Study the feasibility of mitigations for this     |
|                        |   type of attack on the generic code. This could be |
|                        | | be enbled at build time if needed.                |
|                        |                                                     |
|                        | | For cryptographic operations, check if the        |
|                        |   Mbed TLS library has mitigations for this type of |
|                        | | attack.                                           |
|                        |                                                     |
|                        | | FEAT_DIT should be used in RMM.                   |
+------------------------+-----------------------------------------------------+

+------------------------+-----------------------------------------------------+
| ID                     | 08                                                  |
+========================+=====================================================+
| Threat                 | | SMC calls with incorrect arguments can halt       |
|                        |   and/or stall the PE in which they are executed by |
|                        | | causing it to ``panic``.                          |
+------------------------+-----------------------------------------------------+
| Diagram Elements       | DF4, DF5                                            |
+------------------------+-----------------------------------------------------+
| Assets                 | Availability                                        |
+------------------------+-----------------------------------------------------+
| Threat Agent           | Faulty code at Root Level, RealmCode                |
+------------------------+-----------------------------------------------------+
| Threat Type            | Denial of Service                                   |
+------------------------+-----------------------------------------------------+
| Impact                 | Critical (5)                                        |
+------------------------+-----------------------------------------------------+
| Likelihood             | High (4)                                            |
+------------------------+-----------------------------------------------------+
| Total Risk Rating      | Critical (20)                                       |
+------------------------+-----------------------------------------------------+
| Mitigations            | | 1) When possible avoid the use of calls to        |
|                        |   ``panic()``, especially as a result of invalid    |
|                        | | parameter checks.                                 |
|                        | | 2) ``panic()`` should not halt/stall a PE, as     |
|                        |   most of the implementations do, instead, it should|
|                        | | notify EL-3 Firmware of the situation for it to   |
|                        |   take the appropriate action (such as disable RMM  |
|                        | | for the entire system).                           |
+------------------------+-----------------------------------------------------+
| Mitigations            | | 1) Partially/Platform specific.                   |
| implemented?           |   The use of ``panic()`` is sparse and avoided when |
|                        | | possible. Some review of all the calls should be  |
|                        |   done, though.                                     |
|                        | | 2) No.                                            |
|                        |   Current implementation of ``panic()`` stalls the  |
|                        |   PE calling it.                                    |
+------------------------+-----------------------------------------------------+
| Pending actions?       | | 1) Review the current use of ``panic()``.         |
|                        | | 2) Reimplement ``panic()`` to notify the condition|
|                        |   to EL-3 Firmware for further decission making.    |
+------------------------+-----------------------------------------------------+

+------------------------+-----------------------------------------------------+
| ID                     | 9                                                   |
+========================+=====================================================+
| Threat                 | | Incorrect boot arguments (including boot manifest)|
|                        |   might halt/stall a PE.                            |
|                        |                                                     |
|                        | | If ``panic()`` is invoked as part of the RMM boot |
|                        |   process, either during cold or warm boot paths,   |
|                        | | the calling PE might get halted/stalled.          |
+------------------------+-----------------------------------------------------+
| Diagram Elements       | DF1                                                 |
+------------------------+-----------------------------------------------------+
| Assets                 | Availability                                        |
+------------------------+-----------------------------------------------------+
| Threat Agent           | Faulty code at Root Level                           |
+------------------------+-----------------------------------------------------+
| Threat Type            | Denial of Service                                   |
+------------------------+-----------------------------------------------------+
| Impact                 | Critical (5)                                        |
+------------------------+-----------------------------------------------------+
| Likelihood             | High (4)                                            |
+------------------------+-----------------------------------------------------+
| Total Risk Rating      | Critical (20)                                       |
+------------------------+-----------------------------------------------------+
| Mitigations            | | 1) If the boot arguments are invalid, notify EL-3 |
|                        |   Firmware of the situation for it to take the      |
|                        | | appropriate action.                               |
|                        | | 2) Replace any call of ``panic()`` on the         |
|                        |   cold/warm path by returning to EL-3 with an error |
|                        | | message.                                          |
+------------------------+-----------------------------------------------------+
| Mitigations            | | 1) Yes/Platform specific.                         |
| implemented?           |   The `RMM Boot Interface specification`_ defines   |
|                        | | the checks done at boot time and all the possible |
|                        |   error codes returned to EL-3 Firmware. It also    |
|                        | | specifies the action to take by EL-3 upon failure.|
|                        | | 2) Partially.                                     |
|                        |   A review of the RMM boot paths to replace any     |
|                        |   ocurrence of ``panic()`` is needed.               |
+------------------------+-----------------------------------------------------+
| Pending actions?       | | 2) Review the current use of ``panic()`` during   |
|                        |   the boot stages.                                  |
+------------------------+-----------------------------------------------------+

+------------------------+----------------------------------------------------+
| ID                     | 10                                                 |
+========================+====================================================+
| Threat                 | | Misconfiguration of the S1, and, especially, S2  |
|                        |   MMU tables may allow Realms to access sensitive  |
|                        | | data belonging to other Realms.                  |
|                        |                                                    |
|                        | | A misconfiguration of the MMU could lead to an   |
|                        |   open door for software running in other worlds to|
|                        | | access sensitive data or even execute code if the|
|                        |   proper security mechanisms are not in place.     |
+------------------------+----------------------------------------------------+
| Diagram Elements       | DF1                                                |
+------------------------+----------------------------------------------------+
| Assets                 | Sensitive Data, Code execution                     |
+------------------------+----------------------------------------------------+
| Threat Agent           | Faulty code at Root Level                          |
+------------------------+----------------------------------------------------+
| Threat Type            | Information Disclosure, Elevation of Privilege     |
+------------------------+----------------------------------------------------+
| Impact                 | Critical (5)                                       |
+------------------------+----------------------------------------------------+
| Likelihood             | High (4)                                           |
+------------------------+----------------------------------------------------+
| Total Risk Rating      | Critical (20)                                      |
+------------------------+----------------------------------------------------+
| Mitigations            | | When configuring access permissions, the         |
|                        |   principle of least privilege ought to be         |
|                        | | enforced. This means we should not grant more    |
|                        |   privileges than strictly needed, e.g. code       |
|                        | | should be read-only executable, read-only data   |
|                        |   should be read-only execute-never, and so on.    |
+------------------------+----------------------------------------------------+
| Mitigations            | | RMM does not expose the translation library API  |
| implemented?           |   and memory permission is configured at boot time.|
|                        | | This reduces the surface of attack.              |
|                        |                                                    |
|                        | | Memory layout, passed through the Boot Manifest  |
|                        |   to RMM, is validated at boot time.               |
+------------------------+----------------------------------------------------+
| Pending actions?       | None                                               |
+------------------------+----------------------------------------------------+

+------------------------+-----------------------------------------------------+
| ID                     | 11                                                  |
+========================+=====================================================+
| Threat                 | | Leaving sensitive information in the memory,      |
|                        |   can allow an adversary to retrieve them.          |
|                        |                                                     |
|                        | | Accidentally leaving not-needed sensitive data in |
|                        |   internal buffers can leak them if an adversary    |
|                        | | gains access to memory due to a vulnerability.    |
+------------------------+-----------------------------------------------------+
| Diagram Elements       | DF1, DF4, DF5                                       |
+------------------------+-----------------------------------------------------+
| Assets                 | Sensitive Data                                      |
+------------------------+-----------------------------------------------------+
| Threat Agent           | Faulty code at Root Level, RelmCode                 |
+------------------------+-----------------------------------------------------+
| Threat Type            | Information Disclosure                              |
+------------------------+-----------------------------------------------------+
| Impact                 |  Critical (5)                                       |
+------------------------+-----------------------------------------------------+
| Likelihood             |  Medium (3)                                         |
+------------------------+-----------------------------------------------------+
| Total Risk Rating      |  High (15)                                          |
+------------------------+-----------------------------------------------------+
| Mitigations            | | Clear/scrub the sensitive data from internal      |
|                        |   buffers as soon as they are not needed anymore.   |
+------------------------+-----------------------------------------------------+
| Mitigations            | | Yes / Platform specific                           |
| implemented?           |                                                     |
+------------------------+-----------------------------------------------------+
| Pending actions?       | None                                                |
+------------------------+-----------------------------------------------------+

+------------------------+-----------------------------------------------------+
| ID                     | 12                                                  |
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
| ID                     | 13                                                  |
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
| Threat Agent           | Faulty code at Root Level, HostSoftware             |
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
| ID                     | 14                                                  |
+========================+=====================================================+
| Threat                 | | Use of AMU, PMU and MPAM statistics to increase   |
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
+------------------------+-----------------------------------------------------+
| Mitigations            | | No. It is up to the platform and EL3 firmware to  |
|                        |   disable MPAM or context switch it to protect the  |
|                        | | Realm world.                                      |
+------------------------+-----------------------------------------------------+
| Pending actions?       | None.                                               |
+------------------------+-----------------------------------------------------+

+------------------------+------------------------------------------------------------+
| ID                     | 15                                                         |
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
|                        |   RMM uses a combination of manual code reviews            |
|                        | | and automated program analysis and testing to            |
|                        |   detect and fix bugs, included but not limited in         |
|                        | | drivers/libraries controlling hardware IP. All RMM       |
|                        |   code including platform code goes through manual         |
|                        | | code reviews. Additionally, static code analysis         |
|                        |   is performed on all RMM code. The code is also tested    |
|                        | | on FVP platforms.                                        |
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
