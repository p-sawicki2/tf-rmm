.. SPDX-License-Identifier: BSD-3-Clause
.. SPDX-FileCopyrightText: Copyright TF-RMM Contributors.

Threat Analysis components
==========================

In this section we identify all the possible *actors* involved in the Threat
Model.

For each threat, we will identify the *asset* that is under threat, the
*threat agent* and the *threat type*. Each threat will be given a *risk rating*
that represents the impact and likelihood of that threat.

******
Assets
******

We have identified the following assets for RMM:

.. table:: Table 2: RMM Assets

  +--------------------+---------------------------------------------------+
  | Asset              | Description                                       |
  +====================+===================================================+
  | Sensitive Data     | | These include sensitive data that an attacker   |
  |                    |   must not be able to tamper with (e.g. the Realm |
  |                    | | Attestation Key) or see (e.g. secure logs,      |
  |                    |   debugging information such as crash reports).   |
  +--------------------+---------------------------------------------------+
  | Code Execution     | | This represents the requirement that the        |
  |                    |   platform should run only code on the RMM image  |
  |                    | | and that no scalation of privilege or code      |
  |                    |   injected by an attacker should run on R-EL2     |
  |                    | | or R-ELx.                                       |
  +--------------------+---------------------------------------------------+
  | Availability       | | This represents the requirement that RMM        |
  |                    |   services should always be available for use.    |
  +--------------------+---------------------------------------------------+

*************
Threat Agents
*************

To understand the attack surface, it is important to identify potential
attackers, i.e. attack entry points. The following threat agents are
in scope of this threat model.

.. table:: Table 3: Threat Agents

  +-------------------+-------------------------------------------------------+
  | Threat Agent      | Description                                           |
  +===================+=======================================================+
  |   Faulty code at  | | Malicious or faulty code running at Root Level      |
  |   Root Level      |   (e.g. EL-3 Firmware).                               |
  +-------------------+-------------------------------------------------------+
  |   RealmCode       | | Malicious or faulty code running in the Realm       |
  |                   |   world, including R-EL0 and R-EL1 levels.            |
  +-------------------+-------------------------------------------------------+
  |   HostSoftware    | | Malicious or faulty code running in the Secure or   |
  |                   |   Non-Secure world, EL0 and EL1 levels.               |
  +-------------------+-------------------------------------------------------+
  |   RMMCode         | | The very own software that we are trying to protect |
  |                   |   might have bugs and faults that can lead to         |
  |                   | | sensitive data leaks, faults, or be taken advantage |
  |                   |   to by an adversary.                                 |
  +-------------------+-------------------------------------------------------+
  |   AppDebug        | | Physical adversary using  debug signals to access   |
  |                   |   RMM resources.                                      |
  +-------------------+-------------------------------------------------------+
  |  PhysicalAccess   | | Physical adversary having access to external device |
  |                   |   communication bus and to external flash             |
  |                   | | communication bus using common hardware.            |
  +-------------------+-------------------------------------------------------+

.. note::

  In this threat model, an advanced physical attacker that has the capability
  to tamper with a hardware (e.g. "rewiring" a chip using a focused
  ion beam (FIB) workstation or decapsulate the chip using chemicals) is
  considered out-of-scope.

  Likewise, any threat which needs to be metigated by the RME hardware as well
  as by EL3 Root code is out of the scope of this Threat Model.

************
Threat Types
************

In this threat model we categorize threats using the `STRIDE threat
analysis technique`_. In this technique a threat is categorized as one
or more of these types: ``Spoofing``, ``Tampering``, ``Repudiation``,
``Information disclosure``, ``Denial of service`` or
``Elevation of privilege``.

*******************
Threat Risk Ratings
*******************

For each threat identified, a risk rating that ranges
from *informational* to *critical* is given based on the likelihood of the
threat occurring if a mitigation is not in place, and the impact of the
threat (i.e. how severe the consequences could be). Table 4 explains each
rating in terms of score, impact and likelihood.

.. table:: Table 4: Rating and score as applied to impact and likelihood

  +-----------------------+-------------------------+---------------------------+
  | **Rating (Score)**    | **Impact**              | **Likelihood**            |
  +=======================+=========================+===========================+
  | Critical (5)          | | Extreme impact to     | | Threat is almost        |
  |                       |   entire organization   |   certain to be exploited.|
  |                       |   if exploited.         |                           |
  |                       |                         | | Knowledge of the threat |
  |                       |                         |   and how to exploit it   |
  |                       |                         |   are in the public       |
  |                       |                         |   domain.                 |
  +-----------------------+-------------------------+---------------------------+
  | High (4)              | | Major impact to entire| | Threat is relatively    |
  |                       |   organization or single|   easy to detect and      |
  |                       |   line of business if   |   exploit by an attacker  |
  |                       |   exploited             |   with little skill.      |
  +-----------------------+-------------------------+---------------------------+
  | Medium (3)            | | Noticeable impact to  | | A knowledgeable insider |
  |                       |   line of business if   |   or expert attacker could|
  |                       |   exploited.            |   exploit the threat      |
  |                       |                         | | without much difficulty.|
  +-----------------------+-------------------------+---------------------------+
  | Low (2)               | | Minor damage if       | | Exploiting the threat   |
  |                       |   exploited or could    |   would require           |
  |                       |   be used in conjunction| | considerable expertise  |
  |                       |   with other            |   and resources           |
  |                       | | vulnerabilities to    |                           |
  |                       |   perform a more serious|                           |
  |                       |   attack                |                           |
  +-----------------------+-------------------------+---------------------------+
  | Informational (1)     | | Poor programming      | | Threat is not likely    |
  |                       |   practice or poor      |   to be exploited on its  |
  |                       |   design decision that  |   own, but may be used to |
  |                       |   may not represent an  | | gain information for    |
  |                       | | immediate risk on its |   launching another       |
  |                       |   own, but may have     |   attack                  |
  |                       |   security implications |                           |
  |                       |   if multiplied and/or  |                           |
  |                       | | combined with other   |                           |
  |                       |   threats.              |                           |
  +-----------------------+-------------------------+---------------------------+

Aggregate risk scores are assigned to identified threats.
Specifically, the impact score multiplied by the likelihood score.
For example, a threat with high likelihood and low impact would have an
aggregate risk score of eight (8); that is, four (4) for high likelihood
multiplied by two (2) for low impact. The aggregate risk score determines
the finding's overall risk level, as shown in the following table.

.. table:: Table 5: Overall risk levels and corresponding aggregate scores

  +---------------------+-----------------------------------+
  | Overall Risk Level  | Aggregate Risk Score              |
  |                     | (Impact multiplied by Likelihood) |
  +=====================+===================================+
  | Critical            | 20–25                             |
  +---------------------+-----------------------------------+
  | High                | 12–19                             |
  +---------------------+-----------------------------------+
  | Medium              | 6–11                              |
  +---------------------+-----------------------------------+
  | Low                 | 2–5                               |
  +---------------------+-----------------------------------+
  | Informational       | 1                                 |
  +---------------------+-----------------------------------+

The likelihood and impact of a threat depends on the
target environment in which RMM is running. For example, attacks
that require physical access are unlikely in server environments while
they are more common in Internet of Things (IoT) environments.
In this threat model we only consider ``Server`` target environments.

--------------

.. _STRIDE threat analysis technique: https://docs.microsoft.com/en-us/azure/security/develop/threat-modeling-tool-threats#stride-model
