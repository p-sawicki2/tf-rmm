/*
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef SMC_RMI_H
#define SMC_RMI_H

#include <smc.h>

/*
 * This file describes the Realm Management Interface (RMI) Application Binary
 * Interface (ABI) for SMC calls made from Non-secure state to the RMM and
 * serviced by the RMM.
 */

/*
 * The major version number of the RMI implementation.  Increase this whenever
 * the binary format or semantics of the SMC calls change.
 */
#define RMI_ABI_VERSION_MAJOR		UL(1)

/*
 * The minor version number of the RMI implementation.  Increase this when
 * a bug is fixed, or a feature is added without breaking binary compatibility.
 */
#define RMI_ABI_VERSION_MINOR		UL(0)

#define RMI_ABI_VERSION			((RMI_ABI_VERSION_MAJOR << U(16)) | \
					  RMI_ABI_VERSION_MINOR)

#define RMI_ABI_VERSION_GET_MAJOR(_version) ((_version) >> U(16))
#define RMI_ABI_VERSION_GET_MINOR(_version) ((_version) & U(0xFFFF))

#define SMC64_RMI_FID(_offset)		SMC64_STD_FID(RMI, _offset)

#define IS_SMC64_RMI_FID(_fid)		IS_SMC64_STD_FAST_IN_RANGE(RMI, _fid)

/* Command completed successfully. index is zero. */
#define RMI_SUCCESS			U(0)

/*
 * The value of a command input value caused the command to fail.
 * Index is zero.
 */
#define RMI_ERROR_INPUT			U(1)

/*
 * An attribute of a Realm does not match the expected value.
 * index varies between usages.
 */
#define RMI_ERROR_REALM			U(2)

/*
 * An attribute of a REC does not match the expected value.
 * Index is zero.
 */
#define RMI_ERROR_REC			U(3)

/*
 * An RTT walk terminated before reaching the target RTT level, or reached
 * an RTTE with an unexpected value. index: RTT level at which the walk
 * terminated
 */
#define RMI_ERROR_RTT			U(4)

/* An attribute of a device does not match the expected value */
#define RMI_ERROR_DEVICE		U(5)

/* The command is not supported */
#define RMI_ERROR_NOT_SUPPORTED		U(6)

/* RTTE in an auxiliary RTT contained an unexpected value */
#define RMI_ERROR_RTT_AUX		U(7)

/* Max number of RMI Status Errors. */
#define RMI_ERROR_MAX_COUNT		U(8)

/*
 * The number of GPRs (starting from X0) that are
 * configured by the host when a REC is created.
 */
#define REC_CREATE_NR_GPRS		U(8)

#define REC_PARAMS_FLAG_RUNNABLE	(UL(1) << 0)

/*
 * The number of GPRs (starting from X0) per voluntary exit context.
 * Per SMCCC.
 */
#define REC_EXIT_NR_GPRS		U(31)

/* RmiHashAlgorithm type */
#define RMI_HASH_SHA_256		0U
#define RMI_HASH_SHA_512		1U

/* Maximum number of Interrupt Controller List Registers */
#define REC_GIC_NUM_LRS			U(16)

#ifndef CBMC
/* Maximum number of auxiliary granules required for a REC */
#define MAX_REC_AUX_GRANULES		U(16)
#else /* CBMC */
#define MAX_REC_AUX_GRANULES		U(1)
#endif /* CBMC */

/* Whether Host has completed emulation for an Emulatable Data Abort */
#define REC_ENTRY_FLAG_EMUL_MMIO	(UL(1) << 0)

/* Whether to inject a Synchronous External Abort into Realm */
#define REC_ENTRY_FLAG_INJECT_SEA	(UL(1) << 1)

/* Whether to trap WFI/WFE execution by Realm */
#define REC_ENTRY_FLAG_TRAP_WFI		(UL(1) << 2)
#define REC_ENTRY_FLAG_TRAP_WFE		(UL(1) << 3)

/* Host response to RIPAS change request */
#define REC_ENTRY_FLAG_RIPAS_RESPONSE	(UL(1) << 4)

/* Maximum number of RmiAddressRange paramenter passed to PDEV create */
#define PDEV_PARAM_ADDR_RANGE_MAX	U(16)
/* Maximum number of aux granules paramenter passed to PDEV create */
#define PDEV_PARAM_AUX_GRANULES_MAX	U(16)

/*
 * RmiRecExitReason represents the reason for a REC exit.
 * This is returned to NS hosts via RMI_REC_ENTER::run_ptr.
 */
#define RMI_EXIT_SYNC			U(0)
#define RMI_EXIT_IRQ			U(1)
#define RMI_EXIT_FIQ			U(2)
#define RMI_EXIT_PSCI			U(3)
#define RMI_EXIT_RIPAS_CHANGE		U(4)
#define RMI_EXIT_HOST_CALL		U(5)
#define RMI_EXIT_SERROR			U(6)
#define RMI_EXIT_IO			U(7)

/* RmiRttEntryState represents the state of an RTTE */
#define RMI_UNASSIGNED		UL(0)
#define RMI_ASSIGNED		UL(1)
#define RMI_TABLE		UL(2)

/* RmiFeature enumerations */
#define RMI_FEATURE_FALSE	UL(0)
#define RMI_FEATURE_TRUE	UL(1)

/* RmiFeatureRegister0 format */
#define RMI_FEATURE_REGISTER_0_INDEX		UL(0)

#define RMI_FEATURE_REGISTER_0_S2SZ_SHIFT	UL(0)
#define RMI_FEATURE_REGISTER_0_S2SZ_WIDTH	UL(8)

#define RMI_FEATURE_REGISTER_0_LPA2_SHIFT	UL(8)
#define RMI_FEATURE_REGISTER_0_LPA2_WIDTH	UL(1)

#define RMI_FEATURE_REGISTER_0_SVE_EN_SHIFT	UL(9)
#define RMI_FEATURE_REGISTER_0_SVE_EN_WIDTH	UL(1)

#define RMI_FEATURE_REGISTER_0_SVE_VL_SHIFT	UL(10)
#define RMI_FEATURE_REGISTER_0_SVE_VL_WIDTH	UL(4)

#define RMI_FEATURE_REGISTER_0_NUM_BPS_SHIFT	UL(14)
#define RMI_FEATURE_REGISTER_0_NUM_BPS_WIDTH	UL(4)

#define RMI_FEATURE_REGISTER_0_NUM_WPS_SHIFT	UL(18)
#define RMI_FEATURE_REGISTER_0_NUM_WPS_WIDTH	UL(4)

#define RMI_FEATURE_REGISTER_0_PMU_EN_SHIFT	UL(22)
#define RMI_FEATURE_REGISTER_0_PMU_EN_WIDTH	UL(1)

#define RMI_FEATURE_REGISTER_0_PMU_NUM_CTRS_SHIFT	UL(23)
#define RMI_FEATURE_REGISTER_0_PMU_NUM_CTRS_WIDTH	UL(5)

#define RMI_FEATURE_REGISTER_0_HASH_SHA_256_SHIFT	UL(28)
#define RMI_FEATURE_REGISTER_0_HASH_SHA_256_WIDTH	UL(1)

#define RMI_FEATURE_REGISTER_0_HASH_SHA_512_SHIFT	UL(29)
#define RMI_FEATURE_REGISTER_0_HASH_SHA_512_WIDTH	UL(1)

#define RMI_FEATURE_REGISTER_0_DA_EN_SHIFT		UL(30)
#define RMI_FEATURE_REGISTER_0_DA_EN_WIDTH		UL(1)

#define RMI_FEATURE_REGISTER_0_PDEV_NUM_AUX_SHIFT	UL(31)
#define RMI_FEATURE_REGISTER_0_PDEV_NUM_AUX_WIDTH	UL(4)

/* The RmiRipas enumeration represents realm IPA state */

/* Address where no Realm resources are mapped */
#define RMI_EMPTY	UL(0)

/* Address where private code or data owned by the Realm is mapped */
#define RMI_RAM		UL(1)

/* Address which is inaccessible to the Realm due to an action taken by the Host */
#define RMI_DESTROYED	UL(2)

/* Address where MMIO of an assigned Realm device is mapped. */
#define RMI_IO		UL(3)

/* RmiPmuOverflowStatus enumeration representing PMU overflow status */
#define RMI_PMU_OVERFLOW_NOT_ACTIVE	U(0)
#define RMI_PMU_OVERFLOW_ACTIVE		U(1)

/*
 * RmiResponse enumeration represents whether the Host accepted
 * or rejected a Realm request
 */
#define RMI_ACCEPT	0U
#define RMI_REJECT	1U

/*
 * arg0: Requested interface version
 *
 * ret0: Command return status
 * ret1: Lower implemented interface revision
 * ret2: Higher implemented interface revision
 */
#define SMC_RMI_VERSION				SMC64_RMI_FID(U(0x0))

/*
 * arg0 == target granule address
 */
#define SMC_RMI_GRANULE_DELEGATE		SMC64_RMI_FID(U(0x1))

/*
 * arg0 == target granule address
 */
#define SMC_RMI_GRANULE_UNDELEGATE		SMC64_RMI_FID(U(0x2))

/* RmiDataMeasureContent type */
#define RMI_NO_MEASURE_CONTENT	U(0)
#define RMI_MEASURE_CONTENT	U(1)

/*
 * arg0 == RD address
 * arg1 == data address
 * arg2 == map address
 * arg3 == SRC address
 * arg4 == flags
 */
#define SMC_RMI_DATA_CREATE			SMC64_RMI_FID(U(0x3))

/*
 * arg0 == RD address
 * arg1 == data address
 * arg2 == map address
 */
#define SMC_RMI_DATA_CREATE_UNKNOWN		SMC64_RMI_FID(U(0x4))

/*
 * arg0 == RD address
 * arg1 == map address
 *
 * ret1 == Address(PA) of the DATA granule, if ret0 == RMI_SUCCESS.
 *         Otherwise, undefined.
 * ret2 == Top of the non-live address region. Only valid
 *         if ret0 == RMI_SUCCESS or ret0 == (RMI_ERROR_RTT, x)
 */
#define SMC_RMI_DATA_DESTROY			SMC64_RMI_FID(U(0x5))

/*
 * arg0 == RD address
 */
#define SMC_RMI_REALM_ACTIVATE			SMC64_RMI_FID(U(0x7))

/*
 * arg0 == RD address
 * arg1 == struct rmi_realm_params address
 */
#define SMC_RMI_REALM_CREATE			SMC64_RMI_FID(U(0x8))

/*
 * arg0 == RD address
 */
#define SMC_RMI_REALM_DESTROY			SMC64_RMI_FID(U(0x9))

/*
 * arg0 == RD address
 * arg1 == REC address
 * arg2 == struct rmm_rec address
 */
#define SMC_RMI_REC_CREATE			SMC64_RMI_FID(U(0xA))

/*
 * arg0 == REC address
 */
#define SMC_RMI_REC_DESTROY			SMC64_RMI_FID(U(0xB))

/*
 * arg0 == rec address
 * arg1 == struct rec_run address
 */
#define SMC_RMI_REC_ENTER			SMC64_RMI_FID(U(0xC))

/*
 * arg0 == RD address
 * arg1 == RTT address
 * arg2 == map address
 * arg3 == level
 */
#define SMC_RMI_RTT_CREATE			SMC64_RMI_FID(U(0xD))

/*
 * arg0 == RD address
 * arg1 == map address
 * arg2 == level
 *
 * ret1 == Address (PA) of the RTT, if ret0 == RMI_SUCCESS
 *         Otherwise, undefined.
 * ret2 == Top of the non-live address region. Only valid
 *         if ret0 == RMI_SUCCESS or ret0 == (RMI_ERROR_RTT, x)
 */
#define SMC_RMI_RTT_DESTROY			SMC64_RMI_FID(U(0xE))

/*
 * arg0 == RD address
 * arg1 == map address
 * arg2 == level
 * arg3 == s2tte
 */
#define SMC_RMI_RTT_MAP_UNPROTECTED		SMC64_RMI_FID(U(0xF))

/*
 * arg0 == RD address
 * arg1 == map address
 * arg2 == level
 *
 * ret1 == level
 * ret2 == s2tte type
 * ret3 == s2tte
 * ret4 == ripas
 * if ret0 == RMI_SUCCESS, otherwise, undefined.
 */
#define SMC_RMI_RTT_READ_ENTRY			SMC64_RMI_FID(U(0x11))

/*
 * arg0 == RD address
 * arg1 == map address
 * arg2 == level
 */
#define SMC_RMI_RTT_UNMAP_UNPROTECTED		SMC64_RMI_FID(U(0x12))

/*
 * arg0 == calling rec address
 * arg1 == target rec address
 */
#define SMC_RMI_PSCI_COMPLETE			SMC64_RMI_FID(U(0x14))

/*
 * arg0 == Feature register index
 */
#define SMC_RMI_FEATURES			SMC64_RMI_FID(U(0x15))

/*
 * arg0 == RD address
 * arg1 == map address
 * arg2 == level
 *
 * ret1 == Address(PA) of the RTT folded, if ret0 == RMI_SUCCESS
 */
#define SMC_RMI_RTT_FOLD			SMC64_RMI_FID(U(0x16))

/*
 * arg0 == RD address
 */
#define SMC_RMI_REC_AUX_COUNT			SMC64_RMI_FID(U(0x17))

/*
 * arg0 == RD address
 * arg1 == start address
 * arg2 == end address
 *
 * ret1 == Top of the address range where the RIPAS was updated,
 * if ret0 == RMI_SUCCESS
 */
#define SMC_RMI_RTT_INIT_RIPAS			SMC64_RMI_FID(U(0x18))

/*
 * arg0 == RD address
 * arg1 == REC address
 * arg2 == start address
 * arg3 == end address
 *
 * ret1 == Top of the address range where the RIPAS was updated,
 *	   if ret0 == RMI_SUCCESS
 */
#define SMC_RMI_RTT_SET_RIPAS			SMC64_RMI_FID(U(0x19))

#define SMC_RMI_GRANULE_IO_DELEGATE		SMC64_RMI_FID(U(0x20))
#define SMC_RMI_GRANULE_IO_UNDELEGATE		SMC64_RMI_FID(U(0x21))
#define SMC_RMI_IO_CREATE			SMC64_RMI_FID(U(0x22))
#define SMC_RMI_IO_DESTROY			SMC64_RMI_FID(U(0x23))
#define SMC_RMI_PDEV_ABORT			SMC64_RMI_FID(U(0x24))
#define SMC_RMI_PDEV_COMMUNICATE		SMC64_RMI_FID(U(0x25))
#define SMC_RMI_PDEV_CREATE			SMC64_RMI_FID(U(0x26))
#define SMC_RMI_PDEV_DESTROY			SMC64_RMI_FID(U(0x27))
#define SMC_RMI_PDEV_GET_STATE			SMC64_RMI_FID(U(0x28))
#define SMC_RMI_PDEV_IDE_RESET			SMC64_RMI_FID(U(0x29))
#define SMC_RMI_PDEV_NOTIFY			SMC64_RMI_FID(U(0x2A))
#define SMC_RMI_PDEV_SET_KEY			SMC64_RMI_FID(U(0x2B))
#define SMC_RMI_PDEV_STOP			SMC64_RMI_FID(U(0x2C))
#define SMC_RMI_RTT_AUX_CREATE			SMC64_RMI_FID(U(0x2D))
#define SMC_RMI_RTT_AUX_DESTROY			SMC64_RMI_FID(U(0x2E))
#define SMC_RMI_RTT_AUX_FOLD			SMC64_RMI_FID(U(0x2F))
#define SMC_RMI_RTT_AUX_MAP_PROTECTED		SMC64_RMI_FID(U(0x30))
#define SMC_RMI_RTT_AUX_MAP_UNPROTECTED		SMC64_RMI_FID(U(0x31))
#define SMC_RMI_RTT_AUX_READ_ENTRY		SMC64_RMI_FID(U(0x32))
#define SMC_RMI_RTT_AUX_UNMAP_PROTECTED		SMC64_RMI_FID(U(0x33))
#define SMC_RMI_RTT_AUX_UNMAP_UNPROTECTED	SMC64_RMI_FID(U(0x34))
#define SMC_RMI_VDEV_ABORT			SMC64_RMI_FID(U(0x35))
#define SMC_RMI_VDEV_COMMUNICATE		SMC64_RMI_FID(U(0x36))
#define SMC_RMI_VDEV_CREATE			SMC64_RMI_FID(U(0x37))
#define SMC_RMI_VDEV_DESTROY			SMC64_RMI_FID(U(0x38))
#define SMC_RMI_VDEV_GET_STATE			SMC64_RMI_FID(U(0x39))
#define SMC_RMI_VDEV_STOP			SMC64_RMI_FID(U(0x3A))
#define SMC_RMI_RTT_SET_S2AP			SMC64_RMI_FID(U(0x3B))

/* Size of Realm Personalization Value */
#ifndef CBMC
#define RPV_SIZE		64
#else
/*
 * Small RPV size so that `struct rd` fits in the reduced sized granule defined
 * for CBMC
 */
#define RPV_SIZE		1
#endif

/* RmiRealmFlags format */
#define RMI_REALM_FLAGS_LPA2_SHIFT	UL(0)
#define RMI_REALM_FLAGS_LPA2_WIDTH	UL(1)

#define RMI_REALM_FLAGS_SVE_SHIFT	UL(1)
#define RMI_REALM_FLAGS_SVE_WIDTH	UL(1)

#define RMI_REALM_FLAGS_PMU_SHIFT	UL(2)
#define RMI_REALM_FLAGS_PMU_WIDTH	UL(1)

#ifndef __ASSEMBLER__
/*
 * Defines member of structure and reserves space
 * for the next member with specified offset.
 */
#define SET_MEMBER_RMI	SET_MEMBER

/*
 * The Realm attribute parameters are shared by the Host via
 * RMI_REALM_CREATE::params_ptr. The values can be observed or modified
 * either by the Host or by the Realm.
 */
struct rmi_realm_params {
	/* Flags */
	SET_MEMBER_RMI(unsigned long flags, 0, 0x8);		/* Offset 0 */
	/* Requested IPA width */
	SET_MEMBER_RMI(unsigned int s2sz, 0x8, 0x10);		/* 0x8 */
	/* Requested SVE vector length */
	SET_MEMBER_RMI(unsigned int sve_vl, 0x10, 0x18);	/* 0x10 */
	/* Requested number of breakpoints */
	SET_MEMBER_RMI(unsigned int num_bps, 0x18, 0x20);	/* 0x18 */
	/* Requested number of watchpoints */
	SET_MEMBER_RMI(unsigned int num_wps, 0x20, 0x28);	/* 0x20 */
	/* Requested number of PMU counters */
	SET_MEMBER_RMI(unsigned int pmu_num_ctrs, 0x28, 0x30);	/* 0x28 */
	/* Measurement algorithm */
	SET_MEMBER_RMI(unsigned char algorithm, 0x30, 0x400);	/* 0x30 */
	/* Realm Personalization Value */
	SET_MEMBER_RMI(unsigned char rpv[RPV_SIZE], 0x400, 0x800); /* 0x400 */
	SET_MEMBER_RMI(struct {
			/* Virtual Machine Identifier */
			unsigned short vmid;			/* 0x800 */
			/* Realm Translation Table base */
			unsigned long rtt_base;			/* 0x808 */
			/* RTT starting level */
			long rtt_level_start;			/* 0x810 */
			/* Number of starting level RTTs */
			unsigned int rtt_num_start;		/* 0x818 */
		   }, 0x800, 0x1000);
};

/*
 * The REC attribute parameters are shared by the Host via
 * RMI_REC_CREATE::params_ptr. The values can be observed or modified
 * either by the Host or by the Realm which owns the REC.
 */
struct rmi_rec_params {
	/* Flags */
	SET_MEMBER_RMI(unsigned long flags, 0, 0x100);	/* Offset 0 */
	/* MPIDR of the REC */
	SET_MEMBER_RMI(unsigned long mpidr, 0x100, 0x200);	/* 0x100 */
	/* Program counter */
	SET_MEMBER_RMI(unsigned long pc, 0x200, 0x300);	/* 0x200 */
	/* General-purpose registers */
	SET_MEMBER_RMI(unsigned long gprs[REC_CREATE_NR_GPRS], 0x300, 0x800); /* 0x300 */
	SET_MEMBER_RMI(struct {
			/* Number of auxiliary Granules */
			unsigned long num_aux;			/* 0x800 */
			/* Addresses of auxiliary Granules */
			unsigned long aux[MAX_REC_AUX_GRANULES];/* 0x808 */
		   }, 0x800, 0x1000);
};

/*
 * Structure contains data passed from the Host to the RMM on REC entry
 */
struct rmi_rec_enter {
	/* Flags */
	SET_MEMBER_RMI(unsigned long flags, 0, 0x200);	/* Offset 0 */
	/* General-purpose registers */
	SET_MEMBER_RMI(unsigned long gprs[REC_EXIT_NR_GPRS], 0x200, 0x300); /* 0x200 */
	SET_MEMBER_RMI(struct {
			/* GICv3 Hypervisor Control Register */
			unsigned long gicv3_hcr;			/* 0x300 */
			/* GICv3 List Registers */
			unsigned long gicv3_lrs[REC_GIC_NUM_LRS];	/* 0x308 */
		   }, 0x300, 0x800);
};

/*
 * RmiIoAction
 * Represents realm action which triggered REC exit due to IO.
 * Width: 8 bits
 */
typedef unsigned char rmi_io_action_t;
#define RMI_IO_ACTION_GET_INTERFACE_REPORT	U(0)
#define RMI_IO_ACTION_GET_MEASUREMENTS		U(1)
#define RMI_IO_ACTION_LOCK			U(2)
#define RMI_IO_ACTION_START			U(3)
#define RMI_IO_ACTION_STOP			U(4)

/*
 * RmiRecExitFlags
 * Fieldset contains flags provided by the RMM during REC exit.
 * Width: 64 bits
 */
typedef unsigned long rmi_rec_exit_flags_t;
#define RMI_REC_EXIT_FLAGS_RIPAS_IO_SHARED_SHIFT	U(0)
#define RMI_REC_EXIT_FLAGS_RIPAS_IO_SHARED_WIDTH	U(1)

/*
 * Structure contains data passed from the RMM to the Host on REC exit
 */
struct rmi_rec_exit {
	/* Exit reason */
	SET_MEMBER_RMI(unsigned long exit_reason, 0, 0x8);/* Offset 0 */
	/* RmiRecExitFlags: Flags */
	SET_MEMBER_RMI(rmi_rec_exit_flags_t flags, 0x8, 0x100);/* 0x8 */
	SET_MEMBER_RMI(struct {
			/* Exception Syndrome Register */
			unsigned long esr;		/* 0x100 */
			/* Fault Address Register */
			unsigned long far;		/* 0x108 */
			/* Hypervisor IPA Fault Address register */
			unsigned long hpfar;		/* 0x110 */
		   }, 0x100, 0x200);
	/* General-purpose registers */
	SET_MEMBER_RMI(unsigned long gprs[REC_EXIT_NR_GPRS], 0x200, 0x300); /* 0x200 */
	SET_MEMBER_RMI(struct {
			/* GICv3 Hypervisor Control Register */
			unsigned long gicv3_hcr;	/* 0x300 */
			/* GICv3 List Registers */
			unsigned long gicv3_lrs[REC_GIC_NUM_LRS]; /* 0x308 */
			/* GICv3 Maintenance Interrupt State Register */
			unsigned long gicv3_misr;	/* 0x388 */
			/* GICv3 Virtual Machine Control Register */
			unsigned long gicv3_vmcr;	/* 0x390 */
		   }, 0x300, 0x400);
	SET_MEMBER_RMI(struct {
			/* Counter-timer Physical Timer Control Register */
			unsigned long cntp_ctl;		/* 0x400 */
			/* Counter-timer Physical Timer CompareValue Register */
			unsigned long cntp_cval;	/* 0x408 */
			/* Counter-timer Virtual Timer Control Register */
			unsigned long cntv_ctl;		/* 0x410 */
			/* Counter-timer Virtual Timer CompareValue Register */
			unsigned long cntv_cval;	/* 0x418 */
		   }, 0x400, 0x500);
	SET_MEMBER_RMI(struct {
			/* Base address of pending RIPAS change */
			unsigned long ripas_base;	/* 0x500 */
			/* Size of pending RIPAS change */
			unsigned long ripas_top;	/* 0x508 */
			/* RIPAS value of pending RIPAS change */
			unsigned char ripas_value;	/* 0x510 */
		   }, 0x500, 0x600);
	/* Host call immediate value */
	SET_MEMBER_RMI(unsigned int imm, 0x600, 0x608);	/* 0x600 */
	/* Address: VDEV which triggered REC exit due to IO */
	SET_MEMBER_RMI(unsigned long io_vdev, 0x608, 0x610);	/* 0x608 */
	/* RmiIoAction: Action which triggered REC exit due to IO */
	SET_MEMBER_RMI(rmi_io_action_t io_action, 0x610, 0x700); /* 0x610 */
	/* PMU overflow status */
	SET_MEMBER_RMI(unsigned long pmu_ovf_status, 0x700, 0x800);	/* 0x700 */
};

/*
 * Structure contains shared information between RMM and Host
 * during REC entry and REC exit.
 */
struct rmi_rec_run {
	/* Entry information */
	SET_MEMBER_RMI(struct rmi_rec_enter enter, 0, 0x800);	/* Offset 0 */
	/* Exit information */
	SET_MEMBER_RMI(struct rmi_rec_exit exit, 0x800, 0x1000);/* 0x800 */
};

/*
 * RmiPdevClass
 * Represents physical device class.
 * Width: 8 bits
 */
typedef unsigned char rmi_pdev_class_t;
#define RMI_PDEV_CLASS_PCIE			U(0)
#define RMI_PDEV_CLASS_LAST			RMI_PDEV_CLASS_PCIE

/*
 * RmiPdevFlags
 * Fieldset contains flags provided by the Host during PDEV creation
 * Width: 64 bits
 */
typedef unsigned long rmi_pdev_flags_t;
#define RMI_PDEV_FLAGS_RES0_SHIFT		UL(0)
#define RMI_PDEV_FLAGS_RES0_WIDTH		UL(63)

/*
 * RmiPdevEvent
 * Represents physical device event.
 * Width: 8 bits
 */
typedef unsigned char rmi_pdev_event_t;
#define RMI_PDEV_EVENT_IDE_KEY_REFRESH		U(0)

/*
 * RmiPdevState
 * Represents the state of a PDEV
 * Width: 8 bits
 */
typedef unsigned char rmi_pdev_state_t;
#define RMI_PDEV_STATE_NEW			U(0)
#define RMI_PDEV_STATE_NEEDS_KEY		U(1)
#define RMI_PDEV_STATE_HAS_KEY			U(2)
#define RMI_PDEV_STATE_READY			U(3)
#define RMI_PDEV_STATE_COMMUNICATING		U(4)
#define RMI_PDEV_STATE_STOPPING			U(5)
#define RMI_PDEV_STATE_STOPPED			U(6)
#define RMI_PDEV_STATE_ERROR			U(7)

/*
 * RmiSignatureAlgorithm
 * Represents signature algorithm used in PDEV set key RMI call.
 * Width: 8 bits
 */
typedef unsigned char rmi_signature_algorithm_t;
#define RMI_SIGNATURE_ALGORITHM_RSASSA_3072	U(0)
#define RMI_SIGNATURE_ALGORITHM_ECDSA_P256	U(1)
#define RMI_SIGNATURE_ALGORITHM_ECDSA_P384	U(2)

/*
 * RmiIoCreateFlags
 * Fieldset contains flags provided by the Host during IO creation.
 * Width: 64 bits
 */
typedef unsigned long rmi_io_create_flags_t;
#define RMI_IO_CREATE_FLAGS_SHARE_SHIFT		U(0)
#define RMI_IO_CREATE_FLAGS_SHARE_WIDTH		U(1)

/*
 * RmiIoDelegateFlags
 * Fieldset contains flags provided by the Host during IO granule delegation.
 * Width: 64 bits
 */
typedef unsigned long rmi_io_delegate_flags_t;
#define RMI_IO_DELEGATE_FLAGS_SHARE_SHIFT	U(0)
#define RMI_IO_DELEGATE_FLAGS_SHARE_WIDTH	U(1)

/*
 * RmiIoShared
 * Represents whether an IO granule is shared or private
 * Width: 1 bit
 */
#define RMI_IO_GRANULE_PRIVATE			U(0)
#define RMI_IO_GRANULE_SHARED			U(1)

/*
 * RmiIoEnterStatus
 * Represents status passed from the Host to the RMM during device communication.
 * Width: 8 bits
 */
typedef unsigned char rmi_io_enter_status_t;
#define RMI_IO_ENTER_STATUS_SUCCESS		U(0)
#define RMI_IO_ENTER_STATUS_ERROR		U(1)
#define RMI_IO_ENTER_STATUS_NONE		U(2)

/*
 * RmiIoEnter
 * This structure contains data passed from the Host to the RMM during device
 * communication.
 * Width: 256 (0x100) bytes
 */
typedef struct {
	/* RmiIoEnterStatus: Status of device transaction */
	SET_MEMBER_RMI(rmi_io_enter_status_t status, 0, 0x8);
	/* Address: Address of request buffer */
	SET_MEMBER_RMI(unsigned long req_addr, 0x8, 0x10);
	/* Address: Address of response buffer */
	SET_MEMBER_RMI(unsigned long resp_addr, 0x10, 0x18);
	/* UInt64: Amount of valid data in response buffer in bytes */
	SET_MEMBER_RMI(unsigned long resp_len, 0x18, 0x100);
} rmi_io_enter_t;

/*
 * RmiIoExitFlags
 * Fieldset contains flags provided by the RMM during a device transaction.
 * Width: 64 bits
 */
typedef unsigned long rmi_io_exit_flags_t;
#define RMI_IO_EXIT_FLAGS_CACHE_SHIFT		UL(0)
#define RMI_IO_EXIT_FLAGS_CACHE_WIDTH		UL(1)
#define RMI_IO_EXIT_FLAGS_SEND_SHIFT		UL(1)
#define RMI_IO_EXIT_FLAGS_SEND_WIDTH		UL(1)
#define RMI_IO_EXIT_FLAGS_WAIT_SHIFT		UL(2)
#define RMI_IO_EXIT_FLAGS_WAIT_WIDTH		UL(1)
#define RMI_IO_EXIT_FLAGS_MULTI_SHIFT		UL(3)
#define RMI_IO_EXIT_FLAGS_MULTI_WIDTH		UL(1)
#define RMI_IO_EXIT_FLAGS_RES0_SHIFT		UL(4)
#define RMI_IO_EXIT_FLAGS_RES0_WIDTH		UL(63)

/*
 * RmiIoRequestType
 * Represents type of IO request.
 * Width: 8 bits
 */
typedef unsigned char rmi_io_request_type_t;
#define RMI_IO_REQUEST_TYPE_DISCOVERY		U(0)
#define RMI_IO_REQUEST_TYPE_CMA_SPDM		U(1)
#define RMI_IO_REQUEST_TYPE_SECURE_CMA_SPDM	U(2)

/*
 * RmiIoExit
 * This structure contains data passed from the RMM to the Host during device
 * communication.
 * Width: 256 (0x100) bytes.
 */
typedef struct {
	/*
	 * RmiIoExitFlags: Flags indicating the actions the host is requested to
	 * perform
	 */
	SET_MEMBER_RMI(rmi_io_exit_flags_t flags, 0, 0x8);
	/*
	 * UInt64: If flags.cache is true, offset in the device response buffer
	 * to the start of data to be cached in bytes.
	 */
	SET_MEMBER_RMI(unsigned long cache_offset, 0x8, 0x10);
	/*
	 * UInt64: If flags.cache is true, amount of data to be cached in
	 * bytes.
	 */
	SET_MEMBER_RMI(unsigned long cache_len, 0x10, 0x18);
	/* RmiIoRequestType: If flags.send is true, type of request */
	SET_MEMBER_RMI(rmi_io_request_type_t req_type, 0x18, 0x20);
	/*
	 * UInt64: If flags.send is true, amount of valid data in request buffer
	 * in bytes
	 */
	SET_MEMBER_RMI(unsigned long req_len, 0x20, 0x28);
	/*
	 * UInt64: If flags.wait is true, amount of time to wait for device
	 * response in milliseconds
	 */
	SET_MEMBER_RMI(unsigned long timeout, 0x28, 0x100);
} rmi_io_exit_t;

/*
 * RmiIoData
 * This structure contains data structure shared between Host and RMM for
 * device communication.
 * Width: 4096 (0x1000) bytes.
 */
struct rmi_io_data {
	/* RmiIoEnter: Entry information */
	SET_MEMBER_RMI(rmi_io_enter_t rmi_io_enter, 0, 0x800);
	/* RmiIoExit: Exit information */
	SET_MEMBER_RMI(rmi_io_exit_t rmi_io_exit, 0x800, 0x1000);
};

/*
 * RmiAddressRange
 * This structure contains base and top value of an address range.
 * Width: 16 (0x10) bytes.
 */
typedef struct {
	/* Address: Base of the address range (inclusive) */
	SET_MEMBER_RMI(unsigned long base, 0, 0x8);
	/* Address: Top of the address range (exclusive) */
	SET_MEMBER_RMI(unsigned long top, 0x8, 0x10);
} rmi_address_range_t;

/*
 * RmiPdevParams
 * This structure contains parameters provided by Host during PDEV creation.
 * Width: 4096 (0x1000) bytes.
 */
struct rmi_pdev_params {
	/* RmiPdevFlags: Flags */
	SET_MEMBER_RMI(rmi_pdev_flags_t flags, 0, 0x8);
	/* RmiPdevClass: Device class */
	SET_MEMBER_RMI(rmi_pdev_class_t cls, 0x8, 0x10);
	/* Bits64: Physical device identifier */
	SET_MEMBER_RMI(unsigned long pdev_id, 0x10, 0x18);

	/* Bits16: Segment ID */
	SET_MEMBER_RMI(unsigned short segment_id, 0x18, 0x20);
	/* Bits16: Root Port identifier */
	SET_MEMBER_RMI(unsigned short root_id, 0x20, 0x28);
	/* UInt64: Certificate identifier */
	SET_MEMBER_RMI(unsigned long cert_id, 0x28, 0x30);
	/* UInt64: IDE stream identifier */
	SET_MEMBER_RMI(unsigned long ide_sid, 0x30, 0x38);

	/* UInt64: Base and top of requester ID range */
	SET_MEMBER_RMI(unsigned long rid_base, 0x38, 0x40);
	SET_MEMBER_RMI(unsigned long rid_top, 0x40, 0x100);

	/* UInt64: Number of address ranges */
	SET_MEMBER_RMI(unsigned long num_addr_range, 0x100, 0x108);
	/* RmiAddressRange: Address range values */
	SET_MEMBER_RMI(rmi_address_range_t
		       addr_range[PDEV_PARAM_ADDR_RANGE_MAX], 0x108, 0x300);

	/* UInt64: Number of auxiliary granules */
	SET_MEMBER_RMI(unsigned long num_aux, 0x300, 0x308);
	/* Address: Addresses of auxiliary granules */
	SET_MEMBER_RMI(unsigned long aux[PDEV_PARAM_AUX_GRANULES_MAX], 0x308,
		       0x1000);
};

/*
 * RmiVdevFlags
 * Fieldset contains flags provided by the Host during VDEV creation.
 * Width: 64 bits
 */
typedef unsigned long rmi_vdev_flags_t;
#define RMI_VDEV_FLAGS_RES0_SHIFT		UL(0)
#define RMI_VDEV_FLAGS_RES0_WIDTH		UL(63)

/*
 * RmiVdevState
 * Represents the state of the VDEV
 * Width: 8 bits
 */
typedef unsigned char rmi_vdev_state_t;
#define RMI_VDEV_STATE_READY			U(0)
#define RMI_VDEV_STATE_COMMUNICATING		U(1)
#define RMI_VDEV_STATE_STOPPING			U(2)
#define RMI_VDEV_STATE_STOPPED			U(3)
#define RMI_VDEV_STATE_ERROR			U(4)

/*
 * RmiVdevParams
 * The RmiVdevParams structure contains parameters provided by the Host during
 * VDEV creation.
 * Width: 4096 (0x1000) bytes.
 */
struct rmi_vdev_params {
	/* RmiVdevFlags: Flags */
	SET_MEMBER_RMI(rmi_vdev_flags_t flags, 0, 0x8);
	/* Bits64: Virtual device identifier */
	SET_MEMBER_RMI(unsigned long vdev_id, 0x8, 0x10);
	/* Bits64: TDI identifier */
	SET_MEMBER_RMI(unsigned long tdi_id, 0x10, 0x1000);
};
#endif /* __ASSEMBLER__ */

#endif /* SMC_RMI_H */
