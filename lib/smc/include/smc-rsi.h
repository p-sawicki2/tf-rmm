/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef SMC_RSI_H
#define SMC_RSI_H

#include <smc.h>

/*
 * This file describes the Realm Services Interface (RSI) Application Binary
 * Interface (ABI) for SMC calls made from within the Realm to the RMM and
 * serviced by the RMM.
 */

/*
 * The major version number of the RSI implementation.  Increase this whenever
 * the binary format or semantics of the SMC calls change.
 */
#define RSI_ABI_VERSION_MAJOR		UL(1)

/*
 * The minor version number of the RSI implementation.  Increase this when
 * a bug is fixed, or a feature is added without breaking binary compatibility.
 */
#define RSI_ABI_VERSION_MINOR		UL(0)

#define RSI_ABI_VERSION			((RSI_ABI_VERSION_MAJOR << U(16)) | \
					  RSI_ABI_VERSION_MINOR)

#define RSI_ABI_VERSION_GET_MAJOR(_version) ((_version) >> U(16))
#define RSI_ABI_VERSION_GET_MINOR(_version) ((_version) & U(0xFFFF))

#define IS_SMC64_RSI_FID(_fid)		IS_SMC64_STD_FAST_IN_RANGE(RSI, _fid)

#define SMC64_RSI_FID(_offset)		SMC64_STD_FID(RSI, _offset)

/*
 * RsiCommandReturnCode enumeration
 * representing a return code from an RSI command.
 */
/* Command completed successfully */
#define RSI_SUCCESS		UL(0)

/* The value of a command input value caused the command to fail */
#define RSI_ERROR_INPUT		UL(1)

/*
 * The state of the current Realm or current REC
 * does not match the state expected by the command
 */
#define RSI_ERROR_STATE		UL(2)

/* The operation requested by the command is not complete */
#define RSI_INCOMPLETE		UL(3)

#define RSI_ERROR_COUNT		UL(4)

/* RsiHashAlgorithm */
#define RSI_HASH_SHA_256	U(0)
#define RSI_HASH_SHA_512	U(1)

/*
 * RsiRipasChangeDestroyed:
 * RIPAS change from DESTROYED should not be permitted
 */
#define RSI_NO_CHANGE_DESTROYED	U(0)

/* A RIPAS change from DESTROYED should be permitted */
#define RSI_CHANGE_DESTROYED	U(1)

/*
 * RsiResponse enumeration represents whether Host accepted
 * or rejected a Realm request
 */
#define RSI_ACCEPT		U(0)
#define RSI_REJECT		U(1)

/*
 * Returns RSI version.
 * arg1: Requested interface version
 * ret0: Status / error
 * ret1: Lower implemented interface revision
 * ret2: Higher implemented interface revision
 */
#define SMC_RSI_VERSION			SMC64_RSI_FID(U(0x0))

/*
 * Returns RSI Feature register requested by index.
 * arg1: Feature register index
 * ret0: Status / error
 * ret1: Feature register value
 */
#define SMC_RSI_FEATURES		SMC64_RSI_FID(U(0x1))

/*
 * Returns a measurement.
 * arg1: Measurement index (0..4), measurement (RIM or REM) to read
 * ret0: Status / error
 * ret1: Measurement value, bytes:  0 -  7
 * ret2: Measurement value, bytes:  8 - 15
 * ret3: Measurement value, bytes: 16 - 23
 * ret4: Measurement value, bytes: 24 - 31
 * ret5: Measurement value, bytes: 32 - 39
 * ret6: Measurement value, bytes: 40 - 47
 * ret7: Measurement value, bytes: 48 - 55
 * ret8: Measurement value, bytes: 56 - 63
 */
#define SMC_RSI_MEASUREMENT_READ	SMC64_RSI_FID(U(0x2))

/*
 * Extends a REM.
 * arg1:  Measurement index (1..4), measurement (REM) to extend
 * arg2:  Measurement size in bytes
 * arg3:  Challenge value, bytes:  0 -  7
 * arg4:  Challenge value, bytes:  8 - 15
 * arg5:  Challenge value, bytes: 16 - 23
 * arg6:  Challenge value, bytes: 24 - 31
 * arg7:  Challenge value, bytes: 32 - 39
 * arg8:  Challenge value, bytes: 40 - 47
 * arg9:  Challenge value, bytes: 48 - 55
 * arg10: Challenge value, bytes: 56 - 63
 * ret0:  Status / error
 */
#define SMC_RSI_MEASUREMENT_EXTEND	SMC64_RSI_FID(U(0x3))

/*
 * Initialize the operation to retrieve an attestation token.
 * arg1: Challenge value, bytes:  0 -  7
 * arg2: Challenge value, bytes:  8 - 15
 * arg3: Challenge value, bytes: 16 - 23
 * arg4: Challenge value, bytes: 24 - 31
 * arg5: Challenge value, bytes: 32 - 39
 * arg6: Challenge value, bytes: 40 - 47
 * arg7: Challenge value, bytes: 48 - 55
 * arg8: Challenge value, bytes: 56 - 63
 * ret0: Status / error
 * ret1: Upper bound on attestation token size in bytes
 */
#define SMC_RSI_ATTEST_TOKEN_INIT	SMC64_RSI_FID(U(0x4))

/*
 * Continue the operation to retrieve an attestation token.
 * arg1: IPA of the Granule to which the token will be written
 * arg2: Offset within Granule to start of buffer in bytes
 * arg3: Size of buffer in bytes
 * ret0: Status / error
 * ret1: Number of bytes written to buffer
 */
#define SMC_RSI_ATTEST_TOKEN_CONTINUE	SMC64_RSI_FID(U(0x5))

#ifndef __ASSEMBLER__
/*
 * Defines member of structure and reserves space
 * for the next member with specified offset.
 */
#define SET_MEMBER_RSI	SET_MEMBER

/* RsiRealmConfig structure containing realm configuration */
struct rsi_realm_config {
	/* IPA width in bits */
	SET_MEMBER_RSI(unsigned long ipa_width, 0, 8);		/* Offset 0 */
	/* Hash algorithm */
	SET_MEMBER_RSI(unsigned long algorithm, 8, 0x1000);	/* Offset 8 */
};

#endif /* __ASSEMBLER__ */

/*
 * arg1 == IPA of the Granule to which the configuration data will be written
 * ret0 == Status / error
 */
#define SMC_RSI_REALM_CONFIG		SMC64_RSI_FID(U(0x6))

/*
 * arg1 == Base IPA address of target region
 * arg2 == Top address of target region
 * arg3 == RIPAS value
 * arg4 == flags
 * ret0 == Status / error
 * ret1 == Base of IPA region which was not modified by the command
 * ret2 == RSI response
 */
#define SMC_RSI_IPA_STATE_SET		SMC64_RSI_FID(U(0x7))

/*
 * arg1 == IPA of target page
 * ret0 == Status / error
 * ret1 == RIPAS value
 */
#define SMC_RSI_IPA_STATE_GET		SMC64_RSI_FID(U(0x8))

#define RSI_HOST_CALL_NR_GPRS		U(31)

#ifndef __ASSEMBLER__
struct rsi_host_call {
	SET_MEMBER_RSI(struct {
		/* Immediate value */
		unsigned int imm;		/* Offset 0 */
		/* Registers */
		unsigned long gprs[RSI_HOST_CALL_NR_GPRS];
		}, 0, 0x100);
};

#endif /* __ASSEMBLER__ */

/*
 * arg1 == IPA of the Host call data structure
 * ret0 == Status / error
 */
#define SMC_RSI_HOST_CALL		SMC64_RSI_FID(U(0x9))


/*
 * arg1 == Index of the plane to get values from
 * arg2 == Index of the permission to retrieve
 * ret0 == Status / error
 * ret1 == Memory permission value
 */
#define SMC_RSI_MEM_GET_PERM_VALUE	SMC64_RSI_FID(U(0x10))

/*
 * arg1 == Base of target IPA region
 * arg2 == Top of target IPA region
 * arg3 == Permission index
 * arg4 == Cookie
 * ret0 == Status / error
 * ret1 == Base of IPA region which was not modified by the command
 * ret2 == RSI response. Whether the host accepted or rejected the request
 * ret3 == New cookie value
 */
#define SMC_RSI_MEM_SET_PERM_INDEX	SMC64_RSI_FID(U(0x11))

/*
 * arg1 == Index of the plane where to modify the permissions
 * arg2 == Index of the permission to modify
 * arg3 == Memory permission value
 * ret0 == Status / error
 */
#define SMC_RSI_MEM_SET_PERM_VALUE	SMC64_RSI_FID(U(0x12))

/* Number of general purpose registers per Plane */
#define RSI_PLANE_NR_GPRS		31

/* Maximum number of Interrupt Controller List Registers */
#define RSI_PLANE_GIC_NUM_LRS		U(16)

/* RsiPlaneExitReason represents the reason for a Plane exit */
#define RSI_EXIT_SYNC			U(0)
#define RSI_EXIT_IRQ			U(1)

#ifndef __ASSEMBLER__

/*
 * EL1 system registers per Plane
 */
struct rsi_plane_el1_sysregs {
	unsigned long sp_el0;			/*   0x0 */
	unsigned long sp_el1;			/*   0x8 */
	unsigned long elr_el1;			/*  0x10 */
	unsigned long spsr_el1;			/*  0x18 */
	unsigned long pmcr_el0;			/*  0x20 */
	unsigned long pmuserenr_el0;		/*  0x28 */
	unsigned long tpidrro_el0;		/*  0x30 */
	unsigned long tpidr_el0;		/*  0x38 */
	unsigned long csselr_el1;		/*  0x40 */
	unsigned long sctlr_el1;		/*  0x48 */
	unsigned long actlr_el1;		/*  0x50 */
	unsigned long cpacr_el1;		/*  0x58 */
	unsigned long zcr_el1;			/*  0x60 */
	unsigned long ttbr0_el1;		/*  0x68 */
	unsigned long ttbr1_el1;		/*  0x70 */
	unsigned long tcr_el1;			/*  0x78 */
	unsigned long esr_el1;			/*  0x80 */
	unsigned long afsr0_el1;		/*  0x88 */
	unsigned long afsr1_el1;		/*  0x90 */
	unsigned long far_el1;			/*  0x98 */
	unsigned long mair_el1;			/*  0xA0 */
	unsigned long vbar_el1;			/*  0xA8 */
	unsigned long contextidr_el1;		/*  0xB0 */
	unsigned long tpidr_el1;		/*  0xB8 */
	unsigned long amair_el1;		/*  0xC0 */
	unsigned long cntkctl_el1;		/*  0xC8 */
	unsigned long par_el1;			/*  0xD0 */
	unsigned long mdscr_el1;		/*  0xD8 */
	unsigned long mdccint_el1;		/*  0xE0 */
	unsigned long disr_el1;			/*  0xE8 */
	unsigned long mpam0_el1;		/*  0xF0 */

	/* Timer Registers */
	unsigned long cntp_ctl_el0;		/*  0xF8 */
	unsigned long cntp_cval_el0;		/* 0x100 */
	unsigned long cntv_ctl_el0;		/* 0x108 */
	unsigned long cntv_cval_el0;		/* 0x110 */
};

/*
 * Data passed from P0 to the RMM on entry to Pn
 */
struct rsi_plane_entry {
	/* Flags */
	SET_MEMBER_RSI(unsigned long flags, 0, 0x8);				/*   0x0 */
	/* Program counter */
	SET_MEMBER_RSI(unsigned long pc, 0x8, 0x100);				/*   0x8 */
	/* General purpose registers */
	SET_MEMBER_RSI(unsigned long gprs[RSI_PLANE_NR_GPRS], 0x100, 0x200);	/* 0x100 */
	/* EL1 system registers */
	SET_MEMBER_RSI(struct rsi_plane_el1_sysregs el1_sysregs, 0x200, 0x400);	/* 0x200 */
	/* GICv3 registers */
	SET_MEMBER_RSI(
		struct {
			/* GICv3 Hypervisor Control Register */
			unsigned long gicv3_hcr;				/* 0x400 */
			/* GICv3 List Registers */
			unsigned long gicv3_lrs[RSI_PLANE_GIC_NUM_LRS];		/* 0x408 */
		}, 0x400, 0x500);
};

/*
 * Data passed from the RMM to P0 on exit from Pn
 */
struct rsi_plane_exit {
	/* Exit reason */
	SET_MEMBER_RSI(unsigned long exit_reason, 0x0, 0x100);			/*   0x0 */
	/* EL2 system registers */
	SET_MEMBER_RSI(
		struct {
			/* Exception Link Register */
			unsigned long elr_el2;					/* 0x100 */
			/* Exception Syndrome Register */
			unsigned long esr_el2;					/* 0x108 */
			/* Fault Address Register */
			unsigned long far_el2;					/* 0x110 */
			/* Hypervisor IPA Fault Address register */
			unsigned long hpfar_el2;				/* 0x118 */
		}, 0x100, 0x200);
	/* General purpose registers */
	SET_MEMBER_RSI(unsigned long gprs[RSI_PLANE_NR_GPRS], 0x200, 0x300);	/* 0x200 */
	/* EL1 system registers */
	SET_MEMBER_RSI(struct rsi_plane_el1_sysregs el1_sysregs, 0x300, 0x500);	/* 0x300 */
	/* GICv3 registers */
	SET_MEMBER_RSI(
		struct {
			/* GICv3 Hypervisor Control Register */
			unsigned long gicv3_hcr;				/* 0x500 */
			/* GICv3 List Registers */
			unsigned long gicv3_lrs[RSI_PLANE_GIC_NUM_LRS];		/* 0x508 */
			/* GICv3 Maintenance Interrupt State Register */
			unsigned long gicv3_misr;				/* 0x588 */
			/* GICv3 Virtual Machine Control Register */
			unsigned long gicv3_vmcr;				/* 0x590 */
		}, 0x500, 0x600);
};

/*
 * Data shared between P0 and the RMM during entry to and exit from Pn
 */
struct rsi_plane_run {
	/* Entry information */
	SET_MEMBER_RSI(struct rsi_plane_entry entry, 0x0, 0x800);		/*   0x0 */
	/* Exit information */
	SET_MEMBER_RSI(struct rsi_plane_exit exit, 0x800, 0x1000);		/* 0x800 */
};

#endif /* __ASSEMBLER__ */

#endif /* SMC_RSI_H */
