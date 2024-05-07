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

/*
 * The state of a Realm device does not match the state expected by the command.
 */
#define RSI_ERROR_DEVICE	UL(4)

#define RSI_ERROR_COUNT_MAX	UL(5)

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

/*
 * arg1 == IPA of the Host call data structure
 * ret0 == Status / error
 */
#define SMC_RSI_HOST_CALL		SMC64_RSI_FID(U(0x9))

#define SMC_RSI_MEM_GET_PERM_VALUE	SMC64_RSI_FID(U(0x10))
#define SMC_RSI_MEM_SET_PERM_INDEX	SMC64_RSI_FID(U(0x11))
#define SMC_RSI_MEM_SET_PERM_VALUE	SMC64_RSI_FID(U(0x12))
#define SMC_RSI_PLANE_ENTER		SMC64_RSI_FID(U(0x13))
#define SMC_RSI_RDEV_CONTINUE		SMC64_RSI_FID(U(0x14))
#define SMC_RSI_RDEV_GET_DIGESTS	SMC64_RSI_FID(U(0x15))
#define SMC_RSI_RDEV_GET_INTERFACE_REPORT SMC64_RSI_FID(U(0x16))
#define SMC_RSI_RDEV_GET_MEASUREMENTS	SMC64_RSI_FID(U(0x17))
#define SMC_RSI_RDEV_GET_STATE		SMC64_RSI_FID(U(0x18))
#define SMC_RSI_RDEV_LOCK		SMC64_RSI_FID(U(0x19))
#define SMC_RSI_RDEV_START		SMC64_RSI_FID(U(0x1A))
#define SMC_RSI_RDEV_STOP		SMC64_RSI_FID(U(0x1B))
#define SMC_RSI_RDEV_VALIDATE_IO	SMC64_RSI_FID(U(0x1C))
/*
 * arg1 == IPA of the Granule to which the configuration data will be written
 * ret0 == Status / error
 */
#define SMC_RSI_REALM_CONFIG		SMC64_RSI_FID(U(0x1D))

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

#define RSI_HOST_CALL_NR_GPRS		U(31)
struct rsi_host_call {
	SET_MEMBER_RSI(struct {
		/* Immediate value */
		unsigned int imm;		/* Offset 0 */
		/* Registers */
		unsigned long gprs[RSI_HOST_CALL_NR_GPRS];
		}, 0, 0x100);
};

/*
 * RsiFeature
 * Represents whether a feature is enabled.
 * Width: 1 bit
 */
#define RSI_FEATURE_FALSE			U(0)
#define RSI_FEATURE_TRUE			U(1)

/*
 * RsiFeatureRegister0
 * Fieldset contains feature register 0
 * Width: 64 bits
 */
typedef unsigned long rsi_feature_register0_t;
#define RSI_FEATURE_REGISTER_0_INDEX		UL(0)
#define RSI_FEATURE_REGISTER_0_DA_SHIFT		UL(0)
#define RMM_FEATURE_REGISTER_0_DA_WIDTH		UL(1)
#define RSI_FEATURE_REGISTER_0_MRO_SHIFT	UL(1)
#define RMM_FEATURE_REGISTER_0_MRO_WIDTH	UL(1)

/*
 * RsiRdevValidateIoFlags
 * Fieldset contains flags provided when requesting validation of an IO mapping.
 * Width: 64 bits
 */
typedef unsigned long rsi_rdev_validate_io_flags_t;
#define RSI_RDEV_VALIDATE_IO_FLAGS_SHARE_SHIFT	UL(0)
#define RSI_RDEV_VALIDATE_IO_FLAGS_SHARE_WIDTH	UL(1)

/*
 * RsiIoShared
 * Represents whether an IO mapping is shared.
 * Width: 1 bit
 */
#define RSI_IO_MAPPING_PRIVATE			U(0)
#define RSI_IO_MAPPING_SHARED			U(1)

/*
 * RsiDeviceState
 * This enumeration represents state of an assigned Realm device.
 * Width: 64 bits.
 */
typedef unsigned long rsi_device_state_t;
#define RSI_RDEV_STATE_NEW			U(0)
#define RSI_RDEV_STATE_NEW_BUSY			U(1)
#define RSI_RDEV_STATE_LOCKED			U(2)
#define RSI_RDEV_STATE_LOCKED_BUSY		U(3)
#define RSI_RDEV_STATE_STARTED			U(4)
#define RSI_RDEV_STATE_STARTED_BUSY		U(5)
#define RSI_RDEV_STATE_STOPPING			U(6)
#define RSI_RDEV_STATE_STOPPED			U(7)
#define RSI_RDEV_STATE_ERROR			U(8)

/*
 * RsiDeviceDigests
 * This structure contains digests of Realm device attestation evidence.
 * Width: 512 (0x200) bytes.
 */
struct rsi_device_digest {
	/* UInt64: Certificate identifier */
	SET_MEMBER_RSI(unsigned long cert_id, 0, 0x40);
	/* Bits512: Certificate digest */
	SET_MEMBER_RSI(unsigned char cert_digest[64], 0x40, 0x80);
	/* Bits512: Device public key digest */
	SET_MEMBER_RSI(unsigned char key_digest[64], 0x80, 0xc0);
	/* Bits512: Measurement block digest */
	SET_MEMBER_RSI(unsigned char meas_digest[64], 0xc0, 0x100);
	/* Bits512: Interface report digest */
	SET_MEMBER_RSI(unsigned char report_digest[64], 0100, 0x200);
};

/*
 * RsiDeviceMeasurementsParams
 * This structure contains parameters for retrieval of Realm device measurements.
 * Width: 64 (0x40) bytes.
 */
struct rsi_device_measurements_params {
	/* RsiBoolean[256]: Measurement indices */
	SET_MEMBER_RSI(unsigned char meas_ids_bitmap[32], 0, 0x20);
	/* RsiBoolean[256]: Measurement parameters */
	SET_MEMBER_RSI(unsigned char meas_params_bitmap[32], 0x20, 0x40);
};
#endif /* __ASSEMBLER__ */

#endif /* SMC_RSI_H */
