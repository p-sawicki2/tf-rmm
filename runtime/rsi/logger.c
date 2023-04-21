/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <debug.h>
#include <psci.h>
#include <rsi-logger.h>
#include <smc-rsi.h>
#include <string.h>
#include <utils_def.h>

/* RMI handler uses 29 chars for function name */
#define	MAX_NAME_LEN	29UL

/* Max 10 64-bit parameters separated by space */
#define PARAMS_STR_LEN	(10UL * sizeof("0123456789ABCDEF"))

#define	MAX_STATUS_LEN	sizeof("{RSI_ERROR_INPUT}")

#define	BUFFER_SIZE	(MAX_NAME_LEN + PARAMS_STR_LEN + \
			sizeof(" > ") - 1UL + MAX_STATUS_LEN)

struct rsi_handler {
	const char *fn_name;	/* function name */
	unsigned int num_args;	/* number of arguments */
	unsigned int num_vals;	/* number of output values */
};

#define RSI_HANDLER_ID(_id)	SMC64_FID_OFFSET_FROM_RANGE_MIN(RSI, SMC_RSI_##_id)

#define RSI_FUNCTION(_id, _in, _out)[RSI_HANDLER_ID(_id)] = { \
	.fn_name = #_id,	\
	.num_args = _in,	\
	.num_vals = _out	\
}

static const struct rsi_handler rsi_logger[] = {
	RSI_FUNCTION(ABI_VERSION, 0U, 1U),		/* 0xC4000190 */
	RSI_FUNCTION(MEASUREMENT_READ, 1U, 8U),		/* 0xC4000192 */
	RSI_FUNCTION(MEASUREMENT_EXTEND, 10U, 0U),	/* 0xC4000193 */
	RSI_FUNCTION(ATTEST_TOKEN_INIT, 9U, 0U),	/* 0xC4000194 */
	RSI_FUNCTION(ATTEST_TOKEN_CONTINUE, 1U, 1U),	/* 0xC4000195 */
	RSI_FUNCTION(REALM_CONFIG, 1U, 0U),		/* 0xC4000196 */
	RSI_FUNCTION(IPA_STATE_SET, 3U, 1U),		/* 0xC4000197 */
	RSI_FUNCTION(IPA_STATE_GET, 1U, 1U),		/* 0xC4000198 */
	RSI_FUNCTION(HOST_CALL, 1U, 0U)			/* 0xC4000199 */
};

#define RSI_STATUS_HANDLER(_id)[RSI_##_id] = #_id

const char *rsi_status_handler[] = {
	RSI_STATUS_HANDLER(SUCCESS),
	RSI_STATUS_HANDLER(ERROR_INPUT),
	RSI_STATUS_HANDLER(ERROR_STATE),
	RSI_STATUS_HANDLER(INCOMPLETE)
};

COMPILER_ASSERT(ARRAY_LEN(rsi_status_handler) == RSI_ERROR_COUNT);

static size_t print_entry(unsigned int id, unsigned long args[],
			  char *buf, size_t len)
{
	unsigned int num = 7U;	/* up to seven arguments */
	int cnt;

	switch (id) {
	case SMC_RSI_ABI_VERSION ... SMC_RSI_HOST_CALL:
		num = rsi_logger[id - SMC_RSI_ABI_VERSION].num_args;

		if (rsi_logger[id - SMC_RSI_ABI_VERSION].fn_name != NULL) {
			cnt = snprintf(buf, MAX_NAME_LEN + 1UL,
				"%s%s", "SMC_RSI_",
				rsi_logger[id - SMC_RSI_ABI_VERSION].fn_name);
		} else {
			/* Handle gaps in RSI commands numbering */
			cnt = snprintf(buf, MAX_NAME_LEN + 1UL,
					"%s%08x", "SMC_RSI_", id);
		}
		break;

	/* SMC32 PSCI calls */
	case SMC32_PSCI_FID_MIN ... SMC32_PSCI_FID_MAX:
		FALLTHROUGH;
	case SMC64_PSCI_FID_MIN ... SMC64_PSCI_FID_MAX:
		cnt = snprintf(buf, MAX_NAME_LEN + 1UL, "%s%08x", "PSCI_", id);
		break;

	/* Other SMC calls */
	default:
		cnt = snprintf(buf, MAX_NAME_LEN + 1UL, "%s%08x", "SMC_", id);
		break;
	}

	assert((cnt > 0) && (cnt < (int)(MAX_NAME_LEN + 1)));

	(void)memset(buf + cnt, (int)' ', MAX_NAME_LEN - (size_t)cnt);

	buf += MAX_NAME_LEN;
	len -= MAX_NAME_LEN;

	/* Arguments */
	for (unsigned int i = 0U; i < num; i++) {
		cnt = snprintf(buf, len, " %lx", args[i]);
		assert((cnt > 0) && (cnt < (int)len));
		buf += cnt;
		len -= (size_t)cnt;
	}

	return len;
}

static int print_status(char *buf, size_t len, unsigned long res)
{
	return_code_t rc = unpack_return_code(res);

	if ((unsigned long)rc.status >= RSI_ERROR_COUNT) {
		return snprintf(buf, len, " > %lx", res);
	}

	return snprintf(buf, len, " > RSI_%s",
			rsi_status_handler[rc.status]);
}

static int print_code(char *buf, size_t len, unsigned long res)
{
	return snprintf(buf, len, " > %lx", res);
}

void rsi_log_on_exit(unsigned int function_id, unsigned long args[],
		     unsigned long regs[], bool exit_to_rec)
{
	char buffer[BUFFER_SIZE];
	size_t len = print_entry(function_id, args, buffer, sizeof(buffer));

	/* Print result when execution continues in REC */
	if (exit_to_rec) {
		char *buf = buffer + (sizeof(buffer) - len);
		unsigned int num = 3U;	/* results in X1-X3 */
		int cnt;

		switch (function_id) {
		case SMC_RSI_MEASUREMENT_READ ... SMC_RSI_HOST_CALL:
			num = rsi_logger[function_id -
					 SMC_RSI_ABI_VERSION].num_vals;
			/* Print status */
			cnt = print_status(buf, len, regs[0]);
			break;
		case SMC_RSI_ABI_VERSION:
			num = 0U;
			FALLTHROUGH;
		default:
			/* Print result code */
			cnt = print_code(buf, len, regs[0]);
		}

		assert((cnt > 0) && (cnt < (int)len));

		/* Print output values */
		for (unsigned int i = 1U; i <= num; i++) {
			buf += cnt;
			len -= (size_t)cnt;
			cnt = snprintf(buf, len, " %lx", regs[i]);
			assert((cnt > 0) && (cnt < (int)len));
		}
	}

	rmm_log("%s\n", buffer);
}
