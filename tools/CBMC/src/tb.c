/*
 * Copyright (c) 2021-2022, Arm Limited. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

#include "tb.h"
#include "tb_common.h"
#include "tb_realm.h"
#include "tb_rec.h"
#include "tb_rtt.h"

#include "tb_interface_psci.h"
#include "rsi-handler.h"
#include "smc-handler.h"
#include "smc-rsi.h"
#include "smc.h"

void __init_global_state(unsigned long cmd) {
    REACHABLE;
    global_sanity_check();
    // Set up all the system register
    host_util_setup_sysreg_and_boot_manifest();
	switch(cmd) {
        case SMC_RMM_FEATURES: {
        return;
        }
        case SMC_RMM_GRANULE_DELEGATE: {
        init_ns_granule();
        return;
        }
        case SMC_RMM_GRANULE_UNDELEGATE: {
		init_delegated_granule();
		return;
        }
        case SMC_RMM_REALM_ACTIVATE: 
        case SMC_RMM_REALM_DESTROY: 
        case SMC_RMM_REC_AUX_COUNT: {
		init_realm_descriptor_page();
		return;
        }
        case SMC_RMM_REALM_CREATE: {
        // One for the new rd, and two for the potentially continuous root rtt.
		init_delegated_granule();
		init_delegated_granule();
		init_delegated_granule();
        init_realm_param_page();
		return;
        }
        case SMC_RMM_REC_CREATE: {
		init_delegated_granule();
		init_realm_descriptor_page();
        init_rec_param_page();
		return;
        }
        case SMC_RMM_REC_ENTER: {
		struct granule *g_rd = init_realm_descriptor_page();
		init_rec_page(g_rd);
        init_rec_run_page();
        }
        case SMC_RMM_REC_DESTROY: {
		struct granule *g_rd = init_realm_descriptor_page();
		init_rec_page(g_rd);
		return;
        }
        case SMC_RMM_DATA_CREATE: {
		init_realm_descriptor_page();
        //TODO
		/* 3 granules for the RTT, 1 for the data */
		/*init_granule_page(4UL);*/
		/*init_rtt_page(1UL);*/
		return;
        }
        case SMC_RMM_DATA_DESTROY: {
		struct granule* g_rd = init_realm_descriptor_page();
        struct granule* g_root_rtt = root_rtt_from_realm_descriptor(g_rd);
        int64_t start_level = start_level_from_realm_descriptor(g_rd);
        uint64_t level = nondet_uint64_t();
        __CPROVER_assume(valid_max_walk_path_level(start_level, level));
        init_walk_path(g_root_rtt, start_level, level);
		return;
        }
        case SMC_RMM_DATA_CREATE_UNKNOWN: {
		init_realm_descriptor_page();
        //TODO
		/* 3 granules for the RTT */
		/*init_granule_page(3UL);*/
		/*init_rtt_page(1UL);*/
		return;
        }
        case SMC_RMM_RTT_CREATE: {
		struct granule* g_rd = init_realm_descriptor_page();
        struct granule* g_root_rtt = root_rtt_from_realm_descriptor(g_rd);
        int64_t start_level = start_level_from_realm_descriptor(g_rd);
        uint64_t level = nondet_uint64_t();
        __CPROVER_assume(valid_max_walk_path_level(start_level, level));
        init_walk_path(g_root_rtt, start_level, level);
		return;
        }
        case SMC_RMM_RTT_DESTROY: {
		init_realm_descriptor_page();
        //TODO
		/* 3 granules for the RTT */
		/*init_granule_page(3UL);*/
		/*init_rtt_page(1UL);*/
		return;
        }
        case SMC_RMM_RTT_UNMAP_UNPROTECTED:
        case SMC_RMM_RTT_MAP_UNPROTECTED: 
        case SMC_RMM_RTT_READ_ENTRY: {
		struct granule* g_rd = init_realm_descriptor_page();
        struct granule* g_root_rtt = root_rtt_from_realm_descriptor(g_rd);
        int64_t start_level = start_level_from_realm_descriptor(g_rd);
        uint64_t level = nondet_uint64_t();
        __CPROVER_assume(valid_max_walk_path_level(start_level, level));
        init_walk_path(g_root_rtt, start_level, level);
		return;
        }
        case SMC_RSI_MEASUREMENT_READ:
        case SMC_RMM_AFFINITY_INFO:
        case SMC_RMM_PSCI_COMPLETE:
        case SMC_RMM_CPU_OFF:
        case SMC_RMM_CPU_ON:
        case SMC_RMM_CPU_SUSPEND:
        case SMC_RMM_SYSTEM_OFF:
        case SMC_RMM_SYSTEM_RESET:
		    return;

        default:
            ASSERT(false, "tb_handle_smc fail");
	}
}

extern unsigned char granules_buffer[HOST_MEM_SIZE];

// Sanity check on the implementation of CBMC
void global_sanity_check()
{
    __CPROVER_cover(valid_pa(nondet_unsigned_long()));
}

void tb_handle_smc(struct tb_regs* config) {
	unsigned long result = 0;
	switch(config->X0) {
    case SMC_RMM_DATA_CREATE:
		result = smc_data_create(config->X1,
				       config->X2,
				       config->X3,
				       config->X4,
				       config->X5);
        break;
    case SMC_RMM_DATA_CREATE_UNKNOWN:
		result = smc_data_create_unknown(config->X1,
					       config->X2,
					       config->X3);
        break;
    // Need to update the output, the new specs has output values
    case SMC_RMM_DATA_DESTROY:
		result = smc_data_destroy(config->X1, config->X2);
        break;
    case SMC_RMM_FEATURES:
		struct smc_result rst;
        smc_read_feature_register(config->X1, &rst);
        config->X1 = rst.x[1];
        break;
    case SMC_RMM_PSCI_COMPLETE:
		result = smc_psci_complete(config->X1, config->X2);
        break;
	case SMC_RMM_GRANULE_DELEGATE:
		result = smc_granule_delegate(config->X1);
        break;
    case SMC_RMM_GRANULE_UNDELEGATE:
		result = smc_granule_undelegate(config->X1);
        break;
    case SMC_RMM_REALM_ACTIVATE:
		result = smc_realm_activate(config->X1);
        break;
    case SMC_RMM_REC_AUX_COUNT:
		struct smc_result rst;
        smc_rec_aux_count(config->X1, &rst);
		result = rst.x[0];
		config->X1 = rst.x[1];
        break;
    case SMC_RMM_REC_CREATE:
		result = smc_rec_create(config->X1,
				      config->X2,
				      config->X3);
        break;
    case SMC_RMM_REC_DESTROY:
		result = smc_rec_destroy(config->X1);
        break;

    case SMC_RMM_REALM_CREATE:
		result = smc_realm_create(config->X1, config->X2);
        break;
    case SMC_RMM_REALM_DESTROY:
		result = smc_realm_destroy(config->X1);
        break;
    case SMC_RMM_REC_ENTER:
		result = smc_rec_enter(config->X1, config->X2);
        break;
    case SMC_RMM_RTT_CREATE:
		result = smc_rtt_create(config->X1,
				      config->X2,
				      config->X3,
				      config->X4);
        break;
    case SMC_RMM_RTT_DESTROY:
		result = smc_rtt_destroy(config->X1,
				       config->X2,
				       config->X3,
				       config->X4);
        break;
    case SMC_RMM_RTT_FOLD:
		result = smc_rtt_fold(config->X1,
				       config->X2,
				       config->X3,
				       config->X4);
        break;
    case SMC_RMM_RTT_INIT_RIPAS:
		result = smc_rtt_init_ripas(config->X1,
				       config->X2,
				       config->X3);
        break;
    case SMC_RMM_RTT_MAP_UNPROTECTED:
        result = smc_rtt_map_unprotected(config->X1, 
                       config->X2, 
                       config->X3,
                       config->X4);
        break;
    case SMC_RMM_RTT_READ_ENTRY:
		struct smc_result rst;
		smc_rtt_read_entry(config->X1, config->X2, config->X3, &rst);
		result = rst.x[0];
		config->X1 = rst.x[1];
		config->X2 = rst.x[2];
		config->X3 = rst.x[3];
		config->X4 = rst.x[4];
        break;
    case SMC_RMM_RTT_SET_RIPAS:
		result = smc_rtt_set_ripas(config->X1,
				       config->X2,
				       config->X3,
				       config->X4,
				       config->X5);
        break;
    case SMC_RMM_RTT_UNMAP_UNPROTECTED:
        result = smc_rtt_unmap_unprotected(config->X1, 
                       config->X2, 
                       config->X3);
        break;
    /*case RMI_RMM_VERSION:*/
        /*result = smc_version();*/
    default:
		ASSERT(false, "tb_handle_smc fail");
	}

    // Update the return value.
    config->X0 = result;
}

void __tb_expect_fail() 
{
	// Assertion used to check consistency of the testbench
}
