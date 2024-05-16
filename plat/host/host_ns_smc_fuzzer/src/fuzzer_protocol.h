#include <stdint.h>
#include <inttypes.h>
#ifndef FUZZER_PROTOCOL_H_
#define FUZZER_PROTOCOL_H_

#define COMMAND_ALLOCATE_GRANULE 0
#define COMMAND_GRANULE_DELEGATE 1
#define COMMAND_GRANULE_UNDELEGATE 2
#define COMMAND_REALM_CREATE 3
#define COMMAND_REALM_DESTROY 4
#define COMMAND_RTT_CREATE 5
#define COMMAND_RTT_DESTROY 6
#define COMMAND_REC_AUX_COUNT 7
#define COMMAND_REC_CREATE 8
#define COMMAND_REC_DESTROY 9
#define COMMAND_REALM_ACTIVATE 10
#define COMMAND_REC_ENTER 11
#define COMMAND_DATA_CREATE 12
#define COMMAND_DATA_CREATE_UNKNOWN 13
#define COMMAND_RTT_INIT_RIPAS 14
#define COMMAND_DATA_DESTROY 15

struct packet_allocate_granule {
	uint8_t index;
} __packed;

struct packet_granule_delegate {
	uint8_t index;
} __packed;

struct packet_granule_undelegate {
	uint8_t index;
} __packed;

struct packet_realm_create {
	uint8_t rd_index;
	uint8_t param_index;
	uint64_t flags;
	uint32_t s2sz;
	uint32_t num_bps;
	uint32_t num_wps;
	uint32_t pmu_num_ctrs;
	uint16_t vmid;
	uint8_t rtt_base_index;
	uint64_t rtt_level_start;
	uint32_t rtt_num_start;
} __packed;

struct packet_realm_destroy {
	uint8_t rd_index;
} __packed;

struct packet_rtt_create {
	uint8_t rd_index;
	uint8_t rtt_index;
	uint64_t ipa;
	uint32_t level;
} __packed;

struct packet_rtt_destroy {
	uint8_t rd_index;
	uint64_t ipa;
	uint32_t level;
} __packed;

struct packet_rec_aux_count {
	uint8_t rd_index;
} __packed;

struct packet_rec_create {
	uint8_t rd_index;
	uint8_t rec_index;
	uint8_t param_index;
	uint64_t flags;
	uint64_t mpidr;
	uint64_t num_aux;
	uint8_t aux_index0;
	uint8_t aux_index1;
	uint8_t aux_index2;
	uint8_t aux_index3;
	uint8_t aux_index4;
	uint8_t aux_index5;
	uint8_t aux_index6;
	uint8_t aux_index7;
	uint8_t aux_index8;
	uint8_t aux_index9;
	uint8_t aux_index10;
	uint8_t aux_index11;
	uint8_t aux_index12;
	uint8_t aux_index13;
	uint8_t aux_index14;
	uint8_t aux_index15;
} __packed;

struct packet_rec_destroy {
	uint8_t rec_index;
} __packed;

struct packet_realm_activate {
	uint8_t rd_index;
} __packed;

struct packet_rec_enter {
	uint8_t rec_index;
	uint8_t run_index;
} __packed;

struct packet_data_create {
	uint8_t data_index;
	uint8_t rd_index;
	uint64_t ipa;
	uint64_t src;
} __packed;

struct packet_data_create_unknown {
	uint8_t rd_index;
	uint8_t data_index;
	uint64_t ipa;
} __packed;

struct packet_rtt_init_ripas {
	uint8_t rd_index;
	uint64_t base;
	uint64_t top;
} __packed;

struct packet_data_destroy {
	uint8_t rd_index;
	uint64_t ipa;
} __packed;

#define LOG_packet_allocate_granule_FUNC(p) fprintf(stderr, "AllocateGranule(index = 0x%"PRIx8"),\n", p.index); fflush(stdout)

#define LOG_packet_granule_delegate_FUNC(p) fprintf(stderr, "GranuleDelegate(index = 0x%"PRIx8"),\n", p.index); fflush(stdout)

#define LOG_packet_granule_undelegate_FUNC(p) fprintf(stderr, "GranuleUndelegate(index = 0x%"PRIx8"),\n", p.index); fflush(stdout)

#define LOG_packet_realm_create_FUNC(p) fprintf(stderr, "RealmCreate(rd_index = 0x%"PRIx8", param_index = 0x%"PRIx8", flags = 0x%"PRIx64", s2sz = 0x%"PRIx32", num_bps = 0x%"PRIx32", num_wps = 0x%"PRIx32", pmu_num_ctrs = 0x%"PRIx32", vmid = 0x%"PRIx16", rtt_base_index = 0x%"PRIx8", rtt_level_start = 0x%"PRIx64", rtt_num_start = 0x%"PRIx32"),\n", p.rd_index, p.param_index, p.flags, p.s2sz, p.num_bps, p.num_wps, p.pmu_num_ctrs, p.vmid, p.rtt_base_index, p.rtt_level_start, p.rtt_num_start); fflush(stdout)

#define LOG_packet_realm_destroy_FUNC(p) fprintf(stderr, "RealmDestroy(rd_index = 0x%"PRIx8"),\n", p.rd_index); fflush(stdout)

#define LOG_packet_rtt_create_FUNC(p) fprintf(stderr, "RTTCreate(rd_index = 0x%"PRIx8", rtt_index = 0x%"PRIx8", ipa = 0x%"PRIx64", level = 0x%"PRIx32"),\n", p.rd_index, p.rtt_index, p.ipa, p.level); fflush(stdout)

#define LOG_packet_rtt_destroy_FUNC(p) fprintf(stderr, "RTTDestroy(rd_index = 0x%"PRIx8", ipa = 0x%"PRIx64", level = 0x%"PRIx32"),\n", p.rd_index, p.ipa, p.level); fflush(stdout)

#define LOG_packet_rec_aux_count_FUNC(p) fprintf(stderr, "RecAuxCount(rd_index = 0x%"PRIx8"),\n", p.rd_index); fflush(stdout)

#define LOG_packet_rec_create_FUNC(p) fprintf(stderr, "RecCreate(rd_index = 0x%"PRIx8", rec_index = 0x%"PRIx8", param_index = 0x%"PRIx8", flags = 0x%"PRIx64", mpidr = 0x%"PRIx64", num_aux = 0x%"PRIx64", aux_index0 = 0x%"PRIx8", aux_index1 = 0x%"PRIx8", aux_index2 = 0x%"PRIx8", aux_index3 = 0x%"PRIx8", aux_index4 = 0x%"PRIx8", aux_index5 = 0x%"PRIx8", aux_index6 = 0x%"PRIx8", aux_index7 = 0x%"PRIx8", aux_index8 = 0x%"PRIx8", aux_index9 = 0x%"PRIx8", aux_index10 = 0x%"PRIx8", aux_index11 = 0x%"PRIx8", aux_index12 = 0x%"PRIx8", aux_index13 = 0x%"PRIx8", aux_index14 = 0x%"PRIx8", aux_index15 = 0x%"PRIx8"),\n", p.rd_index, p.rec_index, p.param_index, p.flags, p.mpidr, p.num_aux, p.aux_index0, p.aux_index1, p.aux_index2, p.aux_index3, p.aux_index4, p.aux_index5, p.aux_index6, p.aux_index7, p.aux_index8, p.aux_index9, p.aux_index10, p.aux_index11, p.aux_index12, p.aux_index13, p.aux_index14, p.aux_index15); fflush(stdout)

#define LOG_packet_rec_destroy_FUNC(p) fprintf(stderr, "RecDestroy(rec_index = 0x%"PRIx8"),\n", p.rec_index); fflush(stdout)

#define LOG_packet_realm_activate_FUNC(p) fprintf(stderr, "RealmActivate(rd_index = 0x%"PRIx8"),\n", p.rd_index); fflush(stdout)

#define LOG_packet_rec_enter_FUNC(p) fprintf(stderr, "RecEnter(rec_index = 0x%"PRIx8", run_index = 0x%"PRIx8"),\n", p.rec_index, p.run_index); fflush(stdout)

#define LOG_packet_data_create_FUNC(p) fprintf(stderr, "DataCreate(data_index = 0x%"PRIx8", rd_index = 0x%"PRIx8", ipa = 0x%"PRIx64", src = 0x%"PRIx64"),\n", p.data_index, p.rd_index, p.ipa, p.src); fflush(stdout)

#define LOG_packet_data_create_unknown_FUNC(p) fprintf(stderr, "DataCreateUnknown(rd_index = 0x%"PRIx8", data_index = 0x%"PRIx8", ipa = 0x%"PRIx64"),\n", p.rd_index, p.data_index, p.ipa); fflush(stdout)

#define LOG_packet_rtt_init_ripas_FUNC(p) fprintf(stderr, "RttInitRipas(rd_index = 0x%"PRIx8", base = 0x%"PRIx64", top = 0x%"PRIx64"),\n", p.rd_index, p.base, p.top); fflush(stdout)

#define LOG_packet_data_destroy_FUNC(p) fprintf(stderr, "DataDestroy(rd_index = 0x%"PRIx8", ipa = 0x%"PRIx64"),\n", p.rd_index, p.ipa); fflush(stdout)

#endif /* FUZZER_PROTOCOL_H_ */
