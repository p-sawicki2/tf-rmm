#include "tb_rec.h"
#include "tb_realm.h"
#include "rec.h"
#include "realm.h"
#include "tb_common.h"


struct rec nondet_rec(void);
struct rmi_rec_params nondet_struct_rmi_rec_params(void);
struct rmi_rec_params_buffer nondet_rmi_rec_params_buffer(void);

/*struct rec {*/
	/*struct granule *g_rec;	[> the granule in which this REC lives <]*/
	/*unsigned long rec_idx;	[> which REC is this <]*/
	/*bool runnable;*/

	/*struct {*/
		/*unsigned long start;*/
		/*unsigned long end;*/
		/*unsigned long addr;*/
		/*enum ripas ripas;*/
	/*} set_ripas;*/

	/*
	 * Common values across all RECs in a Realm.
	 */
	/*struct {*/
		/*unsigned long ipa_bits;*/
		/*int s2_starting_level;*/
		/*struct granule *g_rtt;*/
		/*struct granule *g_rd;*/
		/*bool pmu_enabled;*/
		/*unsigned int pmu_num_cnts;*/
		/*bool sve_enabled;*/
		/*uint8_t sve_vq;*/
	/*} realm_info;*/


	/*[> Number of auxiliary granules <]*/
	/*unsigned int num_rec_aux;*/

	/*[> Addresses of auxiliary granules <]*/
	/*struct granule *g_aux[MAX_REC_AUX_GRANULES];*/
/*};*/

bool valid_rec_page(struct rec value)
{
    return value.set_ripas.base < value.set_ripas.top
        && value.num_rec_aux < MAX_REC_AUX_GRANULES;
}

struct granule * init_rec_page(struct granule *g_rd)
{
    struct granule g = init_granule();
    __CPROVER_assume(g.state == GRANULE_STATE_REC);

    struct rec rec = nondet_rec();
    //TODO check if this line is needed.
    // It is strange that g_rd is not initialised but g_rtt is later.
    /*rec.realm_info.g_rd = g_rd;*/

    // It must be a valid g_rd
    __CPROVER_assert(valid_pa(g_rd) && g_rd->state == GRANULE_STATE_RD, "internal, `init_rec_page` valid `g_rd`.");
    struct rd * realm = granule_metadata_ptr_to_buffer_ptr(g_rd);
    //TODO add more
    rec.realm_info.g_rtt = realm->s2_ctx.g_rtt;
    rec.realm_info.s2_starting_level = realm->s2_ctx.s2_starting_level;
    struct granule* g_rec = inject_granule(&g, &rec, sizeof(rec));
    rec.g_rec = g_rec;
    return g_rec;
}

void init_rec_param_page(void)
{
    struct granule g = init_granule();
    struct rmi_rec_params params = nondet_struct_rmi_rec_params();
    inject_granule(&g, &params, sizeof(params));
}

struct rmm_rec nondet_struct_rmm_rec(void);
struct rmm_rec Rec(uint64_t addr)
{
    if (!valid_pa(addr))
        return nondet_struct_rmm_rec();

    struct rec *rec_ptr = pa_to_granule_buffer_ptr(addr);
    struct rmm_rec spec_rec = {
        //TODO .attest_state =
	    .owner = granule_metadata_ptr_to_pa(rec_ptr->realm_info.g_rd),
        .flags.runnable = rec_ptr->runnable,
        .state = rec_ptr->g_rec->refcount == 0 ? READY:RUNNING,
        .ripas_addr = rec_ptr->set_ripas.addr,
        .ripas_top = rec_ptr->set_ripas.top,
        .ripas_value = rec_ptr->set_ripas.ripas_val,
        .ripas_destroyed = rec_ptr->set_ripas.change_destroyed,
        .host_call_pending = rec_ptr->host_call
    };

    for(int i = 0; i < rec_ptr->num_rec_aux && i < MAX_REC_AUX_GRANULES; ++i) {
        spec_rec.aux[i] = rec_ptr->g_aux[i];
    }
}

/*struct rmi_rec_params {*/
	/*[> Flags <]*/
	/*SET_MEMBER_RMI(unsigned long flags, 0, 0x100);	[> Offset 0 <]*/
	/*[> MPIDR of the REC <]*/
	/*SET_MEMBER_RMI(unsigned long mpidr, 0x100, 0x200);	[> 0x100 <]*/
	/*[> Program counter <]*/
	/*SET_MEMBER_RMI(unsigned long pc, 0x200, 0x300);	[> 0x200 <]*/
	/*[> General-purpose registers <]*/
	/*SET_MEMBER_RMI(unsigned long gprs[REC_CREATE_NR_GPRS], 0x300, 0x800); [> 0x300 <]*/
	/*SET_MEMBER_RMI(struct {*/
			/*[> Number of auxiliary Granules <]*/
			/*unsigned long num_aux;			[> 0x800 <]*/
			/*[> Addresses of auxiliary Granules <]*/
			/*unsigned long aux[MAX_REC_AUX_GRANULES];[> 0x808 <]*/
		   /*}, 0x800, 0x1000);*/
/*};*/

struct rmi_rec_params_buffer nondet_rmi_rec_params_buffer(void);
struct rmi_rec_params_buffer RecParams(uint64_t addr)
{
    if (!valid_pa(addr))
        return nondet_rmi_rec_params_buffer();

    struct granule *g_param = pa_to_granule_metadata_ptr(addr);
    struct rmi_rec_params *param_ptr = pa_to_granule_buffer_ptr(addr);

    struct rmi_rec_params_buffer spec_param = {
        .flags = param_ptr->flags & REC_PARAMS_FLAG_RUNNABLE,
        .mpidr = param_ptr->mpidr,
        .pc = param_ptr->pc,
        .num_aux = param_ptr->num_aux
    };

    memcpy(&spec_param.gprs[0],&(param_ptr->gprs[0]), REC_CREATE_NR_GPRS * sizeof(spec_param.gprs[0]));
    size_t max_byte_aux = (spec_param.aux<MAX_REC_AUX_GRANULES?spec_param.num_aux:MAX_REC_AUX_GRANULES) * sizeof(spec_param.aux[0]);
    memcpy(&spec_param.aux[0],&(param_ptr->aux[0]), max_byte_aux);

    return spec_param;
}

uint64_t RecIndex(uint64_t mpidr)
{
    return mpidr_to_rec_idx(mpidr);
}

bool RecAuxAligned(struct granule ** aux, uint64_t num_aux)
{
    __CPROVER_assert(num_aux >= 0 && num_aux <= MAX_REC_AUX_GRANULES, "internal: RecAuxAligned range check.");
    for(int i = 0; i < num_aux && i < MAX_REC_AUX_GRANULES; ++i) {
        if(!AddrIsGranuleAligned(aux[i])) return false;
    }
    return true;
}

bool RecAuxAlias(uint64_t rec, struct granule ** aux, uint64_t num_aux)
{
    __CPROVER_assert(num_aux >= 0 && num_aux <= MAX_REC_AUX_GRANULES, "internal: RecAuxAlias range check.");
    for(int i = 0; i < num_aux && i < MAX_REC_AUX_GRANULES; ++i) {
        if (aux[i] == rec) return true;
        for(int j = i + 1; j < num_aux && j < MAX_REC_AUX_GRANULES; ++j)
            if(aux[i] == aux[j]) return true;
    }
    return false;
}

bool RecAuxStateEqual(struct granule **aux, uint64_t num_aux, enum granule_state state)
{
    __CPROVER_assert(num_aux >= 0 && num_aux <= MAX_REC_AUX_GRANULES, "internal: RecAuxStateEqual range check.");
    for(int i = 0; i < num_aux && i < MAX_REC_AUX_GRANULES; ++i) 
        if(!PaIsDelegable(aux[i]) || pa_to_granule_metadata_ptr(aux[i])->state != state)
            return false;
    return true;
}

bool RecAuxEqual(struct granule **lhs, struct granule **rhs, uint64_t num_aux)
{
    __CPROVER_assert(num_aux >= 0 && num_aux <= MAX_REC_AUX_GRANULES, "internal: RecAuxStateEqual range check.");
    for(int i = 0; i < num_aux && i < MAX_REC_AUX_GRANULES; ++i) {
        if (lhs[i] != rhs[i]) return false;
    }
    return true;
}

bool MpidrEqual(uint64_t rec_mpidr, uint64_t params_mpidr)
{
    //TODO
    return true;
}

bool RmiRecParamsIsValid(uint64_t params_addr)
{
    if (!valid_pa(params_addr)) 
        return nondet_bool();

    struct rmi_rec_params *rec_params_buf = pa_to_granule_buffer_ptr(params_addr);

    //TODO it is not clear what this supposed to be
    return mpidr_is_valid(rec_params_buf->mpidr);
}

uint64_t RimExtendRec(struct rmm_realm realm, struct rmi_rec_params_buffer params)
{
    //TODO
    return 0;
}
