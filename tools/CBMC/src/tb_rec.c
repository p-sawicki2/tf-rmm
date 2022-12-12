#include "tb_rec.h"
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
    return value.set_ripas.start < value.set_ripas.end
        && value.num_rec_aux < MAX_REC_AUX_GRANULES;
}

struct granule * init_rec_page(struct granule *g_rd)
{
    struct granule g = init_granule();
    __CPROVER_assume(g.state == GRANULE_STATE_REC);

    struct rec rec = nondet_rec();
    rec.realm_info.g_rd = g_rd;

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
	    .owner = granule_metadata_ptr_to_pa(rec_ptr->realm_info.g_rd),
        .flags.runnable = rec_ptr->runnable,
        .state = rec_ptr->g_rec->refcount == 0 ? READY:RUNNING
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

struct spec_rec_param non_spec_rec_param(void);
struct spec_rec_param RecParams(uint64_t addr)
{
    if (!valid_pa(addr))
        return non_spec_rec_param();

    struct rmi_rec_params *param_ptr = pa_to_granule_buffer_ptr(addr);
}

uint64_t RecIndex(uint64_t mpidr)
{
    //TODO
    return 42;
}
bool RecAuxAligned(uint64_t aux, uint64_t num_aux)
{
    //TODO
    return true;
}
bool RecAuxAlias(uint64_t rec, uint64_t aux, uint64_t num_aux)
{
    //TODO
    return true;
}
bool RecAuxStateEqual(struct granule **rec_aux_addr, uint64_t rd_aux_count, enum granule_state state)
{
    //TODO
    return true;
}
bool RecAuxEqual(struct granule **rec_aux_addr, struct granule **params_aux_addr, uint64_t aux_count)
{
    //TODO
    return true;
}
bool MpidrIsValid(uint64_t mpdir)
{
    //TODO
    return true;
}
bool MpidrEqual(uint64_t rec_mpidr, uint64_t params_mpidr)
{
    //TODO
    return true;
}
bool RmiRecParamsIsValid(uint64_t params_ptr)
{
    //TODO
    return true;
}
uint64_t RimExtendRec(struct rmm_realm realm, struct rmi_rec_params_buffer params)
{
    //TODO
    return 42;
}
