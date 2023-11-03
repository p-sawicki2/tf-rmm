#include "granule.h"
#include "ripas.h"
#include "tb_realm.h"
#include "tb_granules.h"
#include "tb_common.h"

bool valid_rmi_realm_params(struct rmi_realm_params value)
{
	/* Note that rtt_level is maximum of 3 but we allow range to expand to 4. */
	return true;
}

struct rmi_realm_params init_rmi_realm_params(void)
{
	struct rmi_realm_params value = nondet_struct_rmi_realm_params();

	__CPROVER_assume(valid_rmi_realm_params(value));
	return value;
}

struct granule *init_realm_param_page(void)
{
	struct granule g = init_granule();
	struct rmi_realm_params param = init_rmi_realm_params();

	return inject_granule(&g, &param, sizeof(param));
}

struct rmi_realm_params_buffer RealmParams(uint64_t addr)
{
	return nondet_struct_rmi_realm_params_buffer();
}

bool GranuleAccessPermitted(uint64_t addr, enum granule_pas pas)
{
	return true;
}

bool RmiRealmParamsIsValid(uint64_t addr)
{
	return true;
}

bool RealmParamsSupported(struct rmi_realm_params_buffer params)
{
	return true;
}

bool AddrInRange(uint64_t addr, uint64_t base, size_t size)
{
	return true;
}

bool AddrIsAligned(uint64_t addr, int n)
{
	return true;
}

bool RttConfigIsValid(int ipa_width, int rtt_level_start, int rtt_num_start)
{
	return true;
}

bool RttsStateEqual(uint64_t rtt_base, int rtt_num_start, enum granule_state state)
{
	return true;
}

bool VmidIsValid(uint16_t vmid)
{
	return true;
}

bool VmidIsFree(uint16_t vmid)
{
	return true;
}

struct rmm_realm Realm(uint64_t rd)
{
	struct rmm_realm r = {0};
	return r;
}

bool RttsAllProtectedEntriesState(uint64_t rtt_base,
				  int rtt_num_start,
				  enum rmm_rtt_entry_state state)
{
	return true;
}

bool RttsAllUnprotectedEntriesState(uint64_t rtt_base,
				    int rtt_num_start,
				    enum rmm_rtt_entry_state state)
{
	return true;
}

bool RttsAllProtectedEntriesRipas(uint64_t rtt_base, int rtt_num_start, enum ripas ripas)
{
	return true;
}

bool Equal(uint64_t lhs, uint64_t rhs)
{
	return lhs == rhs;
}

uint64_t RimInit(enum hash_algo hash_algo, struct rmi_realm_params_buffer params)
{
	return 0UL;
}
