#include "status.h"
#include "table.h"
#include "utils_def.h"
#include "tb_common.h"
#include "host_defs.h"
#include "host_utils.h"
#include "string.h"
#include "granule.h"
#include "tb_granules.h"
#include "measurement.h"

struct tb_regs __tb_arb_regs() {
	return nondet_tb_regs();
}

bool ResultEqual_2(unsigned int code, unsigned int expected)
{
	return code == expected;
}

// TODO
bool ResultEqual_3(unsigned int code, unsigned int expected, unsigned int level)
{
	return true;
}

bool __tb_arb_bool() 
{
	return nondet_bool();
}

void __tb_lock_invariant(struct tb_lock_status *lock_status) 
{
	// TODO
}

void __tb_expect_fail() 
{
	// TODO
	// Assertion used to check consistency of the testbench
}


struct tb_lock_status __tb_lock_status() 
{
	struct tb_lock_status r = {NULL};
	return r;
}


bool AddrIsInRange(uint64_t map_addr, uint64_t base, uint64_t size) 
{
	return map_addr < MAX_IPA_SIZE &&
		map_addr >= base &&
		base < base + size &&
		map_addr < base + size;
}


unsigned long pow(unsigned long base, unsigned long power)
{
    if (power == 0) {
	return 1UL;
    }
    if (base == 2) {
        return 1UL << power;
    }
    unsigned long rst = base;
    for (unsigned long i = 1UL; i < power; ++i) {
        rst *= base;
    }
    return rst;
}

extern struct granule granules[RMM_MAX_GRANULES];
extern unsigned char granules_buffer[HOST_MEM_SIZE];
bool used_granules_buffer[HOST_NR_GRANULES] = { 0 }; 

bool valid_pa(uint64_t addr) 
{
    //NOTE: the explicit pointer to integer type cast is necessary, as CBMC check fails without it.
    if (GRANULE_ALIGNED(addr) && (uint64_t)granules_buffer <= addr && addr < (uint64_t)granules_buffer + sizeof(granules_buffer)) {
        // Keep these assserts for sanitary check, there was situation these asserts fail possibly due to CBMC dislike type conversion between number and pointer
        ASSERT(GRANULE_ALIGNED(addr), "internal: `valid_pa`, addr in alignment");
        ASSERT(addr >= (uint64_t)granules_buffer, "internal: `valid_pa`, addr in lower range");
        ASSERT(addr < (uint64_t)granules_buffer + sizeof(granules_buffer), "internal: `valid_pa`, addr in upper range");
        return true;
    }
    return false;
}

struct granule* pa_to_granule_metadata_ptr(uint64_t addr)
{
    uint64_t idx = (addr - (unsigned long)granules_buffer)/GRANULE_SIZE;
    __ASSERT(idx >= 0, "internal: `pa_to_granule_metadata_ptr`, addr is in lower range");
    __ASSERT(idx < RMM_MAX_GRANULES, "internal: `pa_to_granule_metadata_ptr`, addr is in upper range");

    return &granules[idx];
}

unsigned long granule_metadata_ptr_to_pa(struct granule* g_ptr)
{
    return (unsigned long)granules_buffer + (g_ptr - granules) * GRANULE_SIZE;
}

void* pa_to_granule_buffer_ptr(uint64_t addr)
{
    __ASSERT((unsigned char *)addr - granules_buffer >= 0, "internal: `pa_to_granule_buffer_ptr`, addr is in lower range");
    // NOTE: Has to do this strange computation and type cast so CBMC can handle.
    return (void*)granules_buffer + ((unsigned char *)addr - granules_buffer);
}

void* granule_metadata_ptr_to_buffer_ptr(struct granule* g_ptr)
{
    if(!valid_granule_metadata_ptr(g_ptr)) return NULL;
    return granules_buffer + (g_ptr - granules) * GRANULE_SIZE;
}

size_t granule_metadata_ptr_to_index(struct granule* g_ptr)
{
    return g_ptr - granules;
}

bool valid_granule_metadata_ptr(struct granule *p) 
{
    return p >= granules 
        && p < granules + RMM_MAX_GRANULES;
}

// Return the first index of `number` of unused continuous indice to both `granules` and `granules_buffer` arrays.
unsigned long next_index()
{
	unsigned long index = nondet_unsigned_long();

    __ASSUME(unused_index(index));
    if(!unused_index(index)) return -1;

    REACHABLE;

    return index;
}

bool unused_index(size_t index)
{
    if(index < HOST_NR_GRANULES && !used_granules_buffer[index]) return true;
    return false;
}

void init_pa_page(const void* content, unsigned long size)
{
    unsigned long index = next_index();
    unsigned long offset = index * GRANULE_SIZE;

	(void)memcpy(granules_buffer + offset, content, size);
    used_granules_buffer[index] = true;
}

struct granule * inject_granule_at(const struct granule* granule_metadata, const void* physical_page, size_t size_physical_page, size_t index)
{
    unsigned long offset = index * GRANULE_SIZE;

    granules[index] = *granule_metadata;
	(void)memcpy(granules_buffer + offset, physical_page, size_physical_page);
    used_granules_buffer[index] = true;
    return &granules[index];
}

struct granule * inject_granule(const struct granule* granule_metadata, const void* physical_page, size_t size_physical_page)
{
    unsigned long index = next_index();
    return inject_granule_at(granule_metadata, physical_page, size_physical_page, index);
}

void measurement_hash_compute(enum hash_algo hash_algo,
                              void *data,
                              size_t size,
                              unsigned char *out)
{
    // TODO magic number for checking.
    *out = 42;
}

