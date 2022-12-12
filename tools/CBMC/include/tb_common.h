/*
 * Copyright (c) 2021-2022, Arm Limited. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

#ifndef TB_COMMON_H
#define TB_COMMON_H

#include "stdbool.h"
#include "stdint.h"
#include "string.h"

/* Forces the model-checker to only consider executions where `p` holds. */
#define __ASSUME(p)				\
	do					\
		{				\
			__CPROVER_assume((p));	\
		} while (false)

#define ASSUME(p) __ASSUME(p)

/*
 * Forces the model checker to only consider executions where the numeric
 * variable `v` has been constrained to lie in the range [lower, upper]
 * inclusive.
 */
#define ASSUME_INCLUSIVE_RANGE(v, lower, upper) ASSUME((v) >= (lower) && (v) <= (upper))

/*
 * Forces the model checker to only consider executions where the numeric
 * variable `v` has been constrained to lie in the range (lower, upper)
 * exclusive.
 */
#define ASSUME_EXCLUSIVE_RANGE(v, lower, upper)	ASSUME((v) > (lower) && (v) < (upper))

/*
 * Challenges the model checker to show that `p` holds in the current execution
 * (in which case this behaves like a no-op), or otherwise come up with a
 * counterexample trace of states and assignments to variables which refutes
 * `p`, associating the name `name` to this trace.
 */
#define __ASSERT(p, name)					\
	do						\
		{					\
			__CPROVER_assert((p), (name));	\
		} while (false)

#define ASSERT(p, name) __ASSERT((p), (name))

/*
 * A marker for reachability: running CBMC with `--cover cover` will check that
 * all instances of `COVER` are reachable from the program entry point.
 */
#define __COVER(p)				\
	do					\
		{				\
			__CPROVER_cover(p);	\
		} while (false)

#define COVER(p) __COVER(p)

#define REACHABLE COVER(true)

/*
 * An assertion that always fails, useful for checking code-paths are never
 * reachable.
 */
#define UNREACHABLE	ASSERT(false, "UNREACHABLE")

////TODO what is this?
//#define uint512_t uint64_t

// Declare nondet_* functions.
// CBMC automatically returns nondet values based on the return types.
// However, enum is treated as integer hence the value might out of range.
bool nondet_bool(void);
unsigned char nondet_unsigned_char(void);
unsigned short nondet_unsigned_short(void);
unsigned int nondet_unsigned_int(void);
unsigned long nondet_unsigned_long(void);
char nondet_char(void);
short nondet_short(void);
int nondet_int(void);
long nondet_long(void);
uint32_t nondet_uint32_t(void);
uint64_t nondet_uint64_t(void);
int64_t nondet_int64_t(void);


//enum type_filed {
    //RmiRealmParams_hash_algo,
    //RmiRealmParams_features_0
//};

////TODO
//// Return the offset of a field in the type.
//size_t get_offset(enum type_filed value);
//#define __OFFSETOF(type,parameter) get_offset(type ## _ ## parameter)

//// Return the size in bytes of a field in the type.
//size_t get_size(enum type_field value);
//#define __SIZEOF(type,parameter) get_size(type ## _ ## parameter)

//unsigned char read_memory(unsigned long addr, size_t offset, size_t size);
//#define ReadMemory(ptr, offset, size) read_memory(ptr,offset,size)

unsigned long pow(unsigned long base, unsigned long power);

struct tb_regs {
	unsigned long X0;
	unsigned long X1;
	unsigned long X2;
	unsigned long X3;
	unsigned long X4;
	unsigned long X5;
	unsigned long X6;
};

struct tb_regs nondet_tb_regs(void);
struct tb_regs __tb_arb_regs(void);


bool ResultEqual_2(unsigned int code, unsigned int expected);
bool ResultEqual_3(unsigned int code, unsigned int expected, unsigned int walk_level);

bool __tb_arb_bool();
void __tb_lock_invariant(struct tb_lock_status *lock_status);
void __tb_expect_fail();


struct tb_lock_status {
	unsigned long something;
};


struct tb_lock_status __tb_lock_status();

//TODO what is this?
bool AddrIsInRange(uint64_t map_addr, uint64_t base, uint64_t size);

/*
 * Functions that manipulates PA, granule metadata and granule buffer, or content.
 */
bool valid_pa(uint64_t addr);
bool valid_granule_metadata_ptr(struct granule *p);
struct granule* pa_to_granule_metadata_ptr(uint64_t addr);
unsigned long granule_metadata_ptr_to_pa(struct granule* g_ptr);
void* granule_metadata_ptr_to_buffer_ptr(struct granule* g_ptr);
size_t granule_metadata_ptr_to_index(struct granule* g_ptr);
void* pa_to_granule_buffer_ptr(uint64_t addr);
//TODO change the function name
void init_pa_page(const void* content, unsigned long size);


// Return an unused continuous index to both `granules` and `granules_buffer` arrays.
unsigned long next_index();
bool unused_index(size_t index);
// Initialise granule at an non-deterministic granule. It updates both granule metadata array and physical page array.
struct granule * inject_granule_at(const struct granule* granule_metadata, const void* physical_page, size_t size_physical_page, size_t idx);
struct granule * inject_granule(const struct granule* granule_metadata, const void* physical_page, size_t size_physical_page);

#endif  /* !TB_COMMON_H */
