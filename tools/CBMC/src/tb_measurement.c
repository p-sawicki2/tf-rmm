#include "measurement.h"
#include "tb_measurement.h"

bool valid_hash_algo(enum hash_algo value) 
{
    return value == HASH_ALGO_SHA256 
        || value == HASH_ALGO_SHA512;
}

enum hash_algo init_hash_algo(void)
{
    enum hash_algo value = nondet_hash_algo();
    __CPROVER_assume(valid_hash_algo(value));
    return value;
}
