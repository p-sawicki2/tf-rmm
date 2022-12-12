#include "measurement.h"
#include "tb_measurement.h"

enum hash_algo nondet_hash_algo(void);

bool valid_hash_algo(enum hash_algo value) 
{
    return value == RMI_HASH_SHA_256 
        || value == RMI_HASH_SHA_512;
}

enum hash_algo init_hash_algo(void)
{
    enum hash_algo value = nondet_hash_algo();
    __CPROVER_assume(valid_hash_algo(value));
    return value;
}
