#!/usr/bin/env python3
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.

import random

def init(seed):
    random.seed(seed)


def deinit():
    pass

# Default pages/memory size
HOST_MEM_SIZE=0x80000
# Default granule counts
RMM_MAX_GRANULES=0x80
# The size of meta-data of a granule, i.e., `struct granule`
SIZE_OF_GRANULE=4
FUZZING_COMMAND_COUNT=10
FUZING_REGISTER_COUNT=7
REGISTER_SIZE=8

FUZZING_FID_BEGIN=0xC4000140
FUZZING_FID_END=0xC4000190

def fuzz(buf, add_buf, max_size):
    """
    Called per fuzzing iteration.

    @type buf: bytearray
    @param buf: The buffer that should be mutated.

    @type add_buf: bytearray
    @param add_buf: A second buffer that can be used as mutation source.

    @type max_size: int
    @param max_size: Maximum size of the mutated output. The mutation must not
        produce data larger than max_size.

    @rtype: bytearray
    @return: A new bytearray containing the mutated data
    """
    # modulo the opcode so it is in the range of FUZZING_FID_BEGIN and FUZZING_FID_END (included).
    machine_state_bytes = (HOST_MEM_SIZE + RMM_MAX_GRANULES * SIZE_OF_GRANULE)
    fuzzing_command_block_size = FUZING_REGISTER_COUNT * REGISTER_SIZE
    for index in range(FUZZING_COMMAND_COUNT):
        fuzzing_command_block_offset = machine_state_bytes + \
                                    index * fuzzing_command_block_size
        opcode = int.from_bytes(buf[fuzzing_command_block_offset:fuzzing_command_block_offset+REGISTER_SIZE], "little") % \
                                            (FUZZING_FID_END - FUZZING_FID_BEGIN + 1) + FUZZING_FID_BEGIN
        buf[fuzzing_command_block_offset:fuzzing_command_block_offset+REGISTER_SIZE] = opcode.to_bytes(8, "little")

    return buf
