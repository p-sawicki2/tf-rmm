#!/usr/bin/env python3
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.

import random
from data_type import *

def init(seed):
    random.seed(seed)


def deinit():
    pass

# Default pages/memory size
HOST_MEM_SIZE = GRANULE_PAGE_COUNT * PAGE_SIZE

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
    # modulo the opcode so it is in the range of FID_BEGIN and FID_END (included).
    machine_state_bytes = (HOST_MEM_SIZE + GRANULE_PAGE_COUNT * SIZE_OF_GRANULE)
    fuzzing_command_block_size = REGISTER_COUNT * REGISTER_SIZE
    for index in range(COMMAND_COUNT):
        fuzzing_command_block_offset = machine_state_bytes + \
                                    index * fuzzing_command_block_size
        opcode = int.from_bytes(buf[fuzzing_command_block_offset:fuzzing_command_block_offset+REGISTER_SIZE], "little") % \
                                            (FID_END - FID_BEGIN + 1) + FID_BEGIN
        buf[fuzzing_command_block_offset:fuzzing_command_block_offset+REGISTER_SIZE] = opcode.to_bytes(8, "little")

    return buf
