#!/usr/bin/env python
# encoding: utf-8
"""
Example Python Module for AFLFuzz

@author:     Christian Holler (:decoder)

@license:

This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at http://mozilla.org/MPL/2.0/.

@contact:    choller@mozilla.com
"""

import random

def init(seed):
    """
    Called once when AFLFuzz starts up. Used to seed our RNG.

    @type seed: int
    @param seed: A 32-bit random value
 
 """
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
        fuzzing_command_block_offset = machine_state_bytes + index * fuzzing_command_block_size
        opcode = int.from_bytes(buf[fuzzing_command_block_offset:fuzzing_command_block_offset+REGISTER_SIZE], "little") % (FUZZING_FID_END - FUZZING_FID_BEGIN + 1) + FUZZING_FID_BEGIN
        buf[fuzzing_command_block_offset:fuzzing_command_block_offset+REGISTER_SIZE] = opcode.to_bytes(8, "little")

    return buf



# Uncomment and implement the following methods if you want to use a custom
# trimming algorithm. See also the documentation for a better API description.

# def init_trim(buf):
#     '''
#     Called per trimming iteration.
#
#     @type buf: bytearray
#     @param buf: The buffer that should be trimmed.
#
#     @rtype: int
#     @return: The maximum number of trimming steps.
#     '''
#     global ...
#
#     # Initialize global variables
#
#     # Figure out how many trimming steps are possible.
#     # If this is not possible for your trimming, you can
#     # return 1 instead and always return 0 in post_trim
#     # until you are done (then you return 1).
#
#     return steps
#
# def trim():
#     '''
#     Called per trimming iteration.
#
#     @rtype: bytearray
#     @return: A new bytearray containing the trimmed data.
#     '''
#     global ...
#
#     # Implement the actual trimming here
#
#     return bytearray(...)
#
# def post_trim(success):
#     '''
#     Called after each trimming operation.
#
#     @type success: bool
#     @param success: Indicates if the last trim operation was successful.
#
#     @rtype: int
#     @return: The next trim index (0 to max number of steps) where max
#              number of steps indicates the trimming is done.
#     '''
#     global ...
#
#     if not success:
#         # Restore last known successful input, determine next index
#     else:
#         # Just determine the next index, based on what was successfully
#         # removed in the last step
#
#     return next_index
#
# def post_process(buf):
#    '''
#    Called just before the execution to write the test case in the format
#    expected by the target
#
#    @type buf: bytearray
#    @param buf: The buffer containing the test case to be executed
#
#    @rtype: bytearray
#    @return: The buffer containing the test case after
#    '''
#
# def post_run():
#     '''
#     Called after each time the execution of the target program by AFL++
#     '''
#     pass
#
# def havoc_mutation(buf, max_size):
#    '''
#    Perform a single custom mutation on a given input.
#
#    @type buf: bytearray
#    @param buf: The buffer that should be mutated.
#
#    @type max_size: int
#    @param max_size: Maximum size of the mutated output. The mutation must not
#        produce data larger than max_size.
#
#    @rtype: bytearray
#    @return: A new bytearray containing the mutated data
#    '''
#
# def havoc_mutation_probability():
#     '''
#     Called for each `havoc_mutation`. Return the probability (in percentage)
#     that `havoc_mutation` is called in havoc. Be default it is 6%.
#
#     @rtype: int
#     @return: The probability (0-100)
#     '''
#     return prob
#
# def queue_get(filename):
#     '''
#     Called at the beginning of each fuzz iteration to determine whether the
#     test case should be fuzzed
#
#     @type filename: str
#     @param filename: File name of the test case in the current queue entry
#
#     @rtype: bool
#     @return: Return True if the custom mutator decides to fuzz the test case,
#         and False otherwise
#     '''
#     return True
#
# def queue_new_entry(filename_new_queue, filename_orig_queue):
#     '''
#     Called after adding a new test case to the queue
#
#     @type filename_new_queue: str
#     @param filename_new_queue: File name of the new queue entry
#
#     @type filename_orig_queue: str
#     @param filename_orig_queue: File name of the original queue entry
#     '''
#     pass
