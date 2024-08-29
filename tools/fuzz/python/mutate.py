#!/usr/bin/env python3
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.

"""A custom mutator to AFL++, when fuzzing RMM"""

import random
from data_type import GRANULE_PAGE_COUNT, PAGE_SIZE \
		, SIZE_OF_GRANULE, COMMAND_COUNT, REGISTER_COUNT \
		, REGISTER_SIZE, FID_BEGIN, FID_END

def init(seed):
	"""Initialisation of seed"""
	random.seed(seed)


def deinit():
	"""De-initialisation of custom mutator"""
	pass

def splice_optout():
	"""Since we do not use the `_add_buf` variable in fuzz function,
	we declare this as suggested by AFL++ for better performance"""
	pass

def fuzz(buf, _add_buf, _max_size):
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
	# Ensure all the granules are UNLOCKED
	granule_meta_offset = GRANULE_PAGE_COUNT * PAGE_SIZE
	machine_state_bytes = GRANULE_PAGE_COUNT * PAGE_SIZE + \
							GRANULE_PAGE_COUNT * SIZE_OF_GRANULE
	for index in range(granule_meta_offset, \
						machine_state_bytes, GRANULE_PAGE_COUNT):
		buf[index] = buf[index] & 0x7F

	# Modulo the opcode so it is in the range of FID_BEGIN and FID_END (included).
	fuzzing_command_block_size = REGISTER_COUNT * REGISTER_SIZE
	for index in range(machine_state_bytes \
					  , machine_state_bytes + \
							COMMAND_COUNT * fuzzing_command_block_size \
					  , fuzzing_command_block_size):
		opcode = int.from_bytes(
				buf[index : index + REGISTER_SIZE]
					, "little") % (FID_END - FID_BEGIN + 1) + FID_BEGIN
		buf[index : index + REGISTER_SIZE] = opcode.to_bytes(8, "little")

	return buf
