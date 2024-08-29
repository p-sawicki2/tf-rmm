#!/usr/bin/env python3
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.

"""Module provide class with methods to generate and parse fuzzing corpus (inputs) and crashes"""

import random
import os
# random.randbytes is only available starting from Python v3.9
if not hasattr(random, 'randbytes'):
	def my_randbytes(n):
		return bytes([random.randint(0, 255) for _ in range(n)])
	random.randbytes = my_randbytes

# Default granule and page counts
GRANULE_PAGE_COUNT=os.getenv("RMM_MAX_GRANULES", 0x80)
# Default pages/memory size
PAGE_SIZE=os.getenv("GRANULE_SIZE", 4096)
# The size of meta-data of a granule, i.e., `struct granule`
SIZE_OF_GRANULE=os.getenv("FUZZ_GRANULE_META_SIZE", 2)

# fuzzing command config
COMMAND_COUNT=os.getenv("FUZZ_COMMAND_COUNT", 20)
REGISTER_COUNT=os.getenv("FUZZ_REGISTER_COUNT", 7)
REGISTER_SIZE=os.getenv("REGISTER_SIZE", 8)

# The opcode range for fuzzing
FID_BEGIN=os.getenv("FUZZ_FID_BEGIN", 0xC4000150)
FID_END=os.getenv("FUZZ_FID_END", 0xC4000190)

def if_string_to_int(v):
	if isinstance(v, str):
		return int(v, 0)
	return v

class RMMCall:
	"""Class to serialise and deserialise RMM interface call."""
	def __init__(self, registers_bytes: [int]):
		# Registers, X0 to X6, values, in the form of a list of integer.
		self.registers_bytes = registers_bytes

	def __repr__(self):
		hex_values = [x.to_bytes(REGISTER_SIZE, byteorder="little", signed=True) for x in self.registers_bytes]
		return ','.join([f"X{index}: {value.hex()}" for index, value in enumerate(hex_values)])

	def to_bytes(self, register_size=REGISTER_SIZE):
		"""Serialise RMM interface call, values of registers, to bytes."""
		return b"".join([ value.to_bytes(register_size, byteorder="little", signed=True) \
									for value in self.registers_bytes])

	def set_register_value(self, register, value):
		self.registers_bytes[register] = value

	@staticmethod
	def from_bytes(raw_bytes: bytearray, register_size=REGISTER_SIZE):
		"""Deserialise an binary to RMMCall."""
		# split the raw bytes array into multiple arrays in `register_size` size.
		registers_bytes = [int.from_bytes(raw_bytes[i : i + register_size], byteorder="little", signed=True) \
									for i in range(0, len(raw_bytes), register_size)]
		return RMMCall(registers_bytes)

	@staticmethod
	def zero(fuzzing_register_count=REGISTER_COUNT):
		registers_bytes = [0] * fuzzing_register_count
		return RMMCall(registers_bytes)

	@staticmethod
	def random(fuzzing_fid_begin = FID_BEGIN
			   , fuzzing_fid_end = FID_END
			   , fuzzing_register_count=REGISTER_COUNT
			   , register_size=REGISTER_SIZE):
		"""Generate a RMMCall containing random values."""
		# Generate fid in the specified range
		return RMMCall([random.randint(fuzzing_fid_begin, fuzzing_fid_end)] + \
		# Generate random x_1 to x_`REGISTER_COUNT` as parameter
			  [random.randint(0, 2 ** register_size - 1) \
							for _ in range(fuzzing_register_count - 1)])

class RMMFuzzingInput:
	"""Class to serialise and deserialise fuzzing corpus (inputs) and crashes,
	which contains machine states and RMM interface calls."""
	def __init__(self, host_mem_bytes:[[bytearray]]
				, granule_meta_bytes:[[bytearray]]
				, rmm_call_sequence:[RMMCall]):
		self.host_mem_bytes = host_mem_bytes
		self.granule_meta_bytes = granule_meta_bytes
		self.rmm_call_sequence = rmm_call_sequence

	def __repr__(self):
		# serialise all content to hex bytes
		return '\n'.join([f"Page #{index}: [{value.hex()}]" \
								for index, value in enumerate(self.host_mem_bytes)] + \
								[f"Granule #{index}: [{int.from_bytes(value, byteorder='little'):0>16b}]" \
								for index, value in enumerate(self.granule_meta_bytes)] + \
						 [f"RMM call #{index}: [{value}]" \
								for index, value in enumerate(self.rmm_call_sequence)])

	@staticmethod
	def zero(page_size = PAGE_SIZE \
			, granule_meta_size = SIZE_OF_GRANULE \
			, granule_page_count = GRANULE_PAGE_COUNT \
			, command_call_count = COMMAND_COUNT \
			, registers_counts = REGISTER_COUNT):
		"""Return a zero filled RMMFuzzingInput"""
		host_mem_bytes = [ bytearray(page_size) \
								for _ in range(granule_page_count) ]
		granule_meta_bytes = [ bytearray(granule_meta_size) \
								for _ in range(granule_page_count) ] 
		rmm_call_sequence = [RMMCall.zero(registers_counts) \
								for _ in range(command_call_count) ]
		return RMMFuzzingInput(host_mem_bytes, granule_meta_bytes, rmm_call_sequence)

	def to_bytes(self, register_size=REGISTER_SIZE):
		"""Serialise fuzzing corpus to bytes"""
		return b"".join(self.host_mem_bytes + self.granule_meta_bytes + \
				[rmm_call.to_bytes(register_size) for rmm_call in self.rmm_call_sequence])

	def set_register_value(self, command, register, value):
		"""Set the register value of a command"""
		self.rmm_call_sequence[command].set_register_value(register, value) 

	def set_register_values(self, scripts : [(int, int, int)]):
		"""Set the register value of a command"""
		for command, register, value in scripts:
			self.rmm_call_sequence[command].set_register_value(register, value) 

	@staticmethod
	def from_bytes(raw_bytes: bytearray \
				  , page_size = PAGE_SIZE \
				  , granule_meta_size = SIZE_OF_GRANULE \
				  , granule_page_count = GRANULE_PAGE_COUNT \
				  , command_call_count = COMMAND_COUNT \
				  , registers_counts = REGISTER_COUNT \
				  , register_size = REGISTER_SIZE):
		"""Deserialise fuzzing crash from bytes"""
		# split the host page memory into a list of arraybyte
		host_mem_byte_count = page_size * granule_page_count
		host_mem_bytes = raw_bytes[:host_mem_byte_count]
		host_mem_bytes = [host_mem_bytes[i : i + page_size] \
								for i in range(0, len(host_mem_bytes), page_size)]

		# split the granule meta data into a list of arraybyte
		granule_meta_byte_end_offset = host_mem_byte_count + granule_meta_size * granule_page_count
		granule_meta_bytes = raw_bytes[host_mem_byte_count : granule_meta_byte_end_offset]
		granule_meta_bytes = [granule_meta_bytes[i : i + granule_meta_size] \
									for i in range(0, len(granule_meta_bytes), granule_meta_size)]

		# split the rmm command calls into a list of RMMCall
		individual_command_byte_count = registers_counts * register_size
		call_command_byte_count = command_call_count * individual_command_byte_count
		rmm_call_sequence_start_offset = granule_meta_byte_end_offset
		rmm_call_sequence_end_offset = rmm_call_sequence_start_offset + call_command_byte_count
		rmm_call_sequence = raw_bytes[rmm_call_sequence_start_offset : rmm_call_sequence_end_offset]
		rmm_call_sequence = [RMMCall.from_bytes(rmm_call_sequence[i : i + individual_command_byte_count]
												, register_size) \
								for i in range(0, len(rmm_call_sequence) \
												   , individual_command_byte_count)]

		return RMMFuzzingInput(host_mem_bytes, granule_meta_bytes, rmm_call_sequence)

	@staticmethod
	def random_granule_meta(size):
		result = bytearray(random.randbytes(size))
		# set the lock bit to zero
		result[1] = result[1] & 0x7F
		return result

	@staticmethod
	def random(page_size = PAGE_SIZE \
			  , granule_meta_size = SIZE_OF_GRANULE \
			  , granule_page_count = GRANULE_PAGE_COUNT \
			  , command_call_count = COMMAND_COUNT \
			  , fuzzing_fid_begin = FID_BEGIN \
			  , fuzzing_fid_end = FID_END \
			  , registers_counts = REGISTER_COUNT \
			  , register_size = REGISTER_SIZE):
		"""Generate a RMMFuzzingInput containing random values."""

		page_size = if_string_to_int(page_size)
		granule_meta_size = if_string_to_int(granule_meta_size)
		granule_page_count = if_string_to_int(granule_page_count)
		command_call_count = if_string_to_int(command_call_count)
		fuzzing_fid_begin = if_string_to_int(fuzzing_fid_begin)
		fuzzing_fid_end = if_string_to_int(fuzzing_fid_end)
		registers_counts = if_string_to_int(registers_counts)
		register_size = if_string_to_int(register_size)
		return RMMFuzzingInput([random.randbytes(page_size) \
									for _ in range(granule_page_count)] \
							   # Clean up the lock bit
							   , [RMMFuzzingInput.random_granule_meta(granule_meta_size) \
									for _ in range(granule_page_count)] \
							   , [RMMCall.random(fuzzing_fid_begin \
												 , fuzzing_fid_end \
												 , registers_counts \
												 , register_size) \
									for _ in range(command_call_count) ])

	@staticmethod
	def random_with_commands(commands, page_size = PAGE_SIZE \
			  , granule_meta_size = SIZE_OF_GRANULE \
			  , granule_page_count = GRANULE_PAGE_COUNT \
			  , command_call_count = COMMAND_COUNT \
			  , fuzzing_fid_begin = FID_BEGIN \
			  , fuzzing_fid_end = FID_END \
			  , registers_counts = REGISTER_COUNT \
			  , register_size = REGISTER_SIZE):
		binary = RMMFuzzingInput.random(page_size, granule_meta_size \
								,granule_page_count, command_call_count \
								,fuzzing_fid_begin, fuzzing_fid_end \
								, registers_counts, register_size)
		binary.set_register_values(commands)
		return binary
