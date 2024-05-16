#!/usr/bin/env python3
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.

# Default pages/memory size
HOST_MEM_SIZE=0x80000
# Default granule counts
RMM_MAX_GRANULES=0x80
# The size of meta-data of a granule, i.e., `struct granule`
SIZE_OF_GRANULE=4

FUZZING_COMMAND_COUNT=10
FUZING_REGISTER_COUNT=7
REGISTER_SIZE=8

# The opcode range for fuzzing
FUZZING_FID_BEGIN=0xC4000140
FUZZING_FID_END=0xC4000190

def generate_data(file_path, machine_state_bytes=(HOST_MEM_SIZE + RMM_MAX_GRANULES * SIZE_OF_GRANULE), fuzzing_command_count=FUZZING_COMMAND_COUNT, fuzing_register_count=FUZING_REGISTER_COUNT, register_size=REGISTER_SIZE):
    # convert, if necessary, str to int
    machine_state_bytes = int(machine_state_bytes)
    fuzzing_command_count = int(fuzzing_command_count)
    fuzing_register_count = int(fuzing_register_count)
    register_size = int(register_size)
    with open(file_path, "wb") as file:
        import random
        # Generate random byte as the system state
        generated_bytes = random.randbytes(machine_state_bytes)

        for _ in range(fuzzing_command_count):
            # Generate fid in smaller range
            x0_fid = random.randint(FUZZING_FID_BEGIN, FUZZING_FID_END)
            generated_bytes += x0_fid.to_bytes(register_size, byteorder="little")

            # Generate random x_1 to x_`REGISTER_COUNT` as parameter
            generated_bytes += random.randbytes((fuzing_register_count - 1) * register_size)

        file.write(bytearray(generated_bytes))
        file.close()

if __name__ == "__main__":

    import sys
    import os

    os.makedirs(os.path.dirname(sys.argv[1]), exist_ok=True)
    generate_data(*sys.argv[1:])
