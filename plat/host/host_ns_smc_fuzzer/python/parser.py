#!/usr/bin/env python3
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.

if __name__ == "__main__":

    from data_type import *
    import sys

    with open(sys.argv[1], "rb") as file:
        fuzzing_input = RMMFuzzingInput.from_bytes(file.read())
        print(fuzzing_input)
