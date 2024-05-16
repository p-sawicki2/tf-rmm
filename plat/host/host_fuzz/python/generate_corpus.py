#!/usr/bin/env python3
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.

if __name__ == "__main__":

    from data_type import *
    import sys
    import os

    if os.path.dirname(sys.argv[1]) != '':
        os.makedirs(os.path.dirname(sys.argv[1]), exist_ok=True)
    with open(sys.argv[1], "wb") as file:
        if len(sys.argv) >= 2:
            fuzzing_corpus = RMMFuzzingInput.random(*sys.argv[2:])
        else:
            fuzzing_corpus = RMMFuzzingInput.random()

        file.write(fuzzing_corpus.to_bytes())
        file.close()

