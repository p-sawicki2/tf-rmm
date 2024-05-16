# Configuration

This fuzzing setting uses [AFL++](https://github.com/AFLplusplus/AFLplusplus).
AFL++ provides different modes, and we are using [`alf-clang-lto`](https://github.com/AFLplusplus/AFLplusplus/blob/stable/instrumentation/README.lto.md) and the [_persistent mode_](https://github.com/AFLplusplus/AFLplusplus/blob/stable/instrumentation/README.persistent_mode.md) for the best performance.
The source code is compile with the compiler `alf-clang-lto`, that (1) 'analyses' and 'instruments' the source code for better fuzzing result, better coverage, for example, and (2) performs link-time optimization (LTO) on the final executable.
By the time we are writting this readme, `alf-clang-lto` only exists in the AFL++ for Linux.
The _persistent mode_, meanwhile, fuzzes the target (binary) mulitple times in a single fork, which accelerates the fuzzing process: we observe the speed-up is around 3-5x for our setup to fuzz RMM.

# Strategy

Although fuzzing can be applied directly to on binary, treating the binary as a 'black-box', we adopt more 'white-box' method: compiling the source code with the AFL++-altered compiler `afl-clang-lto` and providing an separate entry point for the fuzzing engine.
This enables us tailor the fuzzing and achieve better result.

In short, our strategy can be summarised as: given an arbitrary machine state, and given a certain numbers of interface calls to RMM, (1) we expect no program crash and (2) the machine state evolves as expected from the specification.
The first goal (1) is relatively straightforward and is now stable, but the second goal (2) is actively developed.
The machine state contains:

* All granule data, `unsigned char granules_buffer[HOST_MEM_SIZE] __aligned(GRANULE_SIZE);`, orginally declared in `plat/host/common/src/host_utils.c`; and
* All granule meta-data, `struct granule granules[RMM_MAX_GRANULES];`, orginally declared in `lib/granule/src/granule.c`.

The fuzzing entry point, `plat/host/host_ns_smc_fuzzer/src/host_setup.c`, guides the fuzzing engine to assign, or populate, random bytes to those two data structs, in the `iteration_init` function.
Given the initial machine state, the function `execute` hooks the fuzzing engine to generate and call ten random interface calls by default, defined by macro `FUZZING_COMMAND_COUNT`.
In fact, fuzzing engine just feeds random bytes to register `X0` to `X6` and call the handler function `handle_ns_smc` from the source code.

We recommend using _persistent mode_, which means compiling with flag `PERSISTENT_MODE`.
However, when crashes are found, and users want to check and debug the cause, compiling with non-persistent mode allows the binary read an input, i.e., a file, and then execute the crashing cases.
In the persistent mode setup, we only initialise the global once, via `init` function, before the fuzzing loop to gain best performance.
Note that `init` must be called before `_AFL_INIT()`, more details on using persistent mode can be found in [link](https://github.com/AFLplusplus/AFLplusplus/blob/stable/instrumentation/README.persistent_mode.md).

# How to use

Run the following command:
```cmake
cmake -DRMM_CONFIG=host_defcfg \
      -DHOST_VARIANT=host_ns_smc_fuzzer \
      -DCMAKE_BUILD_TYPE=Debug \
      -DCMAKE_C_COMPILER=/usr/local/bin/afl-clang-lto \
      -DCMAKE_AR=/usr/bin/llvm-ar \
      -DCMAKE_LINKER=/usr/local/bin/afl-ld-lto \
      -DRMM_MAX_GRANULES=0x80 \
      -DHOST_MEM_SIZE=0x80000 \
      -DCMAKE_C_FLAGS="-DVERIFICATION_FLAG -DPERSISTENT_MODE" \
      -S ${ROOT_OF_RMM} \
      -B ${TARGET_DIR}
```
The values for `RMM_CONFIG` and `HOST_VARIANT` ensures we are compiling for host mode of RMM and for fuzzing, respectively.
Since fuzzing relies on explicit `assert`, which checks property and crashes the program, we must compile with `debug` mode.
We need to compile the source code and link the binary with AFL++, and therefore, we have to provide the correct path to `afl-clang-lto`, `llvm-ar` and `afl-ld-lto`.
