# CompCert
The formally-verified C compiler.

## Overview
The CompCert C verified compiler is a compiler for the core C language 
that generates code for the ARM, PowerPC, RISC-V and x86 processors.

The distinguishing feature of CompCert is that it has been formally
verified using the Coq proof assistant: the generated assembly code is
formally guaranteed to behave as prescribed by the semantics of the
source C code.

For more information on CompCert (supported platforms, supported C
features, installation instructions, using the compiler, etc), please
refer to the [Web site](https://compcert.org/) and especially
the [user's manual](https://compcert.org/man/).

## Research fork tooling: macOS ARM64

The `fast` branch starts from upstream tag `v3.18`, commit
`14d616046360a0b2611ebdfc2f98368af402e1f7`. That upstream tag still
identifies itself as version 3.17 when running `ccomp -version`; use the
commit to identify this baseline.

The performance target is to close 75% of the initial runtime gap with
clang `-O2` on the frozen suite in `perf/suite.json`. The aggregate metric
is the equal-weight geometric mean of CompCert/clang runtime ratios.
For an initial ratio R0 greater than 1, the target is
`R <= 1 + 0.25 * (R0 - 1)`.

Prerequisites are macOS on Apple silicon, Xcode command-line tools, Python 3,
and GMP development headers/library (`/opt/homebrew/opt/gmp` is supported).
The bootstrap installs opam, OCaml 4.14.4, Coq 8.20.1 and Menhir 20231231
inside this checkout, using the frozen package definitions in
`perf/toolchain.export`. It also avoids detecting SDK functions unavailable
on the running macOS. It does not alter shell startup files.

```sh
make -f Makefile.fast bootstrap
make -f Makefile.fast proofs       # clean proofs, coqchk, one-file rebuild timing
make -f Makefile.fast verify       # build, reference outputs, native tests, ABI, PIC
make -f Makefile.fast baseline     # first performance reference, on an idle Mac
make -f Makefile.fast bench        # subsequent measurements against that reference
```

`baseline` includes bootstrap, proof verification and compiler construction.
The initial reference must use the unchanged upstream compiler. Once its
correctness and noise checks pass, it cannot be overwritten by the runner.
Reports are JSON files in `perf/results`; detailed build/check logs go to
the ignored `perf/artifacts` directory. `make -f Makefile.fast correctness`
checks benchmark outputs without running a speed-measurement series.

The suite uses ten programs and their published expected outputs from the
pinned `test` submodule, with source hashes and arguments fixed in the
manifest. Both compilers must produce identical expected stdout and exit
successfully. Timing excludes process startup. The runner alternates the
compilers, takes nine samples in each of two blocks, and rejects results
with relative median absolute deviation above 5% or block drift above 3%.
macOS QoS requests favor performance cores but do not enforce or verify
exclusive placement on them. A rejected timing series is not a valid baseline
or evidence of an optimization gain.

`perf/guard.py` freezes the upstream formal sources and license byte for byte.
The main correctness theorem, its hypotheses, and `Asm.v` remain unchanged.
Scalar heuristic experiments live on separate `experiment/*` branches and
require passing correctness and noise checks, with a smaller measured gap,
before promotion to `fast`. The small-leaf inlining experiment additionally
provides `make -f Makefile.fast test-inline` to check generated calls and
optimization-option contracts. NEON and a Sail/Arm bridge require future
formal development; this tooling does not implement them.

## License
CompCert is not free software.  This non-commercial release can only
be used for evaluation, research, educational and personal purposes.
A commercial version of CompCert, without this restriction and with
professional support and extra features, can be purchased from
[AbsInt](https://www.absint.com).  See the file [LICENSE](LICENSE) for more
information.

## Copyright
The CompCert verified compiler is Copyright Institut National de
Recherche en Informatique et en Automatique (INRIA) and 
AbsInt Angewandte Informatik GmbH.


## Contact
General discussions on CompCert take place on the
[compcert-users@inria.fr](https://sympa.inria.fr/sympa/info/compcert-users)
mailing list.

For inquiries on the commercial version of CompCert, please contact
info@absint.com
