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
make -f Makefile.fast test-validators # malformed candidates against extracted validators
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

`perf/guard.py` anchors the original source and license hashes to fixed
upstream Git objects. Reviewed changes are recorded in
`perf/proved-changes.json`. All original theorem and lemma statements remain
identical, including the 11 statements in `driver/Compiler.v`. Its pipeline
and composition proofs now include the additional proved RTL passes.
A full check rebuilds the proofs, runs independent `coqchk`, and compares the
two principal theorems' assumptions with the original checked baseline.
Additional computational parameters are restricted to named Boolean options
and a second allocation oracle, whose output is validated. They assert no
optimizer correctness property. The report distinguishes these parameters
from unchanged original logical assumptions. An old success report is
invalidated before verification starts. This source gate complements the
Coq kernel.

### Default-disabled experiments

This branch is `experiment/seven-stage`; it has not been promoted to `fast`.
No speed improvement is claimed. The full option list, combined profiles and
precise limits are in `perf/experiment-profiles.json`. For example:

```sh
COMPCERT_EXPERIMENTS=rtl-unroll2,memory-cleanup ./ccomp -stdlib runtime program.c
COMPCERT_EXPERIMENTS=loop-spill,trace-layout COMPCERT_EXPERIMENT_TRACE=/tmp/compcert-trace.jsonl ./ccomp -stdlib runtime program.c
make -f Makefile.fast test-experiments
make -f Makefile.fast test-neon
make -f Makefile.fast verify
```

Every option is off by default. Unknown options and simultaneous
`rtl-unroll2,rtl-unroll4` are rejected. JSONL tracing records actual heuristic
choices, validated CFG candidates, and per-pass RTL changes. Structural tests
also require real transformations, rather than merely successful compilation.

The experiments currently implement:

* Small nonrecursive leaf inlining, loop-weighted spill costs and an alternative
  trace layout, checked by the existing CompCert inlining/allocation/layout
  correctness machinery. An invalid allocation candidate can use a separately
  validated baseline allocation; an invalid returned layout uses the proved
  deterministic fallback. Exceptions or nontermination inside an oracle are
  not covered by this fallback.
* Alternative 32/64-bit multiply-negate selection using existing modeled ARM64
  operations, with unchanged selection lemma statements.
* A proved CFG-covering validator and two/four-phase candidates. This duplicates
  control flow while preserving operations and projected edges; it is not a
  general trip-count analysis or a proof of profitable loop unrolling.
* One integer constant cached in a fresh register, one independent adjacent
  operation swap, one adjacent identical-load forwarding, and one adjacent
  overwritten-store elimination per function. Constant selection caches its
  results and bounds the cycle-search hint to 32 literals and 128 work items
  per literal, then safely falls back to the first literal. Functions exceeding
  512 RTL instructions are retained to bound compilation cost. Their whole-program simulations
  cover calls and memory. No new general alias analysis or speculative load
  motion is introduced.
* Delayed specialization of an immutable-register comparison: its original
  first execution is retained, then subsequent executions use specialized CFG
  copies. This preserves zero-iteration behavior.
* Two additional rounds of existing constant propagation, CSE and dead-code
  cleanup. Analysis failure still returns a compiler error; this experiment
  does not claim a new proved rollback for those existing partial passes.

`test-experiments` exercises production extracted transformations, malformed
candidate refusal, real memory operations, defined C programs with separate
translation units, each independent option and combined profiles, and the
fixed public suite without timing series. `verify` additionally runs the
original native regression suite, ABI/PIC checks and the NEON comparisons.
The upstream suite is rebuilt and run with default options and both combined
scalar profiles. The GitHub `Verified correctness` workflow contains no speed
benchmark.
Initial performance-baseline capture still requires the unchanged compiler at
`befa8484ea29fe73a90785983541fb45745c26a0` on an idle Mac.

### NEON scope and trust

`aarch64/Neon.v` is an isolated integer-lane model and checked contiguous
vector/tail planner. Its five main model/planner results are closed proofs,
independently kernel-checked, and its extracted behavior is compared with
native NEON instructions over random and boundary inputs. It is not the
compiler's general vector backend.

With `COMPCERT_EXPERIMENTS=neon-packed`, three explicit C builtins are available:
`__builtin_cc_neon_add_u32x2`, `__builtin_cc_neon_sub_u32x2`, and
`__builtin_cc_neon_mul_u32x2`. Each takes two `unsigned long long` arguments
and returns the same type, holding two independent uint32 lanes. Their
numerical semantics are specified in `Builtins1.v`; floating-point scratch
register clobbers and four-instruction sizes are declared in the backend.
The existing `Pbuiltin` semantics carries them through the correctness proof.
The hand-written expansion into hardware NEON instructions is an additional
trusted platform specification/expansion surface, tested against scalar
references. These tests do not prove hardware equivalence.

`Asm.v` remains unchanged. General induction-variable optimization, general
LICM, fusion/interchange/tiling, automatic C-loop vectorization, 128-bit vector
state/ABI, and an Arm/Sail refinement remain unimplemented. The prototype
passes above do not constitute all optimizations found in a production
optimizing compiler. Promotion still requires correctness checks and reliable
measurements showing a smaller gap with clang `-O2`.

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
