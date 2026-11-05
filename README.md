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

This branch is `experiment/wide-array-pairs`; it has not been promoted to `fast`.
No speed improvement is claimed. The full option list, combined profiles and
precise limits are in `perf/experiment-profiles.json`. For example:

```sh
COMPCERT_EXPERIMENTS=rtl-unroll2,memory-cleanup ./ccomp -stdlib runtime program.c
COMPCERT_EXPERIMENTS=memory-neon ./ccomp -stdlib runtime program.c
COMPCERT_EXPERIMENTS=loop-spill,trace-layout COMPCERT_EXPERIMENT_TRACE=/tmp/compcert-trace.jsonl ./ccomp -stdlib runtime program.c
make -f Makefile.fast test-experiments
make -f Makefile.fast test-loops
make -f Makefile.fast test-memory-loops
make -f Makefile.fast compare-assembly
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
* `licm-pure` eagerly caches a total, memory-independent nonconstant operation
  with immutable operands. `licm-preheader` also handles operands computed,
  loaded or returned by calls before a loop: original prefix effects retain
  their order. A checked closed-suffix fallback handles branching preheaders
  and caches at first actual use. This safely supports partial operations such
  as integer division and float-to-integer conversions without executing them
  on zero-trip paths. Each pass selects one expression in functions of at
  most 512 RTL instructions; candidate and reachability searches are bounded.
  Loads themselves and memory-dependent operations are not moved.
* `strength-reduce` tracks a 32-bit modular induction product in a fresh
  accumulator, replacing repeated multiplication with addition. Literal resets
  of the induction or factor maintain the accumulator; other mutations are
  rejected. The whole-program simulation covers all value tags and zero trips.
* `loop-peel` separates the initial traversal from a stable CFG copy after a
  postorder backedge. The compiler renumbers first; the existing CFG projection
  checker validates all operations and successors, with fallback on refusal.
  This is first-traversal peeling, not fusion, interchange or tiling.
* `auto-neon` recognizes adjacent uint32 add-immediate expressions sharing
  their input, automatically emits an existing packed NEON builtin and lowers
  its packing/unpacking through supported scalar ARM64 operations. The proof
  covers undefined/noninteger inputs and rejects unrelated lanes, whose
  different definedness cannot safely be packed by this representation.
  One pair is considered per function, with a 512-instruction size guard.
* Two additional rounds of existing constant propagation, CSE and dead-code
  cleanup. Analysis failure still returns a compiler error; this experiment
  does not claim a new proved rollback for those existing partial passes.
* `memory-vector` exposes the first two loop traversals using a proved CFG
  projection validator, performs existing cleanup and removes unreachable
  nodes, then widens correlated pairs of ordinary 32-bit stores to
  single 64-bit stores (at most one pair per widening rule per function).
  An executed global-address producer and checked
  transparent chain establish offsets zero/four; the indirect output retains
  native register addressing. Exact memory bytes are proved for every value
  tag. Ordinary C tests require the wide store in actual RTL and assembly,
  check surrounding cells and overlapping copies, and reject unsupported
  unrelated values, volatile accesses and arbitrary pointer bases. This is
  scalar memory widening across iterations, not general memory SIMD.
* `ArrayPair`, under `memory-neon`, handles ordinary in-place `uint32_t`
  updates by a constant. It recognizes `for (unsigned i=0; i<n; ++i) p[i]+=K`
  and the corresponding countdown `while` and pointer-increment `for` forms.
  The Clight proof uses the fact that a successful scalar addition has an
  integer operand. A pair uses two ordinary 32-bit loads, one packed NEON
  addition, and two 32-bit stores in source order. The second load can move
  before the first store because the addresses are disjoint. An odd last
  element uses the scalar addition. The proof covers variable 32-bit unsigned
  bounds and four-byte-aligned pointer arguments. The recognizer checks the
  complete function and its types. Tests check exact-length arrays, protected
  boundary pages, modular wraparound, and assembly against Clang `-O2`.
  A second form indexes a named global or static `uint32_t` array declared
  with `_Alignas(8)` or greater. Its index starts at zero and advances by two
  per pair. The declaration specifies the machine base alignment. Coq checks
  the offset within the block from the even index and proves that a single
  `Mint64` load and store produce the
  same result as the two scalar iterations. An odd final element still uses
  a 32-bit load and store. For pointer parameters, a retained source test
  `p == aligned_array` or `p == aligned_array + constant` supplies the
  alignment witness on its true branch. The constant must be a nonnegative,
  in-bounds even index. Both arms must contain the same supported indexed
  loop using a shared index variable. The false branch pairs with separate
  32-bit accesses, as does the ordinary unguarded pointer form.
  Tests check the widened load and store through the NEON result, alignment
  at page boundaries, and four-byte-only alignment on the fallback path.
* `AutoPair`, under `memory-neon`, forms pairs automatically from the scalar
  step-one loop `while(n){x=p[0];y=p[1];if((int)x<(int)y)p[0]=x+K;++p;--n;}`.
  It dispatches two iterations to one packed NEON addition and retains the
  original scalar loop for zero/one remaining iterations. Conditional writes
  and all scalar reads remain in their original order; the second arithmetic
  result is reused only after proving that the first store cannot change the
  adjacent cell, including wrapped pointer offsets. The source already reads
  `n+1` cells when `n>0`; the optimizer adds no array-length precondition.
  No intrinsic, manual source pairing or hand-written scalar tail is needed.
  This first recognizer checks the entire canonical ten-node RTL function,
  its two parameters, void signature and zero stack size; `K` is any constant.
  Matching `while` and pointer-increment `for` source forms are tested.
  The first target keeps both original pointer/count updates and the mid-pair
  count check. Its paired backedge consumes two scalar iterations; its cleanup
  can run at most once. Unrecognized scalar loops are retained.
* `memory-neon` also validates a local signed guard followed by two adjacent
  uint32 add-immediate operations. It packs their independent inputs, uses
  the existing packed uint32x2 NEON addition builtin and extracts both results.
  Its simulation covers arbitrary function signatures, parameters, registers,
  node labels, calls and loop counts. Ordinary C tests cover variable-length
  indexed and pointer-increment loops, source scalar tails, aliased output
  pointers, live result registers and pointers aligned only on four bytes.
  Every original load/store and its order is retained, including volatile
  accesses around the pure arithmetic window. No eight-byte alignment,
  no-alias or no-wrap assumption is added. One pair is selected per function
  with at most 512 RTL nodes, checked unique predecessors and conservative
  register constraints. Packing is lowered immediately by `LowerLong`.
  The signed guard and pair-shaped source loop must already exist; this pass
  does not automatically strip-mine arbitrary scalar loops or synthesize a
  scalar remainder. No intrinsic or manually packed C value is required.
  The previous canonical fixed global-loop path with wide load/store remains
  available after the local pass and its preparation.
* `loop-fusion` proposes interleaving two adjacent pure counted loops, with
  shared or separate counters. A reusable proved symbolic validator checks
  both whole functions: only total, memory-independent operations and known
  branches are executed, and their return expressions must match for all
  value tags. The budgets are 128 execution steps and 128 expression nodes.
  Failed validation retains the original function.
* `loop-interchange` rewires a rectangular pure loop nest, including the
  rotated form emitted for ordinary C. `loop-tile2d` constructs genuine
  2x2 tiles of a fixed 2x3 rectangle, including its partial final column.
  Both use the same symbolic validator and reject dependencies that change
  the result. Native checks assert the actual changed iteration order.
  Their current scope is small, fixed pure nests, without memory reordering.
* `loop-tile` inserts four-iteration tile boundaries while retaining the
  source exit test and exact effect order on every iteration. Its simulation
  covers memory, calls and faults, including tails and counter wrap. This
  order-preserving strip-mining foundation adds control overhead and makes
  no locality or profitability claim.

`test-experiments` exercises production extracted transformations, malformed
candidate refusal, real memory operations, defined C programs with separate
translation units, each independent option and combined profiles, and the
fixed public suite without timing series. `verify` additionally runs the
original native regression suite, ABI/PIC checks and the NEON comparisons.
The upstream suite is rebuilt and run with default options and all combined
profiles, including `memory-loops`. The GitHub `Verified correctness` workflow contains no speed
benchmark.
Initial performance-baseline capture still requires the unchanged compiler at
`befa8484ea29fe73a90785983541fb45745c26a0` on an idle Mac.

`compare-assembly` compiles the same ordinary C functions with baseline
CompCert, the `loops4` profile and clang `-O2`, using macOS ARM64 and disabled
inlining in both compilers. It records assembly and static instruction,
load/store, branch/call, register and packed-lane counts in a JSON report.
No generated program is executed. These observations guide future proved
transformations; instruction-site counts are not speed measurements or
profitability evidence. Custom source units/functions/profiles are supported
by `python3 perf/compare_assembly.py --help`.
It also compares the new ordinary-C memory/fusion/rectangle fixtures against
clang with each new option independently, archiving assembly and static
metrics in `perf/results/memory-assembly.json`. Reproduce that portion with
`python3 perf/compare_memory_loops.py`.

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

`Asm.v` and the packed builtin specifications/expansions are unchanged by the
new automatic vectorizer. Its RTL vectorization and mandatory scalar packing
lowering each have a whole-program correctness proof. Native tests inspect
NEON inside both ordinary C functions and ordinary C loops; source intrinsics
are not required. This is correlated-lane SLP, not general vector loads/stores
or vectorization across loop iterations.

The fixed-global `MemoryNeon` path handles two independent memory lanes under
the source's existing signed guard. Four exact byte-level lemmas establish
wide reads/writes from explicit integer and alignment witnesses. The whole
function simulation delays target execution while the finite source region
executes, then replays the target from the same initial memory. This covers
partial undefined lanes and memory faults without assuming them away.
The existing `Asm.v`, value/memory model, builtin specification and hardware
expansion are unchanged from `7bb08b94`; the new checker verifies those Git
hashes. The pre-existing hardware expansion remains trusted as described
above. Tests require actual NEON arithmetic plus 64-bit memory operations,
compare independent random/boundary lanes and sentinel bytes, and compare
ordinary C outputs with clang. There is no general alias analysis, arbitrary
trip-count vectorization or scalar-remainder construction in this pass.

`PointerNeon` supplies the local path under the same `memory-neon` option.
Its ready/intermediate-state simulation handles the guarded arithmetic window
inside arbitrary surrounding control flow, so the proof needs no fixed trip
count or whole-function template. The source guard proves both values are
integers; the target restores every original live register before the
following memory instructions. Scalar 32-bit memory accesses keep their
original addresses and order, allowing four-byte-aligned pointer inputs and
aliasing without widening memory accesses. Existing loop controls and odd
scalar tails stay intact. Its tests check source, transformed and lowered
execution, memory access order, memory bytes, live registers and fault paths.

`AutoPair` adds the automatic paired-loop path for the scalar lookahead
pattern above. Its complete positive-step simulation preserves original
registers, memory and memory-access order at each matched source instruction.
Tests compare both the production transform and `LowerLong`, including exact
fault prefixes, wraparound data/pointers, partial write permissions, and a
true/true pair with two scalar data additions replaced by one NEON addition.
The source's signed data guards remain necessary. Other step-one loops and
more general dependence analysis remain outside this initial recognizer.

Alias-dependent memory LICM, general nested-region invariant motion,
fusion/interchange/tiling of dynamic or memory-dependent nests, general
cross-iteration memory-loop vectorization with
remainder handling, 128-bit vector state/ABI and Arm/Sail refinement remain
unimplemented. The prototype
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
