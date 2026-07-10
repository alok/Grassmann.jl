# Grassmann

Lean 4 experiments in geometric algebra, Clifford algebras, and numerics-oriented multivector representations.

This repository is no longer a Julia package mirror. The active codebase is a Lean 4 library centered on a fast `MV` representation for Float-heavy workloads, together with a proof-friendly dense `Multivector` type, PGA/CGA constructions, benchmark tooling, and a growing set of geometry and physics experiments.

The repository root is the authoritative Lake workspace. It pins Lean
`v4.27.0-rc1` and mathlib commit
`32d24245c7a12ded17325299fd41d412022cd3fe`; normal builds do not require any
local path dependencies.

## What is here

- Generic geometric algebra infrastructure over arbitrary signatures.
- A `DataArray`-backed `MV sig p` type with parity tracking for fast numeric kernels.
- A dense `Multivector sig F` type that is easier to reason about in proofs.
- A proof-free packed runtime with precomputed sign tables and specialized even-grade kernels for common signatures.
- Projective and conformal geometric algebra modules (`PGA`, `CGA`, `CGAGen`).
- Experiments in curve-shortening flow, visualization, Metal shader generation, and related geometry pipelines.

## Core ideas

The main numeric representation is:

```lean
inductive Parity where
  | even
  | odd
  | full

structure MV (sig : Signature n) (p : Parity) where
  coeffs : DataArray
```

This gives the project a single Float-oriented multivector type with:

- packed storage for even and odd subalgebras,
- parity-aware multiplication,
- direct-dispatch fast paths for common signatures,
- borrowed, single-result-buffer `add`, `sub`, `neg`, and Float scalar kernels,
- borrowed reverse and Clifford-conjugation kernels, plus parity-specialized
  grade involution that returns even inputs and negates odd inputs directly,
- a borrowed, one-buffer full-storage Hodge dual with a compact orientation
  bit stream through dimension 6 and a direct parity fallback above it,
- standard `Zero`, `Inhabited`, and `SMul Float` interfaces for every parity,
  plus `One` for even and full storage only,
- an opt-in bridge back to dense `Multivector` values when reference comparisons or proof-oriented code matter more than runtime.

Odd storage deliberately has no `One` instance because it cannot represent the
scalar blade. Float-backed `MV` exposes executable operations and notation, not
law-bearing ring or module instances.

### Packed runtime and dense reference layers

The default root is the supported proof-free runtime; dense/reference work is
explicitly opt-in:

```lean
-- Packed Float runtime, foundational types, and packed PGA3 API. This import
-- graph does not reach Grassmann.Proof or the project-specific placeholder
-- axioms.
import Grassmann

-- Broad dense/reference API, including MVDense conversions and coercions.
import Grassmann.Reference

-- Canonical-dependency-only development aggregate: Reference plus the broad
-- compile-time validation suites. Application experiments remain opt-in.
import Grassmann.All
```

`Grassmann.SignTablesCore` contains the proof-free cached sign tables used by
`MV`; `Grassmann.SignTables` adds the dense `Multivector` integration. Import
`Grassmann.MVDense` directly when only packed/dense conversions are needed.

## Repository layout

- `Grassmann4/Grassmann.lean`: root import for the public library surface.
- `Grassmann4/Grassmann/MV.lean`: unified numeric multivector representation.
- `Grassmann4/Grassmann/MVDense.lean`: opt-in conversions between packed `MV`
  and dense `Multivector`.
- `Grassmann4/Grassmann/Multivector.lean`: dense proof-friendly representation.
- `Grassmann4/Grassmann/SignTablesCore.lean`: proof-free cached sign tables for
  the packed runtime.
- `Grassmann4/Grassmann/EvenKernelTables.lean`: shared packed even-grade kernel tables.
- `Grassmann4/Grassmann/PGA3Kernel.lean`: Init-only fixed PGA3 kernels shared by
  packed Lean callers and the C ABI.
- `Grassmann4/Grassmann/PGA3Packed.lean`: proof-free packed PGA3 constructors
  and rigid transformations.
- `Grassmann4/Grassmann/Reference.lean`: opt-in dense and extended API.
- `Grassmann4/Grassmann/All.lean`: broad Reference/test aggregate that stays
  within the canonical root dependency closure.
- `Grassmann4/Grassmann/EvenMV.lean`: deprecated packed-even compatibility
  representation; new code should use `MV sig .even`.
- `Grassmann4/Grassmann/PGA.lean`: projective geometric algebra.
- `Grassmann4/Grassmann/CGA.lean`: conformal geometric algebra.
- `Grassmann4/Grassmann/Theorems.lean`: algebraic properties and lemmas.
- `Grassmann4/Grassmann/AnchorTheorems.lean`: important identities, still incomplete.
- `Grassmann4/Grassmann/Bench.lean`: benchmark executable comparing `MV` and dense `Multivector`.
- `Grassmann4/Grassmann/CurveShortening.lean`: standalone discrete geometric-flow
  experiment; packed-`MV` integration is still application work in progress.
- `Grassmann4/Grassmann/MetalCodegen.lean`: Metal shader generation experiments.

## Prerequisites

Install [elan](https://github.com/leanprover/elan), then use the versions pinned
by the repository:

- Lean: `leanprover/lean4:v4.27.0-rc1` (from `lean-toolchain`)
- mathlib: `32d24245c7a12ded17325299fd41d412022cd3fe` (from the root
  `lakefile.toml` and `lake-manifest.json`)

Lake fetches the pinned mathlib dependency. The canonical root workspace has no
required local path dependencies; SciLean, LeanPlot, and LeviCivita checkouts are
not prerequisites for the supported build.

`Grassmann4/lakefile.toml` is a separate experimental, noncanonical workspace
with maintainer-local path dependencies. Do not use it for ordinary builds or
dependency resolution.

## Build and run

From the repository root:

```bash
lake update
lake build
lake build Grassmann.MV Grassmann.MVDense
lake build Grassmann.All
```

All commands in this README assume the repository root as the current directory.

`Grassmann.All` intentionally excludes application experiments and optional
dependency adapters. Build the in-repository curve experiment explicitly with
`lake build Grassmann.CurveShortening`. `Grassmann.CoffeeshopExamples` and
`Grassmann.LeanPlotDemo` require a separately compatible LeanPlot package
profile; LeanPlot is not a dependency of the canonical workspace.

### Correctness guards

```bash
# Full property suite, or focused packed-runtime gates.
lake exe propertytests
lake exe propertytests mv-dispatch
lake exe propertytests packed-reference
lake exe propertytests pga-point-cloud

# Exact kernel and fat-dot regressions.
lake exe fixedkerneltests
lake exe fatdottests
lake exe pga3kerneltests
```

The Julia oracle is optional and has additional Julia/Grassmann.jl setup:

```bash
lake exe oracletests
```

The launcher uses the current outer repository root and inherited Julia
environment. Set `GRASSMANN_REPO_ROOT`, `JULIA`, or `JULIA_DEPOT_PATH` when
invoking it from another directory or with a non-default Julia installation.

### Benchmark guards

```bash
# Correctness-only benchmark smoke test.
lake exe bench verify

# Thresholded local benchmark guards.
Grassmann4/scripts/bench_guard.sh
Grassmann4/scripts/packedmvbench_guard.sh

# Generated-C shape guard for packed linear kernels.
Grassmann4/scripts/packed_linear_codegen_guard.sh

# Focused packed PGA3 transform benchmark.
lake exe packedmvbench all 200
lake exe packedmvbench pga-motor-point 5000
lake exe packedmvbench subtraction 250000
lake exe packedmvbench linear-arithmetic 500000
lake exe packedmvbench unary-involutions 100000
lake exe packedmvbench hodge-dual 100000
```

The subtraction benchmark compares the borrowed, one-buffer `MV.sub` kernel
with `MV.add a (MV.neg b)` over 32-coefficient CGA3 full storage. Both component
kernels are now optimized, but direct subtraction still saves a traversal and
one result buffer. The linear-arithmetic mode compares the one-buffer add,
negation, and scalar kernels with their former boxed `Array.range`/`Array.map`
shape. The unary-involutions mode does the same for full/even/odd reverse,
grade involution, and Clifford conjugation. The thresholded guard checks
absolute ceilings and relative speedups. The Hodge mode compares the one-buffer
full-storage kernel with its former boxed complement/map implementation over all
32 CGA3 coefficients.

`packed_linear_codegen_guard.sh` complements timing with a compiler-structural
gate. It checks the exact non-boxed generated-C bodies for one final
`FloatArray`, borrowed inputs, direct unboxed Float operations, one push per
coefficient, and a tail jump, while excluding legitimate typeclass dictionary
closures and boxed ABI adapters. It also pins the unary loops and verifies that
even involution retains and returns its input while odd involution allocates one
negation result. The Hodge checks pin the unboxed `UInt64` orientation selector,
the dimension <= 6 and fallback tail loops, and the single public result buffer.

The guard thresholds are intentionally conservative but still depend on the
host and build state; use their environment-variable overrides when establishing
a baseline for a different machine.

The 2026-07-09 port acceptance run passed with zero rotor, sandwich, and PGA3
point-transform drift. It measured `122.529580 ns/iter` for packed rotor
composition versus `38096.199170 ns/iter` dense (`310.9x`), `99.087500 ns/iter`
for packed sandwich transforms versus `114705.108330 ns/iter` dense (`1157.6x`),
`438.934170 ns/iter` for packed PGA3 motor multiplication, and
`4340.383400 ns/iter` for packed PGA3 motor-point transforms versus
`412131.550000 ns/iter` dense (`95.0x`).

The 2026-07-09 packed-linear acceptance run measured `93.865084 ns/iter` for
addition versus `339.517418 ns/iter` boxed (`3.617x`), `84.626166 ns/iter` for
negation versus `299.504500 ns/iter` boxed (`3.539x`), and
`84.537666 ns/iter` for scalar multiplication versus `294.006500 ns/iter`
boxed (`3.478x`). Direct subtraction measured `91.165830 ns/iter` versus
`161.609580 ns/iter` for the optimized two-buffer composition (`1.773x`). All
linear preflight comparisons had zero L1 drift, and the generated-C shape guard
passed all four operations with an unboxed `double` scalar ABI.

The 2026-07-09 packed-unary acceptance run also had zero L1 drift across every
CGA3 full/even/odd reverse, grade-involution, and Clifford-conjugation result.
Direct full kernels measured `327.273750`–`395.760000 ns/iter`, parity reverse
and conjugation measured `204.964580`–`216.921250 ns/iter`, even involution
returned its input in `20.438340 ns/iter`, and odd involution used direct
negation in `51.632500 ns/iter`. Compared with the retained boxed shapes, the
nine speedups ranged from `33.439x` to `351.206x`. The generated-C guard passed
all five unary helper loops and all three public involution branches.

The 2026-07-09 packed-Hodge acceptance run had zero L1 drift over all 32 CGA3
coefficients. The one-buffer kernel measured `79.200830 ns/iter` versus
`27113.287500 ns/iter` for the retained boxed shape (`342.336x`). Dimensions
0--6 use a signature-independent orientation bit stream; dimensions 7 and
above use the direct parity fallback. This is the exterior left complement,
not a metric pseudoscalar inverse, so degenerate PGA null blades remain
nonzero. The generated-C guard passed both loops and the public dispatch.

Other useful entrypoints:

- `lake exe jlexamples`: generates the Lean ports of selected Julia examples.
- `lake exe genmetalshaders`: runs the Metal shader generator.
- `lake exe genvectorfield`: runs the vector-field generator.

### Native C ABI

The versioned PGA3 ABI exposes caller-owned fixed `double` buffers; no Lean
heap layout appears in the public header. Build the shared library and run its
C/C++ header, runtime, pthread, layout, transform, ownership-stress, and symbol
checks with:

```bash
Grassmann4/scripts/cabi_smoke.sh
```

The generated library is under `.lake/build/cabi/`. Call
`grassmann_initialize_v1` once on the integration thread before use. Foreign
worker threads must pair `grassmann_thread_initialize_v1` with
`grassmann_thread_finalize_v1`; the process-global Lean runtime intentionally
has no public shutdown call. See `Grassmann4/include/grassmann/cabi.h` for the
version, status codes, packed mask layouts, and complete API.

The 2026-07-09 ABI acceptance run passed the C and C++ header probes, public
symbol audit, foreign-thread call, layout checks, and 100,000-iteration
ownership stress. The informational boundary timings were `14.2 ns/call` for
construction/result copies and `18.8 ns/call` for packed input/extract/result
copies.

## Current status

This codebase is active and exploratory. A few important realities:

- The proof-free `import Grassmann` / `MV` path is the intended representation
  for Float-heavy numerics.
- Dense interoperability is opt-in through `Grassmann.MVDense`; the dense
  `Multivector` path remains important for reference checks, generic code, and
  proofs.
- Some theorem files still contain `sorry` placeholders, especially in `AnchorTheorems.lean`.
- There are multiple experimental branches in-tree, including geometry processing, GPU codegen, and engine integration work.

## Near-term priorities

- Fill the remaining algebraic proof holes in `AnchorTheorems.lean`.
- Expand property tests comparing `MV` against dense `Multivector`.
- Keep benchmarking the direct-dispatch kernels and sandwich products.
- Continue stabilizing geometry and physics experiments built on top of PGA/CGA.

## Notes for contributors

- Lean sources live under `Grassmann4/`.
- The root `lakefile.toml` is the main build entrypoint for this checkout.
- The nested `Grassmann4/lakefile.toml` is experimental and noncanonical; it
  contains local path dependencies and is not part of the supported root build
  contract.
- If you are trying to understand the intent of a subsystem quickly, `Grassmann4/CLAUDE.md` summarizes the architecture and current priorities.

## Why this exists

The goal is to make geometric algebra practical in Lean 4 across two very different modes of work:

- proof-oriented algebraic development,
- fast numeric experimentation on concrete signatures such as `R2`, `R3`, `PGA3`, and `CGA3`.

That tension between theorem-friendly structure and low-level performance is the main design constraint running through the project.
