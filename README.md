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
- an opt-in bridge back to dense `Multivector` values when reference comparisons or proof-oriented code matter more than runtime.

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

# Focused packed PGA3 transform benchmark.
lake exe packedmvbench all 200
lake exe packedmvbench pga-motor-point 5000
lake exe packedmvbench subtraction 250000
```

The subtraction benchmark compares the borrowed, one-buffer `MV.sub` kernel
with the old `MV.add a (MV.neg b)` composition over 32-coefficient CGA3 full
storage. The thresholded guard checks both an absolute ceiling and a minimum
speedup so an accidental return to the two-result path is visible.

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
