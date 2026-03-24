# Grassmann

Lean 4 experiments in geometric algebra, Clifford algebras, and numerics-oriented multivector representations.

This repository is no longer a Julia package mirror. The active codebase is a Lean 4 library centered on a fast `MV` representation for Float-heavy workloads, together with a proof-friendly dense `Multivector` type, PGA/CGA constructions, benchmark tooling, and a growing set of geometry and physics experiments.

## What is here

- Generic geometric algebra infrastructure over arbitrary signatures.
- A `DataArray`-backed `MV sig p` type with parity tracking for fast numeric kernels.
- A dense `Multivector sig F` type that is easier to reason about in proofs.
- Precomputed sign tables and specialized even-grade kernels for common signatures.
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
- a clean bridge back to dense `Multivector` values when proofs or generic code matter more than runtime.

## Repository layout

- `Grassmann4/Grassmann.lean`: root import for the public library surface.
- `Grassmann4/Grassmann/MV.lean`: unified numeric multivector representation.
- `Grassmann4/Grassmann/Multivector.lean`: dense proof-friendly representation.
- `Grassmann4/Grassmann/EvenMV.lean`: precomputed kernels and sign tables.
- `Grassmann4/Grassmann/PGA.lean`: projective geometric algebra.
- `Grassmann4/Grassmann/CGA.lean`: conformal geometric algebra.
- `Grassmann4/Grassmann/Theorems.lean`: algebraic properties and lemmas.
- `Grassmann4/Grassmann/AnchorTheorems.lean`: important identities, still incomplete.
- `Grassmann4/Grassmann/Bench.lean`: benchmark executable comparing `MV` and dense `Multivector`.
- `Grassmann4/Grassmann/CurveShortening.lean`: discrete geometric flow example using GA primitives.
- `Grassmann4/Grassmann/MetalCodegen.lean`: Metal shader generation experiments.

## Prerequisites

The root `lakefile.toml` currently uses local path dependencies. Before building, make sure the referenced repositories exist locally or adjust the paths to match your machine:

- `mathlib`
- `SciLean`
- `LeanPlot`

At the moment the repo is set up more like an active research workspace than a portable, polished package. Expect to edit dependency paths when moving between machines.

One current rough edge: on this checkout, a full root `lake build` can fail inside a transitive Verso/SubVerso dependency (`missing data file for module SubVerso.Highlighting.Messages`) before it reaches the Grassmann targets.

## Build and run

From the repository root:

```bash
lake build
lake build Grassmann.Theorems
lake exe bench
lake exe oracletests
lake exe propertytests
lake exe curvedemo
lake exe genmetalshaders
lake exe genvectorfield
```

Useful entrypoints:

- `lake exe bench`: compares the fast `MV` kernels against the dense representation.
- `lake exe oracletests`: checks selected computations against the Grassmann.jl oracle.
- `lake exe propertytests`: runs property-based checks.
- `lake exe curvedemo`: runs the curve-shortening demo executable.

## Current status

This codebase is active and exploratory. A few important realities:

- The `MV` path is the intended representation for Float-heavy numerics.
- The dense `Multivector` path remains important for generic code and proofs.
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
- There is also a nested `Grassmann4/lakefile.toml` carrying related experimental build configuration; keep the two in sync if you evolve both.
- If you are trying to understand the intent of a subsystem quickly, `Grassmann4/CLAUDE.md` summarizes the architecture and current priorities.

## Why this exists

The goal is to make geometric algebra practical in Lean 4 across two very different modes of work:

- proof-oriented algebraic development,
- fast numeric experimentation on concrete signatures such as `R2`, `R3`, `PGA3`, and `CGA3`.

That tension between theorem-friendly structure and low-level performance is the main design constraint running through the project.
