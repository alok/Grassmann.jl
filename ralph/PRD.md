# Grassmann4 Lean 4 Port Completion

## Objective

Turn the existing Grassmann4 experiment into a dependable, performance-conscious
Lean 4 geometric-algebra library that is useful on its own and through native
bindings. The Julia package remains the behavioral oracle where APIs overlap.

This work continues Linear issue ALOK-749. The outer repository at
`/Users/alokbeniwal/Grassmann` is authoritative; the nested `Grassmann4/.git`
metadata is stale and must not be used for commits.

## Product principles

- Preserve the dense, generic `Multivector` representation as the readable
  reference/proof model.
- Preserve `MV sig p` as the primary Float hot-path representation, with packed
  even/odd storage and direct specialization for common signatures.
- Prefer correct, reusable core algebra over demos or engine-specific glue.
- Keep experimental physics, Metal, Unreal, SciLean-AD, and optimization work
  optional unless it is fully wired and tested.
- Never replace a correctness gap with a placeholder formula, custom axiom, or
  untested FFI declaration.
- Treat existing uncommitted files as in-progress user work: integrate, repair,
  or leave intact; do not discard them.

## Required outcomes

### 1. Canonical build

- A clean, documented command from the outer repository builds the supported
  Grassmann library on the pinned Lean toolchain.
- Root and nested Lake metadata no longer give contradictory instructions for
  the supported build.
- The public root import excludes broken or incomplete application experiments.
- Any supported optional target also builds via an explicit Lake target.

### 2. Core correctness and port parity

- The focused property gates pass for packed/dense equivalence, sparse and
  truncated representations, conversions, stress anchors, and dispatch.
- The Julia oracle suite passes wherever Julia is available; unavailable oracle
  dependencies are reported explicitly rather than silently skipped.
- Basic constructors, products, contractions, involutions, grade projections,
  and R3/PGA3/CGA3 signature behavior have executable regression coverage.
- Newly found port bugs are fixed in the smallest correct layer and covered by
  a test that would have caught them.

### 3. Native bindings

- Replace the current simplified PGA motor implementation with bindings that
  delegate to the same packed `MV PGA3` kernels used by Lean callers.
- Expose an explicit C ABI with stable symbol names and a version query.
- Do not expose Lean heap-object layout as the primary consumer API. Prefer
  caller-owned scalar/out-buffer entry points with explicit lengths/status.
- Provide runtime initialization/shutdown guidance and a C smoke test that
  builds, links, initializes Lean in the required order, calls representative
  point/motor operations, checks results, and exits cleanly.
- Keep the C/C++ header synchronized with the exported functions.

### 4. Performance

- Existing correctness/performance guards pass, or thresholds are changed only
  with measured and documented justification.
- Packed rotor composition, sandwich transforms, and PGA3 motor/point paths do
  not regress materially from the recorded baseline.
- Benchmark the native ABI separately enough to detect marshaling/allocation
  overhead.
- Hot loops use packed/unboxed storage and monomorphic Float/UInt operations;
  avoid boxed `List Float`, generic typeclass dispatch, and avoidable allocation.

### 5. Soundness and supported surface

- The supported runtime import must not depend on `sorryDataAxiom` or other data
  placeholders.
- Custom proof axioms and unfinished theorem modules must be either discharged
  in the supported scope or clearly isolated as opt-in experimental proof work.
- No theorem is strengthened or retained when executable counterexamples show
  it is false; document deferred proof work honestly.

### 6. Delivery

- Changes are split into atomic commits on `codex/alok-749-lean4-port`.
- README/build/bindings documentation matches commands verified in this run.
- ALOK-749 receives a concrete status update with commands, measured results,
  commits, and any explicitly deferred non-core work.

## Verification commands

The exact target names may be repaired during the loop, but completion requires
equivalents of:

```bash
lake build
lake exe propertytests packed-reference
lake exe propertytests sparse-reference
lake exe propertytests truncated-reference
lake exe propertytests repr
lake exe propertytests stress
lake exe propertytests mv-dispatch
lake exe oracletests
Grassmann4/scripts/bench_guard.sh
Grassmann4/scripts/packedmvbench_guard.sh
```

Plus the native binding build/link/run smoke test added by this work.

## Completion rule

Only emit `<promise>COMPLETE</promise>` after every required outcome above is
verified in the current working tree, all intended changes are committed, and
`git status --short` contains no unexplained port-related work.
