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

## Continuation: ALOK-762 PGA3 ABI v1.1

The core port milestone above is complete. The active continuation improves the
same supported runtime and native boundary without widening the proof/reference
surface.

### Required outcomes

- Fuse the fixed PGA3 even-odd-even motor sandwich into one allocation and
  independently compare it with the existing composed kernels over every basis
  pair and mixed coefficients.
- Route public packed odd sandwiches through the fused kernel while preserving
  the generic fallback for every other signature/parity.
- Provide checked rigid-motor unit, normalization, and inverse operations based
  on the quaternion norm and Study condition; reject null and Study-invalid
  inputs rather than silently treating reverse as an inverse.
- Transform flat contiguous XYZ point clouds in one shared-kernel call and one
  caller-owned C ABI call, including empty, in-place, overflow, foreign-thread,
  and ownership-stress behavior.
- Release the additions as ABI v1.1 while retaining the `_v1` major symbol
  family and keeping Lean objects out of the public header.
- Beat the measured 4326.7375 ns/point packed baseline by at least 3x and keep
  the public path below 1500 ns/point on this machine. Batch transforms over at
  least 4096 points must be at least 3x faster per point than repeated scalar
  make/apply/extract calls measured in the same process.
- Re-run the canonical build, reference build, kernel/property/Julia oracle
  checks, C ABI smoke, and both performance guards before completion.

### Continuation completion rule

Only emit a new `<promise>COMPLETE</promise>` after ALOK-762 is verified,
documented, committed atomically, and updated in Linear with exact results.

## Continuation: ALOK-763 Reference axiom firewall

The native runtime and ABI milestone is complete. The active continuation makes
the opt-in dense/reference implementation computationally honest: IEEE-754
operations may execute, but they must not be packaged as exact ring or field
laws.

### Required outcomes

- Introduce a lawless coefficient-operations capability containing only the
  executable operations used by multivector kernels, including the literal
  `2` required by generic translator and conformal formulas.
- Weaken dense, sparse, truncated, representation, and supporting algorithms
  from `Ring F` only where no ring law is consumed. `GAlgebra` is an
  operations-only interface and must remain available for Float; keep actual
  theorem and law-bearing APIs constrained by genuine algebraic structures.
- Make `import Grassmann.Reference` independent of `Grassmann.Proof`,
  `sorryProofAxiom`, `sorryDataAxiom`, and the fake Float `Ring`/`Field`
  instances.
- Move the five unproved and underspecified representation-conversion theorem
  drafts behind an explicit theorem/proof import.
- Add compile-time negative checks that `Ring Float` and `Field Float` cannot be
  synthesized after importing Reference, plus executable Float
  non-associativity and exact-ring compatibility regressions.
- Re-run the canonical/reference builds, every focused property mode, Julia
  oracle, fixed kernels, ABI smoke, and performance guards.

### Continuation completion rule

Only emit a new `<promise>COMPLETE</promise>` after ALOK-763 is axiom-firewalled,
fully verified, committed atomically, and updated in Linear with exact results.

## Continuation: ALOK-765 packed subtraction and broad import

The Reference firewall is complete. The active continuation closes a basic
packed arithmetic omission exposed by the curve-shortening port and makes the
broad dependency-free aggregation build honestly.

### Required outcomes

- Add parity-preserving `MV.sub` and standard subtraction notation using one
  coefficient traversal and one final native result buffer, not an allocated
  negation followed by addition.
- Independently cover even, odd, and full packed layouts across representative
  dimensions/signatures, including direct and typeclass dispatch and dense
  agreement.
- Prove the API repair against Alok's dirty CurveShortening rewrite without
  staging or absorbing that experiment.
- Make `Grassmann.All` aggregate the broad dependency-free Reference and
  validation surface while leaving CurveShortening and LeanPlot-bound
  application modules as explicit opt-in imports.
- Keep a thresholded CGA3 full-storage subtraction benchmark so future changes
  cannot silently restore the two-result add-neg path.
- Re-run canonical, Reference, CurveShortening, All, packed/property, fixed
  kernel, and performance gates.

### Continuation completion rule

Only emit a new `<promise>COMPLETE</promise>` after ALOK-765 is implemented,
fully verified, committed atomically, and updated in Linear with exact results.

## Continuation: ALOK-766 packed linear arithmetic

Packed subtraction and the canonical broad aggregate are complete. The active
continuation removes the same boxed-array overhead from the remaining basic
linear kernels and fills their standard Lean runtime interfaces.

### Required outcomes

- Rewrite packed addition, negation, and Float scalar multiplication as
  borrowed-input, monomorphic, single-buffer tail loops with no boxed
  coefficient arrays or per-element closure/control allocation.
- Provide `Zero`, `SMul Float`, and `Inhabited` uniformly across parity tags.
  Provide `One` only for even and full storage; odd storage cannot represent a
  scalar identity and must continue to reject that instance.
- Cover named functions and notation, exact layouts, dense agreement, buffer
  invariants, positive instances, and the negative odd-identity boundary.
- Add stable CGA3 full-storage benchmark and guard coverage for all three
  rewritten kernels, including comparisons against the previous boxed shape.
- Re-run canonical, Reference, All, dirty CurveShortening, full property,
  generated-code, kernel, native-binding, and performance acceptance.

### Continuation completion rule

Only emit a new `<promise>COMPLETE</promise>` after ALOK-766 is implemented,
fully verified, committed atomically, and updated in Linear with exact results.

## Continuation: ALOK-767 packed unary kernels

Basic packed linear arithmetic is complete. The active continuation removes
boxed-array overhead from reverse and the remaining unary involutions, and
eliminates unnecessary parity-index decoding from valid full-storage loops.

### Required outcomes

- Make valid full-storage packed-index decoding the identity operation and pin
  its exact in-range behavior.
- Rewrite reverse, involute, and conjugate as borrowed-input native kernels with
  no boxed coefficient arrays or per-element callback/control allocation.
- Use exact parity fast paths: even involution returns the immutable input and
  odd involution delegates to the optimized negation kernel.
- Strengthen packed reference checks with buffer invariants and deterministic
  all-slot full/even/odd unary fixtures, including the R2 odd curve layout.
- Add stable CGA3 full/even/odd unary benchmarks and scoped generated-C guards.
- Re-run canonical, Reference, All, dirty CurveShortening, packed/full property,
  kernel, C ABI, and performance acceptance.

### Continuation completion rule

Only emit a new `<promise>COMPLETE</promise>` after ALOK-767 is implemented,
fully verified, committed atomically, and updated in Linear with exact results.

## Continuation: ALOK-768 packed Hodge dual

Packed index decoding and unary involutions are complete. The active
continuation removes the largest remaining boxed unary bottleneck from the
full-storage runtime.

### Required outcomes

- Rewrite full-storage `MV.hodgeDual` as a borrowed, monomorphic, one-result-
  buffer loop with no boxed coefficient arrays, range/map callbacks, or copy
  pass.
- Use a precomputed signature-independent orientation bitmask for dimensions
  whose full sign sequence fits in `UInt64`, plus a correct allocation-tight
  permutation-parity fallback above that boundary. Preserve the current
  left-complement semantics, including nonzero complements in degenerate PGA3.
- Keep the operation full-storage-only: odd-dimensional Hodge changes parity,
  so no invalid same-parity packed API may be introduced.
- Add deterministic all-slot coverage, explicit standard-signature and
  degenerate PGA3 checks, buffer invariants, named randomized dense-reference
  coverage, and second-dual comparison with the independent dense result.
- Add a stable CGA3 boxed-vs-direct benchmark and scoped generated-C guard.
- Re-run canonical, Reference, All, dirty CurveShortening, packed/full property,
  kernel, C ABI, and performance acceptance.

### Continuation completion rule

Only emit a new `<promise>COMPLETE</promise>` after ALOK-768 is implemented,
fully verified, committed atomically, and updated in Linear with exact results.

### Completion

ALOK-768 is complete. Packed Hodge dual now uses one borrowed-input output loop,
a compact unboxed orientation stream through dimension 6, and a direct parity
fallback above that boundary. Exact all-slot, dispatch-boundary, PGA null-blade,
randomized dense-reference, benchmark, and generated-C gates are permanent.
Canonical and broad builds, the full property suite, fixed kernels, Julia
oracle, C ABI v1.1, and both performance guards passed. The final isolated CGA3
measurement was `77.165840 ns/iter` direct versus `26675.972920 ns/iter` boxed
(`345.697x`) with zero L1 drift.

<promise>COMPLETE</promise>
