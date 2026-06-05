# Grassmann4 - Lean 4 Geometric Algebra Library

## Project Overview
A Lean 4 implementation of Clifford/Grassmann algebras with:
- Generic n-dimensional multivectors over any ring
- Precomputed sign tables for O(1) geometric products
- Grade-tracked sparse operations via `GradeSet`
- Packed even-grade storage (`EvenMV`) for spinors/rotors
- DataArray-backed Float kernels for numerics hot paths
- PGA (Projective GA) and CGA (Conformal GA) implementations

## Architecture Highlights
- `MV sig p` - **Primary type**: DataArray-backed multivector with parity tracking (.even/.odd/.full)
- `Multivector sig F` - Dense 2^n coefficient storage (proof-friendly, generic over F)
- `Spinor sig` - Float-only spinor wrapper around `MV sig .even`
- `EvenMV.Kernel` - Precomputed sign tables for R2/R3/R4/STA/PGA3/CGA3
- PGA types: `Motor`, `Point`, `Plane`, `Line` as type aliases for `MV PGA3 .even`/`.odd`

## TODO for Future Sessions

### High Priority
- [ ] **Revisit typeclass dispatch when Lean 4 inlining improves** - Currently `MVMulKernel` typeclass adds ~50% runtime overhead vs direct dispatch (`mulDirect`). Tried `@[inline]`, `@[always_inline]`, `@[specialize]`, `@[default_instance]`, and release mode builds. The elegant typeclass-based code is preserved but `instHMulMV` uses `mulDirect` for performance. Revisit when compiler improves.
- [ ] Fill `sorry` proofs in `AnchorTheorems.lean` - these are the key algebraic identities
- [ ] Profile PGA motor transforms with `hwatch` to verify no unexpected allocations
- [ ] Extend packed `MV` vs dense `Multivector` property tests when adding new operations or signatures

### Medium Priority
- [ ] Add `@[inline]` to remaining hot-path functions in `LinearAlgebra.lean`
- [ ] Consider adding `@[specialize]` to generic rotor functions for common signatures
- [ ] Explore SIMD opportunities via `FloatArray` batch operations

### Lower Priority
- [ ] Complete `RotorExp.lean` with proper bivector exponential (closed-form trig)
- [ ] Add Metal codegen for GPU-accelerated batch transforms
- [ ] Investigate SciLean integration for `DataArray` convergence
- [ ] Add Verso documentation for the library
- [ ] Create visual demos using LeanPlot

### Proof Work
- [ ] Prove `geometricProduct_assoc` (associativity of geometric product)
- [ ] Prove `reverse_mul` (reverse is anti-automorphism)
- [ ] Prove `wedge_assoc` (wedge product associativity)
- [ ] Fill `sorry_proof` holes in `involute_vector`, `involute_bivector`, `involute_pseudoscalar`
- [ ] Prove grade formulas for contractions

### Testing
- [ ] Run Grassmann.jl oracle tests via `lake exe oracletests`
- [ ] Run property tests via `lake exe propertytests`
- [ ] Benchmark with `lake exe bench` and compare to previous baselines
- [ ] Test PGA motor transforms on point clouds

## Recent Optimizations (Dec 2025)
- Added `@[inline]` to core `Multivector`, `Spinor`, `Versor` operations
- Added `@[simp]` lemmas for grade projection, even/odd parts, involutions
- Precomputed even-only sign tables for canonical signatures
- Grade-set-driven sparse products in `GradedMVDA`
- Output-restricted sandwich products (compute only needed grades)
- **Typeclass dispatch experiment**: Tried `MVMulKernel` typeclass for compile-time
  specialization, but it added ~100% overhead. Direct pattern matching is faster.
- **Final design**: MV uses direct dispatch with fast-path pattern matching:
  - For `even×even`: uses precomputed sign tables (R2, R3, R4, STA, PGA3, CGA3)
  - For other parities: falls back to generic kernel

## Benchmark Baseline (Dec 2025)
From `lake exe bench`:
- **MV rotor composition**: ~151ns/iter (vs ~30837ns for dense Multivector) - **204x faster**
- **MV sandwich product**: ~82ns/iter (vs ~90096ns for dense) - **1098x faster**
- **PGA3 motor composition**: ~739ns/iter

The unified MV type provides excellent performance with a clean API. Typeclass dispatch
experiments showed ~50% overhead that can't be eliminated with `@[inline]` etc., so MV
uses direct pattern matching for dispatch.

## Verified Coverage (Jun 2026)
- Packed `MV` dense-reference coverage is in `Grassmann.PropertyTests` and exposed
  through `lake exe propertytests packed-reference`; it checks R3, PGA3, and CGA3
  full/even/odd storage against dense `Multivector` for round-trips, projections,
  scalar products, multiplication, wedge, contractions, derived products,
  involutions, sandwiches, and `GAlgebra` helpers.
- Dispatch equivalence is exposed through `lake exe propertytests mv-dispatch`;
  it compares direct `mulDirect` against the preserved typeclass kernel path for
  R3, PGA3, and CGA3.
- Sparse `MultivectorS` dense-reference coverage is exposed through
  `lake exe propertytests sparse-reference`; it checks R3, PGA3, and CGA3
  sparse operations against dense `Multivector` for arithmetic, products,
  involutions, grade projections, grade-projector identities, and `GAlgebra`
  helpers.
- Representation conversion and truncated-storage coverage are exposed through
  `lake exe propertytests repr` and `lake exe propertytests truncated-reference`;
  these cover dense/sparse round-trips for R3/PGA3/CGA3 and grade-2 truncation
  against dense references.
- Exact higher-dimensional anchor checks are exposed through
  `lake exe propertytests stress`; they cover R4/R5 basis products, wedge,
  rotors, contractions, Hodge square signs, determinant/Hodge anchors,
  composition identities, and the R3 Hodge cross-product identity.
- `scripts/packedmvbench_guard.sh` provides the focused PGA3 motor-point
  correctness/performance guard.

## Build Commands
```bash
lake build                    # Full build
lake build Grassmann.Theorems # Single module
lake exe bench                # Run benchmarks
lake exe oracletests          # Julia oracle comparison
lake exe propertytests        # Property-based tests
```

## Key Files
- `Grassmann.lean` - Root import
- `MV.lean` - **Primary**: Unified multivector type `MV sig p` with parity tracking
- `Multivector.lean` - Dense representation (proof-friendly, generic over F)
- `Spinor.lean` - Float-only spinor wrapper around `MV sig .even`
- `EvenMV.lean` - Kernel sign tables for common signatures (used by MV)
- `SignTables.lean` - Precomputed multiplication signs
- `PGA.lean` - Projective geometric algebra with proof + Float APIs
- `VectorUtils.lean` / `R3Utils.lean` - Generic and 3D-specific utilities
- `Theorems.lean` - Algebraic properties (many with proofs)
- `AnchorTheorems.lean` - Key identities (mostly sorry)

## Unified MV Type (Dec 2025)

The `MV sig p` type is the primary representation for Float-based numerics:

```lean
inductive Parity where
  | even  -- grades 0, 2, 4, ...
  | odd   -- grades 1, 3, 5, ...
  | full  -- all grades

structure MV (sig : Signature n) (p : Parity) where
  coeffs : DataArray
```

**Key benefits:**
- Single unified type for all Float operations
- Automatic parity algebra: `even × even = even`, `even × odd = odd`, etc.
- Packed storage: `.even`/`.odd` use 2^(n-1) coefficients, `.full` uses 2^n
- Generic multiplication kernel works for ALL dimensions
- PGA types (Motor, Point, Plane, Line) as type aliases

**Migration Complete (Dec 2025):**
- Removed deprecated files: `MultivectorDA.lean`, `EvenMVDA.lean`, `GradedMVDA.lean`
- `Spinor` now wraps `MV sig .even` (Float-only)
- `Bench.lean` simplified to MV vs Multivector comparison only
- PGA.lean uses MV-backed types for Float operations, `PGA.Proof` namespace for proofs
