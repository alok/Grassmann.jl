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
- `Multivector sig F` - Dense 2^n coefficient storage (proof-friendly)
- `MultivectorDA` / `EvenMVDA` - Float arrays for performance
- `GradedMVDA` - Compile-time grade tracking with sparse iteration
- `SignTable` - Precomputed sign tables for R2/R3/R4/STA/PGA3/CGA3
- `Spinor` / `Motor` - Packed even-grade representations

## TODO for Future Sessions

### High Priority
- [ ] Fill `sorry` proofs in `AnchorTheorems.lean` - these are the key algebraic identities
- [ ] Add benchmarks comparing `EvenMVDA` vs `EvenMV` vs dense `Multivector` for rotor operations
- [ ] Profile PGA motor transforms with `hwatch` to verify no unexpected allocations
- [ ] Add property tests for `EvenMV` packed operations against dense `Multivector`

### Medium Priority
- [ ] Fix style warning in `PGA.lean:492` (line exceeds 100 chars)
- [ ] Add `@[inline]` to remaining hot-path functions in `LinearAlgebra.lean`
- [ ] Consider adding `@[specialize]` to generic rotor functions for common signatures
- [ ] Explore SIMD opportunities via `FloatArray` batch operations
- [ ] Add `EvenMVDA`-backed versions of `Spinor` for full Float hot path

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

## Benchmark Baseline
From hyperfine (1M operations):
- Naive geometric product: ~37.8 µs/op
- Table geometric product: ~18.4 µs/op (2.05x speedup)

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
- `Multivector.lean` - Core dense representation
- `EvenMV.lean` / `EvenMVDA.lean` - Packed spinor storage
- `SignTables.lean` - Precomputed multiplication signs
- `GradedMVDA.lean` - Grade-tracked sparse kernels
- `PGA.lean` - Projective geometric algebra
- `Theorems.lean` - Algebraic properties (many with proofs)
- `AnchorTheorems.lean` - Key identities (mostly sorry)
