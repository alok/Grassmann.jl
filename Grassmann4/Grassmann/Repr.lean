/-
  Grassmann/Repr.lean - Unified Multivector Representation Typeclass

  This module defines a typeclass that abstracts over different multivector
  representations (Dense, Sparse, Truncated) allowing generic algorithms.

  Design Goals:
  - Write algorithms once, work with any representation
  - Automatic selection of optimal representation
  - Conversion between representations
  - Representation-specific optimizations via typeclass instances
-/
import Grassmann.Multivector
import Grassmann.SparseMultivector
import Grassmann.TruncatedMV
import Grassmann.Proof

open Grassmann.Proof

namespace Grassmann

/-! ## MultivectorRepr Typeclass

The core abstraction for multivector representations.
Each representation must provide coefficient access and products.
-/

/-- Typeclass for multivector representations over signature `sig` and scalar `F`.
    Different representations (Dense, Sparse, Truncated) implement this interface. -/
class MultivectorRepr (M : Type*) (sig : Signature n) (F : Type*) where
  /-- Get coefficient for blade at given index -/
  coeff : M → ℕ → F

  /-- Get scalar part (grade 0, index 0) -/
  scalarPart : M → F

  /-- Zero multivector -/
  zero : M

  /-- Scalar multivector -/
  scalar : F → M

  /-- One (scalar 1) -/
  one : M

  /-- Add two multivectors -/
  add : M → M → M

  /-- Negate -/
  neg : M → M

  /-- Scale by scalar -/
  smul : F → M → M

  /-- Geometric product -/
  mul : M → M → M

  /-- Reverse involution -/
  reverse : M → M

variable {n : ℕ} {sig : Signature n} {F : Type*}

/-! ## Dense Representation Instance -/

instance [Ring F] : MultivectorRepr (Multivector sig F) sig F where
  coeff m idx :=
    if h : idx < 2^n then m.coeffs ⟨idx, h⟩ else 0
  scalarPart := Multivector.scalarPart
  zero := Multivector.zero
  scalar := Multivector.scalar
  one := Multivector.one
  add := Multivector.add
  neg := Multivector.neg
  smul x m := Multivector.smul x m
  mul := Multivector.geometricProduct
  reverse := Multivector.reverse

/-! ## Sparse Representation Instance -/

instance [Ring F] [BEq F] [DecidableEq F] : MultivectorRepr (MultivectorS sig F) sig F where
  coeff := MultivectorS.coeff
  scalarPart := MultivectorS.scalarPart
  zero := MultivectorS.zero
  scalar := MultivectorS.scalar
  one := MultivectorS.one
  add := MultivectorS.add
  neg := MultivectorS.neg
  smul := MultivectorS.smul
  mul := MultivectorS.geometricProduct
  reverse := MultivectorS.reverse

/-! ## Truncated Representation Instance -/

instance [Ring F] [BEq F] [DecidableEq F] {maxGrade : ℕ} :
    MultivectorRepr (TruncatedMV sig maxGrade F) sig F where
  coeff := TruncatedMV.coeff
  scalarPart := TruncatedMV.scalarPart
  zero := TruncatedMV.zero
  scalar := TruncatedMV.scalar
  one := TruncatedMV.one
  add := TruncatedMV.add
  neg := TruncatedMV.neg
  smul := TruncatedMV.smul
  mul := TruncatedMV.geometricProduct
  reverse := TruncatedMV.reverse

/-! ## Generic Operations

The MultivectorRepr typeclass enables writing generic algorithms.

### Known Limitation: Typeclass Inference with Dependent Types

Due to Lean 4's typeclass inference behavior with dependent types like `Signature n`,
generic functions over `MultivectorRepr` often fail to infer instances automatically.

**Problem Example:**
```lean
-- This won't compile: Lean can't infer the MultivectorRepr instance
def genericNormSq [MultivectorRepr M sig F] (m : M) : F :=
  MultivectorRepr.scalarPart (MultivectorRepr.mul m (MultivectorRepr.reverse m))
```

**Workaround Patterns:**

1. **Explicit Instance Passing**: Add `@` and pass instance explicitly
```lean
def normSq {M : Type*} (inst : MultivectorRepr M sig F) (m : M) : F :=
  @MultivectorRepr.scalarPart _ _ _ _ inst
    (@MultivectorRepr.mul _ _ _ _ inst m (@MultivectorRepr.reverse _ _ _ _ inst m))
```

2. **Representation-Specific Functions**: Write specialized versions (current approach)
```lean
-- Use these directly instead of generic:
Multivector.normSq    -- for Dense
MultivectorS.normSq   -- for Sparse
TruncatedMV.normSq    -- for Truncated
```

3. **Local Instance Hints**: Use `haveI` for scoped inference
```lean
def foo (m : Multivector sig F) : F :=
  haveI : MultivectorRepr (Multivector sig F) sig F := inferInstance
  MultivectorRepr.scalarPart m
```

**Current Recommendation:**
Until Lean's typeclass resolution improves for dependent types,
use representation-specific operations directly:
- `Multivector.*`, `MultivectorS.*`, `TruncatedMV.*`

The typeclass infrastructure is in place for future generic algorithms
and documents the shared interface between representations.
-/

/-! ## Representation Selection

Utilities for choosing optimal representation based on dimension and density.
-/

/-- Representation recommendation based on dimension n -/
inductive ReprChoice where
  | dense     -- n ≤ 8, use full 2^n array
  | sparse    -- n > 8, use TreeMap
  | truncated -- n >> 8, use truncated grades
  deriving Repr, BEq

/-- Choose representation based on dimension -/
def chooseRepr (n : ℕ) (_maxNnz : ℕ := 1000) : ReprChoice :=
  if n ≤ 8 then .dense
  else if n ≤ 16 then .sparse
  else .truncated

/-! ## Conversion Between Representations -/

/-- Convert Dense to Sparse -/
def denseToSparse [Ring F] [BEq F] (m : Multivector sig F) : MultivectorS sig F :=
  let indices := List.finRange (2^n)
  indices.foldl (init := MultivectorS.zero) fun acc i =>
    let c := m.coeffs i
    if c == 0 then acc
    else ⟨acc.coeffs.insert i.val c⟩

/-- Convert Sparse to Dense -/
def sparseToDense [Ring F] (m : MultivectorS sig F) : Multivector sig F :=
  ⟨fun i => m.coeff i.val⟩

/-- Convert Sparse to Truncated (drops high grades) -/
def sparseToTruncated [Ring F] [BEq F] (m : MultivectorS sig F) {maxGrade : ℕ} :
    TruncatedMV sig maxGrade F :=
  TruncatedMV.ofSparse m

/-- Convert Truncated to Sparse -/
def truncatedToSparse [Ring F] {maxGrade : ℕ} (m : TruncatedMV sig maxGrade F) : MultivectorS sig F :=
  TruncatedMV.toSparse m

/-! ## Theorems (Stated with sorry_proof)

Representation conversions preserve algebraic structure.
-/

theorem denseToSparse_add [Ring F] [BEq F] [DecidableEq F] (a b : Multivector sig F) :
    denseToSparse (a.add b) = (denseToSparse a).add (denseToSparse b) := by
  sorry_proof

theorem denseToSparse_mul [Ring F] [BEq F] [DecidableEq F] (a b : Multivector sig F) :
    denseToSparse (a * b) = (denseToSparse a) * (denseToSparse b) := by
  sorry_proof

theorem sparseToDense_add [Ring F] [BEq F] (a b : MultivectorS sig F) :
    sparseToDense (a.add b) = (sparseToDense a).add (sparseToDense b) := by
  sorry_proof

theorem sparseToDense_mul [Ring F] [BEq F] [DecidableEq F] (a b : MultivectorS sig F) :
    sparseToDense (a * b) = (sparseToDense a) * (sparseToDense b) := by
  sorry_proof

theorem roundtrip_dense_sparse [Ring F] [BEq F] (m : Multivector sig F) :
    sparseToDense (denseToSparse m) = m := by
  sorry_proof

/-! ## Tests -/

section Tests

-- Test conversion Dense -> Sparse -> Dense roundtrip
#eval! let orig : Multivector R3 Float := Multivector.basis ⟨0, by omega⟩
       let sparse := denseToSparse orig
       let back := sparseToDense sparse
       (back * back).scalarPart  -- 1.0 (e1² = 1)

-- Test Dense normSq directly (without generic)
#eval! let v : Multivector R3 Float := Multivector.basis ⟨0, by omega⟩
       (v * v.reverse).scalarPart  -- 1.0

-- Test Sparse normSq directly
#eval! let v : MultivectorS R3 Float := MultivectorS.basis ⟨0, by omega⟩
       (v * v†ₛ).scalarPart  -- 1.0

#eval IO.println "✓ Repr module loaded"

end Tests

end Grassmann
