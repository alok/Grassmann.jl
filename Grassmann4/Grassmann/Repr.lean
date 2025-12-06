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

/-- Dense representation is the default (priority 1000 > default 100).
    This ensures `Multivector` is preferred when typeclass inference is ambiguous. -/
instance (priority := 1000) [Ring F] : MultivectorRepr (Multivector sig F) sig F where
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

/-- Sparse representation (priority 500, lower than Dense).
    Use explicitly when working with high-dimensional sparse data. -/
instance (priority := 500) [Ring F] [BEq F] [DecidableEq F] :
    MultivectorRepr (MultivectorS sig F) sig F where
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

/-- Truncated representation (priority 200, lowest).
    Use for very high dimensions when only low-grade components matter. -/
instance (priority := 200) [Ring F] [BEq F] [DecidableEq F] {maxGrade : ℕ} :
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

### Instance Priorities

Instance priorities are set to prefer representations by typical use case:
- Dense (Multivector):   priority 1000 — default for n ≤ 8
- Sparse (MultivectorS): priority 500  — explicit opt-in for high-dim sparse
- Truncated (TruncatedMV): priority 200 — for n >> 8, low-grade focus

### Known Limitation: Typeclass Inference with Dependent Types

Due to Lean 4's typeclass inference behavior with dependent types like `Signature n`,
generic functions over `MultivectorRepr` sometimes fail to infer instances.
The issue: when the type parameter `M` appears before `sig`, Lean cannot always
unify `Signature ?n` during instance search.

**Problem Example:**
```lean
-- May fail: Lean can't always infer MultivectorRepr when sig is implicit
def genericNormSq [MultivectorRepr M sig F] (m : M) : F :=
  MultivectorRepr.scalarPart (MultivectorRepr.mul m (MultivectorRepr.reverse m))
```

**Working Patterns:**

1. **Signature-First Generic Functions**: Put `sig` early in the signature
```lean
-- This works better - sig is explicit, M inferred from concrete type
def normSqGeneric {n : ℕ} {sig : Signature n} {F : Type*} {M : Type*}
    [Ring F] [MultivectorRepr M sig F] (m : M) : F :=
  MultivectorRepr.scalarPart (MultivectorRepr.mul m (MultivectorRepr.reverse m))
```

2. **Representation-Specific Functions**: Write specialized versions (current approach)
```lean
-- Direct, no inference issues:
Multivector.normSq    -- for Dense
MultivectorS.normSq   -- for Sparse
TruncatedMV.normSq    -- for Truncated
```

3. **Local Instance Hints**: Use `haveI`/`letI` for scoped inference
```lean
def foo (m : Multivector sig F) : F :=
  haveI : MultivectorRepr (Multivector sig F) sig F := inferInstance
  MultivectorRepr.scalarPart m
```

4. **Explicit @ Application**: For one-off uses
```lean
#check @MultivectorRepr.scalarPart _ 3 R3 Float _ _ inferInstance
```

**Current Recommendation:**
- For library code: use representation-specific operations
- For generic algorithms: put signature parameters early
- Instance priorities ensure Dense is preferred when ambiguous
-/

/-! ## Working Generic Functions

Examples of generic functions that work with typeclass inference.
The `inst` parameter makes the instance explicit, avoiding resolution issues.
-/

/-- Generic norm squared - works across all representations.
    Uses explicit instance parameter to avoid inference issues with dependent types. -/
def normSqGeneric {n : ℕ} {sig : Signature n} {F : Type*} {M : Type*}
    [Ring F] (inst : MultivectorRepr M sig F) (m : M) : F :=
  inst.scalarPart (inst.mul m (inst.reverse m))

/-- Generic scalar extraction. -/
def scalarGeneric {n : ℕ} {sig : Signature n} {F : Type*} {M : Type*}
    [Ring F] (inst : MultivectorRepr M sig F) (m : M) : F :=
  inst.scalarPart m

/-- Generic reverse involution. -/
def reverseGeneric {n : ℕ} {sig : Signature n} {F : Type*} {M : Type*}
    [Ring F] (inst : MultivectorRepr M sig F) (m : M) : M :=
  inst.reverse m

/-- Generic geometric product. -/
def mulGeneric {n : ℕ} {sig : Signature n} {F : Type*} {M : Type*}
    [Ring F] (inst : MultivectorRepr M sig F) (a b : M) : M :=
  inst.mul a b

/-! ### Usage Examples

For concrete types, pass the instance explicitly or use `inferInstance`:

```lean
-- Explicit instance (most reliable):
#check normSqGeneric (inst := inferInstance) (m : Multivector R3 Float)

-- Or use the representation-specific versions directly:
#check Multivector.normSq  -- These don't have inference issues
```
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
