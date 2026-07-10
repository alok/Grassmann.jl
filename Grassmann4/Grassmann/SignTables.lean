/-
  Grassmann/SignTables.lean - Precomputed sign tables for common signatures

  For small dimensions (n ≤ 5), we precompute the full sign table once and use
  O(1) lookups instead of O(n) computation per sign. The table has 4^n entries
  (2^n × 2^n), so memory is:
  - n=2: 16 entries
  - n=3: 64 entries
  - n=4: 256 entries
  - n=5: 1024 entries

  Usage:
  ```lean
  -- Build once, reuse for all products
  let table := R3SignTable
  let product := geometricProductWithTable table a b
  ```
-/
import Grassmann.SignTablesCore
import Grassmann.Multivector

namespace Grassmann

/-! The proof-free tables and `cachedSignTable` selector are provided by
`Grassmann.SignTablesCore`.  This module adds dense `Multivector` integration. -/

variable {n : ℕ}

namespace Multivector

variable {sig : Signature n} {F : Type*} [CoeffOps F]

/-- Geometric product that automatically uses cached sign tables when available. -/
@[inline, specialize]
def geometricProductFast (a b : Multivector sig F) : Multivector sig F :=
  match cachedSignTable (n := n) sig with
  | some table => Multivector.geometricProductWithTable table a b
  | none => Multivector.geometricProduct a b

end Multivector

/-- Override the default `Mul` for dense multivectors with a table‑aware version.
    This keeps APIs the same while making small canonical algebras fast by default. -/
instance (priority := 1100) {n : ℕ} {sig : Signature n} {F : Type*} [CoeffOps F] :
    Mul (Multivector sig F) :=
  ⟨Multivector.geometricProductFast (sig := sig) (n := n)⟩

/-! ## Convenience Multiplication Functions -/

/-- R3 geometric product with precomputed table -/
@[inline]
def mulR3 (a b : Multivector R3 Float) : Multivector R3 Float :=
  Multivector.geometricProductWithTable R3SignTable a b

/-- R4 geometric product with precomputed table -/
@[inline]
def mulR4 (a b : Multivector R4 Float) : Multivector R4 Float :=
  Multivector.geometricProductWithTable R4SignTable a b

/-- STA geometric product with precomputed table -/
@[inline]
def mulSTA (a b : Multivector STA Float) : Multivector STA Float :=
  Multivector.geometricProductWithTable STASignTable a b

/-- PGA3 geometric product with precomputed table -/
@[inline]
def mulPGA3 (a b : Multivector PGA3 Float) : Multivector PGA3 Float :=
  Multivector.geometricProductWithTable PGA3SignTable a b

/-- CGA3 geometric product with precomputed table -/
@[inline]
def mulCGA3 (a b : Multivector CGA3 Float) : Multivector CGA3 Float :=
  Multivector.geometricProductWithTable CGA3SignTable a b

/-! ## Tests -/

-- Verify table construction works
#eval R3SignTable.signs.size  -- Should be 64

-- Verify some signs
#eval R3SignTable.lookup 1 2  -- e1 * e2 -> should be 1 (positive)
#eval R3SignTable.lookup 2 1  -- e2 * e1 -> should be -1 (anticommute)
#eval R3SignTable.lookup 1 1  -- e1 * e1 -> should be 1 (e1^2 = 1 in Euclidean)

end Grassmann
