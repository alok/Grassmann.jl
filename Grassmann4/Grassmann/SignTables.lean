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
import Grassmann.Multivector

namespace Grassmann

/-! ## Precomputed Sign Tables for Standard Signatures -/

/-- Precomputed sign table for R2 (4×4 = 16 entries) -/
def R2SignTable : SignTable 2 := buildSignTable R2

/-- Precomputed sign table for R3 (8×8 = 64 entries) -/
def R3SignTable : SignTable 3 := buildSignTable R3

/-- Precomputed sign table for R4 (16×16 = 256 entries) -/
def R4SignTable : SignTable 4 := buildSignTable R4

/-- Precomputed sign table for STA Cl(1,3) (16×16 = 256 entries) -/
def STASignTable : SignTable 4 := buildSignTable STA

/-- Precomputed sign table for PGA3 Cl(3,0,1) (16×16 = 256 entries) -/
def PGA3SignTable : SignTable 4 := buildSignTable PGA3

/-- Precomputed sign table for CGA3 Cl(4,1) (32×32 = 1024 entries) -/
def CGA3SignTable : SignTable 5 := buildSignTable CGA3

/-! ## Convenience Multiplication Functions -/

/-- R3 geometric product with precomputed table -/
def mulR3 (a b : Multivector R3 Float) : Multivector R3 Float :=
  Multivector.geometricProductWithTable R3SignTable a b

/-- R4 geometric product with precomputed table -/
def mulR4 (a b : Multivector R4 Float) : Multivector R4 Float :=
  Multivector.geometricProductWithTable R4SignTable a b

/-- STA geometric product with precomputed table -/
def mulSTA (a b : Multivector STA Float) : Multivector STA Float :=
  Multivector.geometricProductWithTable STASignTable a b

/-- PGA3 geometric product with precomputed table -/
def mulPGA3 (a b : Multivector PGA3 Float) : Multivector PGA3 Float :=
  Multivector.geometricProductWithTable PGA3SignTable a b

/-- CGA3 geometric product with precomputed table -/
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
