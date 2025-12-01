/-
  Grassmann/SparseMultivector.lean - Sparse multivector representation

  Uses TreeMap for efficient storage of sparse multivectors where most
  coefficients are zero. Good for:
  - High dimensional algebras (N > 8)
  - Vectors, bivectors in high dimensions
  - Operations where result is sparse

  Following Grassmann.jl's tiered approach:
  - N ≤ 8: Use dense Array (MultivectorA)
  - N > 8: Use sparse TreeMap (MultivectorS)
-/
import Grassmann.Multivector  -- Get Ring and existing signatures
import Std.Data.TreeMap

namespace Grassmann

variable {n : ℕ} {sig : Signature n}

/-! ## Sparse Multivector

Key = blade index (bitmask as Nat)
Value = coefficient (only store non-zero)
-/

/-- Sparse multivector using TreeMap for efficient storage of non-zero coefficients -/
structure MultivectorS (sig : Signature n) (F : Type*) where
  /-- TreeMap from blade index to coefficient -/
  coeffs : Std.TreeMap Nat F
  deriving Repr

namespace MultivectorS

variable [Ring F] [BEq F] [DecidableEq F]

/-! ### Constructors -/

/-- Zero multivector (empty map) -/
def zero : MultivectorS sig F := ⟨Std.TreeMap.empty⟩

/-- Scalar multivector -/
def scalar (x : F) : MultivectorS sig F :=
  if x == 0 then zero else ⟨Std.TreeMap.empty.insert 0 x⟩

/-- Unit scalar -/
def one : MultivectorS sig F := scalar 1

/-- From a single blade with coefficient -/
def ofBlade (b : Blade sig) (coeff : F := 1) : MultivectorS sig F :=
  if coeff == 0 then zero else ⟨Std.TreeMap.empty.insert b.bits.toNat coeff⟩

/-- Basis vector e_i -/
def basis (i : Fin n) : MultivectorS sig F :=
  ofBlade ⟨BitVec.ofNat n (1 <<< i.val)⟩

/-! ### Coefficient Access -/

/-- Get coefficient (returns 0 if not stored) -/
def coeff (m : MultivectorS sig F) (idx : Nat) : F :=
  m.coeffs.get? idx |>.getD 0

/-- Get coefficient of specific blade -/
def coeffBlade (m : MultivectorS sig F) (b : Blade sig) : F :=
  m.coeff b.bits.toNat

/-- Scalar part -/
def scalarPart (m : MultivectorS sig F) : F := m.coeff 0

/-- Number of non-zero coefficients -/
def nnz (m : MultivectorS sig F) : Nat := m.coeffs.size

/-- Check if zero -/
def isZero (m : MultivectorS sig F) : Bool := m.coeffs.isEmpty

/-! ### Arithmetic -/

/-- Add two sparse multivectors -/
def add (a b : MultivectorS sig F) : MultivectorS sig F :=
  ⟨b.coeffs.foldl (init := a.coeffs) fun acc k v =>
    let oldVal := acc.get? k |>.getD 0
    let newVal := oldVal + v
    if newVal == 0 then acc.erase k else acc.insert k newVal⟩

/-- Negate -/
def neg (m : MultivectorS sig F) : MultivectorS sig F :=
  ⟨m.coeffs.foldl (init := Std.TreeMap.empty) fun acc k v =>
    acc.insert k (-v)⟩

/-- Subtract -/
def sub (a b : MultivectorS sig F) : MultivectorS sig F :=
  a.add b.neg

/-- Scale -/
def smul (x : F) (m : MultivectorS sig F) : MultivectorS sig F :=
  if x == 0 then zero
  else ⟨m.coeffs.foldl (init := Std.TreeMap.empty) fun acc k v =>
    let newVal := x * v
    if newVal == 0 then acc else acc.insert k newVal⟩

instance : Zero (MultivectorS sig F) := ⟨zero⟩
instance : One (MultivectorS sig F) := ⟨one⟩
instance : Add (MultivectorS sig F) := ⟨add⟩
instance : Neg (MultivectorS sig F) := ⟨neg⟩
instance : Sub (MultivectorS sig F) := ⟨sub⟩
instance : SMul F (MultivectorS sig F) := ⟨smul⟩

/-! ### Products

Sparse products iterate only over non-zero pairs.
Complexity: O(k₁ * k₂) where k = number of non-zero coefficients.
-/

/-- Geometric product - sparse version
    Only iterates over non-zero coefficient pairs. -/
def geometricProduct (a b : MultivectorS sig F) : MultivectorS sig F :=
  ⟨a.coeffs.foldl (init := Std.TreeMap.empty) fun acc1 i ai =>
    b.coeffs.foldl (init := acc1) fun acc2 j bj =>
      let bi : Blade sig := ⟨BitVec.ofNat n i⟩
      let bladeJ : Blade sig := ⟨BitVec.ofNat n j⟩
      let resultIdx := (bi.bits ^^^ bladeJ.bits).toNat
      let sign := geometricSign sig bi bladeJ
      let contrib := if sign < 0 then -(ai * bj) else ai * bj
      let oldVal := acc2.get? resultIdx |>.getD 0
      let newVal := oldVal + contrib
      if newVal == 0 then acc2.erase resultIdx else acc2.insert resultIdx newVal⟩

/-- Wedge product - sparse version
    Only contributes when blades don't share basis vectors. -/
def wedgeProduct (a b : MultivectorS sig F) : MultivectorS sig F :=
  ⟨a.coeffs.foldl (init := Std.TreeMap.empty) fun acc1 i ai =>
    b.coeffs.foldl (init := acc1) fun acc2 j bj =>
      let bi : Blade sig := ⟨BitVec.ofNat n i⟩
      let bladeJ : Blade sig := ⟨BitVec.ofNat n j⟩
      -- Only non-zero when no shared basis vectors
      if (bi.bits &&& bladeJ.bits) == 0 then
        let resultIdx := (bi.bits ||| bladeJ.bits).toNat
        let sign := wedgeSign sig bi bladeJ
        if sign != 0 then
          let contrib := if sign < 0 then -(ai * bj) else ai * bj
          let oldVal := acc2.get? resultIdx |>.getD 0
          let newVal := oldVal + contrib
          if newVal == 0 then acc2.erase resultIdx else acc2.insert resultIdx newVal
        else acc2
      else acc2⟩

instance : Mul (MultivectorS sig F) := ⟨geometricProduct⟩

infixl:65 " ⋀ₛ " => wedgeProduct

/-! ### Involutions -/

/-- Reverse -/
def reverse (m : MultivectorS sig F) : MultivectorS sig F :=
  ⟨m.coeffs.foldl (init := Std.TreeMap.empty) fun acc k v =>
    let g := grade (BitVec.ofNat n k)
    let newVal := if (g * (g - 1) / 2) % 2 == 0 then v else -v
    acc.insert k newVal⟩

postfix:max "†ₛ" => reverse

/-! ### Conversion -/

/-- Convert to list of (index, coefficient) pairs -/
def toList (m : MultivectorS sig F) : List (Nat × F) :=
  m.coeffs.toList

/-- Convert from list -/
def ofList [Zero F] (pairs : List (Nat × F)) : MultivectorS sig F :=
  ⟨pairs.foldl (init := Std.TreeMap.empty) fun acc (k, v) =>
    if v == 0 then acc else acc.insert k v⟩

end MultivectorS

/-! ## Tests -/

section SparseTests

-- Use existing R3 from Grassmann.Blade, and create R8
-- R8 has 256 blades, perfect for sparse testing
def R8Sparse : Signature 8 := ⟨0⟩  -- All positive (Euclidean)

-- Create basis vectors in R3 (using existing signature)
def e1S : MultivectorS R3 Float := MultivectorS.basis ⟨0, by omega⟩
def e2S : MultivectorS R3 Float := MultivectorS.basis ⟨1, by omega⟩
def e3S : MultivectorS R3 Float := MultivectorS.basis ⟨2, by omega⟩

-- Test: vector has only 1 non-zero coefficient
#eval! e1S.nnz  -- 1

-- Test: e1 * e1 = 1 (sparse)
#eval! (e1S * e1S).scalarPart  -- 1.0

-- Test: e1 * e2 gives bivector e12
#eval! (e1S * e2S).nnz  -- 1 (only e12 non-zero)

-- Test: (e1 + e2) * (e1 + e2) = 2
#eval! let v := e1S + e2S
       (v * v).scalarPart  -- 2.0

-- Test: wedge product
#eval! (e1S ⋀ₛ e2S).nnz  -- 1

-- Test: wedge of same vector = 0
#eval! (e1S ⋀ₛ e1S).isZero  -- true

-- R8 tests - show sparse advantage
def e1R8 : MultivectorS R8Sparse Float := MultivectorS.basis ⟨0, by omega⟩
def e2R8 : MultivectorS R8Sparse Float := MultivectorS.basis ⟨1, by omega⟩

-- In R8 (256 blades), vector still has only 1 non-zero
#eval! e1R8.nnz  -- 1

-- Geometric product still efficient
#eval! (e1R8 * e1R8).scalarPart  -- 1.0
#eval! (e1R8 * e2R8).nnz  -- 1

end SparseTests

end Grassmann
