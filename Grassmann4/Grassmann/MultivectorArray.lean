/-
  Grassmann/MultivectorArray.lean - Array-backed efficient multivector

  This provides an alternative representation using Vector (Array with size proof)
  for more efficient computation, especially with Float arithmetic.

  The function-based Multivector is cleaner for proofs, but this Array version
  is better for numerical computation.
-/
import Grassmann.Multivector

namespace Grassmann

variable {n : ℕ} {sig : Signature n}

/-! ## Array-backed Multivector

Uses `Vector F (2^n)` for O(1) random access and cache-friendly memory layout.
-/

/-- Array-backed multivector for efficient computation -/
structure MultivectorA (sig : Signature n) (F : Type*) where
  /-- Coefficients stored in a Vector -/
  coeffs : Vector F (2^n)

namespace MultivectorA

variable [Ring F] [Div F] [Inhabited F]

/-! ### Constructors -/

/-- Zero multivector -/
def zero : MultivectorA sig F :=
  ⟨Vector.replicate (2^n) 0⟩

/-- Scalar multivector -/
def scalar (x : F) : MultivectorA sig F :=
  ⟨Vector.ofFn fun i => if i.val = 0 then x else 0⟩

/-- Unit scalar -/
def one : MultivectorA sig F := scalar 1

/-- From a single blade with coefficient -/
def ofBlade (b : Blade sig) (coeff : F := 1) : MultivectorA sig F :=
  ⟨Vector.ofFn fun i =>
    if i.val = b.bits.toNat then coeff else 0⟩

/-! ### Coefficient Access -/

/-- Get coefficient at index -/
def get (m : MultivectorA sig F) (i : Fin (2^n)) : F :=
  m.coeffs[i]

/-- Get coefficient of a specific blade -/
def coeff (m : MultivectorA sig F) (b : Blade sig) : F :=
  m.get ⟨b.bits.toNat, b.bits.isLt⟩

/-- Get scalar part (grade 0) -/
def scalarPart (m : MultivectorA sig F) : F :=
  m.get ⟨0, Nat.two_pow_pos n⟩

/-- Set coefficient at index -/
def set (m : MultivectorA sig F) (i : Fin (2^n)) (x : F) : MultivectorA sig F :=
  ⟨m.coeffs.set i x⟩

/-! ### Conversion -/

/-- Convert to function-based Multivector -/
@[coe]
def toMultivector (m : MultivectorA sig F) : Multivector sig F :=
  ⟨fun i => m.get i⟩

/-- Convert from function-based Multivector -/
def ofMultivector (m : Multivector sig F) : MultivectorA sig F :=
  ⟨Vector.ofFn m.coeffs⟩

instance : Coe (MultivectorA sig F) (Multivector sig F) := ⟨toMultivector⟩

/-! ### Arithmetic -/

/-- Add two multivectors -/
def add (a b : MultivectorA sig F) : MultivectorA sig F :=
  ⟨Vector.ofFn fun i => a.get i + b.get i⟩

/-- Subtract multivectors -/
def sub (a b : MultivectorA sig F) : MultivectorA sig F :=
  ⟨Vector.ofFn fun i => a.get i - b.get i⟩

/-- Negate a multivector -/
def neg (m : MultivectorA sig F) : MultivectorA sig F :=
  ⟨Vector.ofFn fun i => -m.get i⟩

/-- Scale by a scalar -/
def smul (x : F) (m : MultivectorA sig F) : MultivectorA sig F :=
  ⟨Vector.ofFn fun i => x * m.get i⟩

instance : Zero (MultivectorA sig F) := ⟨MultivectorA.zero⟩
instance : One (MultivectorA sig F) := ⟨MultivectorA.one⟩
instance : Add (MultivectorA sig F) := ⟨MultivectorA.add⟩
instance : Sub (MultivectorA sig F) := ⟨MultivectorA.sub⟩
instance : Neg (MultivectorA sig F) := ⟨MultivectorA.neg⟩
instance : SMul F (MultivectorA sig F) := ⟨MultivectorA.smul⟩

/-! ### Grade Operations -/

/-- Extract grade-k part of a multivector -/
def gradeProject (m : MultivectorA sig F) (k : ℕ) : MultivectorA sig F :=
  ⟨Vector.ofFn fun i =>
    if grade (BitVec.ofNat n i.val) = k then m.get i
    else 0⟩

/-- Even part (grades 0, 2, 4, ...) -/
def evenPart (m : MultivectorA sig F) : MultivectorA sig F :=
  ⟨Vector.ofFn fun i =>
    if grade (BitVec.ofNat n i.val) % 2 = 0 then m.get i
    else 0⟩

/-- Odd part (grades 1, 3, 5, ...) -/
def oddPart (m : MultivectorA sig F) : MultivectorA sig F :=
  ⟨Vector.ofFn fun i =>
    if grade (BitVec.ofNat n i.val) % 2 = 1 then m.get i
    else 0⟩

/-! ### Involutions -/

/-- Reverse (dagger) -/
def reverse (m : MultivectorA sig F) : MultivectorA sig F :=
  ⟨Vector.ofFn fun i =>
    let k := grade (BitVec.ofNat n i.val)
    if (k * (k - 1) / 2) % 2 = 0 then m.get i
    else -(m.get i)⟩

/-- Grade involution -/
def involute (m : MultivectorA sig F) : MultivectorA sig F :=
  ⟨Vector.ofFn fun i =>
    let k := grade (BitVec.ofNat n i.val)
    if k % 2 = 0 then m.get i
    else -(m.get i)⟩

/-- Clifford conjugate -/
def conjugate (m : MultivectorA sig F) : MultivectorA sig F :=
  ⟨Vector.ofFn fun i =>
    let k := grade (BitVec.ofNat n i.val)
    if (k * (k + 1) / 2) % 2 = 0 then m.get i
    else -(m.get i)⟩

postfix:max "†ₐ" => MultivectorA.reverse
postfix:max "ˆₐ" => MultivectorA.involute
postfix:max "‡ₐ" => MultivectorA.conjugate

/-! ### Products -/

/-- Geometric product - O(4^n) forward iteration algorithm.
    For each input pair (i, j), compute output index k = i XOR j and accumulate. -/
def mul (a b : MultivectorA sig F) : MultivectorA sig F :=
  let size := 2^n
  let indices := List.finRange size
  -- Start with zero vector, accumulate contributions in single O(4^n) pass
  let result := indices.foldl (init := Vector.replicate size (0 : F)) fun arr i =>
    indices.foldl (init := arr) fun arr2 j =>
      let bi : Blade sig := ⟨BitVec.ofNat n i.val⟩
      let bj : Blade sig := ⟨BitVec.ofNat n j.val⟩
      let resultIdx := (bi.bits ^^^ bj.bits).toNat
      -- Proof that resultIdx < size (XOR of n-bit values is n-bit)
      if h : resultIdx < size then
        let sign := geometricSign sig bi bj
        let coeff := a.get i * b.get j
        let contrib := if sign < 0 then -coeff else coeff
        let oldVal := arr2.get ⟨resultIdx, h⟩
        arr2.set resultIdx (oldVal + contrib) h
      else arr2
  ⟨result⟩

/-- Wedge product - O(4^n) forward iteration algorithm.
    Only contributes when input blades don't share basis vectors (AND = 0). -/
def wedge (a b : MultivectorA sig F) : MultivectorA sig F :=
  let size := 2^n
  let indices := List.finRange size
  let result := indices.foldl (init := Vector.replicate size (0 : F)) fun arr i =>
    indices.foldl (init := arr) fun arr2 j =>
      let bi : Blade sig := ⟨BitVec.ofNat n i.val⟩
      let bj : Blade sig := ⟨BitVec.ofNat n j.val⟩
      -- Wedge only non-zero when blades share no basis vectors
      if (bi.bits &&& bj.bits) = 0 then
        let resultIdx := (bi.bits ||| bj.bits).toNat
        if h : resultIdx < size then
          let sign := wedgeSign sig bi bj
          if sign ≠ 0 then
            let coeff := a.get i * b.get j
            let contrib := if sign < 0 then -coeff else coeff
            let oldVal := arr2.get ⟨resultIdx, h⟩
            arr2.set resultIdx (oldVal + contrib) h
          else arr2
        else arr2
      else arr2
  ⟨result⟩

/-- Left contraction - O(4^n) forward iteration algorithm.
    Only contributes when first blade is contained in second. -/
def leftContract (a b : MultivectorA sig F) : MultivectorA sig F :=
  let size := 2^n
  let indices := List.finRange size
  let result := indices.foldl (init := Vector.replicate size (0 : F)) fun arr i =>
    indices.foldl (init := arr) fun arr2 j =>
      let bi : Blade sig := ⟨BitVec.ofNat n i.val⟩
      let bj : Blade sig := ⟨BitVec.ofNat n j.val⟩
      -- Left contraction: a ⌋ b only when a ⊆ b (as sets of basis vectors)
      if (bi.bits &&& bj.bits) = bi.bits && bi.grade ≤ bj.grade then
        let resultIdx := (bi.bits ^^^ bj.bits).toNat
        if h : resultIdx < size then
          let sign := geometricSign sig bi bj
          let coeff := a.get i * b.get j
          let contrib := if sign < 0 then -coeff else coeff
          let oldVal := arr2.get ⟨resultIdx, h⟩
          arr2.set resultIdx (oldVal + contrib) h
        else arr2
      else arr2
  ⟨result⟩

instance : Mul (MultivectorA sig F) := ⟨MultivectorA.mul⟩

infixl:65 " ⋀ₐ " => MultivectorA.wedge
infixl:65 " ⌋ₐ " => MultivectorA.leftContract

/-! ### Hodge Dual -/

/-- Hodge dual -/
def hodgeDual (m : MultivectorA sig F) : MultivectorA sig F :=
  ⟨Vector.ofFn fun i =>
    let b : Blade sig := ⟨BitVec.ofNat n i.val⟩
    let dualBits := b.bits ^^^ pseudoscalar
    let dualIdx := dualBits.toNat
    if h : dualIdx < 2^n then
      let sign := leftComplementSign sig ⟨dualBits⟩
      let coeff := m.get ⟨dualIdx, h⟩
      if sign < 0 then -coeff else coeff
    else 0⟩

prefix:max "⋆ₐ" => MultivectorA.hodgeDual

/-! ### Norms -/

/-- Squared norm -/
def normSq (m : MultivectorA sig F) : F :=
  (m * m†ₐ).scalarPart

end MultivectorA

/-! ## Float-specific Operations -/

namespace MultivectorA

variable [Inhabited Float]

/-- Norm (Float) -/
def norm (m : MultivectorA sig Float) : Float :=
  Float.sqrt (m * m†ₐ).scalarPart

/-- Normalize to unit norm -/
def normalize (m : MultivectorA sig Float) : MultivectorA sig Float :=
  let n := m.norm
  if n == 0 then m else m.smul (1 / n)

end MultivectorA

/-! ## Tests -/

section Tests

-- Test zero
#eval! (MultivectorA.zero : MultivectorA R3 Float).scalarPart  -- 0

-- Test scalar
#eval! (MultivectorA.scalar 5 : MultivectorA R3 Float).scalarPart  -- 5

-- Test ofBlade
#eval! (MultivectorA.ofBlade (e1 : Blade R3) : MultivectorA R3 Float).coeff (e1 : Blade R3)  -- 1

-- Test add
#eval! let a := (MultivectorA.scalar 1 : MultivectorA R3 Float)
       let b := (MultivectorA.scalar 2 : MultivectorA R3 Float)
       MultivectorA.scalarPart (a + b)  -- 3

-- Test geometric product: e1 * e1 = 1
#eval! let e1v := (MultivectorA.ofBlade (e1 : Blade R3) : MultivectorA R3 Float)
       (e1v * e1v).scalarPart  -- 1

-- Test geometric product: e1 * e2 = e12
#eval! let e1v := (MultivectorA.ofBlade (e1 : Blade R3) : MultivectorA R3 Float)
       let e2v := MultivectorA.ofBlade (e2 : Blade R3)
       (e1v * e2v).coeff (e12 : Blade R3)  -- 1

-- Test wedge: e1 ∧ e2 = e12
#eval! let e1v := (MultivectorA.ofBlade (e1 : Blade R3) : MultivectorA R3 Float)
       let e2v := MultivectorA.ofBlade (e2 : Blade R3)
       (e1v ⋀ₐ e2v).coeff (e12 : Blade R3)  -- 1

-- Test conversion to/from Multivector
#eval! let m := (MultivectorA.scalar 42 : MultivectorA R3 Float)
       m.toMultivector.scalarPart  -- 42

end Tests

end Grassmann
