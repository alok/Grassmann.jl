/-
  Grassmann/Multivector.lean - Full multivector type

  Port of Grassmann.jl's Chain and Multivector types.

  A multivector is a linear combination of basis blades:
    M = a₀ + a₁e₁ + a₂e₂ + a₃e₃ + a₁₂e₁₂ + a₁₃e₁₃ + a₂₃e₂₃ + a₁₂₃e₁₂₃

  We represent this as an array of 2^n coefficients indexed by basis blade.
  The index of a blade is its bitmask interpreted as a natural number.
-/
import Grassmann.Products

namespace Grassmann

variable {n : ℕ} {sig : Signature n} {F : Type*}

/-! ## Multivector Type

A full multivector with coefficients for all 2^n basis blades.
-/

/-- A multivector in the Clifford algebra with signature `sig` over field `F`.
    Coefficients are indexed by basis blade bitmask (0 to 2^n - 1). -/
structure Multivector (sig : Signature n) (F : Type*) where
  /-- Coefficients indexed by blade bitmask -/
  coeffs : Fin (2^n) → F

namespace Multivector

variable [Zero F] [One F] [Add F] [Neg F] [Mul F] [Sub F]

/-! ### Constructors -/

/-- Zero multivector -/
def zero : Multivector sig F := ⟨fun _ => 0⟩

/-- Scalar multivector -/
def scalar (x : F) : Multivector sig F :=
  ⟨fun i => if i.val = 0 then x else 0⟩

/-- Unit scalar -/
def one : Multivector sig F := scalar 1

/-- Basis vector e_i -/
def basis (i : Fin n) : Multivector sig F :=
  ⟨fun j => if j.val = 1 <<< i.val then 1 else 0⟩

/-- From a single blade with coefficient -/
def ofSingle (s : Single sig F) : Multivector sig F :=
  ⟨fun i => if i.val = s.blade.bits.toNat then s.coeff else 0⟩

/-- From a blade (coefficient 1) -/
def ofBlade (b : Blade sig) : Multivector sig F :=
  ⟨fun i => if i.val = b.bits.toNat then 1 else 0⟩

/-! ### Coefficient Access -/

/-- Get coefficient of a specific blade -/
def coeff (m : Multivector sig F) (b : Blade sig) : F :=
  m.coeffs ⟨b.bits.toNat, by
    have h := b.bits.isLt
    simp only [BitVec.toNat] at h ⊢
    exact h⟩

/-- Get scalar part (grade 0) -/
def scalarPart (m : Multivector sig F) : F :=
  m.coeffs ⟨0, Nat.two_pow_pos n⟩

/-- Set coefficient of a specific blade -/
def setCoeff (m : Multivector sig F) (b : Blade sig) (x : F) : Multivector sig F :=
  ⟨fun i =>
    if i.val = b.bits.toNat then x
    else m.coeffs i⟩

/-! ### Grade Operations -/

/-- Extract grade-k part of a multivector -/
def gradeProject (m : Multivector sig F) (k : ℕ) : Multivector sig F :=
  ⟨fun i =>
    if grade (BitVec.ofNat n i.val) = k then m.coeffs i
    else 0⟩

/-- Grade 0 (scalar) projection -/
def grade0 (m : Multivector sig F) : Multivector sig F := m.gradeProject 0

/-- Grade 1 (vector) projection -/
def grade1 (m : Multivector sig F) : Multivector sig F := m.gradeProject 1

/-- Grade 2 (bivector) projection -/
def grade2 (m : Multivector sig F) : Multivector sig F := m.gradeProject 2

/-- Even part (grades 0, 2, 4, ...) -/
def evenPart (m : Multivector sig F) : Multivector sig F :=
  ⟨fun i =>
    if grade (BitVec.ofNat n i.val) % 2 = 0 then m.coeffs i
    else 0⟩

/-- Odd part (grades 1, 3, 5, ...) -/
def oddPart (m : Multivector sig F) : Multivector sig F :=
  ⟨fun i =>
    if grade (BitVec.ofNat n i.val) % 2 = 1 then m.coeffs i
    else 0⟩

/-! ### Basic Algebra -/

/-- Add two multivectors -/
def add (a b : Multivector sig F) : Multivector sig F :=
  ⟨fun i => a.coeffs i + b.coeffs i⟩

/-- Subtract multivectors -/
def sub (a b : Multivector sig F) : Multivector sig F :=
  ⟨fun i => a.coeffs i - b.coeffs i⟩

/-- Negate a multivector -/
def neg (m : Multivector sig F) : Multivector sig F :=
  ⟨fun i => -m.coeffs i⟩

/-- Scale by a scalar -/
def smul (x : F) (m : Multivector sig F) : Multivector sig F :=
  ⟨fun i => x * m.coeffs i⟩

instance : Zero (Multivector sig F) := ⟨Multivector.zero⟩
instance : One (Multivector sig F) := ⟨Multivector.one⟩
instance : Add (Multivector sig F) := ⟨Multivector.add⟩
instance : Sub (Multivector sig F) := ⟨Multivector.sub⟩
instance : Neg (Multivector sig F) := ⟨Multivector.neg⟩

/-! ### Involutions -/

/-- Reverse (dagger): reverses order of basis vectors.
    For grade k: multiplies by (-1)^(k(k-1)/2) -/
def reverse (m : Multivector sig F) : Multivector sig F :=
  ⟨fun i =>
    let k := grade (BitVec.ofNat n i.val)
    if (k * (k - 1) / 2) % 2 = 0 then m.coeffs i
    else -m.coeffs i⟩

/-- Grade involution: multiplies grade k by (-1)^k -/
def involute (m : Multivector sig F) : Multivector sig F :=
  ⟨fun i =>
    let k := grade (BitVec.ofNat n i.val)
    if k % 2 = 0 then m.coeffs i
    else -m.coeffs i⟩

/-- Clifford conjugate: reverse composed with involute.
    For grade k: multiplies by (-1)^(k(k+1)/2) -/
def conjugate (m : Multivector sig F) : Multivector sig F :=
  ⟨fun i =>
    let k := grade (BitVec.ofNat n i.val)
    if (k * (k + 1) / 2) % 2 = 0 then m.coeffs i
    else -m.coeffs i⟩

postfix:max "†" => Multivector.reverse
postfix:max "ˆ" => Multivector.involute
postfix:max "‡" => Multivector.conjugate

/-! ### Products

Products are computed by iterating over all pairs of basis blades.
We use List.foldl for a clean implementation.
-/

/-- Helper: list of all basis blade indices -/
private def allIndices (n : ℕ) : List (Fin (2^n)) :=
  List.finRange (2^n)

/-- Geometric product of two multivectors.
    This is O(4^n) but correct. -/
def geometricProduct (a b : Multivector sig F) : Multivector sig F :=
  ⟨fun k =>
    let indices := allIndices n
    indices.foldl (init := (0 : F)) fun acc i =>
      indices.foldl (init := acc) fun acc2 j =>
        let bi : Blade sig := ⟨BitVec.ofNat n i.val⟩
        let bj : Blade sig := ⟨BitVec.ofNat n j.val⟩
        let resultBits := bi.bits ^^^ bj.bits
        if resultBits.toNat = k.val then
          let sign := geometricSign sig bi bj
          let coeff := a.coeffs i * b.coeffs j
          acc2 + (if sign < 0 then -coeff else coeff)
        else acc2⟩

/-- Wedge product of two multivectors -/
def wedgeProduct (a b : Multivector sig F) : Multivector sig F :=
  ⟨fun k =>
    let indices := allIndices n
    indices.foldl (init := (0 : F)) fun acc i =>
      indices.foldl (init := acc) fun acc2 j =>
        let bi : Blade sig := ⟨BitVec.ofNat n i.val⟩
        let bj : Blade sig := ⟨BitVec.ofNat n j.val⟩
        if (bi.bits &&& bj.bits) = 0 then
          let resultBits := bi.bits ||| bj.bits
          if resultBits.toNat = k.val then
            let sign := wedgeSign sig bi bj
            let coeff := a.coeffs i * b.coeffs j
            acc2 + (if sign < 0 then -coeff else if sign = 0 then 0 else coeff)
          else acc2
        else acc2⟩

/-- Left contraction of a into b -/
def leftContract (a b : Multivector sig F) : Multivector sig F :=
  ⟨fun k =>
    let indices := allIndices n
    indices.foldl (init := (0 : F)) fun acc i =>
      indices.foldl (init := acc) fun acc2 j =>
        let bi : Blade sig := ⟨BitVec.ofNat n i.val⟩
        let bj : Blade sig := ⟨BitVec.ofNat n j.val⟩
        if (bi.bits &&& bj.bits) = bi.bits && bi.grade ≤ bj.grade then
          let resultBits := bi.bits ^^^ bj.bits
          if resultBits.toNat = k.val then
            let sign := geometricSign sig bi bj
            let coeff := a.coeffs i * b.coeffs j
            acc2 + (if sign < 0 then -coeff else coeff)
          else acc2
        else acc2⟩

instance : Mul (Multivector sig F) := ⟨Multivector.geometricProduct⟩

infixl:65 " ⋀ᵐ " => Multivector.wedgeProduct  -- Use different symbol to avoid conflict
infixl:65 " ⌋ᵐ " => Multivector.leftContract

/-! ### Hodge Dual -/

/-- Hodge dual (complement): maps grade k to grade (n-k) -/
def hodgeDual (m : Multivector sig F) : Multivector sig F :=
  ⟨fun i =>
    let b : Blade sig := ⟨BitVec.ofNat n i.val⟩
    let dualBits := b.bits ^^^ pseudoscalar
    let dualIdx := dualBits.toNat
    if h : dualIdx < 2^n then
      let sign := leftComplementSign sig ⟨dualBits⟩
      let coeff := m.coeffs ⟨dualIdx, h⟩
      if sign < 0 then -coeff else coeff
    else 0⟩

prefix:max "⋆ᵐ" => Multivector.hodgeDual

/-! ### Norms -/

/-- Squared norm: scalar part of m * m† -/
def normSq (m : Multivector sig F) : F :=
  (m * m†).scalarPart

/-- Squared reverse norm: m† * m (alternative convention) -/
def normSqRev (m : Multivector sig F) : F :=
  (m† * m).scalarPart

/-! ### Scalar Product -/

/-- Scalar product of two multivectors: ⟨a†b⟩₀ -/
def scalarProduct (a b : Multivector sig F) : F :=
  (a† * b).scalarPart

/-! ### Right Contraction -/

/-- Right contraction: a ⌊ b -/
def rightContract (a b : Multivector sig F) : Multivector sig F :=
  ⟨fun k =>
    let indices := allIndices n
    indices.foldl (init := (0 : F)) fun acc i =>
      indices.foldl (init := acc) fun acc2 j =>
        let bi : Blade sig := ⟨BitVec.ofNat n i.val⟩
        let bj : Blade sig := ⟨BitVec.ofNat n j.val⟩
        if (bj.bits &&& bi.bits) = bj.bits && bj.grade ≤ bi.grade then
          let resultBits := bi.bits ^^^ bj.bits
          if resultBits.toNat = k.val then
            let sign := geometricSign sig bi bj
            let coeff := a.coeffs i * b.coeffs j
            acc2 + (if sign < 0 then -coeff else coeff)
          else acc2
        else acc2⟩

infixl:65 " ⌊ᵐ " => Multivector.rightContract

/-! ### Fat Dot Product -/

/-- Fat dot / inner product: sum of left and right contractions minus scalar product -/
def fatDot (a b : Multivector sig F) : Multivector sig F :=
  (a ⌋ᵐ b).add (a ⌊ᵐ b)

infixl:65 " ⋅ᵐ " => Multivector.fatDot

/-! ### Commutator and Anti-commutator -/

/-- Commutator product: (ab - ba) / 2 -/
def commutator [Div F] [OfNat F 2] (a b : Multivector sig F) : Multivector sig F :=
  ((a * b).sub (b * a)).smul (1 / (2 : F))

/-- Anti-commutator product: (ab + ba) / 2 -/
def antiCommutator [Div F] [OfNat F 2] (a b : Multivector sig F) : Multivector sig F :=
  ((a * b).add (b * a)).smul (1 / (2 : F))

/-! ### Inverse -/

/-- Inverse of multivector (when it exists): m⁻¹ = m† / (m m†)
    Only valid when normSq is non-zero and invertible. -/
def inv [Div F] (m : Multivector sig F) : Multivector sig F :=
  let nsq := m.normSq
  m†.smul (1 / nsq)

/-! ### Sandwich Product -/

/-- Sandwich product: a * x * a† (for rotations/reflections) -/
def sandwich (a x : Multivector sig F) : Multivector sig F :=
  a * x * a†

end Multivector

/-! ## Float-specific Operations -/

namespace Multivector

/-- Norm (magnitude) of a multivector: √(m m†) -/
def norm (m : Multivector sig Float) : Float :=
  Float.sqrt (m * m†).scalarPart

/-- Normalize a multivector to unit norm -/
def normalize (m : Multivector sig Float) : Multivector sig Float :=
  let n := m.norm
  if n == 0 then m else m.smul (1 / n)

/-- Check if multivector has unit norm (within tolerance) -/
def isUnit (m : Multivector sig Float) (tol : Float := 1e-10) : Bool :=
  let nsq := (m * m†).scalarPart
  Float.abs (nsq - 1) < tol

/-- Square root of a scalar multivector -/
def sqrtScalar (m : Multivector sig Float) : Multivector sig Float :=
  Multivector.scalar (Float.sqrt m.scalarPart)

/-- Exponential of a bivector using closed form (for unit bivector B² = -1):
    exp(θB) = cos(θ) + sin(θ)B -/
def expUnitBivector (B : Multivector sig Float) (theta : Float) : Multivector sig Float :=
  let c := Float.cos theta
  let s := Float.sin theta
  (Multivector.scalar c).add (B.smul s)

/-- Logarithm of a rotor (returns bivector angle×axis) -/
def logRotor (R : Multivector sig Float) : Multivector sig Float :=
  let c := R.scalarPart  -- cos(θ)
  let theta := Float.acos c
  if theta < 1e-10 then
    Multivector.zero  -- Near identity
  else
    let sinTheta := Float.sin theta
    R.evenPart.sub (Multivector.scalar c) |>.smul (theta / sinTheta)

end Multivector

/-! ## Convenience Functions -/

section Convenience

variable [Zero F] [One F] [Add F] [Neg F] [Mul F] [Sub F]

/-- Create a vector from components -/
def vector3 (x y z : F) : Multivector R3 F :=
  Multivector.basis ⟨0, by omega⟩ |>.smul x |>.add
  (Multivector.basis ⟨1, by omega⟩ |>.smul y) |>.add
  (Multivector.basis ⟨2, by omega⟩ |>.smul z)

/-- Create a bivector in R3 -/
def bivector3 (xy xz yz : F) : Multivector R3 F :=
  let e12 : Multivector R3 F := ⟨fun i => if i.val = 0b011 then 1 else 0⟩
  let e13 : Multivector R3 F := ⟨fun i => if i.val = 0b101 then 1 else 0⟩
  let e23 : Multivector R3 F := ⟨fun i => if i.val = 0b110 then 1 else 0⟩
  e12.smul xy |>.add (e13.smul xz) |>.add (e23.smul yz)

end Convenience

/-! ## Tests -/

-- Basic multivector operations
#eval (Multivector.scalar 5 : Multivector R3 Int).scalarPart  -- 5
#eval (Multivector.one : Multivector R3 Int).scalarPart  -- 1

-- Basis vectors
#eval (Multivector.basis ⟨0, by omega⟩ : Multivector R3 Int).coeff (e1 : Blade R3)  -- 1
#eval (Multivector.basis ⟨1, by omega⟩ : Multivector R3 Int).coeff (e2 : Blade R3)  -- 1

-- Grade projection
#eval ((Multivector.one : Multivector R3 Int).add (Multivector.basis ⟨0, by omega⟩)).grade0.scalarPart  -- 1

-- Reverse signs
#eval (Multivector.ofBlade (e1 : Blade R3) : Multivector R3 Int)†.coeff e1  -- 1 (vector unchanged)
#eval (Multivector.ofBlade (e12 : Blade R3) : Multivector R3 Int)†.coeff e12  -- -1 (bivector flips)

-- Geometric product: e1 * e1 = 1
#eval let e1v := (Multivector.ofBlade (e1 : Blade R3) : Multivector R3 Int)
      (e1v * e1v).scalarPart  -- 1

-- Geometric product: e1 * e2 = e12
#eval let e1v := (Multivector.ofBlade (e1 : Blade R3) : Multivector R3 Int)
      let e2v := (Multivector.ofBlade (e2 : Blade R3) : Multivector R3 Int)
      (e1v * e2v).coeff (e12 : Blade R3)  -- 1

-- Geometric product: e2 * e1 = -e12
#eval let e1v := (Multivector.ofBlade (e1 : Blade R3) : Multivector R3 Int)
      let e2v := (Multivector.ofBlade (e2 : Blade R3) : Multivector R3 Int)
      (e2v * e1v).coeff (e12 : Blade R3)  -- -1

-- Wedge product: e1 ∧ e2 = e12
#eval let e1v := (Multivector.ofBlade (e1 : Blade R3) : Multivector R3 Int)
      let e2v := (Multivector.ofBlade (e2 : Blade R3) : Multivector R3 Int)
      (e1v ⋀ᵐ e2v).coeff (e12 : Blade R3)  -- 1

-- Wedge: e1 ∧ e1 = 0
#eval let e1v := (Multivector.ofBlade (e1 : Blade R3) : Multivector R3 Int)
      (e1v ⋀ᵐ e1v).coeff (e12 : Blade R3)  -- 0

-- Test: e12 * e12 = -1 (bivector squares to -1 in Euclidean)
#eval let e12v := (Multivector.ofBlade (e12 : Blade R3) : Multivector R3 Int)
      (e12v * e12v).scalarPart  -- -1

-- Test: (e1 + e2) * (e1 + e2) = e1*e1 + e1*e2 + e2*e1 + e2*e2 = 1 + e12 - e12 + 1 = 2
#eval let v := (Multivector.ofBlade (e1 : Blade R3) : Multivector R3 Int).add
               (Multivector.ofBlade (e2 : Blade R3))
      (v * v).scalarPart  -- 2

-- Left contraction: e1 ⌋ e12 = e2
#eval let e1v := (Multivector.ofBlade (e1 : Blade R3) : Multivector R3 Int)
      let e12v := (Multivector.ofBlade (e12 : Blade R3) : Multivector R3 Int)
      (e1v ⌋ᵐ e12v).coeff (e2 : Blade R3)  -- 1

end Grassmann
