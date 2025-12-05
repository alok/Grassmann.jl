/-
  Grassmann/Multivector.lean - Full multivector type

  Port of Grassmann.jl's Chain and Multivector types.

  A multivector is a linear combination of basis blades:
    M = a₀ + a₁e₁ + a₂e₂ + a₃e₃ + a₁₂e₁₂ + a₁₃e₁₃ + a₂₃e₂₃ + a₁₂₃e₁₂₃

  We represent this as an array of 2^n coefficients indexed by basis blade.
  The index of a blade is its bitmask interpreted as a natural number.

  Design:
  - Multivector structure has NO constraint on scalar type F
  - Operations are guarded by [Ring F], [Field F] etc.
  - Float Ring instance is in Proof.lean with sorry_proof axioms
-/
import Grassmann.Products
import Grassmann.Proof
import Grassmann.GATypeclass
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Int.Cast.Lemmas

namespace Grassmann

variable {n : ℕ} {sig : Signature n} {F : Type*}

/-! ## Multivector Type

A full multivector with coefficients for all 2^n basis blades.
Scalars are over any Ring F.
-/

/-- A multivector in the Clifford algebra with signature `sig` over ring `F`.
    Coefficients are indexed by basis blade bitmask (0 to 2^n - 1). -/
structure Multivector (sig : Signature n) (F : Type*) where
  /-- Coefficients indexed by blade bitmask -/
  coeffs : Fin (2^n) → F

namespace Multivector

variable [Ring F]

@[ext]
theorem ext {a b : Multivector sig F} (h : ∀ i, a.coeffs i = b.coeffs i) : a = b := by
  cases a; cases b; simp only [mk.injEq]; funext i; exact h i

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

/-- Scalar multiplication: s • m -/
instance : SMul F (Multivector sig F) := ⟨Multivector.smul⟩

/-- Allow chained arithmetic: use + - * directly -/
instance : HAdd (Multivector sig F) (Multivector sig F) (Multivector sig F) := ⟨Multivector.add⟩
instance : HSub (Multivector sig F) (Multivector sig F) (Multivector sig F) := ⟨Multivector.sub⟩

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
    O(4^n) forward iteration: for each input pair (i,j), accumulate to output[i XOR j].
    Results are computed once and cached in an Array for O(1) coefficient access. -/
def geometricProduct (a b : Multivector sig F) : Multivector sig F :=
  let size := 2^n
  let indices := allIndices n
  -- Build result array in single O(4^n) pass
  -- Handles degenerate (null) basis vectors: sign == 0 → skip contribution
  let resultArray := indices.foldl (init := Array.replicate size (0 : F)) fun arr i =>
    indices.foldl (init := arr) fun arr2 j =>
      let bi : Blade sig := ⟨BitVec.ofNat n i.val⟩
      let bj : Blade sig := ⟨BitVec.ofNat n j.val⟩
      let sign := geometricSign sig bi bj
      if sign == 0 then arr2  -- Degenerate case: no contribution
      else
        let resultIdx := (bi.bits ^^^ bj.bits).toNat
        if resultIdx < size then
          let coeff := a.coeffs i * b.coeffs j
          let contrib := if sign < 0 then -coeff else coeff
          arr2.modify resultIdx (· + contrib)
        else arr2
  -- Wrap array lookup in Multivector function interface
  ⟨fun k => resultArray.getD k.val 0⟩

/-- Wedge product of two multivectors.
    O(4^n) forward iteration: only contributes when blades share no basis vectors. -/
def wedgeProduct (a b : Multivector sig F) : Multivector sig F :=
  let size := 2^n
  let indices := allIndices n
  let resultArray := indices.foldl (init := Array.replicate size (0 : F)) fun arr i =>
    indices.foldl (init := arr) fun arr2 j =>
      let bi : Blade sig := ⟨BitVec.ofNat n i.val⟩
      let bj : Blade sig := ⟨BitVec.ofNat n j.val⟩
      if (bi.bits &&& bj.bits) = 0 then
        let resultIdx := (bi.bits ||| bj.bits).toNat
        if resultIdx < size then
          let sign := wedgeSign sig bi bj
          if sign ≠ 0 then
            let coeff := a.coeffs i * b.coeffs j
            let contrib := if sign < 0 then -coeff else coeff
            arr2.modify resultIdx (· + contrib)
          else arr2
        else arr2
      else arr2
  ⟨fun k => resultArray.getD k.val 0⟩

/-- Left contraction of a into b.
    O(4^n) forward iteration: only contributes when first blade contained in second. -/
def leftContract (a b : Multivector sig F) : Multivector sig F :=
  let size := 2^n
  let indices := allIndices n
  let resultArray := indices.foldl (init := Array.replicate size (0 : F)) fun arr i =>
    indices.foldl (init := arr) fun arr2 j =>
      let bi : Blade sig := ⟨BitVec.ofNat n i.val⟩
      let bj : Blade sig := ⟨BitVec.ofNat n j.val⟩
      if (bi.bits &&& bj.bits) = bi.bits && bi.grade ≤ bj.grade then
        let sign := geometricSign sig bi bj
        if sign == 0 then arr2  -- Degenerate case
        else
          let resultIdx := (bi.bits ^^^ bj.bits).toNat
          if resultIdx < size then
            let coeff := a.coeffs i * b.coeffs j
            let contrib := if sign < 0 then -coeff else coeff
            arr2.modify resultIdx (· + contrib)
          else arr2
      else arr2
  ⟨fun k => resultArray.getD k.val 0⟩

instance : Mul (Multivector sig F) := ⟨Multivector.geometricProduct⟩

infixl:65 " ⋀ᵐ " => Multivector.wedgeProduct  -- Use different symbol to avoid conflict
infixl:65 " ⌋ᵐ " => Multivector.leftContract

/-! ### Optimized Blade × Multivector Products

These specialized products are O(2^n) instead of O(4^n) for full multivector products.
Use HMul to dispatch to these when multiplying a blade with a multivector.
-/

/-- Left multiply by blade: b * m. O(2^n) - iterates only over m's indices. -/
def bladeLeftMul (b : Blade sig) (m : Multivector sig F) : Multivector sig F :=
  let size := 2^n
  let indices := allIndices n
  let resultArray := indices.foldl (init := Array.replicate size (0 : F)) fun arr j =>
    let bj : Blade sig := ⟨BitVec.ofNat n j.val⟩
    let sign := geometricSign sig b bj
    if sign == 0 then arr
    else
      let resultIdx := (b.bits ^^^ bj.bits).toNat
      if resultIdx < size then
        let coeff := m.coeffs j
        let contrib := if sign < 0 then -coeff else coeff
        arr.modify resultIdx (· + contrib)
      else arr
  ⟨fun k => resultArray.getD k.val 0⟩

/-- Right multiply by blade: m * b. O(2^n) - iterates only over m's indices. -/
def bladeRightMul (m : Multivector sig F) (b : Blade sig) : Multivector sig F :=
  let size := 2^n
  let indices := allIndices n
  let resultArray := indices.foldl (init := Array.replicate size (0 : F)) fun arr i =>
    let bi : Blade sig := ⟨BitVec.ofNat n i.val⟩
    let sign := geometricSign sig bi b
    if sign == 0 then arr
    else
      let resultIdx := (bi.bits ^^^ b.bits).toNat
      if resultIdx < size then
        let coeff := m.coeffs i
        let contrib := if sign < 0 then -coeff else coeff
        arr.modify resultIdx (· + contrib)
      else arr
  ⟨fun k => resultArray.getD k.val 0⟩

/-- HMul: Blade × Multivector → Multivector (O(2^n) specialized) -/
instance : HMul (Blade sig) (Multivector sig F) (Multivector sig F) := ⟨bladeLeftMul⟩

/-- HMul: Multivector × Blade → Multivector (O(2^n) specialized) -/
instance : HMul (Multivector sig F) (Blade sig) (Multivector sig F) := ⟨bladeRightMul⟩

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

/-- Right contraction: a ⌊ b.
    O(4^n) forward iteration: only contributes when second blade contained in first. -/
def rightContract (a b : Multivector sig F) : Multivector sig F :=
  let size := 2^n
  let indices := allIndices n
  let resultArray := indices.foldl (init := Array.replicate size (0 : F)) fun arr i =>
    indices.foldl (init := arr) fun arr2 j =>
      let bi : Blade sig := ⟨BitVec.ofNat n i.val⟩
      let bj : Blade sig := ⟨BitVec.ofNat n j.val⟩
      if (bj.bits &&& bi.bits) = bj.bits && bj.grade ≤ bi.grade then
        let sign := geometricSign sig bi bj
        if sign == 0 then arr2  -- Degenerate case
        else
          let resultIdx := (bi.bits ^^^ bj.bits).toNat
          if resultIdx < size then
            let coeff := a.coeffs i * b.coeffs j
            let contrib := if sign < 0 then -coeff else coeff
            arr2.modify resultIdx (· + contrib)
          else arr2
      else arr2
  ⟨fun k => resultArray.getD k.val 0⟩

infixl:65 " ⌊ᵐ " => Multivector.rightContract

/-! ### Fat Dot Product -/

/-- Fat dot / inner product: sum of left and right contractions minus scalar product -/
def fatDot (a b : Multivector sig F) : Multivector sig F :=
  (a ⌋ᵐ b).add (a ⌊ᵐ b)

infixl:65 " ⋅ᵐ " => Multivector.fatDot

/-! ### Regressive Product (Meet/Vee) -/

/-- Regressive product: a ∨ b = ⋆(⋆a ∧ ⋆b)
    The dual of the wedge product, computes the meet (intersection).
    In PGA: the join of two geometric objects. -/
def regressiveProduct (a b : Multivector sig F) : Multivector sig F :=
  ⋆ᵐ(⋆ᵐa ⋀ᵐ ⋆ᵐb)

infixl:65 " ⋁ᵐ " => Multivector.regressiveProduct

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

/-! ## Float-specific Operations

Float Ring/Field instances are defined in Grassmann.Proof with sorry_proof.
Here we only define Float-specific computational operations.
-/

namespace Multivector

-- Float Ring/Field instance imported from Grassmann.Proof

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

variable {n : ℕ} {sig : Signature n}
variable [Ring F]

/-- Create a vector from an array of components (generic n-dimensional) -/
def vectorFromArray (components : Array F) : Multivector sig F :=
  (List.finRange n).foldl (init := Multivector.zero) fun acc i =>
    let c := components.getD i.val 0
    acc.add ((Multivector.basis i : Multivector sig F).smul c)

/-- Create a vector from a function giving each component (generic n-dimensional) -/
def vectorFromFn (f : Fin n → F) : Multivector sig F :=
  (List.finRange n).foldl (init := Multivector.zero) fun acc i =>
    acc.add ((Multivector.basis i : Multivector sig F).smul (f i))

/-- Create a 2D vector from components -/
def vector2 (x y : F) : Multivector R2 F :=
  Multivector.basis ⟨0, by omega⟩ |>.smul x |>.add
  (Multivector.basis ⟨1, by omega⟩ |>.smul y)

/-- Create a 3D vector from components -/
def vector3 (x y z : F) : Multivector R3 F :=
  Multivector.basis ⟨0, by omega⟩ |>.smul x |>.add
  (Multivector.basis ⟨1, by omega⟩ |>.smul y) |>.add
  (Multivector.basis ⟨2, by omega⟩ |>.smul z)

/-- Create a 4D vector from components -/
def vector4 (x y z w : F) : Multivector (Signature.euclidean 4) F :=
  Multivector.basis ⟨0, by omega⟩ |>.smul x |>.add
  (Multivector.basis ⟨1, by omega⟩ |>.smul y) |>.add
  (Multivector.basis ⟨2, by omega⟩ |>.smul z) |>.add
  (Multivector.basis ⟨3, by omega⟩ |>.smul w)

/-- Create a bivector from pairs of (basis indices, coefficient).
    Each pair (i, j, c) contributes c * (eᵢ ∧ eⱼ) to the result. -/
def bivectorFromPairs (pairs : List (Fin n × Fin n × F)) : Multivector sig F :=
  pairs.foldl (init := Multivector.zero) fun acc (i, j, c) =>
    let ei : Multivector sig F := Multivector.basis i
    let ej : Multivector sig F := Multivector.basis j
    acc.add ((ei ⋀ᵐ ej).smul c)

/-- Create a bivector in R3 from coefficients (e12, e13, e23) -/
def bivector3 (xy xz yz : F) : Multivector R3 F :=
  let e12 : Multivector R3 F := ⟨fun i => if i.val = 0b011 then 1 else 0⟩
  let e13 : Multivector R3 F := ⟨fun i => if i.val = 0b101 then 1 else 0⟩
  let e23 : Multivector R3 F := ⟨fun i => if i.val = 0b110 then 1 else 0⟩
  e12.smul xy |>.add (e13.smul xz) |>.add (e23.smul yz)

end Convenience

/-! ## GAlgebra Instance -/

instance [Ring F] : GAlgebra sig (Multivector sig F) F where
  basisVector := Multivector.basis
  scalar := Multivector.scalar
  zero := Multivector.zero
  one := Multivector.one
  blade bits := Multivector.ofBlade ⟨bits⟩
  mul := Multivector.geometricProduct
  wedge := Multivector.wedgeProduct
  leftContract := Multivector.leftContract
  rightContract := Multivector.rightContract
  reverse := Multivector.reverse
  involute := Multivector.involute
  conjugate := Multivector.conjugate
  scalarPart := Multivector.scalarPart
  add := Multivector.add
  neg := Multivector.neg
  smul := Multivector.smul
  gradeProject := Multivector.gradeProject

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

-- Regressive product: e12 ∨ e23 = e2
#eval let e12v := (Multivector.ofBlade (e12 : Blade R3) : Multivector R3 Int)
      let e23v := (Multivector.ofBlade (e23 : Blade R3) : Multivector R3 Int)
      (e12v ⋁ᵐ e23v).coeff (e2 : Blade R3)

-- Test scalar multiplication with •
#eval let e1v := (Multivector.ofBlade (e1 : Blade R3) : Multivector R3 Int)
      ((3 : Int) • e1v).coeff (e1 : Blade R3)  -- 3

-- Test HMul: Blade × Multivector (O(2^n) specialized)
#eval let mv : Multivector R3 Int := Multivector.ofBlade e1 + Multivector.ofBlade e2
      let result := (e1 : Blade R3) * mv  -- Uses bladeLeftMul, O(2^n)
      (result.coeff Blade.scalar, result.coeff e12)  -- (1, 1)

-- Test HMul: Multivector × Blade (O(2^n) specialized)
#eval let mv : Multivector R3 Int := Multivector.ofBlade e1 + Multivector.ofBlade e2
      let result := mv * (e1 : Blade R3)  -- Uses bladeRightMul, O(2^n)
      (result.coeff Blade.scalar, result.coeff e12)  -- (1, -1)

/-! ## Chain Type (Homogeneous Grade Multivector)

A Chain is a multivector restricted to a single grade.
More efficient for grade-specific operations like rotors (grade 0+2).
-/

/-- A Chain is a grade-k multivector: all terms have the same grade -/
structure Chain (sig : Signature n) (k : ℕ) (F : Type*) where
  /-- Coefficients indexed by grade-k blade bitmask -/
  coeffs : (b : Blade sig) → b.grade = k → F

namespace Chain

variable [Ring F]

/-- Zero chain -/
def zero : Chain sig k F := ⟨fun _ _ => 0⟩

/-- Convert chain to full multivector -/
def toMultivector (c : Chain sig k F) : Multivector sig F :=
  ⟨fun i =>
    let b : Blade sig := ⟨BitVec.ofNat n i.val⟩
    if h : b.grade = k then c.coeffs b h else 0⟩

/-- Extract grade-k chain from multivector -/
def ofMultivector (m : Multivector sig F) (k : ℕ) : Chain sig k F :=
  ⟨fun b _ => m.coeff b⟩

/-- Scalar chain (grade 0) -/
def scalar (x : F) : Chain sig 0 F :=
  ⟨fun b _ =>
    if b.bits = 0 then x else 0⟩

/-- Add chains of same grade -/
def add (a b : Chain sig k F) : Chain sig k F :=
  ⟨fun blade h => a.coeffs blade h + b.coeffs blade h⟩

/-- Negate chain -/
def neg (c : Chain sig k F) : Chain sig k F :=
  ⟨fun blade h => -c.coeffs blade h⟩

/-- Scale chain -/
def smul (x : F) (c : Chain sig k F) : Chain sig k F :=
  ⟨fun blade h => x * c.coeffs blade h⟩

instance : Zero (Chain sig k F) := ⟨Chain.zero⟩
instance : Add (Chain sig k F) := ⟨Chain.add⟩
instance : Neg (Chain sig k F) := ⟨Chain.neg⟩
instance : SMul F (Chain sig k F) := ⟨Chain.smul⟩

end Chain

/-! ## Tensor Operators

Projector, Dyadic, and related tensor operator types from AbstractTensors.jl
-/

/-- A Projector represents a projection operator P where P² = P.
    Geometrically: projects onto a subspace defined by a blade B.
    P_B(x) = (x ⌋ B) ⌊ B⁻¹ -/
structure Projector (sig : Signature n) (F : Type*) where
  /-- The blade defining the subspace to project onto -/
  blade : Blade sig
  /-- Coefficient (usually 1 for unit projectors) -/
  coeff : F

namespace Projector

variable {n : ℕ} {sig : Signature n} {F : Type*} [Ring F]

/-- Create projector from a blade -/
def ofBlade (b : Blade sig) : Projector sig F := ⟨b, 1⟩

/-- Identity projector (onto full space) -/
def identity : Projector sig F := ⟨⟨pseudoscalar⟩, 1⟩

/-- Null projector (projects to zero) -/
def null : Projector sig F := ⟨⟨0⟩, 0⟩

/-- Rank of projector (grade of blade) -/
def rank (p : Projector sig F) : Nat := p.blade.grade

/-- Complement projector: I - P -/
def complement (p : Projector sig F) : Projector sig F :=
  ⟨p.blade.complement, p.coeff⟩

end Projector

/-- A Dyadic represents a tensor product of two vectors: a ⊗ b.
    Acts on vectors v as: (a ⊗ b)(v) = a(b · v) -/
structure Dyadic (sig : Signature n) (F : Type*) where
  /-- Left vector -/
  left : Multivector sig F
  /-- Right vector -/
  right : Multivector sig F

namespace Dyadic

variable {n : ℕ} {sig : Signature n} {F : Type*} [Ring F]

/-- Create dyadic from two vectors -/
def ofVectors (a b : Multivector sig F) : Dyadic sig F := ⟨a, b⟩

/-- Apply dyadic to a vector: (a ⊗ b)(v) = a(b · v) -/
def apply (d : Dyadic sig F) (v : Multivector sig F) : Multivector sig F :=
  let dotProduct := (d.right ⌋ᵐ v).scalarPart
  d.left.smul dotProduct

/-- Add two dyadics -/
def add (d1 d2 : Dyadic sig F) : List (Dyadic sig F) :=
  [d1, d2]  -- Represent as list (full addition needs DyadicChain)

/-- Scale a dyadic -/
def smul (s : F) (d : Dyadic sig F) : Dyadic sig F :=
  ⟨d.left.smul s, d.right⟩

/-- Transpose: (a ⊗ b)ᵀ = b ⊗ a -/
def transpose (d : Dyadic sig F) : Dyadic sig F :=
  ⟨d.right, d.left⟩

/-- Trace: Tr(a ⊗ b) = a · b -/
def trace (d : Dyadic sig F) : F :=
  (d.left ⌋ᵐ d.right).scalarPart

/-- Frobenius norm squared: ||a ⊗ b||² = |a|²|b|² -/
def normSq (d : Dyadic sig F) : F :=
  d.left.normSq * d.right.normSq

end Dyadic

/-- Tensor product notation for dyadics -/
infixl:70 " ⊗ᵈ " => Dyadic.ofVectors

/-- A DyadicChain is a sum of dyadics (full rank-k tensor) -/
structure DyadicChain (sig : Signature n) (F : Type*) where
  terms : List (Dyadic sig F)

namespace DyadicChain

variable {n : ℕ} {sig : Signature n} {F : Type*} [Ring F]

/-- Empty chain -/
def empty : DyadicChain sig F := ⟨[]⟩

/-- Single dyadic -/
def single (d : Dyadic sig F) : DyadicChain sig F := ⟨[d]⟩

/-- Add to chain -/
def add (c : DyadicChain sig F) (d : Dyadic sig F) : DyadicChain sig F :=
  ⟨d :: c.terms⟩

/-- Apply chain to vector -/
def apply (c : DyadicChain sig F) (v : Multivector sig F) : Multivector sig F :=
  c.terms.foldl (init := Multivector.zero) fun acc d =>
    acc.add (d.apply v)

/-- Rank (number of terms) -/
def rank (c : DyadicChain sig F) : Nat := c.terms.length

end DyadicChain

/-- Outermorphism: extends a linear map to act on all grades.
    If f: V → W is linear, then Λf: ΛV → ΛW preserves grade and
    Λf(a ∧ b) = Λf(a) ∧ Λf(b). -/
structure Outermorphism (sig : Signature n) (F : Type*) where
  /-- Matrix representation (action on basis vectors) -/
  matrix : Fin n → Multivector sig F

namespace Outermorphism

variable {n : ℕ} {sig : Signature n} {F : Type*} [Ring F]

/-- Identity outermorphism -/
def identity : Outermorphism sig F :=
  ⟨fun i => Multivector.basis i⟩

/-- Apply to a vector -/
def applyVector (o : Outermorphism sig F) (v : Multivector sig F) : Multivector sig F :=
  (List.finRange n).foldl (init := Multivector.zero) fun acc i =>
    let coeff := v.coeff (Blade.basis i)
    acc.add ((o.matrix i).smul coeff)

/-- Compose two outermorphisms -/
def compose (o1 o2 : Outermorphism sig F) : Outermorphism sig F :=
  ⟨fun i => o1.applyVector (o2.matrix i)⟩

end Outermorphism

/-! ## Tensor Operator Tests -/

section TensorTests

-- Projector test
#eval let p : Projector R3 Float := Projector.ofBlade (e12 : Blade R3)
      p.rank  -- 2

-- Dyadic test
#eval let v1 := vector3 1.0 0.0 0.0
      let v2 := vector3 0.0 1.0 0.0
      let d : Dyadic R3 Float := v1 ⊗ᵈ v2
      d.trace  -- 0.0 (orthogonal vectors)

end TensorTests

/-! ## Repr/ToString for Debugging -/

/-- Show non-zero coefficients of a multivector -/
def Multivector.toTerms (m : Multivector sig Float) (tol : Float := 1e-10) : List (Float × Nat) :=
  (List.finRange (2^n)).filterMap fun i =>
    let c := m.coeffs i
    if Float.abs c > tol then some (c, i.val) else none

/-- Simple string representation -/
instance : ToString (Multivector R3 Float) where
  toString m :=
    let terms := m.toTerms
    if terms.isEmpty then "0"
    else terms.foldl (init := "") fun acc (c, i) =>
      let blade := match i with
        | 0 => "1"
        | 1 => "e1"
        | 2 => "e2"
        | 3 => "e12"
        | 4 => "e3"
        | 5 => "e13"
        | 6 => "e23"
        | 7 => "e123"
        | _ => s!"e[{i}]"
      let sign := if c >= 0 && acc.length > 0 then " + " else if c < 0 then " - " else ""
      let coeff := Float.abs c
      let coeffStr := if coeff == 1 && i != 0 then "" else s!"{coeff}"
      acc ++ sign ++ coeffStr ++ blade

/-! ## Geometric Division ⊘

Geometric division solves x = a·y for x given a and y:
  x ⊘ y = x · y⁻¹ = x · y† / (y · y†)

This is the right inverse operation: (a·b) ⊘ b = a when b is invertible.

From Grassmann.jl: Used for solving geometric equations, finding rotors, etc.
-/

namespace Multivector

/-- Right geometric division: a ⊘ b = a · b⁻¹
    Solves for x in the equation x·b = a
    Requires b to have non-zero norm. -/
def geometricDivRight [Ring F] [Div F]
    (a b : Multivector sig F) : Multivector sig F :=
  let brev := b†
  let normSq := (b * brev).scalarPart
  (a * brev).smul (1 / normSq)

/-- Left geometric division: a ⊘ₗ b = b⁻¹ · a
    Solves for x in the equation b·x = a -/
def geometricDivLeft [Ring F] [Div F]
    (a b : Multivector sig F) : Multivector sig F :=
  let brev := b†
  let normSq := (brev * b).scalarPart
  (brev * a).smul (1 / normSq)

/-- Project multivector a onto blade/multivector B.
    proj_B(a) = (a ⌋ B) · B⁻¹ -/
def project [Ring F] [Div F]
    (a B : Multivector sig F) : Multivector sig F :=
  geometricDivRight (a ⌋ᵐ B) B

/-- Reject multivector a from blade/multivector B.
    rej_B(a) = a - proj_B(a) -/
def reject [Ring F] [Div F]
    (a B : Multivector sig F) : Multivector sig F :=
  a.sub (project a B)

end Multivector

/-- Division operator (right division): a ⊘ b = a · b⁻¹ -/
infixl:70 " ⊘ᵐ " => Multivector.geometricDivRight

/-- Left division operator: a ⊘ₗ b = b⁻¹ · a -/
infixl:70 " ⊘ₗᵐ " => Multivector.geometricDivLeft

/-! ## Cross Product (3D specific) -/

/-- Cross product in 3D: a × b = ⋆(a ∧ b).
    Maps two vectors to a vector (the dual of their bivector). -/
def crossProduct3D [Ring F]
    (a b : Multivector R3 F) : Multivector R3 F :=
  let wedge := a ⋀ᵐ b
  -- Hodge dual in 3D maps bivectors to vectors
  -- e12 → e3, e13 → -e2, e23 → e1
  ⟨fun i =>
    match i.val with
    | 0 => wedge.coeffs ⟨6, by decide⟩   -- e1 ← e23
    | 1 => -(wedge.coeffs ⟨5, by decide⟩)  -- e2 ← -e13
    | 2 => wedge.coeffs ⟨3, by decide⟩   -- e3 ← e12
    | _ => 0⟩

infixl:70 " ×₃ " => crossProduct3D

/-! ## Geometric Division Tests -/

section GeometricDivisionTests

-- Test geometric division: (a*b) ⊘ b should give a
#eval! let a := vector3 1.0 2.0 3.0
       let b := vector3 1.0 0.0 0.0
       let prod := a * b
       let recovered := prod ⊘ᵐ b
       (recovered.coeff (e1 : Blade R3),
        recovered.coeff (e2 : Blade R3),
        recovered.coeff (e3 : Blade R3))
-- Expected: approximately (1, 2, 3)

-- Test projection
#eval! let v := vector3 1.0 1.0 0.0
       let u := vector3 1.0 0.0 0.0  -- x-axis
       let proj := Multivector.project v u
       (proj.coeff (e1 : Blade R3),
        proj.coeff (e2 : Blade R3))
-- Expected: (1, 0) - projection onto x-axis

-- Test cross product
#eval! let a := vector3 1.0 0.0 0.0  -- e1
       let b := vector3 0.0 1.0 0.0  -- e2
       let c := a ×₃ b               -- should be e3
       (c.coeff (e1 : Blade R3),
        c.coeff (e2 : Blade R3),
        c.coeff (e3 : Blade R3))
-- Expected: (0, 0, 1)

end GeometricDivisionTests

end Grassmann
