/-
  Grassmann/SpecialFunctions.lean - Special functions and utilities

  Port of Grassmann.jl's special functions including:
  - Complex number embedding
  - Quaternion operations
  - Dual numbers
  - Split-complex numbers
  - Scalar extraction utilities
-/
import Grassmann.Multivector

namespace Grassmann

variable {n : ℕ} {sig : Signature n} {F : Type*}
variable [Ring F] [Div F]

/-! ## Complex Numbers in Cl(0,1)

Complex numbers can be embedded in the Clifford algebra Cl(0,1) where i² = -1.
We use the signature with one negative dimension.
-/

/-- Complex number signature: Cl(0,1) where e₁² = -1 -/
abbrev C_sig : Signature 1 := ℂ_sig

/-- Complex number as a multivector: z = a + bi where i = e₁ -/
def Complex.ofPair (re im : F) : Multivector C_sig F :=
  (Multivector.scalar re) + (Multivector.basis ⟨0, by omega⟩).smul im

/-- Real part of a complex number (scalar part) -/
def Complex.re (z : Multivector C_sig F) : F := z.scalarPart

/-- Imaginary part (e₁ coefficient) -/
def Complex.im (z : Multivector C_sig F) : F :=
  z.coeff ⟨BitVec.ofNat 1 1⟩

/-- Complex conjugate: a + bi → a - bi -/
def Complex.conj (z : Multivector C_sig F) : Multivector C_sig F :=
  (Multivector.scalar (Complex.re z)) - (Multivector.basis ⟨0, by omega⟩).smul (Complex.im z)

/-- Squared modulus: |z|² = z * z̄ -/
def Complex.normSq (z : Multivector C_sig F) : F :=
  Complex.re z * Complex.re z + Complex.im z * Complex.im z

/-! ## Quaternions in Cl(0,2)

Quaternions can be embedded in Cl(0,2) where e₁² = e₂² = -1.
Standard quaternion basis: 1, i=e₁, j=e₂, k=e₁₂
-/

/-- Quaternion signature: Cl(0,2) -/
abbrev H_sig : Signature 2 := ℍ_sig

/-- Quaternion from components: a + bi + cj + dk -/
def Quaternion.ofComponents (a b c d : F) : Multivector H_sig F :=
  let one := Multivector.scalar a
  let i := (Multivector.basis ⟨0, by omega⟩).smul b  -- e₁
  let j := (Multivector.basis ⟨1, by omega⟩).smul c  -- e₂
  let k := (Multivector.ofBlade ⟨BitVec.ofNat 2 3⟩).smul d  -- e₁₂
  one + i + j + k

/-- Scalar part of quaternion -/
def Quaternion.scalar (q : Multivector H_sig F) : F := q.scalarPart

/-- i component (e₁ coefficient) -/
def Quaternion.i (q : Multivector H_sig F) : F :=
  q.coeff ⟨BitVec.ofNat 2 1⟩

/-- j component (e₂ coefficient) -/
def Quaternion.j (q : Multivector H_sig F) : F :=
  q.coeff ⟨BitVec.ofNat 2 2⟩

/-- k component (e₁₂ coefficient) -/
def Quaternion.k (q : Multivector H_sig F) : F :=
  q.coeff ⟨BitVec.ofNat 2 3⟩

/-- Quaternion conjugate: a + bi + cj + dk → a - bi - cj - dk -/
def Quaternion.conj (q : Multivector H_sig F) : Multivector H_sig F :=
  Quaternion.ofComponents (Quaternion.scalar q)
    (-(Quaternion.i q)) (-(Quaternion.j q)) (-(Quaternion.k q))

/-- Squared norm: |q|² = q * q̄ -/
def Quaternion.normSq (q : Multivector H_sig F) : F :=
  let a := Quaternion.scalar q
  let b := Quaternion.i q
  let c := Quaternion.j q
  let d := Quaternion.k q
  a*a + b*b + c*c + d*d

/-! ## Dual Numbers in Cl(0,0,1)

Dual numbers have the form a + bε where ε² = 0.
Useful for automatic differentiation.
-/

-- Note: Dual numbers require a degenerate signature (metric with zeros)
-- For now, we simulate with a simple structure

/-- Dual number (simplified representation, not using Clifford algebra) -/
structure Dual (F : Type*) where
  re : F  -- real part
  du : F  -- dual part (coefficient of ε)

namespace Dual

variable [Ring F]

def zero : Dual F := ⟨0, 0⟩
def one : Dual F := ⟨1, 0⟩
def epsilon : Dual F := ⟨0, 1⟩

def add (a b : Dual F) : Dual F := ⟨a.re + b.re, a.du + b.du⟩
def neg (a : Dual F) : Dual F := ⟨-a.re, -a.du⟩
def sub (a b : Dual F) : Dual F := ⟨a.re - b.re, a.du - b.du⟩

/-- Dual multiplication: (a + bε)(c + dε) = ac + (ad + bc)ε -/
def mul (a b : Dual F) : Dual F := ⟨a.re * b.re, a.re * b.du + a.du * b.re⟩

instance : Zero (Dual F) := ⟨Dual.zero⟩
instance : One (Dual F) := ⟨Dual.one⟩
instance : Add (Dual F) := ⟨Dual.add⟩
instance : Neg (Dual F) := ⟨Dual.neg⟩
instance : Sub (Dual F) := ⟨Dual.sub⟩
instance : Mul (Dual F) := ⟨Dual.mul⟩

end Dual

/-! ## Split-Complex Numbers in Cl(1,0)

Split-complex (hyperbolic) numbers: a + bj where j² = +1.
Uses signature Cl(1,0).
-/

/-- Split-complex signature: Cl(1,0) where e₁² = +1 -/
abbrev SplitC_sig : Signature 1 := R1

/-- Split-complex from components: a + bj -/
def SplitComplex.ofPair (re hyp : F) : Multivector SplitC_sig F :=
  (Multivector.scalar re) + (Multivector.basis ⟨0, by omega⟩).smul hyp

/-- Real part -/
def SplitComplex.re (z : Multivector SplitC_sig F) : F := z.scalarPart

/-- Hyperbolic part (j coefficient) -/
def SplitComplex.hyp (z : Multivector SplitC_sig F) : F :=
  z.coeff ⟨BitVec.ofNat 1 1⟩

/-- Split-complex conjugate: a + bj → a - bj -/
def SplitComplex.conj (z : Multivector SplitC_sig F) : Multivector SplitC_sig F :=
  (Multivector.scalar (SplitComplex.re z)) - (Multivector.basis ⟨0, by omega⟩).smul (SplitComplex.hyp z)

/-- Squared "norm": z * z̄ = a² - b² (can be negative!) -/
def SplitComplex.normSq (z : Multivector SplitC_sig F) : F :=
  SplitComplex.re z * SplitComplex.re z - SplitComplex.hyp z * SplitComplex.hyp z

/-! ## Utility Functions -/

/-- Check if multivector is purely scalar (Float version using tolerance) -/
def isScalar (m : Multivector sig Float) (tol : Float := 1e-10) : Bool :=
  let nonScalar := m - Multivector.scalar m.scalarPart
  nonScalar.normSq < tol

/-- Check if multivector is purely a vector (grade 1, Float version) -/
def isVector (m : Multivector sig Float) (tol : Float := 1e-10) : Bool :=
  let nonVector := m - m.gradeProject 1
  nonVector.normSq < tol

/-- Check if multivector is purely a bivector (grade 2, Float version) -/
def isBivector (m : Multivector sig Float) (tol : Float := 1e-10) : Bool :=
  let nonBivector := m - m.gradeProject 2
  nonBivector.normSq < tol

/-- Extract vector components as a list -/
def vectorComponents (m : Multivector sig F) : List F :=
  (List.finRange n).map fun i =>
    m.coeff ⟨BitVec.ofNat n (1 <<< i.val)⟩

/-- Create vector from components -/
def vectorFromComponents (cs : List F) : Multivector sig F :=
  (List.finRange n).zip cs |>.foldl (init := Multivector.zero) fun acc (i, c) =>
    acc + (Multivector.basis i).smul c

/-! ## Scalar Extraction -/

/-- Extract all non-zero coefficients -/
def nonZeroCoeffs [DecidableEq F] (m : Multivector sig F) : List (Blade sig × F) :=
  (List.finRange (2^n)).filterMap fun i =>
    let b : Blade sig := ⟨BitVec.ofNat n i.val⟩
    let c := m.coeff b
    if c = 0 then none else some (b, c)

/-! ## Tests -/

section Tests

-- Complex number tests
#eval! let z := Complex.ofPair 3.0 4.0  -- 3 + 4i
       (Complex.re z, Complex.im z)  -- (3, 4)

#eval! let z := Complex.ofPair 3.0 4.0
       Complex.normSq z  -- 9 + 16 = 25

-- Quaternion tests
#eval! let q := Quaternion.ofComponents 1.0 2.0 3.0 4.0
       (Quaternion.scalar q, Quaternion.i q, Quaternion.j q, Quaternion.k q)  -- (1, 2, 3, 4)

#eval! let q := Quaternion.ofComponents 1.0 0.0 0.0 0.0
       Quaternion.normSq q  -- 1

-- Verify i² = -1 in C_sig
#eval! let i : Multivector C_sig Float := Multivector.basis ⟨0, by omega⟩
       (i * i).scalarPart  -- -1

-- Verify j² = +1 in SplitC_sig
#eval! let j : Multivector SplitC_sig Float := Multivector.basis ⟨0, by omega⟩
       (j * j).scalarPart  -- +1

-- Dual number test
#eval! let x : Dual Float := ⟨3.0, 1.0⟩  -- x = 3 + ε (for f(x) = x at x=3)
       let sq := x * x  -- x² = 9 + 6ε (derivative of x² is 2x = 6)
       (sq.re, sq.du)  -- (9, 6)

end Tests

end Grassmann
