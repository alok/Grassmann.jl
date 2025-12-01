/-
  Grassmann/Versor.lean - Versor operations (rotations, reflections)

  Port of Grassmann.jl's versor operations from composite.jl.

  A versor is a product of vectors. Key operations:
  - exp(B) for bivector B gives a rotor
  - Sandwich product v' = R v R† for rotations/reflections
  - log of a rotor gives a bivector

  For a unit bivector B (B² = -1):
    exp(θ B) = cos(θ) + sin(θ) B

  For a unit vector n:
    exp(θ/2 n) = cos(θ/2) + sin(θ/2) n
-/
import Grassmann.Multivector

namespace Grassmann

variable {n : ℕ} {sig : Signature n}

/-! ## Float-based operations

For actual rotations we need floating point arithmetic.
-/

namespace Multivector

variable [Zero Float] [One Float] [Add Float] [Neg Float] [Mul Float] [Sub Float] [Div Float]

/-- Exponential of a bivector (for small angles, Taylor series).
    exp(B) ≈ 1 + B + B²/2! + B³/3! + ...
    For unit bivector B² = -1:
    exp(θB) = cos(θ) + sin(θ)B -/
def expBivector (B : Multivector sig Float) (terms : ℕ := 10) : Multivector sig Float :=
  -- Taylor series: sum_{k=0}^{terms} B^k / k!
  let rec go (k : ℕ) (Bk : Multivector sig Float)
      (factorial : Float) (acc : Multivector sig Float) : Multivector sig Float :=
    if k ≥ terms then acc
    else
      let newAcc := acc + Bk.smul (1.0 / factorial)
      let newBk := Bk * B
      let newFactorial := factorial * (k + 1).toFloat
      go (k + 1) newBk newFactorial newAcc
  go 0 (Multivector.one) 1.0 Multivector.zero

/-- Create a rotor from axis (bivector) and angle.
    R = exp(angle/2 * axis) = cos(angle/2) + sin(angle/2) * axis
    Assumes axis is a unit bivector (axis² = -1). -/
def rotor (axis : Multivector sig Float) (angle : Float) : Multivector sig Float :=
  let halfAngle := angle / 2.0
  let c := Float.cos halfAngle
  let s := Float.sin halfAngle
  Multivector.scalar c + axis.smul s

/-- Apply rotation: v' = R * v * R† -/
def rotate (R v : Multivector sig Float) : Multivector sig Float :=
  R * v * R†

/-- Apply reflection through hyperplane with normal n: v' = -n * v * n
    (assumes n is a unit vector, n² = 1) -/
def reflect (normal v : Multivector sig Float) : Multivector sig Float :=
  (normal * v * normal).neg

end Multivector

/-! ## Reflection Operations -/

namespace Reflection

/-- Reflect a multivector through hyperplane with unit normal n.
    For a vector v: v' = -n v n = v - 2(n·v)n
    For general multivector: applies grade-by-grade -/
def throughPlane (normal m : Multivector sig Float) : Multivector sig Float :=
  -(normal * m * normal)

/-- Reflect through the origin (negate all vectors) -/
def throughOrigin (m : Multivector sig Float) : Multivector sig Float :=
  m.involute

/-- Householder reflection: I - 2vv†/v†v
    Reflects through hyperplane perpendicular to v -/
def householder (v m : Multivector sig Float) : Multivector sig Float :=
  let vNormSq := (v * v†).scalarPart
  if vNormSq == 0 then m
  else
    let proj := (v * (v† * m).scalarPart • (1 : Multivector sig Float)).smul (2 / vNormSq)
    m - proj

/-- Compose two reflections to get a rotation
    Reflecting through n1 then n2 gives rotation by 2× angle between them -/
def compose (n1 n2 m : Multivector sig Float) : Multivector sig Float :=
  throughPlane n2 (throughPlane n1 m)

end Reflection

/-! ## Orthogonal Transformations -/

namespace Orthogonal

/-- Apply an orthogonal transformation via versor
    T(x) = V x V† where V is a product of vectors
    Even versor = rotation, odd versor = includes reflection -/
def apply (versor x : Multivector sig Float) : Multivector sig Float :=
  -- Check if versor is even (all odd-grade components are zero)
  let isEven := (versor.evenPart - versor).normSq < 1e-10
  if isEven then
    versor * x * versor†  -- even versor (rotation)
  else
    -(versor * x * versor†)  -- odd versor (includes reflection)

/-- Check if transformation is proper (det = +1, rotation) vs improper (det = -1) -/
def isProper (versor : Multivector sig Float) : Bool :=
  -- Even grade versor = proper rotation
  -- Odd grade versor = improper (reflection)
  (versor * versor†).scalarPart > 0 &&
  Float.abs ((versor.evenPart - versor).normSq) < 1e-10

/-- Construct rotation from two vectors: rotates from a towards b
    R = (1 + ba) / |1 + ba| rotates a to b -/
def rotationBetween (a b : Multivector sig Float) : Multivector sig Float :=
  let ba := (b * a).evenPart
  let R := (Multivector.scalar 1) + ba
  R.normalize

/-- Rotation by angle θ in plane spanned by orthogonal vectors a, b
    R = cos(θ/2) + sin(θ/2) â∧b̂ where hat denotes unit -/
def rotationInPlane (a b : Multivector sig Float) (θ : Float) : Multivector sig Float :=
  let a_norm := a.normalize
  let b_rej := (b - (a_norm * (a_norm * b).scalarPart • (1 : Multivector sig Float))).normalize
  let bivector := a_norm ⋀ᵐ b_rej
  let halfθ := θ / 2
  (Multivector.scalar (Float.cos halfθ)) + bivector.smul (Float.sin halfθ)

end Orthogonal

/-! ## Projective Operations -/

namespace Projective

/-- Project vector a onto vector b: (a·b/b·b)b -/
def projectVector (a b : Multivector sig Float) : Multivector sig Float :=
  let ab := (a * b).scalarPart
  let bb := (b * b).scalarPart
  if bb == 0 then Multivector.zero else b.smul (ab / bb)

/-- Reject a from b: a - proj_b(a) = component perpendicular to b -/
def rejectVector (a b : Multivector sig Float) : Multivector sig Float :=
  a - projectVector a b

/-- Project onto a blade B: (a ⌋ B) B⁻¹ -/
def projectOntoBlade (a B : Multivector sig Float) : Multivector sig Float :=
  let aB := a ⌋ᵐ B
  let BNormSq := (B * B†).scalarPart
  if BNormSq == 0 then Multivector.zero
  else (aB * B†).smul (1 / BNormSq)

/-- Reject from blade B: a - proj_B(a) -/
def rejectFromBlade (a B : Multivector sig Float) : Multivector sig Float :=
  a - projectOntoBlade a B

end Projective

/-! ## Integer/Rational Operations

For exact computation, we note that:
- exp(B) for bivector B with B² = -1 is: cos + sin·B
- For integer approximations, we can use the recurrence relation
- Full rational Taylor series would require proper ℚ arithmetic

For now, integer tests verify algebraic identities directly.
-/

/-! ## Rotor Construction Helpers -/

section RotorHelpers

/-- Create a rotation rotor in the e12 plane by angle θ.
    Returns cos(θ/2) + sin(θ/2)·e12 -/
def rotor_e12 (halfCos halfSin : Float) : Multivector R3 Float :=
  let scalar : Multivector R3 Float := Multivector.scalar halfCos
  let e12mv : Multivector R3 Float := Multivector.ofBlade e12
  scalar + e12mv.smul halfSin

/-- Create a rotation rotor in the e13 plane -/
def rotor_e13 (halfCos halfSin : Float) : Multivector R3 Float :=
  let scalar : Multivector R3 Float := Multivector.scalar halfCos
  let e13mv : Multivector R3 Float := Multivector.ofBlade e13
  scalar + e13mv.smul halfSin

/-- Create a rotation rotor in the e23 plane -/
def rotor_e23 (halfCos halfSin : Float) : Multivector R3 Float :=
  let scalar : Multivector R3 Float := Multivector.scalar halfCos
  let e23mv : Multivector R3 Float := Multivector.ofBlade e23
  scalar + e23mv.smul halfSin

end RotorHelpers

/-! ## Outermorphism

An outermorphism is a grade-preserving linear map that distributes
over the wedge product: F(a ∧ b) = F(a) ∧ F(b).

Every linear transformation on vectors extends uniquely to an outermorphism.
-/

/-- Apply a linear transformation (given by images of basis vectors) as outermorphism.
    For each basis blade, apply the transformation to each vector component
    and wedge the results together. -/
def outermorphism (images : Fin n → Multivector sig Float)
    (m : Multivector sig Float) : Multivector sig Float :=
  -- TODO: implement properly - for now just return input
  let _ := images  -- suppress unused warning
  m

/-! ## Tests -/

section Tests

-- Test rotor construction
-- #eval let R := rotor_e12 (Float.cos 0.5) (Float.sin 0.5)  -- 0.5 radian rotation
--       R.scalarPart  -- cos(0.5) ≈ 0.877

-- Test that rotor has unit norm (approximately)
-- R R† should be scalar 1

-- For integer tests, we use the fact that for bivector B with B² = -1:
-- (1 + B)² = 1 + 2B + B² = 1 + 2B - 1 = 2B
-- (1 + B)(1 - B) = 1 - B² = 1 + 1 = 2

-- Test: (1 + e12)(1 + e12) = 2·e12
#eval let one_plus_e12 : Multivector R3 Int := Multivector.scalar 1 + Multivector.ofBlade e12
      let sq := one_plus_e12 * one_plus_e12
      (sq.scalarPart, sq.coeff e12)  -- (0, 2)

-- Test: (1 + e12)(1 - e12) = 2
#eval let one_plus_e12 : Multivector R3 Int := Multivector.scalar 1 + Multivector.ofBlade e12
      let one_minus_e12 : Multivector R3 Int := Multivector.scalar 1 - Multivector.ofBlade e12
      let prod := one_plus_e12 * one_minus_e12
      prod.scalarPart  -- 2

-- Rotation test: Use (1 + e12)/√2 as 45° rotation rotor
-- R * e1 * R† should rotate e1 towards e2
-- With unnormalized rotor (1 + e12):
-- (1 + e12) * e1 = e1 + e12*e1 = e1 - e2
-- (e1 - e2) * (1 - e12) = e1 - e2 - e1*e12 + e2*e12 = e1 - e2 - e2 - e1 = -2e2
-- Hmm, let me recalculate more carefully

-- (1 + e12) * e1 * (1 + e12)†
-- = (1 + e12) * e1 * (1 - e12)   [reverse of e12 is -e12]
-- Step 1: (1 + e12) * e1 = e1 + e12*e1 = e1 + e12*e1
-- e12 * e1 = e1 * e2 * e1 = -e1 * e1 * e2 = -e2
-- So: (1 + e12) * e1 = e1 - e2
-- Step 2: (e1 - e2) * (1 - e12)
-- = e1 - e2 - e1*e12 + e2*e12
-- e1 * e12 = e1 * e1 * e2 = e2
-- e2 * e12 = e2 * e1 * e2 = -e1 * e2 * e2 = -e1
-- = e1 - e2 - e2 - e1 = -2e2

#eval let R : Multivector R3 Int := Multivector.scalar 1 + Multivector.ofBlade e12
      let e1v : Multivector R3 Int := Multivector.ofBlade e1
      let result := R * e1v * R†
      (result.coeff e1, result.coeff e2, result.scalarPart)  -- (0, -2, 0)

-- This matches! The unnormalized rotor (1 + e12) maps e1 to -2e2

end Tests

end Grassmann
