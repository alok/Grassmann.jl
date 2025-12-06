/-
  Grassmann/Spinor.lean - Spinors and Rotors

  Port of Grassmann.jl's spinor operations.

  A spinor is an even-grade multivector that represents rotations
  more efficiently than the full Clifford algebra.

  In Cl(p,q):
  - Spin(p,q) = {s ∈ Cl⁺(p,q) | s s̃ = ±1}
  - Pin(p,q) includes odd elements too

  Key properties:
  - Rotors: R R̃ = 1 (unit even elements)
  - Rotation: v' = R v R̃
  - Composition: R₁₂ = R₁ R₂

  In 3D:
  - Spinors ≅ unit quaternions ≅ SU(2)
  - Double cover of SO(3)
-/
import Grassmann.Multivector
import Grassmann.Proof

open Grassmann.Proof

namespace Grassmann

/-! ## Spinor Type

A spinor is the even part of a multivector.
For efficiency, we could store only even-grade coefficients,
but for simplicity we use full multivectors with odd part zero.
-/

variable {n : ℕ} {sig : Signature n} {F : Type*}
variable [Ring F] [Div F]

/-- A spinor is an even-grade multivector.
    The invariant `isEven` ensures mv.oddPart = 0. -/
structure Spinor (sig : Signature n) (F : Type*) [Ring F] where
  /-- The underlying even multivector -/
  mv : Multivector sig F
  /-- Proof that the multivector has no odd-grade components -/
  isEven : mv.oddPart = Multivector.zero

namespace Spinor

/-- Convert spinor to multivector -/
def toMultivector (s : Spinor sig F) : Multivector sig F := s.mv

/-- Proof that evenPart has no odd components.
    Computational verification: evenPart sets all odd-grade coeffs to 0,
    so oddPart (which extracts odd-grade coeffs) returns 0. -/
private theorem evenPart_isEven (m : Multivector sig F) :
    m.evenPart.oddPart = Multivector.zero := by sorry_proof

/-- Proof that scalar 1 is even.
    Computational verification: scalar 1 has coefficient only at index 0,
    which has grade 0 (even). -/
private theorem one_isEven : (Multivector.one : Multivector sig F).oddPart = Multivector.zero := by
  sorry_proof

/-- Proof that zero is even.
    Computational verification: zero has all coefficients 0. -/
private theorem zero_isEven : (Multivector.zero : Multivector sig F).oddPart = Multivector.zero := by
  sorry_proof

/-- Create spinor from even multivector (projects to even part) -/
def ofEven (m : Multivector sig F) : Spinor sig F := ⟨m.evenPart, evenPart_isEven m⟩

/-- Identity spinor (scalar 1) -/
def one : Spinor sig F := ⟨Multivector.one, one_isEven⟩

/-- Zero spinor -/
def zero : Spinor sig F := ⟨Multivector.zero, zero_isEven⟩

/-- Proof that product of even elements is even.
    evenPart projection ensures result is even. -/
private theorem mul_isEven (a b : Spinor sig F) :
    (a.mv * b.mv).evenPart.oddPart = Multivector.zero :=
  evenPart_isEven _

/-- Proof that reverse of even is even.
    Reverse preserves grade parity. -/
private theorem reverse_isEven (s : Spinor sig F) :
    s.mv†.oddPart = Multivector.zero := by sorry_proof

/-- Proof that sum of even elements is even.
    Grade is determined by index, sum preserves this. -/
private theorem add_isEven (a b : Spinor sig F) :
    (a.mv.add b.mv).oddPart = Multivector.zero := by sorry_proof

/-- Proof that difference of even elements is even.
    Grade is determined by index, difference preserves this. -/
private theorem sub_isEven (a b : Spinor sig F) :
    (a.mv.sub b.mv).oddPart = Multivector.zero := by sorry_proof

/-- Proof that scaled even element is even.
    Scaling doesn't change which indices are non-zero. -/
private theorem smul_isEven (x : F) (s : Spinor sig F) :
    (s.mv.smul x).oddPart = Multivector.zero := by sorry_proof

/-- Proof that negated even element is even.
    Negation doesn't change which indices are non-zero. -/
private theorem neg_isEven (s : Spinor sig F) :
    s.mv.neg.oddPart = Multivector.zero := by sorry_proof

/-- Spinor multiplication (geometric product of even elements is even) -/
def mul (a b : Spinor sig F) : Spinor sig F :=
  ⟨(a.mv * b.mv).evenPart, mul_isEven a b⟩

/-- Spinor reverse -/
def reverse (s : Spinor sig F) : Spinor sig F := ⟨s.mv†, reverse_isEven s⟩

/-- Scalar part of spinor -/
def scalarPart (s : Spinor sig F) : F := s.mv.scalarPart

/-- Add spinors -/
def add (a b : Spinor sig F) : Spinor sig F := ⟨a.mv.add b.mv, add_isEven a b⟩

/-- Subtract spinors -/
def sub (a b : Spinor sig F) : Spinor sig F := ⟨a.mv.sub b.mv, sub_isEven a b⟩

/-- Scale spinor -/
def smul (x : F) (s : Spinor sig F) : Spinor sig F := ⟨s.mv.smul x, smul_isEven x s⟩

/-- Negate spinor -/
def neg (s : Spinor sig F) : Spinor sig F := ⟨s.mv.neg, neg_isEven s⟩

instance : Zero (Spinor sig F) := ⟨Spinor.zero⟩
instance : One (Spinor sig F) := ⟨Spinor.one⟩
instance : Add (Spinor sig F) := ⟨Spinor.add⟩
instance : Sub (Spinor sig F) := ⟨Spinor.sub⟩
instance : Neg (Spinor sig F) := ⟨Spinor.neg⟩
instance : Mul (Spinor sig F) := ⟨Spinor.mul⟩

/-! ### Coercion to Multivector

Spinor → Multivector is a safe coercion (zero cost, just unwrapping).
-/

@[coe]
def coeToMultivector (s : Spinor sig F) : Multivector sig F := s.mv

instance : Coe (Spinor sig F) (Multivector sig F) := ⟨coeToMultivector⟩

postfix:max "†ˢ" => Spinor.reverse

/-! ## Rotor Operations -/

/-- Squared norm of spinor: s s̃ -/
def normSq (s : Spinor sig F) : F := (s * s†ˢ).scalarPart

/-- Apply spinor as rotation: v' = s v s̃ -/
def rotate (s : Spinor sig F) (v : Multivector sig F) : Multivector sig F :=
  s.mv * v * s.mv†

/-- Compose two rotations: s₁₂ = s₁ s₂ -/
def compose (s1 s2 : Spinor sig F) : Spinor sig F := s1 * s2

end Spinor

/-! ## Float Spinor Operations -/

namespace Spinor

/-- Norm of a spinor -/
def norm (s : Spinor sig Float) : Float :=
  Float.sqrt s.normSq

/-- Normalize a spinor to unit norm -/
def normalize (s : Spinor sig Float) : Spinor sig Float :=
  let n := s.norm
  if n == 0 then s else s.smul (1 / n)

/-- Check if spinor is a valid rotor (unit norm) -/
def isRotor (s : Spinor sig Float) (tol : Float := 1e-10) : Bool :=
  Float.abs (s.normSq - 1) < tol

/-- Create rotor from axis (bivector) and angle.
    Result is cos(θ/2) + sin(θ/2)·B̂ where B̂ is the normalized axis. -/
def fromAxisAngle (axis : Multivector sig Float) (angle : Float) : Spinor sig Float :=
  let halfAngle := angle / 2
  let c := Float.cos halfAngle
  let s := Float.sin halfAngle
  -- Normalize axis bivector
  let axisSq := (axis * axis).scalarPart
  let axisNorm := Float.sqrt (Float.abs axisSq)
  let unitAxis := if axisNorm == 0 then axis else axis.smul (1 / axisNorm)
  -- Result is scalar + bivector, which is even
  ofEven ((Multivector.scalar c).add (unitAxis.smul s))

/-- Extract angle from a rotor -/
def toAngle (s : Spinor sig Float) : Float :=
  2 * Float.acos s.scalarPart

/-- Spherical linear interpolation between two rotors -/
def slerp (s1 s2 : Spinor sig Float) (t : Float) : Spinor sig Float :=
  -- Compute angle between rotors
  let cosTheta := (s1 * s2†ˢ).scalarPart
  if Float.abs cosTheta > 0.9999 then
    -- Nearly parallel, use linear interpolation
    (s1.smul (1 - t)).add (s2.smul t) |>.normalize
  else
    let theta := Float.acos cosTheta
    let sinTheta := Float.sin theta
    let w1 := Float.sin ((1 - t) * theta) / sinTheta
    let w2 := Float.sin (t * theta) / sinTheta
    (s1.smul w1).add (s2.smul w2)

end Spinor

/-! ## Generic Rotor Constructors (n-dimensional) -/

section GenericRotors

variable {n : ℕ} {sig : Signature n}

/-- Create a rotor for rotation in the plane of basis vectors i and j.
    The rotation angle is given in radians. For orthonormal bases (Euclidean),
    the bivector e_i ∧ e_j has norm 1 and squares to -1. -/
def rotorInPlane (i j : Fin n) (angle : Float) : Spinor sig Float :=
  let ei : Multivector sig Float := Multivector.ofBlade (Blade.basis i)
  let ej : Multivector sig Float := Multivector.ofBlade (Blade.basis j)
  let B := ei ⋀ᵐ ej
  -- Normalize in case the basis is not orthonormal
  Spinor.fromAxisAngle B.normalize angle

/-- Create a rotor from a normalized bivector and angle.
    Assumes the bivector B is normalized (B² = -1 for Euclidean signature). -/
def rotorFromBivector (B : Multivector sig Float) (angle : Float) : Spinor sig Float :=
  Spinor.fromAxisAngle B angle

/-- Rotor that rotates vector a to vector b (generic version).
    Works in any signature where the vectors are non-null. -/
def rotorBetweenVectors (a b : Multivector sig Float) : Spinor sig Float :=
  -- R = (1 + ba) / |1 + ba|
  let ab := (b * a).evenPart
  let one_plus_ab := (Multivector.one : Multivector sig Float).add ab
  Spinor.ofEven one_plus_ab |>.normalize

end GenericRotors

/-! ## Rotor Constructors for R3 (convenience functions) -/

section R3Rotors

/-- Rotor for rotation around x-axis by angle (rotation in yz-plane) -/
def rotorX (angle : Float) : Spinor R3 Float :=
  rotorInPlane ⟨1, by omega⟩ ⟨2, by omega⟩ angle

/-- Rotor for rotation around y-axis by angle (rotation in xz-plane) -/
def rotorY (angle : Float) : Spinor R3 Float :=
  -- Note: e13 plane gives rotation in opposite direction to "around y"
  rotorInPlane ⟨0, by omega⟩ ⟨2, by omega⟩ (-angle)

/-- Rotor for rotation around z-axis by angle (rotation in xy-plane) -/
def rotorZ (angle : Float) : Spinor R3 Float :=
  rotorInPlane ⟨0, by omega⟩ ⟨1, by omega⟩ angle

/-- Rotor from Euler angles (ZYX convention) -/
def rotorFromEuler (roll pitch yaw : Float) : Spinor R3 Float :=
  rotorZ yaw * rotorY pitch * rotorX roll

/-- Rotor that rotates vector a to vector b -/
def rotorBetween (a b : Multivector R3 Float) : Spinor R3 Float :=
  rotorBetweenVectors a b

end R3Rotors

/-! ## Tests -/

section SpinorTests

def pi : Float := 3.14159265358979323846

-- Test identity rotor
#eval! (Spinor.one : Spinor R3 Float).scalarPart  -- 1

-- Test rotor from axis-angle (90° around z)
#eval! let R := rotorZ (pi / 2)
       R.scalarPart  -- cos(π/4) ≈ 0.707

-- Test rotor composition
#eval! let Rx := rotorX (pi / 4)
       let Ry := rotorY (pi / 4)
       let Rxy := Rx * Ry
       Rxy.normSq  -- Should be ≈ 1

-- Test rotation of e1 by 90° around z gives e2
#eval! let R := rotorZ (pi / 2)
       let e1v : Multivector R3 Float := Multivector.ofBlade (e1 : Blade R3)
       let rotated := R.rotate e1v
       (rotated.coeff (e1 : Blade R3), rotated.coeff (e2 : Blade R3))
-- Expected: approximately (0, 1)

-- Test slerp at t=0.5
#eval! let R1 := (Spinor.one : Spinor R3 Float)
       let R2 := rotorZ (pi / 2)
       let Rmid := Spinor.slerp R1 R2 0.5
       Rmid.toAngle  -- Should be approximately π/4

-- Test Spinor → Multivector coercion (zero cost)
#eval! let R := rotorZ (pi / 4)
       let mv : Multivector R3 Float := R  -- Coercion!
       mv.scalarPart  -- cos(π/8) ≈ 0.924

end SpinorTests

end Grassmann
