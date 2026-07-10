/-
  Grassmann/Spinor.lean - Spinors and Rotors (DataArray-backed)

  A spinor is an even-grade multivector that represents rotations.
  This implementation wraps `MV sig .even` for fast Float operations.

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
import Grassmann.MVDense

namespace Grassmann

/-! ## Spinor Type

A spinor is the even part of a multivector.
We store only even-grade coefficients via `MV sig .even`,
halving both memory and arithmetic costs.
-/

variable {n : ℕ} {sig : Signature n}

/-- A spinor is an even-grade multivector (Float-backed via DataArray).
    The packed representation guarantees evenness by construction. -/
structure Spinor (sig : Signature n) where
  /-- The underlying even multivector -/
  mv : MV sig .even

namespace Spinor

/-- Convert spinor to proof-friendly multivector -/
@[inline]
def toMultivector (s : Spinor sig) : Multivector sig Float := s.mv.toMultivector

/-- Create spinor from even multivector (projects to even part) -/
@[inline]
def ofMultivector (m : Multivector sig Float) : Spinor sig :=
  ⟨MV.ofMultivector m .even⟩

/-- Create spinor from MV -/
@[inline]
def ofMV (m : MV sig .even) : Spinor sig := ⟨m⟩

/-- Identity spinor (scalar 1) -/
@[inline]
def one : Spinor sig := ⟨MV.one sig⟩

/-- Zero spinor -/
@[inline]
def zero : Spinor sig := ⟨MV.zero sig .even⟩

/-- Spinor multiplication (geometric product of even elements is even) -/
@[inline]
def mul (a b : Spinor sig) : Spinor sig :=
  ⟨a.mv * b.mv⟩

/-- Spinor reverse (dagger) -/
@[inline]
def reverse (s : Spinor sig) : Spinor sig := ⟨MV.rev s.mv⟩

/-- Scalar part of spinor (packed index 0). -/
@[inline]
def scalarPart (s : Spinor sig) : Float := s.mv.scalarPart

/-- Add spinors -/
@[inline]
def add (a b : Spinor sig) : Spinor sig := ⟨a.mv + b.mv⟩

/-- Subtract spinors -/
@[inline]
def sub (a b : Spinor sig) : Spinor sig := ⟨a.mv + (-b.mv)⟩

/-- Scale spinor -/
@[inline]
def smul (x : Float) (s : Spinor sig) : Spinor sig := ⟨MV.smul x s.mv⟩

/-- Negate spinor -/
@[inline]
def neg (s : Spinor sig) : Spinor sig := ⟨-s.mv⟩

instance : Zero (Spinor sig) := ⟨Spinor.zero⟩
instance : One (Spinor sig) := ⟨Spinor.one⟩
instance : Add (Spinor sig) := ⟨Spinor.add⟩
instance : Neg (Spinor sig) := ⟨Spinor.neg⟩
instance : Mul (Spinor sig) := ⟨Spinor.mul⟩

/-! ### Coercion to Multivector -/

@[coe]
def coeToMultivector (s : Spinor sig) : Multivector sig Float := s.toMultivector

instance : Coe (Spinor sig) (Multivector sig Float) := ⟨coeToMultivector⟩
instance : Coe (Spinor sig) (MV sig .even) := ⟨fun s => s.mv⟩

postfix:max "†ˢ" => Spinor.reverse

/-! ## Rotor Operations -/

/-- Squared norm of spinor: s s̃ -/
@[inline]
def normSq (s : Spinor sig) : Float := (s * s†ˢ).scalarPart

/-- Apply spinor as rotation: v' = s v s̃ -/
@[inline]
def rotate (s : Spinor sig) (v : MV sig .odd) : MV sig .odd :=
  -- s * v gives even × odd = odd
  -- (s * v) * s† gives odd × even = odd
  mvSandwich s.mv v

/-- Rotate a full multivector by a spinor: v' = s v s̃ -/
@[inline]
def rotateFull (s : Spinor sig) (v : MV sig .full) : MV sig .full :=
  mvSandwich s.mv v

/-- Compose two rotations: s₁₂ = s₁ s₂ -/
@[inline]
def compose (s1 s2 : Spinor sig) : Spinor sig := s1 * s2

end Spinor

/-! ## Float Spinor Operations -/

namespace Spinor

/-- Norm of a spinor -/
@[inline]
def norm (s : Spinor sig) : Float :=
  Float.sqrt (Float.abs s.normSq)

/-- Normalize a spinor to unit norm -/
@[inline]
def normalize (s : Spinor sig) : Spinor sig :=
  let n := s.norm
  if n == 0 then s else s.smul (1 / n)

/-- Check if spinor is a valid rotor (unit norm) -/
@[inline]
def isRotor (s : Spinor sig) (tol : Float := 1e-10) : Bool :=
  Float.abs (s.normSq - 1) < tol

/-- Create rotor from axis (bivector) and angle.
    Result is cos(θ/2) + sin(θ/2)·B̂ where B̂ is the normalized axis. -/
def fromAxisAngle (axis : Multivector sig Float) (angle : Float) : Spinor sig :=
  let halfAngle := angle / 2
  let c := Float.cos halfAngle
  let s := Float.sin halfAngle
  -- Normalize axis bivector
  let axisSq := (axis * axis).scalarPart
  let axisNorm := Float.sqrt (Float.abs axisSq)
  let unitAxis := if axisNorm == 0 then axis else axis.smul (1 / axisNorm)
  -- Result is scalar + bivector, which is even
  ofMultivector ((Multivector.scalar c).add (unitAxis.smul s))

/-- Extract angle from a rotor -/
def toAngle (s : Spinor sig) : Float :=
  2 * Float.acos s.scalarPart

/-- Spherical linear interpolation between two rotors -/
def slerp (s1 s2 : Spinor sig) (t : Float) : Spinor sig :=
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
    The rotation angle is given in radians. -/
def rotorInPlane (i j : Fin n) (angle : Float) : Spinor sig :=
  let ei : Multivector sig Float := Multivector.ofBlade (Blade.basis i)
  let ej : Multivector sig Float := Multivector.ofBlade (Blade.basis j)
  let B := ei ⋀ᵐ ej
  Spinor.fromAxisAngle B.normalize angle

/-- Create a rotor from a normalized bivector and angle. -/
def rotorFromBivector (B : Multivector sig Float) (angle : Float) : Spinor sig :=
  Spinor.fromAxisAngle B angle

/-- Rotor that rotates vector a to vector b (generic version). -/
def rotorBetweenVectors (a b : Multivector sig Float) : Spinor sig :=
  let ab := (b * a).evenPart
  let one_plus_ab := (Multivector.one : Multivector sig Float).add ab
  Spinor.ofMultivector one_plus_ab |>.normalize

end GenericRotors

/-! ## Rotor Constructors for R3 (convenience functions) -/

section R3Rotors

/-- Rotor for rotation around x-axis by angle (rotation in yz-plane) -/
def rotorX (angle : Float) : Spinor R3 :=
  rotorInPlane ⟨1, by omega⟩ ⟨2, by omega⟩ angle

/-- Rotor for rotation around y-axis by angle (rotation in xz-plane) -/
def rotorY (angle : Float) : Spinor R3 :=
  rotorInPlane ⟨0, by omega⟩ ⟨2, by omega⟩ (-angle)

/-- Rotor for rotation around z-axis by angle (rotation in xy-plane) -/
def rotorZ (angle : Float) : Spinor R3 :=
  rotorInPlane ⟨0, by omega⟩ ⟨1, by omega⟩ angle

/-- Rotor from Euler angles (ZYX convention) -/
def rotorFromEuler (roll pitch yaw : Float) : Spinor R3 :=
  rotorZ yaw * rotorY pitch * rotorX roll

/-- Rotor that rotates vector a to vector b -/
def rotorBetween (a b : Multivector R3 Float) : Spinor R3 :=
  rotorBetweenVectors a b

end R3Rotors

/-! ## Type Checks (runtime tests moved to Bench.lean) -/

section SpinorTests

-- Type checking for API consistency
#check (Spinor.one : Spinor R3)
#check (rotorZ 0.5 : Spinor R3)
#check (rotorX 0.5 * rotorY 0.5 : Spinor R3)
#check (Spinor.slerp (Spinor.one : Spinor R3) (rotorZ 0.5) 0.5)
#check ((rotorZ 0.5 : Spinor R3) : Multivector R3 Float)  -- Coercion

end SpinorTests

end Grassmann
