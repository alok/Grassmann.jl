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

namespace Grassmann

/-! ## Spinor Type

A spinor is the even part of a multivector.
For efficiency, we could store only even-grade coefficients,
but for simplicity we use full multivectors with odd part zero.
-/

variable {n : ℕ} {sig : Signature n} {F : Type*}
variable [Zero F] [One F] [Add F] [Neg F] [Mul F] [Sub F] [Div F]

/-- A spinor is an even-grade multivector -/
structure Spinor (sig : Signature n) (F : Type*) where
  /-- The underlying even multivector -/
  mv : Multivector sig F
  -- Ideally we'd prove: mv.oddPart = 0

namespace Spinor

/-- Convert spinor to multivector -/
def toMultivector (s : Spinor sig F) : Multivector sig F := s.mv

/-- Create spinor from even multivector (assumes input is even) -/
def ofEven (m : Multivector sig F) : Spinor sig F := ⟨m.evenPart⟩

/-- Identity spinor (scalar 1) -/
def one : Spinor sig F := ⟨Multivector.one⟩

/-- Zero spinor -/
def zero : Spinor sig F := ⟨Multivector.zero⟩

/-- Spinor multiplication (geometric product of even elements is even) -/
def mul (a b : Spinor sig F) : Spinor sig F :=
  ⟨(a.mv * b.mv).evenPart⟩

/-- Spinor reverse -/
def reverse (s : Spinor sig F) : Spinor sig F := ⟨s.mv†⟩

/-- Scalar part of spinor -/
def scalarPart (s : Spinor sig F) : F := s.mv.scalarPart

/-- Add spinors -/
def add (a b : Spinor sig F) : Spinor sig F := ⟨a.mv.add b.mv⟩

/-- Subtract spinors -/
def sub (a b : Spinor sig F) : Spinor sig F := ⟨a.mv.sub b.mv⟩

/-- Scale spinor -/
def smul (x : F) (s : Spinor sig F) : Spinor sig F := ⟨s.mv.smul x⟩

/-- Negate spinor -/
def neg (s : Spinor sig F) : Spinor sig F := ⟨s.mv.neg⟩

instance : Zero (Spinor sig F) := ⟨Spinor.zero⟩
instance : One (Spinor sig F) := ⟨Spinor.one⟩
instance : Add (Spinor sig F) := ⟨Spinor.add⟩
instance : Sub (Spinor sig F) := ⟨Spinor.sub⟩
instance : Neg (Spinor sig F) := ⟨Spinor.neg⟩
instance : Mul (Spinor sig F) := ⟨Spinor.mul⟩

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

/-- Create rotor from axis (bivector) and angle -/
def fromAxisAngle (axis : Multivector sig Float) (angle : Float) : Spinor sig Float :=
  let halfAngle := angle / 2
  let c := Float.cos halfAngle
  let s := Float.sin halfAngle
  -- Normalize axis bivector
  let axisSq := (axis * axis).scalarPart
  let axisNorm := Float.sqrt (Float.abs axisSq)
  let unitAxis := if axisNorm == 0 then axis else axis.smul (1 / axisNorm)
  ⟨(Multivector.scalar c).add (unitAxis.smul s)⟩

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

/-! ## Rotor Constructors for R3 -/

section R3Rotors

/-- Rotor for rotation around x-axis by angle -/
def rotorX (angle : Float) : Spinor R3 Float :=
  Spinor.fromAxisAngle (Multivector.ofBlade (e23 : Blade R3)) angle

/-- Rotor for rotation around y-axis by angle -/
def rotorY (angle : Float) : Spinor R3 Float :=
  Spinor.fromAxisAngle (Multivector.ofBlade (e13 : Blade R3)) (-angle)

/-- Rotor for rotation around z-axis by angle -/
def rotorZ (angle : Float) : Spinor R3 Float :=
  Spinor.fromAxisAngle (Multivector.ofBlade (e12 : Blade R3)) angle

/-- Rotor from Euler angles (ZYX convention) -/
def rotorFromEuler (roll pitch yaw : Float) : Spinor R3 Float :=
  rotorZ yaw * rotorY pitch * rotorX roll

/-- Rotor that rotates vector a to vector b -/
def rotorBetween (a b : Multivector R3 Float) : Spinor R3 Float :=
  -- R = (1 + ba) / |1 + ba|
  let ab := (b * a).evenPart
  let one_plus_ab := (Multivector.one : Multivector R3 Float).add ab
  Spinor.ofEven one_plus_ab |>.normalize

end R3Rotors

/-! ## Tests -/

section SpinorTests

/-- Pi constant -/
def pi : Float := 3.14159265358979323846

-- Test identity rotor
#eval (Spinor.one : Spinor R3 Float).scalarPart  -- 1

-- Test rotor from axis-angle (90° around z)
#eval let R := rotorZ (pi / 2)
      R.scalarPart  -- cos(π/4) ≈ 0.707

-- Test rotor composition
#eval let Rx := rotorX (pi / 4)
      let Ry := rotorY (pi / 4)
      let Rxy := Rx * Ry
      Rxy.normSq  -- Should be ≈ 1

-- Test rotation of e1 by 90° around z gives e2
#eval let R := rotorZ (pi / 2)
      let e1v : Multivector R3 Float := Multivector.ofBlade (e1 : Blade R3)
      let rotated := R.rotate e1v
      (rotated.coeff (e1 : Blade R3), rotated.coeff (e2 : Blade R3))
-- Expected: approximately (0, 1)

-- Test slerp at t=0.5
#eval let R1 := (Spinor.one : Spinor R3 Float)
      let R2 := rotorZ (pi / 2)
      let Rmid := Spinor.slerp R1 R2 0.5
      Rmid.toAngle  -- Should be approximately π/4

end SpinorTests

end Grassmann
