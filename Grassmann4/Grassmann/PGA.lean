/-
  Grassmann/PGA.lean - Projective Geometric Algebra

  Port of Grassmann.jl's projective model operations.

  PGA (Plane-based Geometric Algebra) for 3D uses Cl(3,0,1):
  - 3 Euclidean dimensions (e₁² = e₂² = e₃² = 1)
  - 1 degenerate dimension (e₀² = 0)

  This file provides:
  - PGA3 basis elements and operations
  - Proof-friendly Multivector-based API (PGA.Proof namespace)
  - Float-optimized MV-backed API (PGA.Point, PGA.Plane, etc. from MV.lean)

  In PGA3:
  - Points are grade-3 trivectors (e.g., P = e₁₂₃ + xe₀₂₃ + ye₀₃₁ + ze₀₁₂)
  - Lines are grade-2 bivectors
  - Planes are grade-1 vectors
  - The origin is represented by e₁₂₃ (pseudoscalar without e₀)
-/
import Grassmann.Multivector
import Grassmann.PGA3Packed

namespace Grassmann

/-! ## PGA Signature

PGA3 has signature Cl(3,0,1), with one degenerate projective dimension.
PGA3 is defined in Manifold.lean as: Signature.clr 3 0 1.
-/

namespace PGA

/-! ## Proof-Friendly API (Generic over F)

These functions use dense `Multivector` for proofs and generic scalar types.
For Float-optimized operations, use the MV-backed types directly.
-/

namespace Proof

variable {F : Type*} [CoeffOps F] [Div F]

/-- Create a point from Euclidean coordinates -/
def point (x y z : F) : Multivector PGA3 F :=
  (Multivector.ofBlade e123 : Multivector PGA3 F)
    |>.add ((Multivector.ofBlade e023).smul x)
    |>.add ((Multivector.ofBlade e031).smul y)
    |>.add ((Multivector.ofBlade e012).smul z)

/-- Extract Euclidean coordinates from a PGA point (Float version) -/
def extractPoint (p : Multivector PGA3 Float) : Float × Float × Float :=
  let w := p.coeff e123
  if w == 0 then
    (0, 0, 0)  -- Point at infinity
  else
    (p.coeff e023 / w, p.coeff e031 / w, p.coeff e012 / w)

/-- Create a plane from normal (nx, ny, nz) and distance d -/
def plane (nx ny nz d : F) : Multivector PGA3 F :=
  (Multivector.ofBlade e1 : Multivector PGA3 F).smul nx
    |>.add ((Multivector.ofBlade e2).smul ny)
    |>.add ((Multivector.ofBlade e3).smul nz)
    |>.add ((Multivector.ofBlade e0).smul d)

/-- Create a line from direction (dx, dy, dz) and moment (mx, my, mz) -/
def lineFromDirMoment (dx dy dz mx my mz : F) : Multivector PGA3 F :=
  (Multivector.ofBlade e23 : Multivector PGA3 F).smul dx
    |>.add ((Multivector.ofBlade e31).smul dy)
    |>.add ((Multivector.ofBlade e12).smul dz)
    |>.add ((Multivector.ofBlade e01).smul mx)
    |>.add ((Multivector.ofBlade e02).smul my)
    |>.add ((Multivector.ofBlade e03).smul mz)

/-- Join of two points gives a line: P₁ ∨ P₂ -/
def joinPoints (p1 p2 : Multivector PGA3 F) : Multivector PGA3 F :=
  let dual1 := ⋆ᵐp1
  let dual2 := ⋆ᵐp2
  ⋆ᵐ(dual1 ⋀ᵐ dual2)

/-- Join of three points gives a plane -/
def joinThreePoints (p1 p2 p3 : Multivector PGA3 F) : Multivector PGA3 F :=
  let dual1 := ⋆ᵐp1
  let dual2 := ⋆ᵐp2
  let dual3 := ⋆ᵐp3
  ⋆ᵐ((dual1 ⋀ᵐ dual2) ⋀ᵐ dual3)

/-- Meet of two planes gives a line: Π₁ ∧ Π₂ -/
def meetPlanes (pi1 pi2 : Multivector PGA3 F) : Multivector PGA3 F :=
  pi1 ⋀ᵐ pi2

/-- Meet of three planes gives a point -/
def meetThreePlanes (pi1 pi2 pi3 : Multivector PGA3 F) : Multivector PGA3 F :=
  (pi1 ⋀ᵐ pi2) ⋀ᵐ pi3

/-- Create a rotor for rotation by angle θ around line through origin -/
def rotor (dx dy dz : Float) (theta : Float) : Multivector PGA3 Float :=
  let halfAngle := theta / 2.0
  let c := Float.cos halfAngle
  let s := Float.sin halfAngle
  let B := (Multivector.ofBlade e23 : Multivector PGA3 Float).smul dx
    |>.add ((Multivector.ofBlade e31).smul dy)
    |>.add ((Multivector.ofBlade e12).smul dz)
  (Multivector.scalar c : Multivector PGA3 Float).add (B.smul s)

/-- Create a translator for translation by (tx, ty, tz) -/
def translator (tx ty tz : F) : Multivector PGA3 F :=
  (Multivector.one : Multivector PGA3 F)
    |>.add ((Multivector.ofBlade e01).smul (-(tx / (2 : F))))
    |>.add ((Multivector.ofBlade e02).smul (ty / (2 : F)))
    |>.add ((Multivector.ofBlade e03).smul (-(tz / (2 : F))))

/-- Apply motor transformation: X' = M X M̃ -/
def applyMotor (motor x : Multivector PGA3 F) : Multivector PGA3 F :=
  motor * x * motor†

/-- Squared distance between two points -/
def distanceSq (p1 p2 : Multivector PGA3 F) : F :=
  let l := joinPoints p1 p2
  (l * l†).scalarPart

end Proof

end PGA

/-! ## Type Checks -/

section PGATests

open PGA

-- Proof-friendly API (Multivector-based)
#check (Proof.point (1 : Float) 2 3 : Multivector PGA3 Float)
#check (Proof.plane (1 : Float) 0 0 5 : Multivector PGA3 Float)
#check (Proof.rotor 0 0 1 0.5 : Multivector PGA3 Float)

-- Float-optimized API (MV-backed)
#check (point3 1 2 3 : PGA.Point PGA3)
#check (plane3 1 0 0 5 : PGA.Plane PGA3)
#check (line3 1 0 0 0 0 0 : PGA.Line PGA3)
#check (motor3 0 0 1 0.5 : PGA.Motor PGA3)

end PGATests

end Grassmann
