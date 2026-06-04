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
import Grassmann.MV

namespace Grassmann

/-! ## PGA Signature

PGA3 has signature Cl(3,0,1) which we model as Cl(3,1) with special interpretation.
PGA3 is defined in Manifold.lean as: Signature.cl 3 1
-/

namespace PGA

/-! ## Basis Elements

In PGA3:
- e1, e2, e3: Euclidean vectors (square to +1)
- e0: degenerate/null dimension (squares to 0 in true PGA)
  Note: In our Cl(3,1) model, e0 squares to -1, but we interpret it projectively.
-/

/-- Euclidean basis e₁ -/
def e1 : Blade PGA3 := ⟨0b0001⟩
/-- Euclidean basis e₂ -/
def e2 : Blade PGA3 := ⟨0b0010⟩
/-- Euclidean basis e₃ -/
def e3 : Blade PGA3 := ⟨0b0100⟩
/-- Degenerate/projective basis e₀ -/
def e0 : Blade PGA3 := ⟨0b1000⟩

-- Bivectors (lines in PGA)
/-- e₀₁ bivector -/
def e01 : Blade PGA3 := ⟨0b1001⟩
/-- e₀₂ bivector -/
def e02 : Blade PGA3 := ⟨0b1010⟩
/-- e₀₃ bivector -/
def e03 : Blade PGA3 := ⟨0b1100⟩
/-- e₁₂ bivector -/
def e12 : Blade PGA3 := ⟨0b0011⟩
/-- e₃₁ bivector (note: e31 = -e13) -/
def e31 : Blade PGA3 := ⟨0b0101⟩
/-- e₂₃ bivector -/
def e23 : Blade PGA3 := ⟨0b0110⟩

-- Trivectors (points in PGA)
/-- e₁₂₃ trivector (ideal point / origin pseudoscalar) -/
def e123 : Blade PGA3 := ⟨0b0111⟩
/-- e₀₂₃ trivector -/
def e023 : Blade PGA3 := ⟨0b1110⟩
/-- e₀₃₁ trivector -/
def e031 : Blade PGA3 := ⟨0b1101⟩
/-- e₀₁₂ trivector -/
def e012 : Blade PGA3 := ⟨0b1011⟩

-- Pseudoscalar
/-- e₀₁₂₃ pseudoscalar -/
def e0123 : Blade PGA3 := ⟨0b1111⟩

/-! ## Proof-Friendly API (Generic over F)

These functions use dense `Multivector` for proofs and generic scalar types.
For Float-optimized operations, use the MV-backed types directly.
-/

namespace Proof

variable {F : Type*} [Ring F] [Div F]

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
    |>.add ((Multivector.ofBlade e01).smul (tx / (2 : F)))
    |>.add ((Multivector.ofBlade e02).smul (ty / (2 : F)))
    |>.add ((Multivector.ofBlade e03).smul (tz / (2 : F)))

/-- Apply motor transformation: X' = M X M̃ -/
def applyMotor (motor x : Multivector PGA3 F) : Multivector PGA3 F :=
  motor * x * motor†

/-- Squared distance between two points -/
def distanceSq (p1 p2 : Multivector PGA3 F) : F :=
  let l := joinPoints p1 p2
  (l * l†).scalarPart

end Proof

/-! ## Float-Optimized API (DataArray-backed)

The types `PGA.Motor`, `PGA.Point`, `PGA.Plane`, `PGA.Line` are imported from
`Grassmann.MV` and backed by DataArray for efficient Float computation.
-/

/-- Create a PGA3 point from Euclidean coordinates (Float, DataArray-backed).
    P = e123 + x·e023 + y·e031 + z·e012 -/
def point3 (x y z : Float) : Point PGA3 :=
  MV.zero PGA3 .odd
    |>.setCoeff 7 1.0    -- e123
    |>.setCoeff 14 x     -- e023
    |>.setCoeff 13 y     -- e031
    |>.setCoeff 11 z     -- e012

/-- Create a PGA3 plane from normal (nx,ny,nz) and distance d (Float, DataArray-backed). -/
def plane3 (nx ny nz d : Float) : Plane PGA3 :=
  MV.zero PGA3 .odd
    |>.setCoeff 1 nx     -- e1
    |>.setCoeff 2 ny     -- e2
    |>.setCoeff 4 nz     -- e3
    |>.setCoeff 8 d      -- e0

/-- Create a PGA3 line from direction and moment (Float, DataArray-backed). -/
def line3 (dx dy dz mx my mz : Float) : Line PGA3 :=
  MV.zero PGA3 .even
    |>.setCoeff 6 dx     -- e23
    |>.setCoeff 5 dy     -- e31
    |>.setCoeff 3 dz     -- e12
    |>.setCoeff 9 mx     -- e01
    |>.setCoeff 10 my    -- e02
    |>.setCoeff 12 mz    -- e03

/-- Create a PGA3 motor from rotation angle and axis (Float, DataArray-backed). -/
def motor3 (dx dy dz theta : Float) : Motor PGA3 :=
  let halfAngle := theta / 2.0
  let c := Float.cos halfAngle
  let s := Float.sin halfAngle
  MV.zero PGA3 .even
    |>.setCoeff 0 c             -- scalar
    |>.setCoeff 6 (s * dx)      -- e23
    |>.setCoeff 5 (s * dy)      -- e31
    |>.setCoeff 3 (s * dz)      -- e12

/-- Extract Euclidean coordinates from a DataArray-backed PGA3 point. -/
def extractPoint3 (p : Point PGA3) : Float × Float × Float :=
  let mv := p.toMV
  let w := mv.coeff 7  -- e123 coefficient
  if w == 0 then
    (0, 0, 0)
  else
    (mv.coeff 14 / w, mv.coeff 13 / w, mv.coeff 11 / w)

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
