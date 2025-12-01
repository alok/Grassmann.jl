/-
  Grassmann/PGA.lean - Projective Geometric Algebra

  Port of Grassmann.jl's projective model operations.

  PGA (Plane-based Geometric Algebra) for 3D uses Cl(3,0,1):
  - 3 Euclidean dimensions (e₁² = e₂² = e₃² = 1)
  - 1 degenerate dimension (e₀² = 0)

  This is equivalent to working in Cl(3,1) but interpreting
  the null vector as representing points at infinity.

  In PGA3:
  - Points are grade-3 trivectors (e.g., P = e₁₂₃ + xe₀₂₃ + ye₀₃₁ + ze₀₁₂)
  - Lines are grade-2 bivectors
  - Planes are grade-1 vectors
  - The origin is represented by e₁₂₃ (pseudoscalar without e₀)

  Advantages of PGA:
  - Efficient for rigid body mechanics
  - Points, lines, planes as first-class citizens
  - Motors (dual quaternions) for rigid transformations
-/
import Grassmann.Multivector

namespace Grassmann

/-! ## PGA Signature

PGA3 has signature Cl(3,0,1) which we model as Cl(3,1) with special interpretation.
PGA3 is defined in Manifold.lean as: Signature.cl 3 1
-/

namespace PGA

variable {F : Type*} [Ring F] [Div F]

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

/-! ## Points, Lines, Planes

In PGA:
- Plane: aₓe₁ + aᵧe₂ + a_ze₃ + de₀ (grade-1 vector)
- Line: grade-2 bivector (6 components: 3 direction + 3 moment)
- Point: grade-3 trivector (e₁₂₃ + xe₀₂₃ + ye₀₃₁ + ze₀₁₂)
-/

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
  -- Direction components: e23, e31, e12
  (Multivector.ofBlade e23 : Multivector PGA3 F).smul dx
    |>.add ((Multivector.ofBlade e31).smul dy)
    |>.add ((Multivector.ofBlade e12).smul dz)
    -- Moment components: e01, e02, e03
    |>.add ((Multivector.ofBlade e01).smul mx)
    |>.add ((Multivector.ofBlade e02).smul my)
    |>.add ((Multivector.ofBlade e03).smul mz)

/-- Join of two points gives a line: P₁ ∨ P₂ -/
def joinPoints (p1 p2 : Multivector PGA3 F) : Multivector PGA3 F :=
  -- In PGA, join is the regressive product: A ∨ B = (A* ∧ B*)*
  let dual1 := ⋆ᵐp1
  let dual2 := ⋆ᵐp2
  ⋆ᵐ(dual1 ⋀ᵐ dual2)

/-- Join of three points gives a plane -/
def joinThreePoints (p1 p2 p3 : Multivector PGA3 F) : Multivector PGA3 F :=
  let dual1 := ⋆ᵐp1
  let dual2 := ⋆ᵐp2
  let dual3 := ⋆ᵐp3
  ⋆ᵐ((dual1 ⋀ᵐ dual2) ⋀ᵐ dual3)

/-- Join of a point and a line gives a plane -/
def joinPointLine (p : Multivector PGA3 F) (l : Multivector PGA3 F) : Multivector PGA3 F :=
  ⋆ᵐ((⋆ᵐp) ⋀ᵐ (⋆ᵐl))

/-- Meet of two planes gives a line: Π₁ ∧ Π₂ -/
def meetPlanes (pi1 pi2 : Multivector PGA3 F) : Multivector PGA3 F :=
  pi1 ⋀ᵐ pi2

/-- Meet of three planes gives a point -/
def meetThreePlanes (pi1 pi2 pi3 : Multivector PGA3 F) : Multivector PGA3 F :=
  (pi1 ⋀ᵐ pi2) ⋀ᵐ pi3

/-- Meet of a plane and a line gives a point -/
def meetPlaneLine (pi : Multivector PGA3 F) (l : Multivector PGA3 F) : Multivector PGA3 F :=
  pi ⋀ᵐ l

/-! ## Motors (Rigid Transformations)

A motor in PGA is an even-grade multivector that represents rigid motion.
Motor = Rotor + Translator
M = 1 + d/2 · e₀ · L where L is the rotation line
-/

/-- Create a rotor for rotation by angle θ around line through origin with direction (dx, dy, dz) -/
def rotor (dx dy dz : Float) (theta : Float) : Multivector PGA3 Float :=
  let halfAngle := theta / 2.0
  let c := Float.cos halfAngle
  let s := Float.sin halfAngle
  -- Rotation bivector: direction as bivector
  let B := (Multivector.ofBlade e23 : Multivector PGA3 Float).smul dx
    |>.add ((Multivector.ofBlade e31).smul dy)
    |>.add ((Multivector.ofBlade e12).smul dz)
  (Multivector.scalar c : Multivector PGA3 Float).add (B.smul s)

/-- Create a translator for translation by (tx, ty, tz) -/
def translator (tx ty tz : F) : Multivector PGA3 F :=
  -- T = 1 + (t/2) ∧ e₀ = 1 + tx/2 · e₀₁ + ty/2 · e₀₂ + tz/2 · e₀₃
  (Multivector.one : Multivector PGA3 F)
    |>.add ((Multivector.ofBlade e01).smul (tx / (2 : F)))
    |>.add ((Multivector.ofBlade e02).smul (ty / (2 : F)))
    |>.add ((Multivector.ofBlade e03).smul (tz / (2 : F)))

/-- Apply motor transformation: X' = M X M̃ where M̃ is reverse -/
def applyMotor (motor x : Multivector PGA3 F) : Multivector PGA3 F :=
  motor * x * motor†

/-! ## Distances and Angles

In PGA, distances and angles can be computed from the meet/join operations.
-/

/-- Squared distance between two points -/
def distanceSq (p1 p2 : Multivector PGA3 F) : F :=
  let l := joinPoints p1 p2
  -- Distance² is related to the line's moment
  (l * l†).scalarPart

end PGA

/-! ## Tests -/

section PGATests

open PGA

-- Test point construction
-- #eval let p := point (1 : Float) 2 3
--       (p.coeff e123, p.coeff e023, p.coeff e031, p.coeff e012)
--       -- Should be (1, 1, 2, 3)

-- Test plane construction
-- #eval let pi := plane (1 : Float) 0 0 5  -- x = 5 plane
--       (pi.coeff e1, pi.coeff e2, pi.coeff e3, pi.coeff e0)
--       -- Should be (1, 0, 0, 5)

-- Test origin
-- #eval let o := point (0 : Float) 0 0
--       (o.coeff e123, o.coeff e023, o.coeff e031, o.coeff e012)
--       -- Should be (1, 0, 0, 0)

-- Test meet of coordinate planes gives axis line
-- #eval let piX := plane (1 : Float) 0 0 0  -- x = 0 plane
--       let piY := plane 0 1 0 0            -- y = 0 plane
--       let zAxis := meetPlanes piX piY     -- Should give z-axis
--       zAxis.coeff e12  -- z-axis has e12 component

-- Test translator
-- #eval let T := translator (1 : Float) 0 0  -- translate by (1, 0, 0)
--       let p := point 0 0 0                  -- origin
--       let p' := applyMotor T p              -- translated point
--       (p'.coeff e023, p'.coeff e031, p'.coeff e012)
--       -- Should move the point

end PGATests

end Grassmann
