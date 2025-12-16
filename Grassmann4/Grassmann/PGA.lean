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
import Grassmann.MultivectorDA
import Grassmann.Spinor
import Grassmann.EvenMVDA

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

/-- A PGA plane (grade 1) as a graded multivector. -/
abbrev Plane (F : Type*) [Ring F] := GradedMV PGA3 F GradeSet.vector

/-- A PGA line (grade 2) as a graded multivector. -/
abbrev Line (F : Type*) [Ring F] := GradedMV PGA3 F GradeSet.bivector

/-- A PGA point (grade 3) as a graded multivector. -/
abbrev Point (F : Type*) [Ring F] := GradedMV PGA3 F (GradeSet.singleton 3)

/-- Create a point from Euclidean coordinates -/
def point (x y z : F) : Multivector PGA3 F :=
  (Multivector.ofBlade e123 : Multivector PGA3 F)
    |>.add ((Multivector.ofBlade e023).smul x)
    |>.add ((Multivector.ofBlade e031).smul y)
    |>.add ((Multivector.ofBlade e012).smul z)

namespace Point

variable {F : Type*} [Ring F]

/-- Create a point from Euclidean coordinates (typed wrapper). -/
@[inline]
def mk (x y z : F) : Point F :=
  ⟨PGA.point (F := F) x y z⟩

end Point

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

namespace Plane

variable {F : Type*} [Ring F]

/-- Create a plane from normal and distance (typed wrapper). -/
@[inline]
def mk (nx ny nz d : F) : Plane F :=
  ⟨PGA.plane (F := F) nx ny nz d⟩

end Plane

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

namespace Line

variable {F : Type*} [Ring F]

/-- Create a line from direction and moment (typed wrapper). -/
@[inline]
def fromDirMoment (dx dy dz mx my mz : F) : Line F :=
  ⟨PGA.lineFromDirMoment (F := F) dx dy dz mx my mz⟩

end Line

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

/-! ### Typed join/meet helpers

These are thin wrappers around the multivector-level operations above, but the
types communicate intent *and* enable downstream code to pick grade-restricted
fast paths (e.g. motors acting on points/lines/planes). -/

namespace Point

variable {F : Type*} [Ring F]

/-- Join of two points gives a line (typed wrapper). -/
@[inline]
def join (p1 p2 : Point F) : Line F :=
  ⟨PGA.joinPoints (F := F) p1.mv p2.mv⟩

/-- Join of three points gives a plane (typed wrapper). -/
@[inline]
def joinThree (p1 p2 p3 : Point F) : Plane F :=
  ⟨PGA.joinThreePoints (F := F) p1.mv p2.mv p3.mv⟩

/-- Join of a point and a line gives a plane (typed wrapper). -/
@[inline]
def joinLine (p : Point F) (l : Line F) : Plane F :=
  ⟨PGA.joinPointLine (F := F) p.mv l.mv⟩

end Point

namespace Plane

variable {F : Type*} [Ring F]

/-- Meet of two planes gives a line (typed wrapper). -/
@[inline]
def meet (π1 π2 : Plane F) : Line F :=
  ⟨PGA.meetPlanes (F := F) π1.mv π2.mv⟩

/-- Meet of three planes gives a point (typed wrapper). -/
@[inline]
def meetThree (π1 π2 π3 : Plane F) : Point F :=
  ⟨PGA.meetThreePlanes (F := F) π1.mv π2.mv π3.mv⟩

/-- Meet of a plane and a line gives a point (typed wrapper). -/
@[inline]
def meetLine (π : Plane F) (l : Line F) : Point F :=
  ⟨PGA.meetPlaneLine (F := F) π.mv l.mv⟩

end Plane

/-! ## Motors (Rigid Transformations)

A motor in PGA is an even-grade multivector that represents rigid motion.
Motor = Rotor + Translator
M = 1 + d/2 · e₀ · L where L is the rotation line
-/

/-- A PGA motor is an even-grade multivector.
    We store it packed using `Spinor` (backed by `EvenMV`) for performance. -/
abbrev Motor (F : Type*) [Ring F] [Div F] := Spinor PGA3 F

namespace Motor

variable {F : Type*} [Ring F] [Div F]

/-- Pack an (even) multivector motor into the fast motor representation. -/
@[inline]
def pack (m : Multivector PGA3 F) : Motor F := Spinor.ofEven m

/-- Convert a packed motor back to a dense multivector. -/
@[inline]
def unpack (m : Motor F) : Multivector PGA3 F := m.toMultivector

/-- Compose two motors (rigid transforms). -/
@[inline]
def compose (m1 m2 : Motor F) : Motor F := m1 * m2

/-- Apply a motor to any PGA multivector via sandwich product: `X' = M X M̃`. -/
@[inline]
def apply (m : Motor F) (x : Multivector PGA3 F) : Multivector PGA3 F := m.rotate x

/-- Fast path for transforming a *plane* (grade 1) by a motor.
    Assumes `plane` is actually a grade-1 element. -/
@[inline]
def applyPlaneFast (m : Motor F) (plane : Multivector PGA3 F) : Multivector PGA3 F :=
  EvenMV.sandwichGradeSetFast (sig := PGA3) (n := 4) (F := F)
    m.mv plane GradeSet.vector (GradeSet.odd 4)

/-- Even faster plane transform when you only need the grade‑1 output.

    Assumes `m` is a motor/versor so the sandwich preserves grade. -/
@[inline]
def applyPlaneGrade1Fast (m : Motor F) (plane : Multivector PGA3 F) : Multivector PGA3 F :=
  EvenMV.sandwichGradeSetFastOut (sig := PGA3) (n := 4) (F := F)
    m.mv plane GradeSet.vector (GradeSet.odd 4) GradeSet.vector

/-- Fast path for transforming a *line* (grade 2) by a motor.
    Assumes `line` is actually a grade-2 element. -/
@[inline]
def applyLineFast (m : Motor F) (line : Multivector PGA3 F) : Multivector PGA3 F :=
  EvenMV.sandwichGradeSetFast (sig := PGA3) (n := 4) (F := F)
    m.mv line GradeSet.bivector (GradeSet.even 4)

/-- Even faster line transform when you only need the grade‑2 output.

    Assumes `m` is a motor/versor so the sandwich preserves grade. -/
@[inline]
def applyLineGrade2Fast (m : Motor F) (line : Multivector PGA3 F) : Multivector PGA3 F :=
  EvenMV.sandwichGradeSetFastOut (sig := PGA3) (n := 4) (F := F)
    m.mv line GradeSet.bivector (GradeSet.even 4) GradeSet.bivector

/-- Fast path for transforming a *point* (grade 3) by a motor.
    Assumes `p` is actually a grade-3 element. -/
@[inline]
def applyPointFast (m : Motor F) (p : Multivector PGA3 F) : Multivector PGA3 F :=
  EvenMV.sandwichGradeSetFast (sig := PGA3) (n := 4) (F := F)
    m.mv p (GradeSet.singleton 3) (GradeSet.odd 4)

/-- Even faster point transform when you only need the grade‑3 output.

    This computes only the `{3}` grade (4 coefficients) of `m * p * m̃`.

    Assumes:
    - `p` is a point (grade 3)
    - `m` is a *proper motor* (versor) so the sandwich preserves grade.

    For arbitrary even elements (that may introduce a grade‑1 part), use `applyPointFast`. -/
@[inline]
def applyPointGrade3Fast (m : Motor F) (p : Multivector PGA3 F) : Multivector PGA3 F :=
  EvenMV.sandwichGradeSetFastOut (sig := PGA3) (n := 4) (F := F)
    m.mv p (GradeSet.singleton 3) (GradeSet.odd 4) (GradeSet.singleton 3)

/-- Transform a typed plane by a motor, producing a typed plane. -/
@[inline]
def applyPlane (m : Motor F) (π : Plane F) : Plane F :=
  ⟨applyPlaneGrade1Fast (F := F) m π.mv⟩

/-- Transform a typed line by a motor, producing a typed line. -/
@[inline]
def applyLine (m : Motor F) (l : Line F) : Line F :=
  ⟨applyLineGrade2Fast (F := F) m l.mv⟩

/-- Transform a typed point by a motor, producing a typed point. -/
@[inline]
def applyPoint (m : Motor F) (p : Point F) : Point F :=
  ⟨applyPointGrade3Fast (F := F) m p.mv⟩

end Motor

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

/-- Apply a motor transformation using the packed motor representation.
    This avoids allocating/iterating over odd blades in the motor itself. -/
@[inline]
def applyMotorFast (motor : Motor F) (x : Multivector PGA3 F) : Multivector PGA3 F :=
  Motor.apply motor x

/-! ## Distances and Angles

In PGA, distances and angles can be computed from the meet/join operations.
-/

/-- Squared distance between two points -/
def distanceSq (p1 p2 : Multivector PGA3 F) : F :=
  let l := joinPoints p1 p2
  -- Distance² is related to the line's moment
  (l * l†).scalarPart

end PGA

/-! ## DataArray backend (Float hot path)

This section provides a single "plain data" representation for real-time use.
It is the recommended API surface for performance-critical code (e.g. an engine):
- coefficients are stored contiguously (`DataArray`)
- motors are stored packed (`EvenMVDA`)
- transforms compute only the needed output grades (point/plane/line)
- no on-the-fly representation churn inside inner loops
-/

namespace PGA.DA

/-- Dense PGA3 multivector backed by `DataArray`. -/
abbrev MV := MultivectorDA PGA3

/-- Packed PGA3 motor (even element) backed by `DataArray`. -/
abbrev Motor := EvenMVDA PGA3

/-! ### Constructors (no closures) -/

/-- Create a PGA3 point from Euclidean coordinates.

Layout matches the scalar indices used throughout the library:
`P = e123 + x·e023 + y·e031 + z·e012`. -/
def point (x y z : Float) : MV := Id.run do
  let mut out := DataArray.zeros 16
  out := out.set! 7 1.0
  out := out.set! 14 x
  out := out.set! 13 y
  out := out.set! 11 z
  return ⟨out⟩

/-- Create a PGA3 plane from normal (nx,ny,nz) and distance d. -/
def plane (nx ny nz d : Float) : MV := Id.run do
  let mut out := DataArray.zeros 16
  out := out.set! 1 nx
  out := out.set! 2 ny
  out := out.set! 4 nz
  out := out.set! 8 d
  return ⟨out⟩

/-- Create a PGA3 line from direction (dx,dy,dz) and moment (mx,my,mz). -/
def lineFromDirMoment (dx dy dz mx my mz : Float) : MV := Id.run do
  let mut out := DataArray.zeros 16
  -- Direction: e23,e31,e12
  out := out.set! 6 dx
  out := out.set! 5 dy
  out := out.set! 3 dz
  -- Moment: e01,e02,e03
  out := out.set! 9 mx
  out := out.set! 10 my
  out := out.set! 12 mz
  return ⟨out⟩

/-! ### Motors -/

namespace Motor

/-- Pack an (even) dense motor into the fast packed representation. -/
@[inline]
def pack (m : MV) : Motor := EvenMVDA.ofMultivectorDAEven (sig := PGA3) (n := 4) m

/-- Compose two motors (rigid transforms). -/
@[inline]
def compose (m1 m2 : Motor) : Motor := m1 * m2

/-- Apply a motor to a point, computing only grade‑3 output. -/
@[inline]
def applyPoint (m : Motor) (p : MV) : MV :=
  EvenMVDA.sandwichGradeSetFastOut (sig := PGA3) (n := 4)
    m p (GradeSet.singleton 3) (GradeSet.odd 4) (GradeSet.singleton 3)

/-- Apply a motor to a plane, computing only grade‑1 output. -/
@[inline]
def applyPlane (m : Motor) (π : MV) : MV :=
  EvenMVDA.sandwichGradeSetFastOut (sig := PGA3) (n := 4)
    m π GradeSet.vector (GradeSet.odd 4) GradeSet.vector

/-- Apply a motor to a line, computing only grade‑2 output. -/
@[inline]
def applyLine (m : Motor) (l : MV) : MV :=
  EvenMVDA.sandwichGradeSetFastOut (sig := PGA3) (n := 4)
    m l GradeSet.bivector (GradeSet.even 4) GradeSet.bivector

end Motor

/-! ### Utilities -/

/-- Extract Euclidean coordinates from a DataArray-backed PGA3 point. -/
def extractPoint (p : MV) : Float × Float × Float :=
  let w := MultivectorDA.coeffIdx p 7
  if w == 0 then
    (0, 0, 0)
  else
    (MultivectorDA.coeffIdx p 14 / w, MultivectorDA.coeffIdx p 13 / w, MultivectorDA.coeffIdx p 11 / w)

end PGA.DA

/-! ## Tests -/

section PGATests

open PGA

-- Test point construction
#eval! let p := point (1 : Float) 2 3
       (p.coeff e123, p.coeff e023, p.coeff e031, p.coeff e012)
       -- Should be (1, 1, 2, 3)

-- Test plane construction
#eval! let pi := plane (1 : Float) 0 0 5  -- x = 5 plane
       (pi.coeff e1, pi.coeff e2, pi.coeff e3, pi.coeff e0)
       -- Should be (1, 0, 0, 5)

-- Test origin
#eval! let o := point (0 : Float) 0 0
       (o.coeff e123, o.coeff e023, o.coeff e031, o.coeff e012)
       -- Should be (1, 0, 0, 0)

-- Test meet of coordinate planes gives axis line
#eval! let piX := plane (1 : Float) 0 0 0  -- x = 0 plane
       let piY := plane 0 1 0 0            -- y = 0 plane
       let zAxis := meetPlanes piX piY     -- Should give z-axis
       zAxis.coeff e12  -- z-axis has e12 component

-- Test translator
#eval! let T := translator (1 : Float) 0 0  -- translate by (1, 0, 0)
       let p := point 0 0 0                  -- origin
       let p' := applyMotor T p              -- translated point
       (p'.coeff e023, p'.coeff e031, p'.coeff e012)
       -- Should move the point

end PGATests

end Grassmann
