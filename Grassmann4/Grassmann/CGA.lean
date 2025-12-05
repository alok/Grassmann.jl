/-
  Grassmann/CGA.lean - Conformal Geometric Algebra

  Port of Grassmann.jl's conformal model operations.

  CGA embeds n-dimensional Euclidean space into (n+2)-dimensional
  space with signature (n+1, 1). This allows:
  - Points, lines, circles, planes, spheres as blades
  - Intersections via meet (regressive product)
  - Transformations via versors

  For 3D CGA (CGA3), we work in Cl(4,1):
  - e₁, e₂, e₃: Euclidean basis (each squares to +1)
  - e₊: extra positive dimension (e₊² = +1)
  - e₋: extra negative dimension (e₋² = -1)

  The null basis:
  - e∞ = e₋ + e₊ (point at infinity)
  - e₀ = (e₋ - e₊)/2 (origin)

  A Euclidean point x is embedded as:
  - P = x + (x²/2)e∞ + e₀
-/
import Grassmann.Multivector

namespace Grassmann

/-! ## CGA Signature Configuration

Port of Grassmann.jl's `hasinf`, `hasorigin` functions from DirectSum.jl.
These predicates detect whether a signature has conformal null vectors.
-/

/-- Configuration for a conformal geometric algebra -/
structure CGAConfig (n : Nat) where
  /-- The base Euclidean dimension (e.g., 3 for CGA3) -/
  euclideanDim : Nat
  /-- Index of the positive extra basis (e₊) -/
  ePlusIdx : Fin n
  /-- Index of the negative extra basis (e₋) -/
  eMinusIdx : Fin n
  /-- Proof that we have exactly 2 extra dimensions -/
  h_dim : n = euclideanDim + 2

namespace CGAConfig

/-- Standard CGA3 configuration -/
def cga3 : CGAConfig 5 where
  euclideanDim := 3
  ePlusIdx := ⟨3, by omega⟩
  eMinusIdx := ⟨4, by omega⟩
  h_dim := rfl

/-- Standard CGA2 configuration (for 2D conformal GA) -/
def cga2 : CGAConfig 4 where
  euclideanDim := 2
  ePlusIdx := ⟨2, by omega⟩
  eMinusIdx := ⟨3, by omega⟩
  h_dim := rfl

/-- Standard CGA4 configuration (for 4D conformal GA) -/
def cga4 : CGAConfig 6 where
  euclideanDim := 4
  ePlusIdx := ⟨4, by omega⟩
  eMinusIdx := ⟨5, by omega⟩
  h_dim := rfl

end CGAConfig

/-- Check if a signature has the infinity point e∞ (conformal model).
    Port of DirectSum.jl's `hasinf` function.
    True if signature has both a positive and negative extra dimension
    that can be combined into null vectors. -/
def Signature.hasInf (sig : Signature n) : Bool :=
  -- Check if we have at least one positive and one negative dimension
  -- beyond what would be purely Euclidean or anti-Euclidean
  sig.numPositive > 0 && sig.numNegative > 0

/-- Check if a signature has the origin point e₀ (conformal model).
    Port of DirectSum.jl's `hasorigin` function.
    Same condition as hasInf since both null vectors exist together. -/
def Signature.hasOrigin (sig : Signature n) : Bool := sig.hasInf

/-- Check if this is a conformal geometric algebra signature.
    True if it looks like Cl(p+1, 1) for some p ≥ 0. -/
def Signature.isConformal (sig : Signature n) : Bool :=
  sig.numNegative == 1 && sig.numPositive >= 1 && sig.numDegenerate == 0

/-- Infer the base Euclidean dimension from a conformal signature.
    For Cl(p+1, 1), the Euclidean dimension is p. -/
def Signature.conformalBaseDim (sig : Signature n) : Nat :=
  if sig.isConformal then sig.numPositive - 1 else 0

/-! ## CGA Signature

CGA3 has signature Cl(4,1): 4 positive, 1 negative dimension.
CGA3 is defined in Manifold.lean as: Signature.cl 4 1
-/

namespace CGA

variable {F : Type*} [Ring F] [Div F]

/-! ## Basis Elements

In CGA3, we have:
- e1, e2, e3: Euclidean vectors
- e4 (e₊): positive extra dimension
- e5 (e₋): negative extra dimension
-/

/-- Euclidean basis e₁ -/
def e1 : Blade CGA3 := ⟨0b00001⟩
/-- Euclidean basis e₂ -/
def e2 : Blade CGA3 := ⟨0b00010⟩
/-- Euclidean basis e₃ -/
def e3 : Blade CGA3 := ⟨0b00100⟩
/-- Positive extra dimension e₊ (e4) -/
def eplus : Blade CGA3 := ⟨0b01000⟩
/-- Negative extra dimension e₋ (e5) -/
def eminus : Blade CGA3 := ⟨0b10000⟩

/-- Point at infinity: e∞ = e₋ + e₊ -/
def einf : Multivector CGA3 F :=
  (Multivector.ofBlade eminus).add (Multivector.ofBlade eplus)

/-- Origin: e₀ = (e₋ - e₊)/2 -/
def eo : Multivector CGA3 F :=
  ((Multivector.ofBlade eminus).sub (Multivector.ofBlade eplus)).smul (1 / (2 : F))

/-! ## Point Embedding

A Euclidean point (x, y, z) is embedded as:
  P = x·e₁ + y·e₂ + z·e₃ + (x² + y² + z²)/2 · e∞ + e₀
-/

/-- Embed a 3D Euclidean point into CGA -/
def point (x y z : F) : Multivector CGA3 F :=
  let euclidean := (Multivector.ofBlade e1 : Multivector CGA3 F).smul x
    |>.add ((Multivector.ofBlade e2).smul y)
    |>.add ((Multivector.ofBlade e3).smul z)
  let sqNorm := x * x + y * y + z * z
  euclidean.add ((einf : Multivector CGA3 F).smul (sqNorm / (2 : F)))
    |>.add (eo : Multivector CGA3 F)

/-- Extract Euclidean coordinates from a CGA point (assumes normalized) -/
def extractPoint (p : Multivector CGA3 F) : F × F × F :=
  (p.coeff e1, p.coeff e2, p.coeff e3)

/-! ## Geometric Objects

In CGA, geometric objects are represented by blades:
- Point: grade-1 null vector (P · P = 0)
- Point pair: grade-2 blade (two points)
- Circle/Line: grade-3 blade
- Sphere/Plane: grade-4 blade
-/

/-- Create a line through two points: L = P₁ ∧ P₂ ∧ e∞ -/
def line (p1 p2 : Multivector CGA3 F) : Multivector CGA3 F :=
  (p1 ⋀ᵐ p2) ⋀ᵐ (einf : Multivector CGA3 F)

/-- Create a circle through three points: C = P₁ ∧ P₂ ∧ P₃ -/
def circle (p1 p2 p3 : Multivector CGA3 F) : Multivector CGA3 F :=
  (p1 ⋀ᵐ p2) ⋀ᵐ p3

/-- Create a plane through three points: Π = P₁ ∧ P₂ ∧ P₃ ∧ e∞ -/
def plane (p1 p2 p3 : Multivector CGA3 F) : Multivector CGA3 F :=
  ((p1 ⋀ᵐ p2) ⋀ᵐ p3) ⋀ᵐ (einf : Multivector CGA3 F)

/-- Create a sphere through four points: S = P₁ ∧ P₂ ∧ P₃ ∧ P₄ -/
def sphere (p1 p2 p3 p4 : Multivector CGA3 F) : Multivector CGA3 F :=
  ((p1 ⋀ᵐ p2) ⋀ᵐ p3) ⋀ᵐ p4

/-- Sphere from center and radius: S = c - (r²/2)e∞ where c is embedded center -/
def sphereCenterRadius (cx cy cz r : F) : Multivector CGA3 F :=
  let c := point cx cy cz
  c.sub ((einf : Multivector CGA3 F).smul (r * r / (2 : F)))

/-- Plane from normal and distance: Π = n + d·e∞ where n is unit normal -/
def planeNormalDist (nx ny nz d : F) : Multivector CGA3 F :=
  let n := (Multivector.ofBlade e1 : Multivector CGA3 F).smul nx
    |>.add ((Multivector.ofBlade e2).smul ny)
    |>.add ((Multivector.ofBlade e3).smul nz)
  n.add ((einf : Multivector CGA3 F).smul d)

/-! ## Regressive (Meet) Product

The meet of two objects gives their intersection.
For blades A and B: A ∨ B = (A* ∧ B*)* where * is dual
-/

/-- Regressive (meet) product: A ∨ B = (A* ∧ B*)* -/
def meet (a b : Multivector CGA3 F) : Multivector CGA3 F :=
  (⋆ᵐ((⋆ᵐa) ⋀ᵐ (⋆ᵐb)))

infixl:60 " ⋁ᶜ " => meet

/-! ## Transformations

In CGA, transformations are represented by versors:
- Translation: T = 1 - (t/2)e∞ where t is translation vector
- Rotation: R = cos(θ/2) + sin(θ/2)B where B is bivector
- Reflection: through plane with normal n
- Scaling: about a point
-/

/-- Create a translator for vector (tx, ty, tz) -/
def translator (tx ty tz : F) : Multivector CGA3 F :=
  let t := (Multivector.ofBlade e1 : Multivector CGA3 F).smul tx
    |>.add ((Multivector.ofBlade e2).smul ty)
    |>.add ((Multivector.ofBlade e3).smul tz)
  let half_t_einf := (t ⋀ᵐ (einf : Multivector CGA3 F)).smul (1 / (2 : F))
  (Multivector.one : Multivector CGA3 F).sub half_t_einf

/-- Apply versor transformation: x' = V x V† / (V V†) -/
def transform (versor x : Multivector CGA3 F) : Multivector CGA3 F :=
  let vx := versor * x * versor†
  let norm := (versor * versor†).scalarPart
  vx.smul (1 / norm)

end CGA

/-! ## Tests -/

section CGATests

open CGA

-- Test point embedding
#eval! let p := point (1 : Float) 2 3
       (p.coeff e1, p.coeff e2, p.coeff e3)  -- (1, 2, 3)

-- Test e∞ · e₀ = -1 (they're dual null vectors)
#eval! let ei := (einf : Multivector CGA3 Float)
       let eo' := (eo : Multivector CGA3 Float)
       (ei * eo').scalarPart  -- should be -1

-- Test point is null: P · P = 0
#eval! let p := point (1 : Float) 0 0
       (p * p).scalarPart  -- should be 0 (or very close)

-- Test origin embedding
#eval! let o := point (0 : Float) 0 0
       (o.coeff e1, o.coeff e2, o.coeff e3)  -- (0, 0, 0)

-- Line through two points has grade 3
#eval! let p1 := point (0 : Float) 0 0
       let p2 := point 1 0 0
       let l := line p1 p2
       -- l should be a grade-3 blade (trivector)
       l.scalarPart  -- 0 (no scalar part)

end CGATests

/-! ## Advanced CGA Operations

Additional operations from Grassmann.jl for conformal geometry.
-/

namespace CGA

/-! ### Null Vector Properties -/

/-- Check if a CGA vector is null (P·P = 0).
    Points in CGA are represented by null vectors. -/
def isNull (p : Multivector CGA3 Float) (tol : Float := 1e-10) : Bool :=
  let sq := (p * p).scalarPart
  Float.abs sq < tol

/-- Normalize a CGA point so that e∞ coefficient is 1.
    Standard form: P = x + (x²/2)e∞ + e₀ with e∞ coeff = 1 -/
def normalizePoint (p : Multivector CGA3 Float) : Multivector CGA3 Float :=
  -- e∞ = e₊ + e₋, so coefficient is p[e₊] + p[e₋]
  let einfCoeff := p.coeff eplus + p.coeff eminus
  if Float.abs einfCoeff < 1e-10 then p
  else p.smul (1.0 / einfCoeff)

/-! ### Distances and Angles -/

/-- Squared distance between two CGA points.
    d²(P₁, P₂) = -2(P₁ · P₂) when points are normalized -/
def squaredDistance (p1 p2 : Multivector CGA3 Float) : Float :=
  let p1n := normalizePoint p1
  let p2n := normalizePoint p2
  ((-2.0) * (p1n ⌋ᵐ p2n).scalarPart)

/-- Euclidean distance between two CGA points -/
def distance (p1 p2 : Multivector CGA3 Float) : Float :=
  let d2 := squaredDistance p1 p2
  if d2 < 0 then 0.0 else Float.sqrt d2

/-! ### Reflection Operations -/

/-- Reflect a point through a plane.
    reflection(P, Π) = Π · P · Π⁻¹ -/
def reflectThroughPlane (p plane : Multivector CGA3 Float) : Multivector CGA3 Float :=
  let planeSq := (plane * plane).scalarPart
  if Float.abs planeSq < 1e-10 then p
  else
    let planeInv := plane.smul (1.0 / planeSq)
    plane * p * planeInv

/-- Reflect a point through a sphere.
    Inversion in sphere S: S · P · S -/
def invertInSphere (p sphere : Multivector CGA3 Float) : Multivector CGA3 Float :=
  sphere * p * sphere

/-! ### Circle and Sphere Properties -/

/-- Extract center of a sphere (dual representation).
    Given a sphere S as a grade-4 blade, extract its center. -/
def sphereCenter (S : Multivector CGA3 Float) : Multivector CGA3 Float :=
  -- The center is S ∧ e∞ projected back
  let center := S ⋀ᵐ (einf : Multivector CGA3 Float)
  normalizePoint center

/-- Extract radius of a sphere.
    r² = S·S / (S ∧ e∞)² for a sphere blade S -/
def sphereRadius (S : Multivector CGA3 Float) : Float :=
  let Ssq := (S * S).scalarPart
  let Sinf := S ⋀ᵐ (einf : Multivector CGA3 Float)
  let SinfSq := (Sinf * Sinf).scalarPart
  if Float.abs SinfSq < 1e-10 then 0.0
  else Float.sqrt (Float.abs (Ssq / SinfSq))

/-! ### Flat and Round Discrimination -/

/-- Check if a geometric object is "flat" (contains e∞).
    Flats: lines, planes. Rounds: circles, spheres. -/
def isFlat (obj : Multivector CGA3 Float) : Bool :=
  -- Object is flat if obj ∧ e∞ = 0
  let wedgeInf := obj ⋀ᵐ (einf : Multivector CGA3 Float)
  -- Check if all coefficients are near zero
  let maxCoeff := (List.finRange 32).foldl (init := 0.0) fun acc i =>
    let c := Float.abs (wedgeInf.coeffs i)
    if c > acc then c else acc
  maxCoeff < 1e-10

/-- Check if a geometric object is "round" (doesn't contain e∞).
    Rounds: circles, spheres, point pairs. -/
def isRound (obj : Multivector CGA3 Float) : Bool := !isFlat obj

/-! ### Tangent Operations -/

/-- Tangent vector at a point on a circle.
    Given a point P on circle C, compute the tangent direction. -/
def tangentAtPoint (P C : Multivector CGA3 Float) : Multivector CGA3 Float :=
  -- Tangent is P ⌋ C (left contraction)
  P ⌋ᵐ C

/-! ### Motor (Rigid Body Motion) -/

/-- A motor is a rotor + translator combined: M = T·R
    Motors represent rigid body motions (rotations + translations). -/
def motor (translation rotation : Multivector CGA3 Float) : Multivector CGA3 Float :=
  translation * rotation

/-- Decompose a motor into translation and rotation components.
    Returns (translation_vector, rotation_rotor). -/
def decomposeMotor (M : Multivector CGA3 Float) : Multivector CGA3 Float × Multivector CGA3 Float :=
  -- The scalar + bivector part is the rotation
  let R := (M.gradeProject 0).add (M.gradeProject 2)
  -- T = M · R†
  let T := M * R†
  (T, R)

end CGA

/-! ## CGA Signature Tests -/

section CGASignatureTests

-- Test hasInf/hasOrigin
#eval CGA3.hasInf     -- true (Cl(4,1) has both + and -)
#eval CGA3.hasOrigin  -- true
#eval R3.hasInf       -- false (pure Euclidean)
#eval STA.hasInf      -- true (Cl(1,3) has both)

-- Test isConformal
#eval CGA3.isConformal        -- true (Cl(4,1) = Cl(3+1, 1))
#eval R3.isConformal          -- false
#eval (Signature.cl 3 1).isConformal  -- true (CGA2)

-- Test conformalBaseDim
#eval CGA3.conformalBaseDim   -- 3 (base Euclidean dim)
#eval (Signature.cl 3 1).conformalBaseDim  -- 2

end CGASignatureTests

/-! ## Advanced CGA Tests -/

section AdvancedCGATests

open CGA

-- Test distance between points
#eval! let p1 := point (0 : Float) 0 0
       let p2 := point 1 0 0
       distance p1 p2  -- Expected: 1.0

-- Test point normalization
#eval! let p := point (1 : Float) 2 3
       let pn := normalizePoint p
       -- e∞ coefficient should be 1 after normalization
       pn.coeff eplus + pn.coeff eminus

-- Test isNull
#eval! let p := point (1 : Float) 0 0
       isNull p  -- Expected: true (points are null vectors)

-- Test isFlat
#eval! let p1 := point (0 : Float) 0 0
       let p2 := point 1 0 0
       let l := line p1 p2
       isFlat l  -- Expected: true (lines are flat)

#eval! let p1 := point (0 : Float) 0 0
       let p2 := point 1 0 0
       let p3 := point 0 1 0
       let c := circle p1 p2 p3
       isFlat c  -- Expected: false (circles are round)

end AdvancedCGATests

end Grassmann
