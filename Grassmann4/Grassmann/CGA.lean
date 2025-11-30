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

/-! ## CGA Signature

CGA3 has signature Cl(4,1): 4 positive, 1 negative dimension.
CGA3 is defined in Manifold.lean as: Signature.cl 4 1
-/

namespace CGA

variable {F : Type*} [Zero F] [One F] [Add F] [Neg F] [Mul F] [Sub F] [Div F] [OfNat F 2]

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
#eval let p := point (1 : Float) 2 3
      (p.coeff e1, p.coeff e2, p.coeff e3)  -- (1, 2, 3)

-- Test e∞ · e₀ = -1 (they're dual null vectors)
#eval let ei := (einf : Multivector CGA3 Float)
      let eo' := (eo : Multivector CGA3 Float)
      (ei * eo').scalarPart  -- should be -1

-- Test point is null: P · P = 0
#eval let p := point (1 : Float) 0 0
      (p * p).scalarPart  -- should be 0 (or very close)

-- Test origin embedding
#eval let o := point (0 : Float) 0 0
      (o.coeff e1, o.coeff e2, o.coeff e3)  -- (0, 0, 0)

-- Line through two points has grade 3
#eval let p1 := point (0 : Float) 0 0
      let p2 := point 1 0 0
      let l := line p1 p2
      -- l should be a grade-3 blade (trivector)
      l.scalarPart  -- 0 (no scalar part)

end CGATests

end Grassmann
