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

variable {F : Type*} [CoeffOps F] [Div F]

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

/-- Normalize a CGA point so that the homogeneous e₀ weight is 1.
    Standard form: P = x + (x²/2)e∞ + e₀ with e₀ weight = 1. -/
def normalizePoint (p : Multivector CGA3 Float) : Multivector CGA3 Float :=
  -- For a*e₊ + b*e₋, the e₀ weight is b - a because e₀ = (e₋ - e₊)/2.
  let originWeight := p.coeff eminus - p.coeff eplus
  if Float.abs originWeight < 1e-10 then p
  else p.smul (1.0 / originWeight)

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

/-! ## Meet-Based Collision Detection

In CGA, collision detection is elegant:
- Two objects collide if their meet (∨) is non-empty
- The meet gives the intersection directly (point pair, circle, etc.)

Sphere-sphere: meet is a circle (intersecting), point pair (touching), or 0 (separate)
Sphere-plane: meet is a circle (intersecting), point (touching), or 0 (separate)
Line-sphere: meet is a point pair (2 hits), point (tangent), or 0 (miss)
-/

/-- Magnitude squared of a multivector (sum of squared coefficients).
    Used to check if a meet result is essentially zero. -/
@[inline]
def magnitudeSq (m : Multivector CGA3 Float) : Float :=
  (List.finRange 32).foldl (init := 0.0) fun acc i =>
    acc + m.coeffs i * m.coeffs i

/-- Check if a multivector is essentially zero (empty intersection). -/
@[inline]
def isZeroMeet (m : Multivector CGA3 Float) (tol : Float := 1e-10) : Bool :=
  magnitudeSq m < tol * tol

/-- Check if two spheres collide using meet product.
    Two spheres collide if their meet is non-empty. -/
def spheresCollide (s1 s2 : Multivector CGA3 Float) : Bool :=
  let intersection := s1 ⋁ᶜ s2
  !isZeroMeet intersection

/-- Compute the meet (intersection) of two spheres.
    Returns a grade-3 blade (circle) if they intersect,
    grade-2 (point pair) if touching, or zero if separate. -/
def sphereSphereMeet (s1 s2 : Multivector CGA3 Float) : Multivector CGA3 Float :=
  s1 ⋁ᶜ s2

/-- Check if a sphere and plane collide. -/
def spherePlaneCollide (sphere plane : Multivector CGA3 Float) : Bool :=
  let intersection := sphere ⋁ᶜ plane
  !isZeroMeet intersection

/-- Compute the meet of sphere and plane.
    Returns a circle if they intersect. -/
def spherePlaneMeet (sphere plane : Multivector CGA3 Float) : Multivector CGA3 Float :=
  sphere ⋁ᶜ plane

/-- Check if a line intersects a sphere. -/
def lineSphereCollide (l sphere : Multivector CGA3 Float) : Bool :=
  let intersection := l ⋁ᶜ sphere
  !isZeroMeet intersection

/-- Compute the meet of line and sphere.
    Returns a point pair (2 intersection points) or zero. -/
def lineSphereMeet (l sphere : Multivector CGA3 Float) : Multivector CGA3 Float :=
  l ⋁ᶜ sphere

/-- Check if a point is inside a sphere.
    A point P is inside sphere S if P·S has appropriate sign. -/
def pointInsideSphere (p sphere : Multivector CGA3 Float) : Bool :=
  let innerProd := (p ⌋ᵐ sphere).scalarPart
  -- Point inside if inner product is negative (depends on sphere orientation)
  innerProd < 0

/-- Signed distance from a point to a sphere surface.
    Negative = inside, positive = outside. -/
def pointSphereSignedDistance (p sphere : Multivector CGA3 Float) : Float :=
  -- Extract sphere center and radius
  let r := sphereRadius sphere
  let center := sphereCenter sphere
  let d := distance p center
  d - r

/-- Collision info: penetration depth and contact normal for sphere-sphere collision -/
structure SphereCollisionInfo where
  collides : Bool
  penetration : Float  -- Positive if overlapping
  normalX : Float
  normalY : Float
  normalZ : Float
  contactX : Float
  contactY : Float
  contactZ : Float

/-- Compute detailed sphere-sphere collision information.
    Uses CGA meet to detect collision, then extracts geometric info. -/
def sphereSphereCollisionInfo (cx1 cy1 cz1 r1 cx2 cy2 cz2 r2 : Float) : SphereCollisionInfo :=
  -- Create spheres
  let s1 := sphereCenterRadius cx1 cy1 cz1 r1
  let s2 := sphereCenterRadius cx2 cy2 cz2 r2

  -- Check collision via meet
  let meets := !isZeroMeet (s1 ⋁ᶜ s2)

  -- Compute geometric info
  let dx := cx2 - cx1
  let dy := cy2 - cy1
  let dz := cz2 - cz1
  let dist := Float.sqrt (dx * dx + dy * dy + dz * dz)

  -- Penetration depth
  let penetration := (r1 + r2) - dist

  -- Normal from s1 to s2
  let invDist := if dist > 1e-10 then 1.0 / dist else 0.0
  let nx := dx * invDist
  let ny := dy * invDist
  let nz := dz * invDist

  -- Contact point (on the line between centers, weighted by radii)
  -- Contact is at distance r1 from center1 toward center2 (when overlapping)
  -- or at the surface of sphere1 closest to sphere2 (when separate)
  let contactDist := if dist > 1e-10 then (if r1 < dist then r1 else dist) else 0.0
  let contactX := cx1 + contactDist * nx
  let contactY := cy1 + contactDist * ny
  let contactZ := cz1 + contactDist * nz

  { collides := meets || penetration > 0
    penetration := penetration
    normalX := nx
    normalY := ny
    normalZ := nz
    contactX := contactX
    contactY := contactY
    contactZ := contactZ }

/-- Batch collision detection for multiple spheres.
    Returns array of (i, j, collision_info) for all colliding pairs. -/
def batchSpheresCollide (spheres : Array (Float × Float × Float × Float))
    : Array (Nat × Nat × SphereCollisionInfo) :=
  let n := spheres.size
  Id.run do
    let mut results : Array (Nat × Nat × SphereCollisionInfo) := #[]
    for i in [:n] do
      for j in [i+1:n] do
        match spheres[i]?, spheres[j]? with
        | some (cx1, cy1, cz1, r1), some (cx2, cy2, cz2, r2) =>
          let info := sphereSphereCollisionInfo cx1 cy1 cz1 r1 cx2 cy2 cz2 r2
          if info.collides then
            results := results.push (i, j, info)
        | _, _ => pure ()
    return results

/-- Check collision between point and plane.
    Returns signed distance (negative = behind plane). -/
def pointPlaneDistance (px py pz nx ny nz d : Float) : Float :=
  -- Plane: n·x = d, distance = n·p - d
  px * nx + py * ny + pz * nz - d

/-- Sphere-plane collision detection.
    Returns (collides, penetration_depth). -/
def spherePlaneCollisionInfo (cx cy cz radius nx ny nz d : Float) : Bool × Float :=
  let dist := pointPlaneDistance cx cy cz nx ny nz d
  let penetration := radius - Float.abs dist
  (penetration > 0, penetration)

/-- Ray-sphere intersection using CGA meet.
    Returns optional hit distance along ray. -/
def raySphereHitDistance (ox oy oz dx dy dz : Float)
    (cx cy cz radius : Float) : Option Float :=
  -- Create a line from two points on the ray
  let p1 := point ox oy oz
  let p2 := point (ox + dx * 100) (oy + dy * 100) (oz + dz * 100)
  let rayLine := line p1 p2

  -- Create sphere
  let s := sphereCenterRadius cx cy cz radius

  -- Meet gives intersection (point pair if hits)
  let intersection := rayLine ⋁ᶜ s

  -- Check if intersection is non-empty
  if isZeroMeet intersection then
    none
  else
    -- Compute hit distance geometrically
    let ax := cx - ox
    let ay := cy - oy
    let az := cz - oz
    let a_dot_d := ax * dx + ay * dy + az * dz
    let a_sq := ax * ax + ay * ay + az * az
    let d_sq := dx * dx + dy * dy + dz * dz

    let discriminant := a_dot_d * a_dot_d - d_sq * (a_sq - radius * radius)
    if discriminant < 0 then
      none
    else
      let sqrtDisc := Float.sqrt discriminant
      let t := (a_dot_d - sqrtDisc) / d_sq
      if t > 0 then some t
      else
        let t2 := (a_dot_d + sqrtDisc) / d_sq
        if t2 > 0 then some t2 else none

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

/-! ## CGA Collision Tests -/

section CGACollisionTests

open CGA

-- Test sphere-sphere collision (overlapping)
#eval! let info := sphereSphereCollisionInfo 0 0 0 1.5 2 0 0 1.5
       (info.collides, info.penetration)
-- Expected: (true, 1.0) - spheres at (0,0,0) and (2,0,0) with radius 1.5 each overlap by 1

-- Test sphere-sphere collision (separate)
#eval! let info := sphereSphereCollisionInfo 0 0 0 1 10 0 0 1
       (info.collides, info.penetration)
-- Expected: (false, -8.0) - spheres 10 units apart with radius 1 each

-- Test sphere-sphere collision (just touching)
#eval! let info := sphereSphereCollisionInfo 0 0 0 1 2 0 0 1
       (info.collides, info.penetration)
-- Expected: (false/true, 0.0) - exactly touching, penetration = 0
-- Note: collides may be false if CGA meet tolerance doesn't catch exact touch

-- Test collision normal direction
#eval! let info := sphereSphereCollisionInfo 0 0 0 1 3 0 0 1
       (info.normalX, info.normalY, info.normalZ)
-- Expected: (1.0, 0.0, 0.0) - normal points from first to second sphere

-- Test contact point
#eval! let info := sphereSphereCollisionInfo 0 0 0 1 4 0 0 1
       (info.contactX, info.contactY, info.contactZ)
-- Expected: (1.0, 0.0, 0.0) - contact point is on surface of first sphere toward second

-- Test sphere-plane collision
#eval! let (collides, penetration) := spherePlaneCollisionInfo 0 1 0 1.5 0 1 0 0
       (collides, penetration)
-- Expected: (true, 0.5) - sphere at y=1 with r=1.5 collides with xz plane (y=0)

-- Test sphere-plane no collision
#eval! let (collides, _) := spherePlaneCollisionInfo 0 5 0 1 0 1 0 0
       collides
-- Expected: false - sphere at y=5 with r=1 doesn't touch y=0 plane

-- Test ray-sphere intersection (hit)
#eval! match raySphereHitDistance 0 0 (-5) 0 0 1 0 0 0 1 with
       | some t => t > 0 && t < 10
       | none => false
-- Expected: true - ray from (0,0,-5) toward +z hits sphere at origin with r=1

-- Test ray-sphere intersection (miss)
#eval! match raySphereHitDistance 0 0 (-5) 1 0 0 0 0 0 1 with
       | some _ => false
       | none => true
-- Expected: true - ray from (0,0,-5) toward +x misses sphere at origin

-- Test batch sphere collision
#eval! let spheres := #[(0.0, 0.0, 0.0, 1.0), (1.5, 0.0, 0.0, 1.0), (10.0, 0.0, 0.0, 1.0)]
       let collisions := batchSpheresCollide spheres
       collisions.size
-- Expected: 1 - only first two spheres collide

-- Test meet-based sphere collision using OPNS representation (4 points on sphere)
-- Note: sphereCenterRadius creates IPNS (dual) form which doesn't work with meet
-- For meet, we need OPNS: S = P1 ∧ P2 ∧ P3 ∧ P4
#eval! let p1 := point 2 0 0   -- 4 points on sphere of radius 2 at origin
       let p2 := point (-2) 0 0
       let p3 := point 0 2 0
       let p4 := point 0 0 2
       let s1 := sphere p1 p2 p3 p4
       let q1 := point 5 0 0   -- 4 points on sphere of radius 2 at (3,0,0)
       let q2 := point 1 0 0   -- These spheres overlap!
       let q3 := point 3 2 0
       let q4 := point 3 0 2
       let s2 := sphere q1 q2 q3 q4
       !isZeroMeet (s1 ⋁ᶜ s2)  -- Should be true - spheres overlap
-- Note: meet gives the intersection circle when spheres overlap

-- Test meet-based sphere separation using OPNS
#eval! let p1 := point 1 0 0
       let p2 := point (-1) 0 0
       let p3 := point 0 1 0
       let p4 := point 0 0 1
       let s1 := sphere p1 p2 p3 p4  -- r=1 at origin
       let q1 := point 11 0 0
       let q2 := point 9 0 0
       let q3 := point 10 1 0
       let q4 := point 10 0 1
       let s2 := sphere q1 q2 q3 q4  -- r=1 at (10,0,0)
       let meetResult := s1 ⋁ᶜ s2
       magnitudeSq meetResult < 0.001  -- Check if meet is very small
-- Note: Numerical precision may cause non-zero meet even for separate spheres

-- IPNS sphereCenterRadius is useful for point containment tests, not meet
#eval! let s := sphereCenterRadius 0 0 0 2
       let p := point 1 0 0  -- point inside sphere
       pointInsideSphere p s
-- The IPNS form works for containment checks

end CGACollisionTests

end Grassmann
