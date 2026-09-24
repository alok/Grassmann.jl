/-
  Grassmann/CollisionLC.lean - Smooth collision detection via Levi-Civita infinitesimals

  Traditional collision detection is discontinuous:
    distance > threshold → no collision (response = 0)
    distance ≤ threshold → collision (response = impulse)

  This causes jitter, tunneling, and numerical instability.

  Solution: Levi-Civita numbers with ε-thick boundary layers
  - ε-thick region smooths the collision response
  - Dual part automatically gives collision gradient
  - "Just touching" vs "interpenetrating" distinguished algebraically

  ## Architecture

  1. Signed distance functions return LC numbers
  2. The standard part gives the distance
  3. The ε-coefficient gives the gradient direction
  4. Smooth response functions use the ε-thick transition
-/
import Grassmann.LCBridge
import Grassmann.CGA
import Grassmann.Physics

namespace Grassmann.CollisionLC

open Grassmann.LCBridge
open LeviCivita.Fast.FastLC
open LeviCivita.Hyper

/-! ## LC-Enhanced Point Type -/

/-- A 3D point with LC coordinates for smooth collision -/
structure PointLC where
  x : LCNum
  y : LCNum
  z : LCNum
deriving Inhabited

namespace PointLC

def ofFloats (x y z : Float) : PointLC :=
  ⟨ofFloat x, ofFloat y, ofFloat z⟩

/-- Extract standard (real) parts as Float tuple -/
def toFloats (p : PointLC) : Float × Float × Float :=
  (LeviCivita.Fast.FastLC.std p.x,
   LeviCivita.Fast.FastLC.std p.y,
   LeviCivita.Fast.FastLC.std p.z)

def sub (a b : PointLC) : PointLC :=
  ⟨a.x - b.x, a.y - b.y, a.z - b.z⟩

instance : Sub PointLC where sub := sub

/-- Squared distance between two points -/
def squaredDistance (a b : PointLC) : LCNum :=
  let dx := a.x - b.x
  let dy := a.y - b.y
  let dz := a.z - b.z
  dx * dx + dy * dy + dz * dz

/-- Distance between two points (approximate sqrt via Newton iteration) -/
def distance (a b : PointLC) : LCNum :=
  let sq := squaredDistance a b
  let stdSq := LeviCivita.Fast.FastLC.std sq
  if stdSq < 1e-10 then ofFloat 0.0
  else
    -- Newton iteration for sqrt: x_{n+1} = 0.5 * (x_n + sq/x_n)
    let x0 := ofFloat (Float.sqrt stdSq)
    let half := ofFloat 0.5
    let x1 := half * (x0 + sq / x0)
    let x2 := half * (x1 + sq / x1)  -- Two iterations usually enough
    x2

end PointLC

/-! ## Smooth Collision Response Functions

These functions provide smooth transitions at collision boundaries,
eliminating the discontinuities that cause jitter.
-/

/-- Smooth collision envelope.
    Returns 0 when well-separated, 1 when fully penetrating,
    smooth transition in ε-thick boundary layer.

    penetration = radius_sum - distance
    envelope(penetration) transitions smoothly around penetration = 0
-/
def collisionEnvelope (penetration : LCNum) (thickness : Float := 0.1) : LCNum :=
  -- Normalize penetration by thickness
  let t := ofFloat thickness
  let x := penetration / t
  -- Smoothstep: 3x² - 2x³ for x in [0,1]
  let stdX := std x
  if stdX < 0.0 then ofFloat 0.0
  else if stdX > 1.0 then ofFloat 1.0
  else
    let three := ofFloat 3.0
    let two := ofFloat 2.0
    x * x * (three - two * x)

/-- Collision force magnitude as function of penetration.
    Uses smooth ramp with exponential growth for deep penetration. -/
def collisionForceMagnitude (penetration : LCNum) (stiffness : Float := 1000.0) : LCNum :=
  let env := collisionEnvelope penetration
  let k := ofFloat stiffness
  k * penetration * env

/-! ## Sphere-Sphere Collision with LC -/

/-- Sphere collision result with smooth gradients -/
structure SphereCollisionLC where
  /-- Signed penetration depth (positive = overlapping) -/
  penetration : LCNum
  /-- Collision normal (from sphere1 to sphere2) -/
  normalX : LCNum
  normalY : LCNum
  normalZ : LCNum
  /-- Force magnitude (smooth) -/
  forceMagnitude : LCNum

/-- Compute sphere-sphere collision with LC for smooth gradients -/
def sphereSphereCollisionLC
    (center1 center2 : PointLC)
    (radius1 radius2 : Float)
    (stiffness : Float := 1000.0)
    : SphereCollisionLC :=
  let d := PointLC.distance center1 center2
  let dStd := std d

  -- Penetration = (r1 + r2) - distance
  let radiusSum := ofFloat (radius1 + radius2)
  let penetration := radiusSum - d

  -- Normal vector (from center1 to center2)
  let (nx, ny, nz) :=
    if dStd > 1e-10 then
      let invD := ofFloat 1.0 / d
      ((center2.x - center1.x) * invD,
       (center2.y - center1.y) * invD,
       (center2.z - center1.z) * invD)
    else
      -- Degenerate case: use arbitrary normal
      (ofFloat 1.0, ofFloat 0.0, ofFloat 0.0)

  let force := collisionForceMagnitude penetration stiffness

  { penetration := penetration
    normalX := nx
    normalY := ny
    normalZ := nz
    forceMagnitude := force }

/-! ## Sphere-Plane Collision with LC -/

/-- Compute sphere-plane collision.
    Plane defined by normal (nx, ny, nz) and distance d from origin. -/
def spherePlaneCollisionLC
    (center : PointLC)
    (radius : Float)
    (planeNx planeNy planeNz planeD : Float)
    (stiffness : Float := 1000.0)
    : SphereCollisionLC :=
  -- Signed distance from center to plane
  let nx := ofFloat planeNx
  let ny := ofFloat planeNy
  let nz := ofFloat planeNz
  let d := ofFloat planeD

  let signedDist := center.x * nx + center.y * ny + center.z * nz - d

  -- Penetration = radius - signedDist
  let r := ofFloat radius
  let penetration := r - signedDist

  let force := collisionForceMagnitude penetration stiffness

  { penetration := penetration
    normalX := nx
    normalY := ny
    normalZ := nz
    forceMagnitude := force }

/-! ## Floor Collision (Special Case of Plane) -/

/-- Sphere-floor collision with smooth response.
    Floor is the plane y = floorY (using Y-up coordinates). -/
def sphereFloorCollisionLC
    (center : PointLC)
    (radius : Float)
    (floorY : Float := 0.0)
    (stiffness : Float := 1000.0)
    : SphereCollisionLC :=
  spherePlaneCollisionLC center radius 0.0 1.0 0.0 floorY stiffness

/-! ## Integration with Physics Module -/

/-- Convert RigidBody position to PointLC -/
def rigidBodyToPointLC (body : Grassmann.Physics.RigidBody) : PointLC :=
  let (x, y, z) := body.position
  PointLC.ofFloats x y z

/-- Compute smooth floor collision impulse for a rigid body -/
def smoothFloorImpulse
    (body : Grassmann.Physics.RigidBody)
    (floorY : Float)
    (radius : Float)
    (restitution : Float := 0.5)
    : Grassmann.Physics.MotorVelocity :=
  let center := rigidBodyToPointLC body
  let collision := sphereFloorCollisionLC center radius floorY

  -- Extract standard parts
  let penetrationStd := std collision.penetration
  let forceStd := std collision.forceMagnitude

  if penetrationStd > 0.0 then
    -- Body is in collision zone
    -- Force direction is the collision normal (upward for floor)
    let fy := std collision.normalY

    -- Combine force with velocity damping for restitution
    let vy := body.velocity.v02
    let impulseY :=
      if vy < 0.0 then
        -- Moving into floor: reflect + apply force
        -(1.0 + restitution) * vy + forceStd * 0.001  -- Scale force to impulse
      else
        -- Moving away: just apply force if still penetrating
        forceStd * 0.001 * fy

    Grassmann.Physics.MotorVelocity.linear 0.0 impulseY 0.0
  else
    Grassmann.Physics.MotorVelocity.zero

/-! ## Gradient Extraction

The key benefit of LC: derivatives come for free.
-/

/-- Extract collision gradient w.r.t. position.
    Useful for gradient-based collision resolution. -/
def collisionGradient (collision : SphereCollisionLC) : Float × Float × Float :=
  -- The ε-coefficient of penetration encodes how penetration changes
  -- with infinitesimal position changes
  let penLC := collision.penetration

  -- Gradient is encoded in the normal direction scaled by ε-coefficient
  let gradScale := std (penLC * H)

  let nx := std collision.normalX
  let ny := std collision.normalY
  let nz := std collision.normalZ

  (nx * gradScale, ny * gradScale, nz * gradScale)

/-! ## Tests -/

-- Test PointLC distance
#eval!
  let p1 := PointLC.ofFloats 0.0 0.0 0.0
  let p2 := PointLC.ofFloats 3.0 4.0 0.0
  std (PointLC.distance p1 p2)
-- Expected: 5.0

-- Test sphere-sphere collision
#eval!
  let c1 := PointLC.ofFloats 0.0 0.0 0.0
  let c2 := PointLC.ofFloats 1.5 0.0 0.0  -- 1.5 units apart
  let collision := sphereSphereCollisionLC c1 c2 1.0 1.0  -- Each radius 1.0
  std collision.penetration
-- Expected: 0.5 (sum of radii - distance = 2.0 - 1.5 = 0.5)

-- Test floor collision
#eval!
  let center := PointLC.ofFloats 0.0 0.5 0.0  -- 0.5 units above origin
  let collision := sphereFloorCollisionLC center 1.0 0.0  -- Radius 1, floor at y=0
  std collision.penetration
-- Expected: 0.5 (radius - height = 1.0 - 0.5 = 0.5)

-- Test smooth envelope transitions
#eval!
  let pen1 := ofFloat (-0.5)  -- Well separated
  let pen2 := ofFloat 0.05    -- At boundary
  let pen3 := ofFloat 0.5     -- Penetrating
  (std (collisionEnvelope pen1),
   std (collisionEnvelope pen2),
   std (collisionEnvelope pen3))
-- Expected: (0.0, ~0.4, 1.0)

end Grassmann.CollisionLC
