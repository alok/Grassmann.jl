/-
  Grassmann/Physics.lean - Motor-based rigid body dynamics

  PGA motors naturally represent rigid body transforms: M = R · T
  Motor velocity is a bivector: V = ω·B + v·I where
  - ω·B is the angular velocity (rotation bivector)
  - v·I is the linear velocity (translation bivector)

  Integration: M(t+dt) = exp(dt · V) · M(t)

  This gives smooth, singularity-free rigid body dynamics.
-/
import Grassmann.PGA
import Grassmann.StaticOpt
import Grassmann.CGA

namespace Grassmann.Physics

open Grassmann

/-! ## Motor Velocity

A motor velocity (twist) is a bivector in PGA3:
- Grades 2 components encode angular + linear velocity
- exp(dt · V) gives the incremental motor
-/

/-- Motor velocity (twist) in PGA3.
    Components: ω₁₂, ω₁₃, ω₂₃ (angular) + v₀₁, v₀₂, v₀₃ (linear) -/
structure MotorVelocity where
  /-- Angular velocity around e₁₂ axis (rotation in xy plane) -/
  omega12 : Float
  /-- Angular velocity around e₁₃ axis (rotation in xz plane) -/
  omega13 : Float
  /-- Angular velocity around e₂₃ axis (rotation in yz plane) -/
  omega23 : Float
  /-- Linear velocity along e₁ (via e₀₁ bivector) -/
  v01 : Float
  /-- Linear velocity along e₂ (via e₀₂ bivector) -/
  v02 : Float
  /-- Linear velocity along e₃ (via e₀₃ bivector) -/
  v03 : Float
  deriving Repr

namespace MotorVelocity

/-- Zero velocity -/
def zero : MotorVelocity :=
  { omega12 := 0, omega13 := 0, omega23 := 0, v01 := 0, v02 := 0, v03 := 0 }

/-- Pure angular velocity around z-axis -/
def angularZ (omega : Float) : MotorVelocity :=
  { omega12 := omega, omega13 := 0, omega23 := 0, v01 := 0, v02 := 0, v03 := 0 }

/-- Pure linear velocity -/
def linear (vx vy vz : Float) : MotorVelocity :=
  { omega12 := 0, omega13 := 0, omega23 := 0, v01 := vx, v02 := vy, v03 := vz }

/-- Add two velocities -/
def add (a b : MotorVelocity) : MotorVelocity :=
  { omega12 := a.omega12 + b.omega12
    omega13 := a.omega13 + b.omega13
    omega23 := a.omega23 + b.omega23
    v01 := a.v01 + b.v01
    v02 := a.v02 + b.v02
    v03 := a.v03 + b.v03 }

/-- Scale velocity by scalar -/
def scale (s : Float) (v : MotorVelocity) : MotorVelocity :=
  { omega12 := s * v.omega12
    omega13 := s * v.omega13
    omega23 := s * v.omega23
    v01 := s * v.v01
    v02 := s * v.v02
    v03 := s * v.v03 }

/-- Convert to PGA3 bivector -/
def toBivector (v : MotorVelocity) : Multivector PGA3 Float :=
  -- PGA3 indices: e0=1, e1=2, e2=4, e3=8
  -- Bivectors: e01=3, e02=5, e03=9, e12=6, e13=10, e23=12
  ⟨fun i =>
    if i.val = 3 then v.v01       -- e01
    else if i.val = 5 then v.v02  -- e02
    else if i.val = 9 then v.v03  -- e03
    else if i.val = 6 then v.omega12   -- e12
    else if i.val = 10 then v.omega13  -- e13
    else if i.val = 12 then v.omega23  -- e23
    else 0⟩

/-- Extract from PGA3 bivector -/
def fromBivector (b : Multivector PGA3 Float) : MotorVelocity :=
  { omega12 := b.coeffs ⟨6, by decide⟩
    omega13 := b.coeffs ⟨10, by decide⟩
    omega23 := b.coeffs ⟨12, by decide⟩
    v01 := b.coeffs ⟨3, by decide⟩
    v02 := b.coeffs ⟨5, by decide⟩
    v03 := b.coeffs ⟨9, by decide⟩ }

/-- Magnitude of angular velocity -/
def angularMagnitude (v : MotorVelocity) : Float :=
  Float.sqrt (v.omega12 * v.omega12 + v.omega13 * v.omega13 + v.omega23 * v.omega23)

/-- Magnitude of linear velocity -/
def linearMagnitude (v : MotorVelocity) : Float :=
  Float.sqrt (v.v01 * v.v01 + v.v02 * v.v02 + v.v03 * v.v03)

end MotorVelocity

instance : Add MotorVelocity := ⟨MotorVelocity.add⟩
instance : HMul Float MotorVelocity MotorVelocity := ⟨MotorVelocity.scale⟩

/-! ## Motor Exponential

exp(B) for bivector B gives a motor.
For small B: exp(B) ≈ 1 + B + B²/2
For rotation: exp(θ/2 · B) where B is unit bivector
-/

/-- First-order motor exponential: exp(B) ≈ 1 + B -/
@[inline]
def motorExpFirstOrder (B : Multivector PGA3 Float) : Multivector PGA3 Float :=
  Multivector.scalar 1.0 + B

/-- Second-order motor exponential: exp(B) ≈ 1 + B + B²/2 -/
@[inline]
def motorExpSecondOrder (B : Multivector PGA3 Float) : Multivector PGA3 Float :=
  let B2 := B * B
  Multivector.scalar 1.0 + B + B2.smul 0.5

/-- Full motor exponential using Rodrigues formula.
    For pure rotation bivector B with |B| = θ/2:
    exp(B) = cos(|B|) + sin(|B|)/|B| · B -/
def motorExp (B : Multivector PGA3 Float) : Multivector PGA3 Float :=
  -- Extract rotation part (e12, e13, e23) and translation part (e01, e02, e03)
  let omega12 := B.coeffs ⟨6, by decide⟩
  let omega13 := B.coeffs ⟨10, by decide⟩
  let omega23 := B.coeffs ⟨12, by decide⟩

  let thetaSq := omega12 * omega12 + omega13 * omega13 + omega23 * omega23
  let theta := Float.sqrt thetaSq

  if theta < 1e-8 then
    -- Small angle approximation
    motorExpSecondOrder B
  else
    -- Rodrigues formula for rotation part
    let c := Float.cos theta
    let s := Float.sin theta
    let sincTheta := s / theta

    -- R = cos(θ) + sin(θ)/θ · (rotation bivector)
    let R : Multivector PGA3 Float := ⟨fun i =>
      if i.val = 0 then c
      else if i.val = 6 then sincTheta * omega12
      else if i.val = 10 then sincTheta * omega13
      else if i.val = 12 then sincTheta * omega23
      else 0⟩

    -- For translation, we need T = 1 + t·e∞ (but this is PGA, not CGA)
    -- In PGA, pure translation: T = 1 + (d/2)·e0·n where n is direction
    -- Combined: M = T·R, but for velocity we have exp(ω + v) ≈ exp(ω)·exp(v)
    let v01 := B.coeffs ⟨3, by decide⟩
    let v02 := B.coeffs ⟨5, by decide⟩
    let v03 := B.coeffs ⟨9, by decide⟩

    -- Translation part: add e0·v components to rotor
    -- T·R = (1 + v·e0∧n)·R = R + v·e0∧n·R
    ⟨fun i =>
      if i.val = 0 then R.coeffs ⟨0, by decide⟩
      else if i.val = 6 then R.coeffs ⟨6, by decide⟩
      else if i.val = 10 then R.coeffs ⟨10, by decide⟩
      else if i.val = 12 then R.coeffs ⟨12, by decide⟩
      else if i.val = 3 then v01 * c  -- e01 translation
      else if i.val = 5 then v02 * c  -- e02 translation
      else if i.val = 9 then v03 * c  -- e03 translation
      else 0⟩

/-! ## Rigid Body State

A rigid body has a motor (pose) and motor velocity (twist).
-/

/-- Rigid body state in PGA3 -/
structure RigidBody where
  /-- Current pose as motor -/
  motor : Multivector PGA3 Float
  /-- Current velocity as twist -/
  velocity : MotorVelocity
  /-- Mass (for dynamics) -/
  mass : Float := 1.0
  /-- Inverse inertia tensor (simplified as scalar for now) -/
  invInertia : Float := 1.0

namespace RigidBody

/-- Identity body at origin with zero velocity -/
def identity : RigidBody :=
  { motor := Multivector.scalar 1.0
    velocity := MotorVelocity.zero
    mass := 1.0
    invInertia := 1.0 }

/-- Integrate body forward by dt using motor exponential -/
def integrate (body : RigidBody) (dt : Float) : RigidBody :=
  let dM := motorExp (body.velocity.toBivector.smul dt)
  { body with motor := dM * body.motor }

/-- Apply impulse to body (changes velocity) -/
def applyImpulse (body : RigidBody) (impulse : MotorVelocity) : RigidBody :=
  { body with velocity := MotorVelocity.add body.velocity (MotorVelocity.scale body.invInertia impulse) }

/-- Apply gravity (linear acceleration in -y direction) -/
def applyGravity (body : RigidBody) (g : Float) (dt : Float) : RigidBody :=
  let dv := MotorVelocity.linear 0 (-g * dt) 0
  { body with velocity := MotorVelocity.add body.velocity dv }

/-- Damp velocity (simple drag) -/
def applyDamping (body : RigidBody) (linearDamp angularDamp : Float) (dt : Float) : RigidBody :=
  let linFactor := Float.exp (-linearDamp * dt)
  let angFactor := Float.exp (-angularDamp * dt)
  { body with velocity :=
    { omega12 := body.velocity.omega12 * angFactor
      omega13 := body.velocity.omega13 * angFactor
      omega23 := body.velocity.omega23 * angFactor
      v01 := body.velocity.v01 * linFactor
      v02 := body.velocity.v02 * linFactor
      v03 := body.velocity.v03 * linFactor } }

/-- Extract position from motor (for rendering) -/
def position (body : RigidBody) : Float × Float × Float :=
  -- Transform origin point through motor
  let origin : Multivector PGA3 Float := ⟨fun i =>
    if i.val = 15 then 1.0 else 0⟩  -- e0123 = pseudoscalar point at origin
  let transformed := body.motor.sandwich origin
  -- Extract xyz from transformed point
  -- In PGA, point P = e123 + x·e023 + y·e031 + z·e012
  let x := transformed.coeffs ⟨14, by decide⟩  -- e023
  let y := transformed.coeffs ⟨13, by decide⟩  -- e031
  let z := transformed.coeffs ⟨11, by decide⟩  -- e012
  (x, y, z)

end RigidBody

/-! ## Collision Response

Collision response uses motor velocity reflection.
When two bodies collide, we compute impulse from penetration and normal.
-/

/-- Collision result -/
structure CollisionResult where
  hasCollision : Bool
  penetration : Float
  normalX : Float
  normalY : Float
  normalZ : Float
  contactX : Float
  contactY : Float
  contactZ : Float

/-- Compute collision impulse for sphere-floor collision -/
def floorCollisionImpulse (body : RigidBody) (floorY : Float) (radius : Float)
    (restitution : Float := 0.5) : Option MotorVelocity :=
  let (_, y, _) := body.position
  let penetration := floorY + radius - y
  if penetration > 0 then
    -- Body is penetrating floor
    -- Reflect velocity in y direction
    let vy := body.velocity.v02
    if vy < 0 then
      -- Moving down, need to bounce
      let impulseY := -(1 + restitution) * vy
      some (MotorVelocity.linear 0 impulseY 0)
    else
      -- Already moving up, just need position correction
      some MotorVelocity.zero
  else
    none

/-- Compute collision impulse for sphere-sphere collision -/
def sphereCollisionImpulse (body1 body2 : RigidBody) (r1 r2 : Float)
    (restitution : Float := 0.5) : Option (MotorVelocity × MotorVelocity) :=
  let (x1, y1, z1) := body1.position
  let (x2, y2, z2) := body2.position
  let dx := x2 - x1
  let dy := y2 - y1
  let dz := z2 - z1
  let distSq := dx*dx + dy*dy + dz*dz
  let minDist := r1 + r2

  if distSq < minDist * minDist && distSq > 1e-10 then
    let dist := Float.sqrt distSq
    let nx := dx / dist
    let ny := dy / dist
    let nz := dz / dist

    -- Relative velocity along normal
    let v1n := body1.velocity.v01 * nx + body1.velocity.v02 * ny + body1.velocity.v03 * nz
    let v2n := body2.velocity.v01 * nx + body2.velocity.v02 * ny + body2.velocity.v03 * nz
    let relVn := v1n - v2n

    if relVn > 0 then
      -- Bodies approaching
      let totalInvMass := 1.0/body1.mass + 1.0/body2.mass
      let j := -(1 + restitution) * relVn / totalInvMass

      let imp1 := MotorVelocity.linear (-j * nx / body1.mass) (-j * ny / body1.mass) (-j * nz / body1.mass)
      let imp2 := MotorVelocity.linear (j * nx / body2.mass) (j * ny / body2.mass) (j * nz / body2.mass)
      some (imp1, imp2)
    else
      none
  else
    none

/-! ## Physics World

A collection of rigid bodies with gravity and collision handling.
-/

/-- Physics world state -/
structure World where
  bodies : Array RigidBody
  gravity : Float := 9.81
  floorY : Float := 0.0
  sphereRadius : Float := 1.0  -- Uniform radius for now

namespace World

/-- Create a PGA3 translator motor -/
private def makeTranslator (tx ty tz : Float) : Multivector PGA3 Float :=
  (Multivector.one : Multivector PGA3 Float)
    |>.add ((Multivector.ofBlade PGA.e01).smul (tx / 2))
    |>.add ((Multivector.ofBlade PGA.e02).smul (ty / 2))
    |>.add ((Multivector.ofBlade PGA.e03).smul (tz / 2))

/-- Create world with n bodies at given positions -/
def create (positions : Array (Float × Float × Float)) (radius : Float := 1.0) : World :=
  let bodies := positions.map fun (x, y, z) =>
    let translation := makeTranslator x y z
    { RigidBody.identity with motor := translation }
  { bodies := bodies, sphereRadius := radius }

/-- Handle floor collision for a single body -/
private def handleFloorCollision (b : RigidBody) (floorY radius : Float) : RigidBody :=
  match floorCollisionImpulse b floorY radius with
  | some imp =>
    let b' := b.applyImpulse imp
    let (_, y, _) := b'.position
    let correction := floorY + radius - y
    if correction > 0 then
      let correctionMotor := makeTranslator 0 correction 0
      { b' with motor := correctionMotor * b'.motor }
    else b'
  | none => b

/-- Step the simulation forward by dt (simplified version) -/
def step (world : World) (dt : Float) : World :=
  -- 1. Apply gravity and integrate
  let bodies := world.bodies.map fun b =>
    let b' := b.applyGravity world.gravity dt
    b'.integrate dt

  -- 2. Handle floor collisions
  let bodies := bodies.map fun b =>
    handleFloorCollision b world.floorY world.sphereRadius

  -- 3. Apply damping
  let bodies := bodies.map fun b => b.applyDamping 0.1 0.1 dt

  { world with bodies := bodies }

/-- Get all positions for rendering -/
def positions (world : World) : Array (Float × Float × Float) :=
  world.bodies.map RigidBody.position

/-- Run simulation for n steps -/
def simulate (world : World) (dt : Float) (steps : Nat) : World :=
  match steps with
  | 0 => world
  | n + 1 => simulate (world.step dt) dt n

end World

/-! ## Tests -/

-- Test motor velocity conversion
#eval!
  let v := MotorVelocity.linear 1 2 3
  let b := v.toBivector
  let v' := MotorVelocity.fromBivector b
  (v'.v01, v'.v02, v'.v03)
-- Expected: (1.0, 2.0, 3.0)

-- Test angular velocity
#eval!
  let v := MotorVelocity.angularZ 0.5
  v.angularMagnitude
-- Expected: 0.5

-- Test motor exponential (small angle)
#eval!
  let B := (MotorVelocity.angularZ 0.01).toBivector
  let M := motorExp B
  M.scalarPart  -- Should be close to 1
-- Expected: ~0.99995

-- Test rigid body integration
#eval!
  let body : RigidBody := {
    motor := Multivector.scalar 1.0
    velocity := MotorVelocity.linear 1 0 0
    mass := 1.0
    invInertia := 1.0 }
  let body' := body.integrate 1.0
  body'.position
-- Expected: approximately (1, 0, 0) - but motor exp for translation is tricky

-- Test floor collision - manually test body position
#eval!
  let body : RigidBody := {
    motor := Multivector.scalar 1.0
    velocity := MotorVelocity.linear 0 (-5) 0  -- Falling down
    mass := 1.0
    invInertia := 1.0 }
  let body' := body.integrate 0.5  -- Move down
  body'.velocity.v02  -- Show the velocity
-- Note: Position should have moved down due to negative y velocity

-- Test physics world step
#eval!
  let world := World.create #[(0, 5, 0), (3, 5, 0)] 1.0
  let world' := world.simulate 0.016 10  -- ~10 frames at 60fps
  world'.positions.size
-- Expected: 2

/-! ## Unreal Engine Visualization Export

Functions to export simulation data for Unreal MCP visualization.
Converts motor-based physics to Unreal transform format.
-/

/-- A frame of simulation data for Unreal -/
structure UnrealFrame where
  frameIndex : Nat
  time : Float
  positions : Array (Float × Float × Float)
  deriving Repr, Inhabited

/-- Convert position tuple to Unreal-compatible format (Y-up to Z-up) -/
def toUnrealPos (pos : Float × Float × Float) : Float × Float × Float :=
  let (x, y, z) := pos
  -- Unreal uses Z-up, our physics uses Y-up
  -- Also scale from meters to Unreal units (cm)
  (x * 100, z * 100, y * 100)

/-- Generate simulation frames for Unreal visualization -/
def generateUnrealFrames (world : World) (dt : Float) (numFrames : Nat)
    : Array UnrealFrame := Id.run do
  let mut frames : Array UnrealFrame := #[]
  let mut w := world
  for i in [:numFrames] do
    let positions := w.positions.map toUnrealPos
    frames := frames.push {
      frameIndex := i
      time := dt * Float.ofNat i
      positions := positions
    }
    w := w.step dt
  frames

/-- Format a single position as Unreal MCP command -/
def formatUnrealSetTransform (actorName : String) (pos : Float × Float × Float) : String :=
  let (x, y, z) := pos
  s!"set_actor_transform {actorName} location=[{x}, {y}, {z}]"

/-- Generate all set_actor_transform commands for a frame -/
def frameToCommands (frame : UnrealFrame) (actorNames : Array String) : Array String :=
  if h : frame.positions.size = actorNames.size then
    let rec go (i : Nat) (acc : Array String) : Array String :=
      if hi : i < actorNames.size then
        let name := actorNames[i]
        have hi' : i < frame.positions.size := by omega
        let pos := frame.positions[i]
        go (i + 1) (acc.push (formatUnrealSetTransform name pos))
      else acc
    go 0 #[]
  else #[]

/-- Demo: Create a bouncing balls simulation for Unreal -/
def bouncingBallsDemo : Array UnrealFrame :=
  -- Create 4 spheres at different heights
  let world := World.create #[
    (0, 5, 0),      -- Red sphere at center
    (2, 8, 0),      -- Green sphere offset
    (-2, 11, 0),    -- Blue sphere higher
    (1, 6, 2)       -- Yellow sphere offset in z
  ] 1.0
  generateUnrealFrames world 0.016 300  -- ~5 seconds at 60fps

-- Test Unreal frame generation
#eval!
  let frames := bouncingBallsDemo
  (frames.size, frames[0]!.positions.size)
-- Expected: (300, 4)

-- Test single frame positions
#eval!
  let frames := bouncingBallsDemo
  frames[0]!.positions[0]!
-- Expected: (0, 0, 500) - in Unreal units (cm), Z-up

-- Test frame after some simulation
#eval!
  let frames := bouncingBallsDemo
  frames[30]!.positions[0]!
-- Expected: position after ~0.5 seconds of falling

/-! ## Pendulum Simulation

A pendulum using motor-based constraint solving.
The pendulum bob is constrained to a fixed distance from the pivot.
-/

/-- Pendulum state -/
structure Pendulum where
  /-- Current angle from vertical (radians) -/
  angle : Float
  /-- Angular velocity -/
  angularVelocity : Float
  /-- Length of pendulum -/
  length : Float
  /-- Pivot position -/
  pivotX : Float
  pivotY : Float
  pivotZ : Float
  /-- Mass of bob -/
  mass : Float := 1.0

namespace Pendulum

/-- Create a pendulum with initial angle -/
def create (pivotX pivotY pivotZ : Float) (length : Float) (initAngle : Float := 0.5) : Pendulum :=
  { angle := initAngle
    angularVelocity := 0
    length := length
    pivotX := pivotX
    pivotY := pivotY
    pivotZ := pivotZ }

/-- Get bob position (swings in XY plane, Z fixed) -/
def bobPosition (p : Pendulum) : Float × Float × Float :=
  let x := p.pivotX + p.length * Float.sin p.angle
  let y := p.pivotY - p.length * Float.cos p.angle
  (x, y, p.pivotZ)

/-- Step pendulum using simple Euler integration.
    θ'' = -(g/L) * sin(θ) -/
def step (p : Pendulum) (g : Float) (dt : Float) (damping : Float := 0.01) : Pendulum :=
  -- Angular acceleration: -(g/L) * sin(θ)
  let angularAccel := -(g / p.length) * Float.sin p.angle
  -- Euler integration
  let newAngVel := p.angularVelocity + angularAccel * dt
  -- Apply damping
  let newAngVel := newAngVel * (1 - damping)
  let newAngle := p.angle + newAngVel * dt
  { p with angle := newAngle, angularVelocity := newAngVel }

/-- Create PGA motor for pendulum bob position -/
def toMotor (p : Pendulum) : Multivector PGA3 Float :=
  let (x, y, z) := p.bobPosition
  World.makeTranslator x y z

end Pendulum

/-- Run pendulum simulation for n steps -/
def simulatePendulum (p : Pendulum) (g : Float) (dt : Float) (steps : Nat) : Array Pendulum :=
  let rec go (n : Nat) (current : Pendulum) (acc : Array Pendulum) : Array Pendulum :=
    if n = 0 then acc
    else
      let next := current.step g dt
      go (n - 1) next (acc.push next)
  go steps p #[p]

/-- Generate Unreal frames for pendulum -/
def pendulumToFrames (p : Pendulum) (g : Float) (dt : Float) (numFrames : Nat)
    : Array UnrealFrame :=
  let rec go (n : Nat) (idx : Nat) (current : Pendulum) (acc : Array UnrealFrame)
      : Array UnrealFrame :=
    if n = 0 then acc
    else
      let pos := toUnrealPos current.bobPosition
      let frame : UnrealFrame := {
        frameIndex := idx
        time := dt * Float.ofNat idx
        positions := #[pos]
      }
      go (n - 1) (idx + 1) (current.step g dt) (acc.push frame)
  go numFrames 0 p #[]

/-- Demo: Pendulum simulation for Unreal -/
def pendulumDemo : Array UnrealFrame :=
  let p := Pendulum.create 0 10 0 5.0 0.8  -- Pivot at (0,10,0), length 5, initial angle 0.8 rad
  pendulumToFrames p 9.81 0.016 600  -- ~10 seconds at 60fps

-- Test pendulum
#eval!
  let p := Pendulum.create 0 10 0 5.0 0.5
  p.bobPosition
-- Expected: ~(2.4, 5.6, 0) since sin(0.5)≈0.48, cos(0.5)≈0.88

#eval!
  let p := Pendulum.create 0 10 0 5.0 0.5
  let p' := p.step 9.81 0.1
  p'.angularVelocity
-- Expected: negative (accelerating toward center)

/-! ## Combined Demo: Bouncing Balls + Pendulum

A complete physics scene with multiple elements.
-/

/-- Combined physics scene state -/
structure PhysicsScene where
  world : World         -- Bouncing balls
  pendulum : Pendulum   -- Swinging pendulum
  time : Float := 0

namespace PhysicsScene

/-- Create a demo scene -/
def create : PhysicsScene :=
  { world := World.create #[(0, 8, -5), (3, 10, -5), (-2, 12, -5)] 1.0
    pendulum := Pendulum.create 0 15 5 6.0 0.7
    time := 0 }

/-- Step the entire scene -/
def step (scene : PhysicsScene) (dt : Float) : PhysicsScene :=
  { world := scene.world.step dt
    pendulum := scene.pendulum.step scene.world.gravity dt
    time := scene.time + dt }

/-- Get all positions (balls + pendulum bob) for Unreal -/
def positions (scene : PhysicsScene) : Array (Float × Float × Float) :=
  let ballPositions := scene.world.positions.map toUnrealPos
  let pendulumPos := toUnrealPos scene.pendulum.bobPosition
  ballPositions.push pendulumPos

/-- Generate combined frames -/
def toFrames (scene : PhysicsScene) (dt : Float) (numFrames : Nat)
    : Array UnrealFrame :=
  let rec go (n : Nat) (idx : Nat) (current : PhysicsScene) (acc : Array UnrealFrame)
      : Array UnrealFrame :=
    if n = 0 then acc
    else
      let frame : UnrealFrame := {
        frameIndex := idx
        time := current.time
        positions := current.positions
      }
      go (n - 1) (idx + 1) (current.step dt) (acc.push frame)
  go numFrames 0 scene #[]

end PhysicsScene

/-- Demo: Full physics scene with balls and pendulum -/
def physicsSceneDemo : Array UnrealFrame :=
  PhysicsScene.create.toFrames 0.016 600  -- 10 seconds

-- Test combined scene
#eval!
  let scene := PhysicsScene.create
  scene.positions.size
-- Expected: 4 (3 balls + 1 pendulum bob)

#eval!
  let frames := physicsSceneDemo
  (frames.size, frames[0]!.positions.size)
-- Expected: (600, 4)

/-! ## CGA-Based Collision Detection

Integration with CGA meet products for elegant collision detection.
-/

/-- Check all sphere-sphere collisions using CGA meet -/
def cgaCheckSphereCollisions (world : World) : Array (Nat × Nat × CGA.SphereCollisionInfo) :=
  let n := world.bodies.size
  let r := world.sphereRadius
  -- Use simple fold-based approach to avoid termination issues
  let pairs := Id.run do
    let mut results : Array (Nat × Nat) := #[]
    for i in List.range n do
      for j in List.range n do
        if i < j then results := results.push (i, j)
    results
  pairs.filterMap fun (i, j) =>
    if hi : i < world.bodies.size then
      if hj : j < world.bodies.size then
        let b1 := world.bodies[i]
        let b2 := world.bodies[j]
        let (x1, y1, z1) := b1.position
        let (x2, y2, z2) := b2.position
        let info := CGA.sphereSphereCollisionInfo x1 y1 z1 r x2 y2 z2 r
        if info.collides then some (i, j, info) else none
      else none
    else none

/-- Apply CGA collision response -/
def applyCGACollisionResponse (world : World) : World :=
  let collisions := cgaCheckSphereCollisions world
  let rec applyImpulses (idx : Nat) (bodies : Array RigidBody) : Array RigidBody :=
    if h : idx < collisions.size then
      let (i, j, info) := collisions[idx]
      let bodies' :=
        if hi : i < bodies.size then
          if hj : j < bodies.size then
            let b1 := bodies[i]
            let b2 := bodies[j]
            -- Compute impulse magnitude
            let relVx := b1.velocity.v01 - b2.velocity.v01
            let relVy := b1.velocity.v02 - b2.velocity.v02
            let relVz := b1.velocity.v03 - b2.velocity.v03
            let relVn := relVx * info.normalX + relVy * info.normalY + relVz * info.normalZ
            if relVn > 0 then
              let restitution := 0.8
              let totalInvMass := 1.0/b1.mass + 1.0/b2.mass
              let jImpulse := -(1 + restitution) * relVn / totalInvMass
              let impulse1X := -jImpulse * info.normalX / b1.mass
              let impulse1Y := -jImpulse * info.normalY / b1.mass
              let impulse1Z := -jImpulse * info.normalZ / b1.mass
              let impulse2X := jImpulse * info.normalX / b2.mass
              let impulse2Y := jImpulse * info.normalY / b2.mass
              let impulse2Z := jImpulse * info.normalZ / b2.mass
              let newB1 := b1.applyImpulse (MotorVelocity.linear impulse1X impulse1Y impulse1Z)
              let newB2 := b2.applyImpulse (MotorVelocity.linear impulse2X impulse2Y impulse2Z)
              bodies.set! i newB1 |>.set! j newB2
            else bodies
          else bodies
        else bodies
      applyImpulses (idx + 1) bodies'
    else bodies
  { world with bodies := applyImpulses 0 world.bodies }

/-- Enhanced world step with CGA collision -/
def World.stepWithCGA (world : World) (dt : Float) : World :=
  -- 1. Apply gravity and integrate
  let bodies := world.bodies.map fun b =>
    let b' := b.applyGravity world.gravity dt
    b'.integrate dt
  let world' := { world with bodies := bodies }
  -- 2. CGA sphere-sphere collision
  let world' := applyCGACollisionResponse world'
  -- 3. Floor collisions
  let bodies := world'.bodies.map fun b =>
    World.handleFloorCollision b world'.floorY world'.sphereRadius
  -- 4. Damping
  let bodies := bodies.map fun b => b.applyDamping 0.1 0.1 dt
  { world' with bodies := bodies }

/-- Demo: Colliding balls with CGA detection -/
def cgaCollisionDemo : Array UnrealFrame :=
  -- Place balls close together so they'll collide
  let world := World.create #[
    (-3, 5, 0),     -- Ball moving right
    (3, 5, 0),      -- Ball moving left
    (0, 10, 0)      -- Ball falling from above
  ] 1.5
  -- Give initial velocities
  let bodies := world.bodies
  let bodies :=
    if h0 : 0 < bodies.size
    then bodies.set! 0 { bodies[0] with velocity := MotorVelocity.linear 5 0 0 }
    else bodies
  let bodies :=
    if h1 : 1 < bodies.size
    then bodies.set! 1 { bodies[1] with velocity := MotorVelocity.linear (-5) 0 0 }
    else bodies
  let world := { world with bodies := bodies }
  -- Simulate with CGA collision using recursive function
  let rec simulate (n : Nat) (w : World) (acc : Array UnrealFrame) : Array UnrealFrame :=
    if n = 0 then acc
    else
      let positions := w.positions.map toUnrealPos
      let frame : UnrealFrame := {
        frameIndex := 400 - n
        time := 0.016 * Float.ofNat (400 - n)
        positions := positions
      }
      simulate (n - 1) (w.stepWithCGA 0.016) (acc.push frame)
  simulate 400 world #[]

-- Test CGA collision demo
#eval!
  let frames := cgaCollisionDemo
  frames.size
-- Expected: 400

#eval!
  let world := World.create #[(0, 5, 0), (1.5, 5, 0)] 1.0  -- Overlapping spheres
  let collisions := cgaCheckSphereCollisions world
  collisions.size
-- Expected: 1 (one collision pair)

end Grassmann.Physics
