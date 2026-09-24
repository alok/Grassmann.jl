/-
  Grassmann/Constraints.lean - PGA-based constraint types for rigid body dynamics

  Constraints in PGA are naturally expressed as geometric conditions:
  - Ball joint: Point P lies on both bodies
      P = M₁ · P₀ · M₁† = M₂ · P₀ · M₂†
  - Hinge joint: Line L shared by both bodies
      L = M₁ · L₀ · M₁† = M₂ · L₀ · M₂†
  - Slider: Point constrained to line
      P lies on L

  Solving uses motor gradient descent on constraint residuals.
-/
import Grassmann.PGA
import Grassmann.Physics
import Grassmann.LCBridge

namespace Grassmann.Constraints

open Grassmann
open Grassmann.Physics

/-! ## Constraint Types -/

/-- Reference to a rigid body by index -/
structure BodyRef where
  index : Nat
  deriving Repr, Inhabited

/-- A point in local coordinates of a body -/
structure LocalPoint where
  x : Float
  y : Float
  z : Float
  deriving Repr, Inhabited

/-- An axis in local coordinates of a body -/
structure LocalAxis where
  x : Float
  y : Float
  z : Float
  deriving Repr, Inhabited

/-- Ball joint: connects two bodies at a point.
    The constraint is that the world-space positions of the attachment points match. -/
structure BallJoint where
  /-- First body -/
  body1 : BodyRef
  /-- Attachment point in body1's local frame -/
  anchor1 : LocalPoint
  /-- Second body -/
  body2 : BodyRef
  /-- Attachment point in body2's local frame -/
  anchor2 : LocalPoint
  deriving Repr, Inhabited

/-- Hinge joint: allows rotation around a shared axis.
    Constrains both position (ball joint) and axis alignment. -/
structure HingeJoint where
  /-- First body -/
  body1 : BodyRef
  /-- Attachment point in body1's local frame -/
  anchor1 : LocalPoint
  /-- Hinge axis in body1's local frame -/
  axis1 : LocalAxis
  /-- Second body -/
  body2 : BodyRef
  /-- Attachment point in body2's local frame -/
  anchor2 : LocalPoint
  /-- Hinge axis in body2's local frame -/
  axis2 : LocalAxis
  deriving Repr, Inhabited

/-- Slider joint: allows translation along a line.
    Point on body2 must lie on a line fixed to body1. -/
structure SliderJoint where
  /-- First body (defines the line) -/
  body1 : BodyRef
  /-- Point on the line in body1's local frame -/
  linePoint : LocalPoint
  /-- Direction of line in body1's local frame -/
  lineDir : LocalAxis
  /-- Second body -/
  body2 : BodyRef
  /-- Point that must stay on the line, in body2's local frame -/
  slidePoint : LocalPoint
  deriving Repr, Inhabited

/-- Fixed joint: no relative motion allowed.
    Bodies maintain constant relative pose. -/
structure FixedJoint where
  body1 : BodyRef
  body2 : BodyRef
  /-- The relative motor from body1 to body2 (constant) -/
  relativeMotor : Multivector PGA3 Float

/-- A general constraint is one of the joint types -/
inductive Constraint
  | ball (j : BallJoint)
  | hinge (j : HingeJoint)
  | slider (j : SliderJoint)
  | fixed (j : FixedJoint)

/-! ## Constraint Residuals

The residual measures how much a constraint is violated.
For gradient-based solving, we want differentiable residuals.
-/

/-- Convert local point to PGA3 point -/
def localPointToPGA (p : LocalPoint) : Multivector PGA3 Float :=
  -- PGA point: e123 + x*e032 + y*e013 + z*e021
  -- Using normalized homogeneous coordinates
  ⟨fun i =>
    if i.val = 7 then 1.0        -- e123 (scalar part of point)
    else if i.val = 14 then p.x  -- e032
    else if i.val = 13 then p.y  -- e013
    else if i.val = 11 then p.z  -- e021
    else 0⟩

/-- Transform a point by a motor (sandwich product) -/
def transformPoint (motor point : Multivector PGA3 Float) : Multivector PGA3 Float :=
  motor.sandwich point

/-- Compute world-space position of a local point on a body -/
def worldPoint (body : RigidBody) (localPt : LocalPoint) : Multivector PGA3 Float :=
  transformPoint body.motor (localPointToPGA localPt)

/-- Extract xyz from PGA point (approximate for non-normalized) -/
def extractXYZ (point : Multivector PGA3 Float) : Float × Float × Float :=
  let w := point.coeffs ⟨7, by decide⟩   -- e123 coefficient
  let scale := if w.abs < 1e-10 then 1.0 else 1.0 / w
  (point.coeffs ⟨14, by decide⟩ * scale,  -- x from e032
   point.coeffs ⟨13, by decide⟩ * scale,  -- y from e013
   point.coeffs ⟨11, by decide⟩ * scale)  -- z from e021

/-- Ball joint residual: distance between world anchor points -/
def ballJointResidual (bodies : Array RigidBody) (joint : BallJoint) : Float :=
  if h1 : joint.body1.index < bodies.size then
    if h2 : joint.body2.index < bodies.size then
      let p1 := worldPoint bodies[joint.body1.index] joint.anchor1
      let p2 := worldPoint bodies[joint.body2.index] joint.anchor2
      let (x1, y1, z1) := extractXYZ p1
      let (x2, y2, z2) := extractXYZ p2
      let dx := x2 - x1
      let dy := y2 - y1
      let dz := z2 - z1
      Float.sqrt (dx*dx + dy*dy + dz*dz)
    else 0.0
  else 0.0

/-- Convert local axis to PGA3 direction bivector -/
def localAxisToPGA (a : LocalAxis) : Multivector PGA3 Float :=
  -- Direction as grade-1 element (vector)
  ⟨fun i =>
    if i.val = 2 then a.x       -- e1
    else if i.val = 4 then a.y  -- e2
    else if i.val = 8 then a.z  -- e3
    else 0⟩

/-- Transform an axis by a motor (just the rotational part) -/
def transformAxis (motor axis : Multivector PGA3 Float) : Multivector PGA3 Float :=
  motor.sandwich axis

/-- Hinge joint residual: ball residual + axis misalignment -/
def hingeJointResidual (bodies : Array RigidBody) (joint : HingeJoint) : Float :=
  if h1 : joint.body1.index < bodies.size then
    if h2 : joint.body2.index < bodies.size then
      -- Position residual (ball joint part)
      let p1 := worldPoint bodies[joint.body1.index] joint.anchor1
      let p2 := worldPoint bodies[joint.body2.index] joint.anchor2
      let (x1, y1, z1) := extractXYZ p1
      let (x2, y2, z2) := extractXYZ p2
      let dx := x2 - x1
      let dy := y2 - y1
      let dz := z2 - z1
      let posError := dx*dx + dy*dy + dz*dz

      -- Axis alignment residual
      let a1 := transformAxis bodies[joint.body1.index].motor (localAxisToPGA joint.axis1)
      let a2 := transformAxis bodies[joint.body2.index].motor (localAxisToPGA joint.axis2)
      -- Cross product magnitude = sin(angle) * |a1| * |a2|
      let a1x := a1.coeffs ⟨2, by decide⟩
      let a1y := a1.coeffs ⟨4, by decide⟩
      let a1z := a1.coeffs ⟨8, by decide⟩
      let a2x := a2.coeffs ⟨2, by decide⟩
      let a2y := a2.coeffs ⟨4, by decide⟩
      let a2z := a2.coeffs ⟨8, by decide⟩
      let crossX := a1y * a2z - a1z * a2y
      let crossY := a1z * a2x - a1x * a2z
      let crossZ := a1x * a2y - a1y * a2x
      let axisError := crossX*crossX + crossY*crossY + crossZ*crossZ

      Float.sqrt (posError + axisError)
    else 0.0
  else 0.0

/-- Slider joint residual: distance from point to line -/
def sliderJointResidual (bodies : Array RigidBody) (joint : SliderJoint) : Float :=
  if h1 : joint.body1.index < bodies.size then
    if h2 : joint.body2.index < bodies.size then
      -- Line point and direction in world space
      let lineP := worldPoint bodies[joint.body1.index] joint.linePoint
      let lineD := transformAxis bodies[joint.body1.index].motor (localAxisToPGA joint.lineDir)

      -- Slide point in world space
      let slideP := worldPoint bodies[joint.body2.index] joint.slidePoint

      -- Vector from line point to slide point
      let (lpx, lpy, lpz) := extractXYZ lineP
      let (spx, spy, spz) := extractXYZ slideP
      let vx := spx - lpx
      let vy := spy - lpy
      let vz := spz - lpz

      -- Project onto line direction, compute perpendicular component
      let dx := lineD.coeffs ⟨2, by decide⟩
      let dy := lineD.coeffs ⟨4, by decide⟩
      let dz := lineD.coeffs ⟨8, by decide⟩
      let dLen := Float.sqrt (dx*dx + dy*dy + dz*dz)
      if dLen < 1e-10 then 0.0 else
        let dnx := dx / dLen
        let dny := dy / dLen
        let dnz := dz / dLen
        let proj := vx * dnx + vy * dny + vz * dnz
        let perpX := vx - proj * dnx
        let perpY := vy - proj * dny
        let perpZ := vz - proj * dnz
        Float.sqrt (perpX*perpX + perpY*perpY + perpZ*perpZ)
    else 0.0
  else 0.0

/-- Compute residual for any constraint -/
def constraintResidual (bodies : Array RigidBody) (c : Constraint) : Float :=
  match c with
  | .ball j => ballJointResidual bodies j
  | .hinge j => hingeJointResidual bodies j
  | .slider j => sliderJointResidual bodies j
  | .fixed _ => 0.0  -- TODO: implement fixed joint residual

/-- Total residual for a system of constraints -/
def totalResidual (bodies : Array RigidBody) (constraints : Array Constraint) : Float :=
  constraints.foldl (init := 0.0) fun acc c =>
    acc + constraintResidual bodies c

/-! ## Motor Gradient Descent Solver

Solves constraint systems by iteratively adjusting body motors to minimize
the total residual. Uses finite-difference gradients (LC autodiff TODO).
-/

/-- Perturb a single motor coefficient by epsilon -/
def perturbMotorCoeff (motor : Multivector PGA3 Float) (idx : Fin 16) (eps : Float)
    : Multivector PGA3 Float :=
  ⟨fun i => if i = idx then motor.coeffs i + eps else motor.coeffs i⟩

/-- Compute finite-difference gradient of residual w.r.t. motor coefficients.
    Returns a 16-element array of partial derivatives. -/
def motorGradient (bodies : Array RigidBody) (bodyIdx : Nat) (constraints : Array Constraint)
    (eps : Float := 1e-6) : Array Float :=
  if h : bodyIdx < bodies.size then
    let body := bodies[bodyIdx]
    let baseResidual := totalResidual bodies constraints
    Array.ofFn fun (idx : Fin 16) =>
      let perturbedMotor := perturbMotorCoeff body.motor idx eps
      let perturbedBody := { body with motor := perturbedMotor }
      let perturbedBodies := bodies.set (Fin.mk bodyIdx h) perturbedBody
      let perturbedResidual := totalResidual perturbedBodies constraints
      (perturbedResidual - baseResidual) / eps
  else
    Array.replicate 16 0.0

/-- Update motor by gradient descent step.
    Subtracts stepSize * gradient from each motor coefficient. -/
def motorGradientStep (motor : Multivector PGA3 Float) (grad : Array Float) (stepSize : Float)
    : Multivector PGA3 Float :=
  ⟨fun i =>
    if h : i.val < grad.size
    then motor.coeffs i - stepSize * grad[i.val]
    else motor.coeffs i⟩

/-- Normalize a motor to maintain unit magnitude (for rotational part).
    Motors should satisfy M·M† = 1. -/
def normalizeMotor (m : Multivector PGA3 Float) : Multivector PGA3 Float :=
  -- The scalar part of M·M† gives the normalization factor
  let mRev := m.reverse
  let mmRev := m.geometricProduct mRev
  let s := mmRev.scalarPart
  let scale := if s.abs < 1e-10 then 1.0 else 1.0 / Float.sqrt s.abs
  m.smul scale

/-- Solver configuration -/
structure SolverConfig where
  /-- Maximum iterations -/
  maxIters : Nat := 100
  /-- Convergence threshold for residual -/
  tolerance : Float := 1e-6
  /-- Gradient descent step size -/
  stepSize : Float := 0.01
  /-- Epsilon for finite differences -/
  epsilon : Float := 1e-6
  deriving Repr, Inhabited

/-- Solver result -/
structure SolverResult where
  /-- Updated body configurations -/
  bodies : Array RigidBody
  /-- Final residual -/
  residual : Float
  /-- Number of iterations used -/
  iterations : Nat
  /-- Whether convergence was achieved -/
  converged : Bool
  deriving Inhabited

/-- Helper: update one body at index i -/
def updateBody (bodies : Array RigidBody) (i : Nat) (constraints : Array Constraint)
    (config : SolverConfig) : Array RigidBody :=
  if h : i < bodies.size then
    let grad := motorGradient bodies i constraints config.epsilon
    let body := bodies[i]
    let newMotor := motorGradientStep body.motor grad config.stepSize
    let normalizedMotor := normalizeMotor newMotor
    bodies.set (Fin.mk i h) { body with motor := normalizedMotor }
  else
    bodies

/-- Single iteration of constraint solver: update all bodies -/
def solverIteration (bodies : Array RigidBody) (constraints : Array Constraint)
    (config : SolverConfig) : Array RigidBody :=
  (List.range bodies.size).foldl (init := bodies) fun acc i =>
    updateBody acc i constraints config

/-- Helper for gradient descent loop -/
partial def solveLoop (bodies : Array RigidBody) (constraints : Array Constraint)
    (config : SolverConfig) (iter : Nat) : SolverResult :=
  let residual := totalResidual bodies constraints
  if iter ≥ config.maxIters || residual ≤ config.tolerance then
    { bodies := bodies
      residual := residual
      iterations := iter
      converged := residual ≤ config.tolerance }
  else
    let newBodies := solverIteration bodies constraints config
    solveLoop newBodies constraints config (iter + 1)

/-- Solve constraint system via gradient descent.
    Iteratively adjusts motors until residual is below tolerance or maxIters reached. -/
def solveConstraints (bodies : Array RigidBody) (constraints : Array Constraint)
    (config : SolverConfig := {}) : SolverResult :=
  solveLoop bodies constraints config 0

/-- Convenience: solve and return only if converged -/
def solveConstraintsStrict (bodies : Array RigidBody) (constraints : Array Constraint)
    (config : SolverConfig := {}) : Option (Array RigidBody) :=
  let result := solveConstraints bodies constraints config
  if result.converged then some result.bodies else none

/-! ## Tests -/

-- Test local point to PGA
#eval!
  let p := localPointToPGA ⟨1.0, 2.0, 3.0⟩
  (p.coeffs ⟨7, by decide⟩, p.coeffs ⟨14, by decide⟩)
-- Expected: (1.0, 1.0) - e123 and e032 coefficients

-- Test ball joint residual with identity motors (should be distance between anchors)
#eval!
  let body1 : RigidBody := RigidBody.identity
  let body2 : RigidBody := RigidBody.identity
  let joint : BallJoint := {
    body1 := ⟨0⟩
    anchor1 := ⟨0, 0, 0⟩
    body2 := ⟨1⟩
    anchor2 := ⟨3, 4, 0⟩
  }
  ballJointResidual #[body1, body2] joint
-- Expected: 5.0 (distance from origin to (3,4,0))

-- Test solver: two bodies with ball joint, should bring anchors together
#eval!
  let body1 : RigidBody := RigidBody.identity
  let body2 : RigidBody := RigidBody.identity
  let joint : BallJoint := {
    body1 := ⟨0⟩
    anchor1 := ⟨1, 0, 0⟩   -- Anchor 1 unit from body1 origin
    body2 := ⟨1⟩
    anchor2 := ⟨-1, 0, 0⟩  -- Anchor 1 unit from body2 origin (other side)
  }
  let constraints := #[Constraint.ball joint]
  let initialResidual := totalResidual #[body1, body2] constraints
  let result := solveConstraints #[body1, body2] constraints
    { maxIters := 50, stepSize := 0.1, tolerance := 0.1 }
  (initialResidual, result.residual, result.iterations, result.converged)
-- Initial residual: 2.0 (anchors 2 units apart)
-- Should converge to lower residual

end Grassmann.Constraints
