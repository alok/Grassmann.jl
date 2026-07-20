import GrassmannFields.R3

/-!
# A mixed-grade rotor field

The example is intentionally compact enough to explain live: one geometric
product produces scalar and bivector parts, then a rotor sandwich acts on all
four grades at once.
-/

namespace GrassmannFields.Examples.MixedRotor

open Grassmann GrassmannFields

/-- Pi used by the deterministic Float demo. -/
def pi : Float := 3.14159265358979323846

/-- Position vector `x e1 + y e2` in full packed storage. -/
def positionMV (p : Vec3) : MV R3 .full :=
  MV.ofPairs R3 .full [(1, p.x), (2, p.y)]

/-- Swirling vector `(-y + 0.35)e1 + x e2 + 0.25e3`. -/
def velocityMV (p : Vec3) : MV R3 .full :=
  MV.ofPairs R3 .full [(1, -p.y + 0.35), (2, p.x), (4, 0.25)]

/-- The grade-3 modulation `0.20 sin(pi(x+y)) e123`. -/
def pseudoscalarMV (p : Vec3) : MV R3 .full :=
  MV.ofPairs R3 .full [(7, 0.20 * Float.sin (pi * (p.x + p.y)))]

/-- Base field `v + p*v + tau*I`; `p*v` supplies grades zero and two. -/
def baseField (p : Vec3) : MV R3 .full :=
  let position := positionMV p
  let velocity := velocityMV p
  let product : MV R3 .full := position * velocity
  velocity + product + pseudoscalarMV p

/-- Unit `e12` rotor for a right-handed turn about `e3`. -/
def rotor (theta : Float) : MV R3 .even :=
  let half := theta / 2.0
  MV.ofPairs R3 .even [(0, Float.cos half), (3, -Float.sin half)]

/-- Rotate every grade of the base value while leaving the sample lattice fixed. -/
def fieldAt (theta : Float) (p : Vec3) : MV R3 .full :=
  mvSandwich (rotor theta) (baseField p)

/-- Stage-safe 5-by-5 default lattice. -/
def defaultGrid : PlanarGrid :=
  {
    xMin := -1.0
    xMax := 1.0
    yMin := -1.0
    yMax := 1.0
    z := 0.0
    xCount := 5
    yCount := 5
  }

/-- Number of precomputed rotor frames in the meetup scene. -/
def defaultFrameCount : Nat := 24

/-- Frame parameter over one complete turn, without duplicating the endpoint. -/
def frameParameter (index frameCount : Nat) : Float :=
  2.0 * pi * index.toFloat / frameCount.toFloat

/-- Compute and validate one sampled frame in Lean. -/
def buildFrame (grid : PlanarGrid) (theta : Float) : Except String Frame3 := do
  let samples ← samplePlanarMV grid (fieldAt theta)
  let frame : Frame3 := { parameter := theta, samples }
  frame.validate
  return frame

/-- Compute a reusable sequence of rotor frames. -/
def buildFrames (grid : PlanarGrid := defaultGrid)
    (frameCount : Nat := defaultFrameCount) : Except String (Array Frame3) := do
  if frameCount == 0 then
    throw "frameCount must be positive"
  if frameCount > maxFrameCount then
    throw s!"frameCount must not exceed {maxFrameCount}"
  let mut frames := Array.emptyWithCapacity frameCount
  for index in [:frameCount] do
    let theta := frameParameter index frameCount
    frames := frames.push (← buildFrame grid theta)
  validateFrames frames
  return frames

end GrassmannFields.Examples.MixedRotor
