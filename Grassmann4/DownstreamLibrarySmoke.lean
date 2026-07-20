import Grassmann
import GrassmannFields
import GrassmannViz

/-!
# Public library smoke check

This module intentionally imports only the three Lake-library roots, then
constructs a new field and visualization scene without touching implementation
modules or packed storage. It is compiled by the meetup preflight.
-/

open GrassmannFields GrassmannViz

def consumerGrid : PlanarGrid := {
  xMin := -0.5
  xMax := 0.5
  yMin := -0.5
  yMax := 0.5
  xCount := 3
  yCount := 3
}

def consumerField (point : Vec3) : R3Grades := {
  scalar := point.x * point.y
  vector := { x := -point.y, y := point.x, z := 0.25 }
  bivectorNormal := { x := point.x, y := point.y, z := 1.0 }
  pseudoscalar := point.x - point.y
}

def consumerScene : Except String MultivectorFieldProps := do
  let samples ← samplePlanar consumerGrid consumerField
  mkScene
    "A downstream multivector field"
    "constructed through the public library roots"
    "G(x,y) = xy + (-y,x,1/4) + (x,y,1)* + (x-y)I"
    #[{ parameter := 0.0, samples }]

#eval consumerScene.bind MultivectorFieldProps.summary

