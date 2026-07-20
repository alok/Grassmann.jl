import GrassmannFields
import Lean.Data.Json

/-!
# Versioned JSON scene for multivector fields

This module is the only serialization boundary between the reusable field
library and a view. Validation happens before `toJson` or a renderer call.
-/

namespace GrassmannViz

open Lean GrassmannFields
open GrassmannFields.Examples.MixedRotor

deriving instance ToJson, FromJson for Vec3
deriving instance ToJson, FromJson for R3Grades
deriving instance ToJson, FromJson for Sample3
deriving instance ToJson, FromJson for Frame3

/-- Current wire-format version for the offline component. -/
def currentSchemaVersion : Nat := 2

/-- Complete props for a rectangular planar lattice consumed by the InfoView. -/
structure MultivectorFieldProps where
  schemaVersion : Nat := currentSchemaVersion
  title : String
  subtitle : String
  formula : String
  parameterLabel : String := "parameter"
  frames : Array Frame3
  initialFrame : Nat := 0
  initialSample : Nat := 0
  deriving Repr, BEq, ToJson, FromJson

private def pushUnique (values : Array Float) (value : Float) : Array Float :=
  if values.any fun existing => existing == value then values else values.push value

private def validatePlanarLattice (samples : Array Sample3) : Except String Unit := do
  let first := samples[0]!.position
  unless samples.all fun sample => sample.position.z == first.z do
    throw "the InfoView renderer requires one shared planar z coordinate"
  let xs := samples.foldl (fun values sample => pushUnique values sample.position.x) #[]
  let ys := samples.foldl (fun values sample => pushUnique values sample.position.y) #[]
  unless xs.size * ys.size == samples.size do
    throw "the InfoView renderer requires a complete rectangular x/y lattice"
  for y in ys do
    for x in xs do
      unless samples.any fun sample =>
          sample.position.x == x && sample.position.y == y && sample.position.z == first.z do
        throw "the InfoView renderer requires every x/y lattice position exactly once"

/-- Validate a complete renderer payload. -/
def MultivectorFieldProps.validate (props : MultivectorFieldProps) : Except String Unit := do
  if props.schemaVersion != currentSchemaVersion then
    throw s!"unsupported multivector-field schema version {props.schemaVersion}"
  if props.title.trimAscii.isEmpty then
    throw "scene title must not be empty"
  if props.formula.trimAscii.isEmpty then
    throw "scene formula must not be empty"
  if props.parameterLabel.trimAscii.isEmpty then
    throw "scene parameterLabel must not be empty"
  validateFrames props.frames
  validatePlanarLattice props.frames[0]!.samples
  if props.initialFrame >= props.frames.size then
    throw s!"initialFrame {props.initialFrame} is outside {props.frames.size} frames"
  let sampleCount := props.frames[props.initialFrame]!.samples.size
  if props.initialSample >= sampleCount then
    throw s!"initialSample {props.initialSample} is outside {sampleCount} samples"

/-- Construct scene props only after checking the full frame sequence. -/
def mkScene (title subtitle formula : String) (frames : Array Frame3)
    (initialFrame : Nat := 0) (parameterLabel : String := "parameter")
    (initialSample : Nat := 0) :
    Except String MultivectorFieldProps := do
  let props : MultivectorFieldProps := {
    title
    subtitle
    formula
    parameterLabel
    frames
    initialFrame
    initialSample
  }
  props.validate
  return props

/-- Off-center default whose scalar, vector, bivector, and pseudoscalar parts are nonzero. -/
def defaultInitialSample : Nat := 9

/-- Build the default meetup scene entirely in Lean. -/
def defaultScene (grid : PlanarGrid := defaultGrid)
    (frameCount : Nat := defaultFrameCount)
    (initialSample : Nat := defaultInitialSample) : Except String MultivectorFieldProps := do
  let frames ← buildFrames grid frameCount
  mkScene
    "A multivector field, computed by Lean"
    "Cl(3,0) · packed MV runtime · every frame precomputed"
    "Fθ(p) = Rθ * (v(p) + p * v(p) + τ(p) I) * reverse(Rθ)"
    frames
    (initialSample := initialSample)
    (parameterLabel := "θ")

/-- Small executable summary used as the no-webview fallback. -/
def MultivectorFieldProps.summary (props : MultivectorFieldProps) : Except String String := do
  props.validate
  let samplesPerFrame := props.frames[0]!.samples.size
  return s!"schema {props.schemaVersion}; {props.frames.size} frames; " ++
    s!"{samplesPerFrame} samples/frame; {props.frames.size * samplesPerFrame} " ++
    "Lean-computed multivectors"

end GrassmannViz
