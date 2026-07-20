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
def currentSchemaVersion : Nat := 1

/-- Complete, validated props consumed by the local InfoView renderer. -/
structure MultivectorFieldProps where
  schemaVersion : Nat := currentSchemaVersion
  title : String
  subtitle : String
  formula : String
  frames : Array Frame3
  initialFrame : Nat := 0
  deriving Repr, BEq, ToJson, FromJson

/-- Validate a complete renderer payload. -/
def MultivectorFieldProps.validate (props : MultivectorFieldProps) : Except String Unit := do
  if props.schemaVersion != currentSchemaVersion then
    throw s!"unsupported multivector-field schema version {props.schemaVersion}"
  if props.title.trimAscii.isEmpty then
    throw "scene title must not be empty"
  if props.formula.trimAscii.isEmpty then
    throw "scene formula must not be empty"
  validateFrames props.frames
  if props.initialFrame >= props.frames.size then
    throw s!"initialFrame {props.initialFrame} is outside {props.frames.size} frames"

/-- Construct scene props only after checking the full frame sequence. -/
def mkScene (title subtitle formula : String) (frames : Array Frame3)
    (initialFrame : Nat := 0) : Except String MultivectorFieldProps := do
  let props : MultivectorFieldProps := {
    title
    subtitle
    formula
    frames
    initialFrame
  }
  props.validate
  return props

/-- Build the default meetup scene entirely in Lean. -/
def defaultScene (grid : PlanarGrid := defaultGrid)
    (frameCount : Nat := defaultFrameCount) : Except String MultivectorFieldProps := do
  let frames ← buildFrames grid frameCount
  mkScene
    "A multivector field, computed by Lean"
    "Cl(3,0) · packed MV runtime · every frame precomputed"
    "Fθ(p) = Rθ · (v(p) + p·v(p) + τ(p)I) · reverse(Rθ)"
    frames

/-- Small executable summary used as the no-webview fallback. -/
def MultivectorFieldProps.summary (props : MultivectorFieldProps) : Except String String := do
  props.validate
  let samplesPerFrame := props.frames[0]!.samples.size
  return s!"schema {props.schemaVersion}; {props.frames.size} frames; " ++
    s!"{samplesPerFrame} samples/frame; {props.frames.size * samplesPerFrame} " ++
    "Lean-computed multivectors"

end GrassmannViz
