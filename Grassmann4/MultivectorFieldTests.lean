import GrassmannViz.Scene

namespace MultivectorFieldTests

open Grassmann GrassmannFields
open GrassmannFields.Examples.MixedRotor
open GrassmannViz Lean

private def require (label : String) (condition : Bool) : IO Unit :=
  unless condition do
    throw <| IO.userError s!"FAIL: {label}"

private def approx (a b : Float) (tolerance : Float := 1e-9) : Bool :=
  let difference := Float.abs (a - b)
  difference.isFinite && difference <= tolerance

private def approxVec (a b : Vec3) (tolerance : Float := 1e-9) : Bool :=
  approx a.x b.x tolerance && approx a.y b.y tolerance && approx a.z b.z tolerance

private def approxGrades (a b : R3Grades) (tolerance : Float := 1e-9) : Bool :=
  approx a.scalar b.scalar tolerance && approxVec a.vector b.vector tolerance &&
    approxVec a.bivectorNormal b.bivectorNormal tolerance &&
    approx a.pseudoscalar b.pseudoscalar tolerance

private def approxSample (a b : Sample3) (tolerance : Float := 1e-9) : Bool :=
  approxVec a.position b.position tolerance && approxGrades a.value b.value tolerance

private def approxFrame (a b : Frame3) (tolerance : Float := 1e-9) : Bool :=
  approx a.parameter b.parameter tolerance && a.samples.size == b.samples.size &&
    (Array.range a.samples.size).all fun i =>
      approxSample a.samples[i]! b.samples[i]! tolerance

private def approxScene (a b : MultivectorFieldProps) (tolerance : Float := 1e-9) : Bool :=
  a.schemaVersion == b.schemaVersion && a.title == b.title && a.subtitle == b.subtitle &&
    a.formula == b.formula && a.parameterLabel == b.parameterLabel &&
    a.initialFrame == b.initialFrame && a.initialSample == b.initialSample &&
    a.frames.size == b.frames.size &&
    (Array.range a.frames.size).all fun i => approxFrame a.frames[i]! b.frames[i]! tolerance

private def testGradeMapping : IO Unit := do
  let mixed : MV R3 .full := MV.ofPairs R3 .full [
    (0, 2.0), (1, 3.0), (2, 4.0), (4, 5.0),
    (6, 7.0), (5, 11.0), (3, 13.0), (7, 17.0)
  ]
  let grades := R3Grades.ofMV mixed
  require "grade map scalar" (grades.scalar == 2.0)
  require "grade map vector" (grades.vector == { x := 3.0, y := 4.0, z := 5.0 })
  require "grade map e23/e31/e12 normal"
    (grades.bivectorNormal == { x := 7.0, y := -11.0, z := 13.0 })
  require "grade map pseudoscalar" (grades.pseudoscalar == 17.0)
  let gradeRecord (scalar vx vy vz bx byCoeff bz pseudoscalar : Float) : R3Grades := {
    scalar
    vector := { x := vx, y := vy, z := vz }
    bivectorNormal := { x := bx, y := byCoeff, z := bz }
    pseudoscalar
  }
  let basisCases : List (Nat × R3Grades) := [
    (0, gradeRecord 9.0 0.0 0.0 0.0 0.0 0.0 0.0 0.0),
    (1, gradeRecord 0.0 9.0 0.0 0.0 0.0 0.0 0.0 0.0),
    (2, gradeRecord 0.0 0.0 9.0 0.0 0.0 0.0 0.0 0.0),
    (4, gradeRecord 0.0 0.0 0.0 9.0 0.0 0.0 0.0 0.0),
    (6, gradeRecord 0.0 0.0 0.0 0.0 9.0 0.0 0.0 0.0),
    (5, gradeRecord 0.0 0.0 0.0 0.0 0.0 (-9.0) 0.0 0.0),
    (3, gradeRecord 0.0 0.0 0.0 0.0 0.0 0.0 9.0 0.0),
    (7, gradeRecord 0.0 0.0 0.0 0.0 0.0 0.0 0.0 9.0)
  ]
  for (mask, expected) in basisCases do
    require s!"basis mask {mask} grade mapping"
      (R3Grades.ofMV (MV.ofPairs R3 .full [(mask, 9.0)]) == expected)

private def testGrid : IO Unit := do
  let points ← IO.ofExcept defaultGrid.points
  require "5x5 grid has 25 points" (points.size == 25)
  require "row-major first point" (points[0]! == { x := -1.0, y := -1.0, z := 0.0 })
  require "row-major x changes first" (points[1]! == { x := -0.5, y := -1.0, z := 0.0 })
  require "row-major next row" (points[5]! == { x := -1.0, y := -0.5, z := 0.0 })
  require "row-major final point" (points[24]! == { x := 1.0, y := 1.0, z := 0.0 })
  require "xCount underflow rejected"
    (({ defaultGrid with xCount := 1 }).points matches .error _)
  require "zero-width x range rejected"
    (({ defaultGrid with xMax := defaultGrid.xMin }).points matches .error _)
  require "non-finite grid rejected"
    (({ defaultGrid with yMax := 1.0 / 0.0 }).points matches .error _)
  require "oversized grid rejected"
    (({ defaultGrid with xCount := 65, yCount := 65 }).points matches .error _)
  let extremeGrid : PlanarGrid := {
    defaultGrid with
    xMin := -1e308
    xMax := 1e308
    xCount := 3
    yCount := 2
  }
  let extremePoints ← IO.ofExcept extremeGrid.points
  require "finite extreme endpoints interpolate to finite positions"
    (extremePoints.all Vec3.isFinite)

private def testFieldFormula : IO Unit := do
  let p : Vec3 := { x := 0.5, y := -0.25, z := 0.0 }
  let grades := R3Grades.ofMV (baseField p)
  require "base scalar formula" (approx grades.scalar (0.35 * p.x))
  require "base vector formula"
    (approxVec grades.vector { x := -p.y + 0.35, y := p.x, z := 0.25 })
  require "base bivector formula"
    (approxVec grades.bivectorNormal {
      x := 0.25 * p.y
      y := -(0.25 * p.x)
      z := p.x * p.x + p.y * p.y - 0.35 * p.y
    })
  require "base pseudoscalar formula"
    (approx grades.pseudoscalar (0.20 * Float.sin (pi * (p.x + p.y))))
  let theta := pi / 3.0
  let rotated := R3Grades.ofMV (fieldAt theta p)
  require "rotor sandwich preserves scalar" (approx rotated.scalar grades.scalar)
  require "rotor sandwich preserves pseudoscalar"
    (approx rotated.pseudoscalar grades.pseudoscalar)
  let quarterTurn := R3Grades.ofMV (fieldAt (pi / 2.0) p)
  require "quarter-turn rotates the visible vector counterclockwise"
    (approxVec quarterTurn.vector { x := -0.5, y := 0.6, z := 0.25 })
  require "quarter-turn rotates the visible bivector normal counterclockwise"
    (approxVec quarterTurn.bivectorNormal { x := 0.125, y := -0.0625, z := 0.4 })

private def testFrames : IO Unit := do
  let frames ← IO.ofExcept buildFrames
  require "default frame count" (frames.size == defaultFrameCount)
  require "default samples per frame" (frames.all fun frame => frame.samples.size == 25)
  require "every frame is finite"
    (frames.all fun frame => frame.parameter.isFinite && frame.samples.all fun sample =>
      sample.position.isFinite && sample.value.isFinite)
  require "zero frames rejected" ((buildFrames (frameCount := 0) matches .error _))
  require "public zero-count frame parameter is finite and guarded"
    (frameParameter 0 0 == 0.0)
  require "non-finite field output rejected"
    ((samplePlanar defaultGrid fun _ => {
      scalar := 0.0 / 0.0
      vector := { x := 0.0, y := 0.0, z := 0.0 }
      bivectorNormal := { x := 0.0, y := 0.0, z := 0.0 }
      pseudoscalar := 0.0
    }) matches .error _)
  let badPositions := frames.set! 1 {
    frames[1]! with
    samples := frames[1]!.samples.set! 0 {
      frames[1]!.samples[0]! with position := { x := 99.0, y := 0.0, z := 0.0 }
    }
  }
  require "inconsistent frame positions rejected"
    ((validateFrames badPositions) matches .error _)
  let mediumGrid : PlanarGrid := {
    defaultGrid with
    xCount := 25
    yCount := 20
  }
  let mediumSamples ← IO.ofExcept <| samplePlanar mediumGrid fun _ => default
  let mediumFrame : Frame3 := { parameter := 0.0, samples := mediumSamples }
  let oversizedScene := Array.replicate 132 mediumFrame
  require "total scene sample cap rejects oversized payloads"
    ((validateFrames oversizedScene) matches .error _)

private def testScene : IO Unit := do
  let scene ← IO.ofExcept defaultScene
  require "scene validates" (scene.validate matches .ok ())
  require "scene schema version" (scene.schemaVersion == currentSchemaVersion)
  require "scene has 24 by 25 samples"
    (scene.frames.size == 24 && scene.frames.all fun frame => frame.samples.size == 25)
  require "default scene selects a rich off-center sample"
    (scene.initialSample == 9 &&
      let value := scene.frames[scene.initialFrame]!.samples[scene.initialSample]!.value
      value.scalar != 0.0 && value.vector.norm != 0.0 &&
        value.bivectorNormal.norm != 0.0 && value.pseudoscalar != 0.0)
  require "out-of-range initial frame rejected"
    (({ scene with initialFrame := scene.frames.size }).validate matches .error _)
  require "out-of-range initial sample rejected"
    (({ scene with initialSample := scene.frames[0]!.samples.size }).validate matches .error _)
  require "unsupported schema rejected"
    (({ scene with schemaVersion := currentSchemaVersion + 1 }).validate matches .error _)
  require "empty parameter label rejected"
    (({ scene with parameterLabel := " " }).validate matches .error _)
  let nonplanarSamples := scene.frames[0]!.samples.set! 0 {
    scene.frames[0]!.samples[0]! with position := { x := -1.0, y := -1.0, z := 0.25 }
  }
  require "nonplanar scene rejected"
    (({ scene with frames := #[{ parameter := 0.0, samples := nonplanarSamples }] }).validate
      matches .error _)
  let sparseSamples := #[scene.frames[0]!.samples[0]!, scene.frames[0]!.samples[1]!,
    scene.frames[0]!.samples[5]!]
  require "incomplete rectangular lattice rejected"
    (({ scene with frames := #[{ parameter := 0.0, samples := sparseSamples }] }).validate
      matches .error _)
  let encoded := toJson scene
  let decoded : MultivectorFieldProps ← IO.ofExcept (fromJson? encoded)
  require "decoded widget props validate" (decoded.validate matches .ok ())
  -- Core Float JSON uses decimal `Float.toString`, so this is a documented
  -- numeric tolerance rather than bit-exact Float round-tripping.
  require "widget props JSON round-trip preserves semantic values within 1e-5"
    (approxScene decoded scene 1e-5)
  let summary ← IO.ofExcept scene.summary
  require "scene summary reports frame count" (summary.contains "24 frames")
  require "scene summary reports sample count" (summary.contains "25 samples/frame")

def run : IO Unit := do
  testGradeMapping
  testGrid
  testFieldFormula
  testFrames
  testScene
  IO.println "multivector field tests passed"

end MultivectorFieldTests

def main : IO Unit :=
  MultivectorFieldTests.run
