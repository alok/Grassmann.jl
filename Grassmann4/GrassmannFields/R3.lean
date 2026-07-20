import Grassmann.MV

/-!
# Semantic three-dimensional multivector fields

The records in this module deliberately hide `MV` storage details. A renderer
receives grade semantics, not packed indices or a `DataArray`.
-/

namespace GrassmannFields

open Grassmann

/-- A small Cartesian vector used for field positions and grade components. -/
structure Vec3 where
  x : Float
  y : Float
  z : Float
  deriving Repr, BEq, Inhabited

namespace Vec3

/-- Whether all coordinates can safely cross a serialization boundary. -/
def isFinite (v : Vec3) : Bool :=
  v.x.isFinite && v.y.isFinite && v.z.isFinite

/-- Component-wise addition. -/
def add (a b : Vec3) : Vec3 :=
  { x := a.x + b.x, y := a.y + b.y, z := a.z + b.z }

/-- Scalar multiplication. -/
def smul (s : Float) (v : Vec3) : Vec3 :=
  { x := s * v.x, y := s * v.y, z := s * v.z }

/-- Euclidean magnitude, used only for presentation metadata and tests. -/
def norm (v : Vec3) : Float :=
  Float.sqrt (v.x * v.x + v.y * v.y + v.z * v.z)

end Vec3

/-- The four semantic grades of a full `Cl(3, 0)` multivector.

`bivectorNormal` is the dual plane normal `(e23, e31, e12)`. Since the logical
mask `5` names `e13`, its y component is the negative of coefficient 5.
-/
structure R3Grades where
  scalar : Float
  vector : Vec3
  bivectorNormal : Vec3
  pseudoscalar : Float
  deriving Repr, BEq, Inhabited

namespace R3Grades

/-- Project a packed full-storage multivector onto renderer-independent grades. -/
def ofMV (m : MV R3 .full) : R3Grades :=
  {
    scalar := m.coeff 0
    vector := { x := m.coeff 1, y := m.coeff 2, z := m.coeff 4 }
    bivectorNormal := { x := m.coeff 6, y := -m.coeff 5, z := m.coeff 3 }
    pseudoscalar := m.coeff 7
  }

/-- Whether every exported coefficient is finite. -/
def isFinite (g : R3Grades) : Bool :=
  g.scalar.isFinite && g.vector.isFinite && g.bivectorNormal.isFinite &&
    g.pseudoscalar.isFinite

end R3Grades

/-- A closed rectangular lattice in the plane `z = constant`. -/
structure PlanarGrid where
  xMin : Float
  xMax : Float
  yMin : Float
  yMax : Float
  z : Float := 0.0
  xCount : Nat
  yCount : Nat
  deriving Repr, BEq

/-- A field is an ordinary Lean function from a point to a value. -/
abbrev Field3 (M : Type) := Vec3 → M

/-- One renderer-independent sampled multivector. -/
structure Sample3 where
  position : Vec3
  value : R3Grades
  deriving Repr, BEq, Inhabited

/-- One Lean-computed animation frame. -/
structure Frame3 where
  parameter : Float
  samples : Array Sample3
  deriving Repr, BEq, Inhabited

/-- Maximum number of samples accepted in one stage-safe frame. -/
def maxSamplesPerFrame : Nat := 4096

/-- Maximum number of frames accepted by the reusable validator. -/
def maxFrameCount : Nat := 240

private def validateFinite (label : String) (x : Float) : Except String Unit := do
  unless x.isFinite do
    throw s!"{label} must be finite"

/-- Validate dimensions and endpoints before sampling a planar grid. -/
def PlanarGrid.validate (grid : PlanarGrid) : Except String Unit := do
  validateFinite "grid.xMin" grid.xMin
  validateFinite "grid.xMax" grid.xMax
  validateFinite "grid.yMin" grid.yMin
  validateFinite "grid.yMax" grid.yMax
  validateFinite "grid.z" grid.z
  if grid.xCount < 2 then
    throw "grid.xCount must be at least 2"
  if grid.yCount < 2 then
    throw "grid.yCount must be at least 2"
  if grid.xMin >= grid.xMax then
    throw "grid x range must be strictly increasing"
  if grid.yMin >= grid.yMax then
    throw "grid y range must be strictly increasing"
  if grid.xCount * grid.yCount > maxSamplesPerFrame then
    throw s!"grid has more than {maxSamplesPerFrame} samples"

private def axisCoordinate (lo hi : Float) (index count : Nat) : Float :=
  lo + (hi - lo) * index.toFloat / (count - 1).toFloat

/-- Generate validated points in deterministic row-major order: y, then x. -/
def PlanarGrid.points (grid : PlanarGrid) : Except String (Array Vec3) := do
  grid.validate
  let mut points := Array.emptyWithCapacity (grid.xCount * grid.yCount)
  for yi in [:grid.yCount] do
    let y := axisCoordinate grid.yMin grid.yMax yi grid.yCount
    for xi in [:grid.xCount] do
      let x := axisCoordinate grid.xMin grid.xMax xi grid.xCount
      points := points.push { x, y, z := grid.z }
  return points

/-- Sample any field after adapting its result to semantic `Cl(3, 0)` grades. -/
def samplePlanarWith {M : Type} (grid : PlanarGrid) (field : Field3 M)
    (toGrades : M → R3Grades) : Except String (Array Sample3) := do
  let points ← grid.points
  let samples := points.map fun position =>
    { position, value := toGrades (field position) }
  for sample in samples do
    unless sample.value.isFinite do
      throw s!"field produced a non-finite coefficient at {repr sample.position}"
  return samples

/-- Sample a field that already returns semantic grade records. -/
def samplePlanar (grid : PlanarGrid) (field : Field3 R3Grades) :
    Except String (Array Sample3) :=
  samplePlanarWith grid field id

/-- Sample the primary packed full-storage `Cl(3, 0)` runtime. -/
def samplePlanarMV (grid : PlanarGrid) (field : Field3 (MV R3 .full)) :
    Except String (Array Sample3) :=
  samplePlanarWith grid field R3Grades.ofMV

/-- Validate one frame before it crosses into a visualization library. -/
def Frame3.validate (frame : Frame3) : Except String Unit := do
  validateFinite "frame.parameter" frame.parameter
  if frame.samples.isEmpty then
    throw "frame.samples must not be empty"
  if frame.samples.size > maxSamplesPerFrame then
    throw s!"frame has more than {maxSamplesPerFrame} samples"
  for sample in frame.samples do
    unless sample.position.isFinite do
      throw "frame contains a non-finite sample position"
    unless sample.value.isFinite do
      throw "frame contains a non-finite multivector coefficient"

private def matchingPositions (expected actual : Array Sample3) : Bool :=
  expected.size == actual.size &&
    (Array.range expected.size).all fun i =>
      expected[i]!.position == actual[i]!.position

/-- Validate a frame sequence and its shared sampling lattice. -/
def validateFrames (frames : Array Frame3) : Except String Unit := do
  if frames.isEmpty then
    throw "frames must not be empty"
  if frames.size > maxFrameCount then
    throw s!"scene has more than {maxFrameCount} frames"
  for frame in frames do
    frame.validate
  let expected := frames[0]!.samples
  for frame in frames do
    unless matchingPositions expected frame.samples do
      throw "every frame must use the same sample positions in the same order"

end GrassmannFields
