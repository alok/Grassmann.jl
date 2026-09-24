/-
  Grassmann/UnrealAssets.lean - Asset interchange between Lean and Unreal Engine

  Provides types and operations for:
  - Mesh data (vertices, normals, UVs, indices)
  - Scene hierarchies with PGA transforms
  - Point clouds for geometric computations
  - Animation keyframes using motor interpolation

  Uses PGA (Projective Geometric Algebra) for all transforms.
-/
import Grassmann.UnrealFFI
import Lean.Data.Json

namespace Grassmann.UnrealAssets

open UnrealFFI

/-! ## Vertex and Mesh Types -/

/-- A 3D vertex with position, normal, and UV coordinates. -/
structure Vertex where
  position : Float × Float × Float
  normal   : Float × Float × Float
  uv       : Float × Float
  deriving Repr, BEq

/-- A triangle face defined by three vertex indices. -/
structure Triangle where
  v0 : Nat
  v1 : Nat
  v2 : Nat
  deriving Repr, BEq

/-- A mesh consisting of vertices and triangles. -/
structure Mesh where
  name     : String
  vertices : Array Vertex
  triangles: Array Triangle
  deriving Repr

/-- A point cloud for geometric computations. -/
structure PointCloud where
  name   : String
  points : Array (Float × Float × Float)
  deriving Repr

/-! ## Transform and Scene Types -/

/-- A PGA motor stored as 16 floats.
    Motors represent rigid body transformations (rotation + translation). -/
structure Motor where
  coeffs : FloatArray

instance : Repr Motor where
  reprPrec m _ := s!"Motor({m.coeffs.toList})"

/-- Identity motor (no transformation). -/
def Motor.identity : Motor :=
  let arr := zeros 16
  ⟨arr.set! 0 1.0⟩

/-- Create motor from axis-angle rotation. -/
def Motor.fromAxisAngle (ax ay az theta : Float) : Motor :=
  ⟨pgaRotor ax ay az theta⟩

/-- Create motor from translation. -/
def Motor.fromTranslation (tx ty tz : Float) : Motor :=
  ⟨pgaTranslator tx ty tz⟩

/-- Create motor from UE FQuat and FVector. -/
def Motor.fromUE (qx qy qz qw tx ty tz : Float) : Motor :=
  ⟨pgaMotorFromUE qx qy qz qw tx ty tz⟩

/-- Compose two motors: M1 then M2. -/
def Motor.compose (m1 m2 : Motor) : Motor :=
  ⟨pgaMotorCompose m1.coeffs m2.coeffs⟩

/-- Apply motor to a point. -/
def Motor.applyPoint (m : Motor) (x y z : Float) : Float × Float × Float :=
  let p := pgaPoint x y z
  let result := pgaMotorApplyPoint m.coeffs p
  let extracted := pgaExtractPoint result
  (extracted.get! 0, extracted.get! 1, extracted.get! 2)

/-- Convert motor to UE quaternion (x, y, z, w). -/
def Motor.toQuat (m : Motor) : Float × Float × Float × Float :=
  let q := pgaMotorToQuat m.coeffs
  (q.get! 0, q.get! 1, q.get! 2, q.get! 3)

/-- Convert motor to UE translation (x, y, z). -/
def Motor.toTranslation (m : Motor) : Float × Float × Float :=
  let t := pgaMotorToTranslation m.coeffs
  (t.get! 0, t.get! 1, t.get! 2)

/-- A scene node with transform and optional mesh. -/
structure SceneNode where
  name      : String
  transform : Motor
  mesh      : Option Mesh := none
  children  : Array SceneNode := #[]
  deriving Repr

/-- A complete scene with root nodes. -/
structure Scene where
  name  : String
  roots : Array SceneNode
  deriving Repr

/-! ## Animation Types -/

/-- A motor keyframe at a specific time. -/
structure MotorKeyframe where
  time  : Float
  motor : Motor
  deriving Repr

instance : Inhabited MotorKeyframe where
  default := { time := 0.0, motor := Motor.identity }

/-- An animation track for a single object. -/
structure AnimationTrack where
  targetName : String
  keyframes  : Array MotorKeyframe
  deriving Repr

/-- A complete animation with multiple tracks. -/
structure Animation where
  name     : String
  duration : Float
  tracks   : Array AnimationTrack
  deriving Repr

/-- Interpolate between two motors using SLERP for rotation. -/
def Motor.slerp (m1 m2 : Motor) (t : Float) : Motor :=
  -- Extract quaternion components
  let q1 := pgaMotorToQuat m1.coeffs
  let q2 := pgaMotorToQuat m2.coeffs
  let t1 := pgaMotorToTranslation m1.coeffs
  let t2 := pgaMotorToTranslation m2.coeffs
  -- SLERP quaternions
  let q := quatSlerp (q1.get! 0) (q1.get! 1) (q1.get! 2) (q1.get! 3)
                     (q2.get! 0) (q2.get! 1) (q2.get! 2) (q2.get! 3) t
  -- LERP translations
  let tx := (1.0 - t) * t1.get! 0 + t * t2.get! 0
  let ty := (1.0 - t) * t1.get! 1 + t * t2.get! 1
  let tz := (1.0 - t) * t1.get! 2 + t * t2.get! 2
  Motor.fromUE (q.get! 0) (q.get! 1) (q.get! 2) (q.get! 3) tx ty tz

/-- Sample animation at a specific time. -/
def AnimationTrack.sample (track : AnimationTrack) (time : Float) : Option Motor :=
  if track.keyframes.isEmpty then none
  else if track.keyframes.size == 1 then some track.keyframes[0]!.motor
  else
    -- Find surrounding keyframes
    let (prev, next) := Id.run do
      let mut prev := track.keyframes[0]!
      let mut next := track.keyframes[0]!
      for kf in track.keyframes do
        if kf.time <= time then prev := kf
        if kf.time >= time && next.time < time then next := kf
      return (prev, next)
    if prev.time == next.time then some prev.motor
    else
      let t := (time - prev.time) / (next.time - prev.time)
      some (Motor.slerp prev.motor next.motor t)

/-! ## JSON Serialization -/

instance : Lean.ToJson Vertex where
  toJson v :=
    let (px, py, pz) := v.position
    let (nx, ny, nz) := v.normal
    let (u, vv) := v.uv
    Lean.Json.mkObj [
      ("position", Lean.Json.arr #[Lean.toJson px, Lean.toJson py, Lean.toJson pz]),
      ("normal", Lean.Json.arr #[Lean.toJson nx, Lean.toJson ny, Lean.toJson nz]),
      ("uv", Lean.Json.arr #[Lean.toJson u, Lean.toJson vv])
    ]

instance : Lean.ToJson Triangle where
  toJson t := Lean.Json.arr #[Lean.toJson t.v0, Lean.toJson t.v1, Lean.toJson t.v2]

instance : Lean.ToJson Motor where
  toJson m :=
    let coeffs := m.coeffs.toList.map Lean.toJson
    Lean.Json.arr coeffs.toArray

instance : Lean.ToJson PointCloud where
  toJson pc :=
    let points := pc.points.map fun (x, y, z) =>
      Lean.Json.arr #[Lean.toJson x, Lean.toJson y, Lean.toJson z]
    Lean.Json.mkObj [
      ("name", Lean.toJson pc.name),
      ("points", Lean.Json.arr points)
    ]

instance : Lean.ToJson Mesh where
  toJson mesh :=
    Lean.Json.mkObj [
      ("name", Lean.toJson mesh.name),
      ("vertices", Lean.Json.arr (mesh.vertices.map Lean.toJson)),
      ("triangles", Lean.Json.arr (mesh.triangles.map Lean.toJson))
    ]

instance : Lean.ToJson MotorKeyframe where
  toJson kf := Lean.Json.mkObj [
    ("time", Lean.toJson kf.time),
    ("motor", Lean.toJson kf.motor)
  ]

instance : Lean.ToJson AnimationTrack where
  toJson track := Lean.Json.mkObj [
    ("target", Lean.toJson track.targetName),
    ("keyframes", Lean.Json.arr (track.keyframes.map Lean.toJson))
  ]

/-! ## FFI Exports for Unreal Engine -/

/-- Create a motor from UE transform data. -/
@[export grassmann_motor_from_ue_transform]
def motorFromUETransform (qx qy qz qw tx ty tz : Float) : FloatArray :=
  (Motor.fromUE qx qy qz qw tx ty tz).coeffs

/-- Convert motor to UE transform components.
    Returns 7 floats: [qx, qy, qz, qw, tx, ty, tz] -/
@[export grassmann_motor_to_ue_transform]
def motorToUETransform (motor : @& FloatArray) : FloatArray :=
  let m : Motor := ⟨motor⟩
  let (qx, qy, qz, qw) := m.toQuat
  let (tx, ty, tz) := m.toTranslation
  ⟨#[qx, qy, qz, qw, tx, ty, tz]⟩

/-- Transform a batch of points using a motor.
    Input: motor (16 floats), points (n*3 floats)
    Output: transformed points (n*3 floats) -/
@[export grassmann_transform_points_batch]
def transformPointsBatch (motor : @& FloatArray) (points : @& FloatArray) : FloatArray :=
  let m : Motor := ⟨motor⟩
  let numPoints := points.size / 3
  Id.run do
    let mut result : FloatArray := ⟨#[]⟩
    for i in [:numPoints] do
      let x := points.get! (i * 3)
      let y := points.get! (i * 3 + 1)
      let z := points.get! (i * 3 + 2)
      let (rx, ry, rz) := m.applyPoint x y z
      result := result.push rx
      result := result.push ry
      result := result.push rz
    return result

/-- Compose multiple motors in sequence.
    Input: array of motors (n*16 floats)
    Output: composed motor (16 floats) -/
@[export grassmann_compose_motors_sequence]
def composeMotorsSequence (motors : @& FloatArray) : FloatArray :=
  let numMotors := motors.size / 16
  if numMotors == 0 then
    Motor.identity.coeffs
  else
    Id.run do
      let mut result := Motor.identity
      for i in [:numMotors] do
        let mut motorCoeffs : FloatArray := ⟨#[]⟩
        for j in [:16] do
          motorCoeffs := motorCoeffs.push (motors.get! (i * 16 + j))
        result := Motor.compose result ⟨motorCoeffs⟩
      return result.coeffs

/-- Interpolate between two motors at parameter t ∈ [0,1].
    Uses SLERP for rotation, LERP for translation. -/
@[export grassmann_motor_slerp]
def motorSlerp (m1 m2 : @& FloatArray) (t : Float) : FloatArray :=
  (Motor.slerp ⟨m1⟩ ⟨m2⟩ t).coeffs

/-- Sample animation at time, returning motor for target.
    Input: keyframe times (n floats), keyframe motors (n*16 floats), sample time
    Output: interpolated motor (16 floats) -/
@[export grassmann_sample_animation]
def sampleAnimation (times : @& FloatArray) (motors : @& FloatArray) (t : Float) : FloatArray :=
  let n := times.size
  if n == 0 then Motor.identity.coeffs
  else if n == 1 then
    Id.run do
      let mut m : FloatArray := ⟨#[]⟩
      for j in [:16] do
        m := m.push (motors.get! j)
      return m
  else
    Id.run do
      -- Find surrounding keyframes
      let mut prevIdx := 0
      let mut nextIdx := 0
      for i in [:n] do
        if times.get! i <= t then prevIdx := i
        if times.get! i >= t && times.get! nextIdx < t then nextIdx := i
      if prevIdx == nextIdx then
        let mut m : FloatArray := ⟨#[]⟩
        for j in [:16] do
          m := m.push (motors.get! (prevIdx * 16 + j))
        return m
      else
        let t0 := times.get! prevIdx
        let t1 := times.get! nextIdx
        let alpha := (t - t0) / (t1 - t0)
        let mut m1 : FloatArray := ⟨#[]⟩
        let mut m2 : FloatArray := ⟨#[]⟩
        for j in [:16] do
          m1 := m1.push (motors.get! (prevIdx * 16 + j))
          m2 := m2.push (motors.get! (nextIdx * 16 + j))
        return motorSlerp m1 m2 alpha

/-! ## Mesh Transformation Utilities -/

/-- Transform all vertices of a mesh by a motor. -/
def Mesh.transform (mesh : Mesh) (motor : Motor) : Mesh :=
  let newVertices := mesh.vertices.map fun v =>
    let (px, py, pz) := v.position
    let (nx, ny, nz) := v.normal
    let newPos := motor.applyPoint px py pz
    -- Transform normal (rotation only, using motor which handles this correctly)
    let newNorm := motor.applyPoint nx ny nz
    { v with position := newPos, normal := newNorm }
  { mesh with vertices := newVertices }

/-- Merge multiple meshes into one. -/
def Mesh.merge (meshes : Array Mesh) (name : String := "merged") : Mesh :=
  Id.run do
    let mut allVertices : Array Vertex := #[]
    let mut allTriangles : Array Triangle := #[]
    let mut vertexOffset := 0
    for mesh in meshes do
      allVertices := allVertices ++ mesh.vertices
      for tri in mesh.triangles do
        allTriangles := allTriangles.push {
          v0 := tri.v0 + vertexOffset
          v1 := tri.v1 + vertexOffset
          v2 := tri.v2 + vertexOffset
        }
      vertexOffset := vertexOffset + mesh.vertices.size
    return { name := name, vertices := allVertices, triangles := allTriangles }

/-! ## Point Cloud Operations -/

/-- Transform all points in a cloud by a motor. -/
def PointCloud.transform (cloud : PointCloud) (motor : Motor) : PointCloud :=
  let newPoints := cloud.points.map fun (x, y, z) => motor.applyPoint x y z
  { cloud with points := newPoints }

/-- Compute centroid of point cloud. -/
def PointCloud.centroid (cloud : PointCloud) : Float × Float × Float :=
  if cloud.points.isEmpty then (0, 0, 0)
  else
    let n := cloud.points.size.toFloat
    let (sx, sy, sz) := cloud.points.foldl (init := (0.0, 0.0, 0.0)) fun (ax, ay, az) (x, y, z) =>
      (ax + x, ay + y, az + z)
    (sx / n, sy / n, sz / n)

/-- Compute bounding box as (min, max) points. -/
def PointCloud.bounds (cloud : PointCloud) : (Float × Float × Float) × (Float × Float × Float) :=
  if cloud.points.isEmpty then ((0, 0, 0), (0, 0, 0))
  else
    let (x0, y0, z0) := cloud.points[0]!
    cloud.points.foldl (init := ((x0, y0, z0), (x0, y0, z0)))
      fun ((minX, minY, minZ), (maxX, maxY, maxZ)) (x, y, z) =>
        ((min minX x, min minY y, min minZ z),
         (max maxX x, max maxY y, max maxZ z))

end Grassmann.UnrealAssets
