import Bench.Grassmann.Common
import Grassmann.Projective
import Grassmann.Conformal

/-!
# Projective (`PGA3`) and Conformal (`CGA3`) high-level geometry benchmarks (Lean only)

Cases live under `grassmann/projective/*` and `grassmann/conformal/*`:
closed-form `O(1)` `motorExp`/`motorLog`/SLERP/Study normalization, column-major 4×4 matrix
extraction, flat XYZ batch transforms, rigid-body RK4 dynamics, exact PGA3 triangle-mesh plane
slicing, and `FloatArray`-backed `CGA3` constructors + `interpreteCGA3` round/flat classification.
-/

namespace Bench.Grassmann

open _root_.Grassmann DirectSum StaticVectors Bench
open _root_.Grassmann.Projective _root_.Grassmann.Conformal

/-- Checksum of a `ConformalObject`. -/
@[inline] private def checkConfObj : ConformalObject → Float
  | .empty => 0.0
  | .point (x, y, z) => x + y + z
  | .pointPair (ax, ay, az) (bx, by_, bz) _ => ax + ay + az + bx + by_ + bz
  | .line (ox, oy, oz) (dx, dy, dz) => ox + oy + oz + dx + dy + dz
  | .circle (cx, cy, cz) (nx, ny, nz) r _ => cx + cy + cz + nx + ny + nz + r
  | .plane (cx, cy, cz) (nx, ny, nz) => cx + cy + cz + nx + ny + nz
  | .sphere (cx, cy, cz) r _ => cx + cy + cz + r
  | .dipole (px, py, pz) (dx, dy, dz) => px + py + pz + dx + dy + dz
  | .tangent (px, py, pz) (nx, ny, nz) => px + py + pz + nx + ny + nz

/-- Closed CCW unit cube `[-1, 1]³` (8 vertices, 12 triangles) for `sliceMeshByPlane`. -/
private def benchCubeMesh : FloatArray × Array UInt32 :=
  let verts : List Float :=
    [ -1, -1, -1,   1, -1, -1,   1,  1, -1,  -1,  1, -1,
      -1, -1,  1,   1, -1,  1,   1,  1,  1,  -1,  1,  1 ]
  let pos := verts.foldl FloatArray.push (FloatArray.emptyWithCapacity 24)
  let idx : Array UInt32 := #[
    0, 3, 2,  0, 2, 1,
    4, 5, 6,  4, 6, 7,
    0, 1, 5,  0, 5, 4,
    3, 7, 6,  3, 6, 2,
    0, 4, 7,  0, 7, 3,
    1, 2, 6,  1, 6, 5
  ]
  (pos, idx)

/-- Closed CCW UV-sphere mesh (`latRings` × `lonSegs` → `2 * latRings * lonSegs` triangles,
default `20 × 24 = 960` tris) for realistic `sliceMeshByPlane` benchmarking. -/
private def benchSphereMesh (latRings : Nat := 20) (lonSegs : Nat := 24) :
    FloatArray × Array UInt32 := Id.run do
  let pi := Float.acos (-1.0)
  let mut pos := FloatArray.emptyWithCapacity ((latRings + 1) * lonSegs * 3)
  for i in [0:latRings + 1] do
    let phi := pi * i.toFloat / latRings.toFloat
    let sp := Float.sin phi
    let cp := Float.cos phi
    for j in [0:lonSegs] do
      let theta := 2.0 * pi * j.toFloat / lonSegs.toFloat
      pos := ((pos.push (sp * Float.cos theta)).push cp).push (sp * Float.sin theta)
  let mut idx := Array.mkEmpty (latRings * lonSegs * 6)
  for i in [0:latRings] do
    for j in [0:lonSegs] do
      let j1 := (j + 1) % lonSegs
      let a := (i * lonSegs + j).toUInt32
      let b := ((i + 1) * lonSegs + j).toUInt32
      let c := ((i + 1) * lonSegs + j1).toUInt32
      let d := (i * lonSegs + j1).toUInt32
      idx := (((((idx.push a).push b).push c).push a).push c).push d
  (pos, idx)

private def benchSlerpT : Float := 0.35
private def benchRk4Dt : Float := 0.005

/-- Step 4 `PGA3` and `CGA3` geometry cases. -/
def projectiveAndConformal : BenchM Unit := do
  let p := s!"K={ringSize}"
  let b1 := ringOf 6 0x9A01 (Chain.mk (V := PGA3) (G := 2) (α := Float))
  let m1 := b1.map motorExp
  let b2 := ringOf 6 0x9A02 (Chain.mk (V := PGA3) (G := 2) (α := Float))
  let m2 := b2.map motorExp
  let mNoisy := ringOf 8 0x9A03 (Half.mk (V := PGA3) (odd := false) (α := Float))

  case1 "projective/motorExp" (fun b => total (motorExp b).v) b1 p
  case1 "projective/motorLog" (fun m => total (motorLog m).v) m1 p
  case1 "projective/normalizeMotor3" (fun m => total (normalizeMotor3 m).v) mNoisy p
  case2 "projective/motorSlerp" (fun a b => total (motorSlerp a b benchSlerpT).v) m1 m2 p
  case1 "projective/motorToMat4" (fun m => (motorToMat4 m).foldl (· + ·) 0.0) m1 p

  let ptsFlat := randFloats (3 * ringSize) 0x9A04 (-5.0) 5.0
  let ptsFA := ptsFlat.foldl FloatArray.push (FloatArray.emptyWithCapacity (3 * ringSize))
  let mFixed := m1[0]!
  bench "projective/transformXYZBatch" (ops := ringSize) (param := p) fun s =>
    let out := transformXYZBatch (blackBox s mFixed) ptsFA
    out.get! 0 + out.get! (3 * ringSize - 1)

  let zeroForque : Motor3 → Line3 → Line3 := fun _ _ => (Chain.ofList? [0.0, 0.0, 0.0, 0.0, 0.0, 0.0]).get!
  let body : RigidBody3 :=
    { motor := identityMotor3
      vel := (Chain.ofList? [0.0, 0.0, 0.0, 0.05, 1.0, 0.02]).get!
      mass := 1.0, ix := 1.0, iy := 2.0, iz := 3.0 }
  bench "projective/rigidBodyStepRK4" (ops := ringSize) (param := p) fun s =>
    let rec go (k : Nat) (st : RigidBody3) : Float :=
      match k with
      | 0 => total st.motor.v + total st.vel.v
      | k + 1 => go k (rigidBodyStepRK4 st zeroForque benchRk4Dt)
    go ringSize (blackBox s body)

  let (cubePos, cubeIdx) := benchCubeMesh
  let planes := (Array.range ringSize).map fun i =>
    let t := (i.toFloat / ringSize.toFloat) * 1.4 - 0.7
    mkPlane3PointNormal 0.0 t 0.0 1.0 1.0 1.0
  bench "projective/sliceMeshByPlane" (ops := 1) (param := "12 tris") fun s =>
    let pl := planes[s % ringSize]!
    let res := sliceMeshByPlane cubePos cubeIdx (blackBox s pl)
    res.posHalf.positions.size.toFloat + res.negHalf.positions.size.toFloat +
      res.contourSegments3D.size.toFloat + res.contourPolylines2D.size.toFloat

  let (sphPos, sphIdx) := benchSphereMesh 20 24
  bench "projective/sliceMeshByPlane (960 tris)" (ops := 1) (param := "960 tris") fun s =>
    let pl := planes[s % ringSize]!
    let res := sliceMeshByPlane sphPos sphIdx (blackBox s pl)
    res.posHalf.positions.size.toFloat + res.negHalf.positions.size.toFloat +
      res.contourSegments3D.size.toFloat + res.contourPolylines2D.size.toFloat

  -- Conformal (CGA3)
  let coords := randFloats (4 * ringSize) 0x9A05 (-4.0) 4.0
  let xyzs : Array (Float × Float × Float × Float) := (Array.range ringSize).map fun i =>
    (coords[4 * i]!, coords[4 * i + 1]!, coords[4 * i + 2]!, (coords[4 * i + 3]!).abs + 0.25)
  case1 "conformal/point3" (fun (x, y, z, _) => total (point3 x y z).v) xyzs p
  case1 "conformal/dualSphere3" (fun (x, y, z, r) => total (dualSphere3 x y z r).v) xyzs p

  let circles : Array (Multivector CGA3 Float) := xyzs.map fun (cx, cy, cz, r) =>
    let p1 := point3 (cx + r) cy cz
    let p2 := point3 cx (cy + r) cz
    let p3 := point3 (cx - r) cy cz
    (((p1 ∧ p2) ∧ p3 : Chain CGA3 3 Float)).toMultivector
  let pointPairs : Array (Multivector CGA3 Float) := xyzs.map fun (cx, cy, cz, r) =>
    let p1 := point3 (cx + r) cy cz
    let p2 := point3 (cx - r) cy cz
    ((p1 ∧ p2 : Chain CGA3 2 Float)).toMultivector
  let lines : Array (Multivector CGA3 Float) := xyzs.map fun (cx, cy, cz, r) =>
    let p1 := point3 cx cy cz
    let p2 := point3 (cx + r) (cy + 0.5 * r) (cz - 0.25 * r)
    (((p1 ∧ p2) ∧ inf CGA3 : Chain CGA3 3 Float)).toMultivector
  let cPlanes : Array (Multivector CGA3 Float) := xyzs.map fun (cx, cy, cz, r) =>
    let p1 := point3 cx cy cz
    let p2 := point3 (cx + r) cy cz
    let p3 := point3 cx (cy + r) cz
    ((((p1 ∧ p2) ∧ p3) ∧ inf CGA3 : Chain CGA3 4 Float)).toMultivector
  let spheres : Array (Multivector CGA3 Float) := xyzs.map fun (cx, cy, cz, r) =>
    (dualSphere3 cx cy cz r).toMultivector
  case1 "conformal/interpreteCGA3 circle" (fun x => checkConfObj (interpreteCGA3 x)) circles p
  case1 "conformal/interpreteCGA3 pointPair" (fun x => checkConfObj (interpreteCGA3 x)) pointPairs p
  case1 "conformal/interpreteCGA3 line" (fun x => checkConfObj (interpreteCGA3 x)) lines p
  case1 "conformal/interpreteCGA3 plane" (fun x => checkConfObj (interpreteCGA3 x)) cPlanes p
  case1 "conformal/interpreteCGA3 sphere"
    (fun x => checkConfObj (interpreteCGA3 x (isIPNS := true))) spheres p

end Bench.Grassmann
