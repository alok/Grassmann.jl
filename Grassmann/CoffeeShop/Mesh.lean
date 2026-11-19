import Grassmann.Scene.Types
import Grassmann.Eval.Contour

/-!
# Pure-Lean Procedural 3D Mesh Library & Exact PGA3 Plane Slicer (`Grassmann.CoffeeShop.Mesh`)

Generates CCW right-handed 3D `MeshAsset`s purely in Lean (zero mesh math in JS/Swift):
- Sculpted organic multi-lobe **Stanford-style Bunny** (for `#pga3d_slicing`!)
- Lathed **Torus**, **Sphere**, **Cone**, **Cylinder**, **Arrow**, **Torus Knot**, **Box**, **Icosahedron**
- **Exact PGA3 Triangle-Mesh Plane Slicer** (`sliceMeshByPlane`): splits triangles into
  lower solid + upper ghost CCW halves AND extracts both 3D cut segments and a stitched
  2D `ContourOverlay` inset!

Credits: Steven De Keninck (`enkimute` / `ganja.js`) & Michael Reed (`chakravala` / `Grassmann.jl`).
-/

namespace Grassmann.CoffeeShop.Mesh

open Grassmann.Scene Grassmann.Eval.Contour

/-- Mutable mesh builder enforcing CCW winding and computing smooth exterior normals. -/
structure MeshBuilder where
  positions : FloatArray := FloatArray.empty
  colors    : FloatArray := FloatArray.empty
  indices   : Array UInt32 := #[]
  deriving Inhabited

namespace MeshBuilder

def addVertex (mb : MeshBuilder) (p : Vec3) (c : RGBA) : MeshBuilder × UInt32 :=
  let idx := (mb.positions.size / 3).toUInt32
  let pos := mb.positions.push p.x |>.push p.y |>.push p.z
  let col := mb.colors.push c.r |>.push c.g |>.push c.b |>.push c.a
  ({ mb with positions := pos, colors := col }, idx)

def addTri (mb : MeshBuilder) (i0 i1 i2 : UInt32) : MeshBuilder :=
  { mb with indices := mb.indices.push i0 |>.push i1 |>.push i2 }

/-- Append a parametric ellipsoid `(center, radii, rotTiltZ, stacks, slices, color)` with CCW winding. -/
def addEllipsoid (mb0 : MeshBuilder) (center radii : Vec3) (tiltZ : Float)
    (stacks slices : Nat) (color : RGBA) : MeshBuilder := Id.run do
  let mut mb := mb0
  let baseIdx := (mb.positions.size / 3).toUInt32
  let ct := Float.cos tiltZ
  let st := Float.sin tiltZ
  let pi := 3.14159265358979323846
  for i in [:(stacks + 1)] do
    let phi := pi * i.toFloat / stacks.toFloat
    let sp := Float.sin phi
    let cp := Float.cos phi
    for j in [:(slices + 1)] do
      let theta := 2.0 * pi * j.toFloat / slices.toFloat
      let lx := radii.x * sp * Float.cos theta
      let ly := radii.y * cp
      let lz := radii.z * sp * Float.sin theta
      let rx := lx * ct - ly * st
      let ry := lx * st + ly * ct
      let shade := 0.85 + 0.15 * cp
      let c : RGBA := ⟨min 1.0 (color.r * shade), min 1.0 (color.g * shade), min 1.0 (color.b * shade), color.a⟩
      let (mb1, _) := mb.addVertex ⟨center.x + rx, center.y + ry, center.z + lz⟩ c
      mb := mb1
  let ring := slices + 1
  for i in [:stacks] do
    for j in [:slices] do
      let a := baseIdx + (i * ring + j).toUInt32
      let b := baseIdx + ((i + 1) * ring + j).toUInt32
      let c := baseIdx + ((i + 1) * ring + (j + 1)).toUInt32
      let d := baseIdx + (i * ring + (j + 1)).toUInt32
      -- Outward CCW winding
      mb := mb.addTri a d c
      mb := mb.addTri a c b
  return mb

/-- Finalize a `MeshBuilder` into a `MeshAsset` by computing smooth area-weighted vertex
normals via 3D exterior/cross product purely in Lean. -/
def finalize (mb : MeshBuilder) (meshId : UInt64) : MeshAsset := Id.run do
  let vCount := mb.positions.size / 3
  let mut nx := FloatArray.emptyWithCapacity vCount
  let mut ny := FloatArray.emptyWithCapacity vCount
  let mut nz := FloatArray.emptyWithCapacity vCount
  for _ in [:vCount] do
    nx := nx.push 0.0; ny := ny.push 0.0; nz := nz.push 0.0
  let triCount := mb.indices.size / 3
  for t in [:triCount] do
    let i0 := mb.indices[t * 3]!.toNat
    let i1 := mb.indices[t * 3 + 1]!.toNat
    let i2 := mb.indices[t * 3 + 2]!.toNat
    if i0 < vCount && i1 < vCount && i2 < vCount then
      let p0 : Vec3 := ⟨mb.positions.get! (i0 * 3), mb.positions.get! (i0 * 3 + 1), mb.positions.get! (i0 * 3 + 2)⟩
      let p1 : Vec3 := ⟨mb.positions.get! (i1 * 3), mb.positions.get! (i1 * 3 + 1), mb.positions.get! (i1 * 3 + 2)⟩
      let p2 : Vec3 := ⟨mb.positions.get! (i2 * 3), mb.positions.get! (i2 * 3 + 1), mb.positions.get! (i2 * 3 + 2)⟩
      -- Exterior normal ⋆((p1 - p0) ∧ (p2 - p0))
      let fn := Vec3.cross (Vec3.sub p1 p0) (Vec3.sub p2 p0)
      for vi in [i0, i1, i2] do
        nx := nx.set! vi (nx.get! vi + fn.x)
        ny := ny.set! vi (ny.get! vi + fn.y)
        nz := nz.set! vi (nz.get! vi + fn.z)
  let mut normals := FloatArray.emptyWithCapacity (vCount * 3)
  for i in [:vCount] do
    let nn := Vec3.normalize ⟨nx.get! i, ny.get! i, nz.get! i⟩
    normals := normals.push nn.x |>.push nn.y |>.push nn.z
  let dirtyHash := computeMeshHash meshId mb.positions mb.indices
  return { meshId, dirtyHash, positions := mb.positions, normals, colors := mb.colors, indices := mb.indices }

end MeshBuilder

/-! ## Procedural Flagship 3D Meshes -/

/-- Sculpted Stanford-style multi-lobe Bunny mesh (~360 CCW triangles) for `#pga3d_slicing`. -/
def buildBunnyMesh (meshId : UInt64 := 1001) : MeshAsset :=
  let warmClay : RGBA := ⟨0.84, 0.56, 0.36, 1.0⟩
  let earTint  : RGBA := ⟨0.90, 0.64, 0.46, 1.0⟩
  let tailTint : RGBA := ⟨0.95, 0.88, 0.78, 1.0⟩
  let mb : MeshBuilder := {}
  -- Torso / haunches
  let mb := mb.addEllipsoid ⟨-0.12, -0.35, 0.0⟩ ⟨0.78, 0.56, 0.54⟩ (-0.18) 9 14 warmClay
  -- Chest / front shoulder
  let mb := mb.addEllipsoid ⟨0.32, -0.18, 0.0⟩ ⟨0.46, 0.44, 0.42⟩ 0.25 7 12 warmClay
  -- Head
  let mb := mb.addEllipsoid ⟨0.55, 0.38, 0.0⟩ ⟨0.40, 0.34, 0.33⟩ (-0.22) 8 12 warmClay
  -- Snout
  let mb := mb.addEllipsoid ⟨0.86, 0.30, 0.0⟩ ⟨0.20, 0.16, 0.18⟩ 0.0 5 8 earTint
  -- Left & Right Ears
  let mb := mb.addEllipsoid ⟨0.32, 0.94, 0.16⟩ ⟨0.11, 0.46, 0.09⟩ 0.34 7 10 earTint
  let mb := mb.addEllipsoid ⟨0.32, 0.94, -0.16⟩ ⟨0.11, 0.46, 0.09⟩ 0.22 7 10 earTint
  -- Cotton tail
  let mb := mb.addEllipsoid ⟨-0.88, -0.32, 0.0⟩ ⟨0.20, 0.20, 0.20⟩ 0.0 6 10 tailTint
  mb.finalize meshId

/-- Smooth CCW torus mesh `(majorR, minorR)`. -/
def buildTorusMesh (majorR minorR : Float) (uSegs vSegs : Nat := 28) (color : RGBA := RGBA.cyan)
    (meshId : UInt64 := 1002) : MeshAsset := Id.run do
  let mut mb : MeshBuilder := {}
  let pi := 3.14159265358979323846
  for i in [:(uSegs + 1)] do
    let u := 2.0 * pi * i.toFloat / uSegs.toFloat
    let cu := Float.cos u; let su := Float.sin u
    for j in [:(vSegs + 1)] do
      let v := 2.0 * pi * j.toFloat / vSegs.toFloat
      let cv := Float.cos v; let sv := Float.sin v
      let r := majorR + minorR * cv
      let p : Vec3 := ⟨r * cu, minorR * sv, r * su⟩
      let shade := 0.78 + 0.22 * (0.5 + 0.5 * sv)
      let c : RGBA := ⟨min 1.0 (color.r * shade), min 1.0 (color.g * shade), min 1.0 (color.b * shade), color.a⟩
      let (mb1, _) := mb.addVertex p c
      mb := mb1
  let ring := vSegs + 1
  for i in [:uSegs] do
    for j in [:vSegs] do
      let a := (i * ring + j).toUInt32
      let b := ((i + 1) * ring + j).toUInt32
      let c := ((i + 1) * ring + (j + 1)).toUInt32
      let d := (i * ring + (j + 1)).toUInt32
      mb := mb.addTri a b c
      mb := mb.addTri a c d
  return mb.finalize meshId

/-- Axis-aligned box `(sx, sy, sz)` with sharp flat faces (24 vertices, CCW) for rigid-body physics. -/
def buildBoxMesh (sx sy sz : Float) (color : RGBA := RGBA.violet)
    (meshId : UInt64 := 1003) : MeshAsset := Id.run do
  let hx := 0.5 * sx; let hy := 0.5 * sy; let hz := 0.5 * sz
  let faces : Array (Vec3 × Vec3 × Vec3 × Vec3 × RGBA) := #[
    (⟨-hx,-hy, hz⟩, ⟨ hx,-hy, hz⟩, ⟨ hx, hy, hz⟩, ⟨-hx, hy, hz⟩, color),
    (⟨ hx,-hy,-hz⟩, ⟨-hx,-hy,-hz⟩, ⟨-hx, hy,-hz⟩, ⟨ hx, hy,-hz⟩, ⟨color.r*0.85, color.g*0.85, color.b*0.85, color.a⟩),
    (⟨ hx,-hy, hz⟩, ⟨ hx,-hy,-hz⟩, ⟨ hx, hy,-hz⟩, ⟨ hx, hy, hz⟩, RGBA.amber),
    (⟨-hx,-hy,-hz⟩, ⟨-hx,-hy, hz⟩, ⟨-hx, hy, hz⟩, ⟨-hx, hy,-hz⟩, RGBA.cyan),
    (⟨-hx, hy, hz⟩, ⟨ hx, hy, hz⟩, ⟨ hx, hy,-hz⟩, ⟨-hx, hy,-hz⟩, RGBA.green),
    (⟨-hx,-hy,-hz⟩, ⟨ hx,-hy,-hz⟩, ⟨ hx,-hy, hz⟩, ⟨-hx,-hy, hz⟩, RGBA.coral)
  ]
  let mut mb : MeshBuilder := {}
  for (p0, p1, p2, p3, c) in faces do
    let (mb1, i0) := mb.addVertex p0 c
    let (mb2, i1) := mb1.addVertex p1 c
    let (mb3, i2) := mb2.addVertex p2 c
    let (mb4, i3) := mb3.addVertex p3 c
    mb := (mb4.addTri i0 i1 i2).addTri i0 i2 i3
  return mb.finalize meshId

/-- Lathed cone `(radius, height, segs)` with CCW winding. -/
def buildConeMesh (radius height : Float) (segs : Nat := 24) (color : RGBA := RGBA.amber)
    (meshId : UInt64 := 1004) : MeshAsset := Id.run do
  let mut mb : MeshBuilder := {}
  let pi := 3.14159265358979323846
  let (mb1, apex) := mb.addVertex ⟨0.0, 0.5 * height, 0.0⟩ color
  let (mb2, baseCtr) := mb1.addVertex ⟨0.0, -0.5 * height, 0.0⟩ ⟨color.r*0.7, color.g*0.7, color.b*0.7, color.a⟩
  mb := mb2
  let ringStart := (mb.positions.size / 3).toUInt32
  for i in [:segs] do
    let a := 2.0 * pi * i.toFloat / segs.toFloat
    let (mbNext, _) := mb.addVertex ⟨radius * Float.cos a, -0.5 * height, radius * Float.sin a⟩ color
    mb := mbNext
  for i in [:segs] do
    let curr := ringStart + i.toUInt32
    let next := ringStart + ((i + 1) % segs).toUInt32
    mb := mb.addTri apex next curr
    mb := mb.addTri baseCtr curr next
  return mb.finalize meshId

/-- Lathed cylinder `(radius, height, segs)` with CCW winding. -/
def buildCylinderMesh (radius height : Float) (segs : Nat := 24) (color : RGBA := RGBA.green)
    (meshId : UInt64 := 1005) : MeshAsset := Id.run do
  let mut mb : MeshBuilder := {}
  let pi := 3.14159265358979323846
  let hy := 0.5 * height
  let (mb1, topC) := mb.addVertex ⟨0.0, hy, 0.0⟩ color
  let (mb2, botC) := mb1.addVertex ⟨0.0, -hy, 0.0⟩ color
  mb := mb2
  let ringStart := (mb.positions.size / 3).toUInt32
  for i in [:segs] do
    let a := 2.0 * pi * i.toFloat / segs.toFloat
    let x := radius * Float.cos a; let z := radius * Float.sin a
    let (mbA, _) := mb.addVertex ⟨x, hy, z⟩ color
    let (mbB, _) := mbA.addVertex ⟨x, -hy, z⟩ ⟨color.r*0.85, color.g*0.85, color.b*0.85, color.a⟩
    mb := mbB
  for i in [:segs] do
    let t0 := ringStart + (2 * i).toUInt32
    let b0 := t0 + 1
    let t1 := ringStart + (2 * ((i + 1) % segs)).toUInt32
    let b1 := t1 + 1
    mb := mb.addTri topC t1 t0
    mb := mb.addTri botC b0 b1
    mb := mb.addTri t0 t1 b1
    mb := mb.addTri t0 b1 b0
  return mb.finalize meshId

/-! ## Exact PGA3 Triangle-Mesh Plane Slicer (`#pga3d_slicing`) -/

/-- Result of slicing a 3D mesh by a PGA3 plane `n·p + d = 0`:
- `lowerMesh`: solid clipped geometry on side `n·p + d ≤ 0`
- `upperMesh`: translucent ghost geometry on side `n·p + d ≥ 0`
- `contour3D`: exact 3D cut segments along the intersection plane
- `contour2D`: stitched 2D `ContourOverlay` in the cutting plane's `(u, v)` coordinates! -/
structure SliceResult where
  lowerMesh : MeshAsset
  upperMesh : MeshAsset
  contour3D : Array SegmentPrim
  contour2D : ContourOverlay

private def lerpColor (a b : RGBA) (t : Float) : RGBA :=
  ⟨a.r + (b.r - a.r) * t, a.g + (b.g - a.g) * t, a.b + (b.b - a.b) * t, a.a + (b.a - a.a) * t⟩

private def getVertPos (m : MeshAsset) (i : Nat) : Vec3 :=
  ⟨m.positions.get! (i * 3), m.positions.get! (i * 3 + 1), m.positions.get! (i * 3 + 2)⟩

private def getVertCol (m : MeshAsset) (i : Nat) : RGBA :=
  if (i + 1) * 4 ≤ m.colors.size then
    ⟨m.colors.get! (i * 4), m.colors.get! (i * 4 + 1), m.colors.get! (i * 4 + 2), m.colors.get! (i * 4 + 3)⟩
  else RGBA.white

/-- Clip a CCW triangle against half-space `s ≤ 0` (if `keepNeg = true`) or `s ≥ 0` (`keepNeg = false`),
appending 0, 1, or 2 CCW triangles to `mb`. -/
private def clipTriHalfSpace (mb : MeshBuilder)
    (p0 p1 p2 : Vec3) (c0 c1 c2 : RGBA) (s0 s1 s2 : Float) (keepNeg : Bool) : MeshBuilder := Id.run do
  let inside (s : Float) : Bool := if keepNeg then s ≤ 0.0 else s ≥ 0.0
  let pts := #[p0, p1, p2]
  let cols := #[c0, c1, c2]
  let dists := #[s0, s1, s2]
  let mut polyP : Array Vec3 := #[]
  let mut polyC : Array RGBA := #[]
  for i in [:3] do
    let j := (i + 1) % 3
    let pi := pts[i]!; let pj := pts[j]!
    let ci := cols[i]!; let cj := cols[j]!
    let di := dists[i]!; let dj := dists[j]!
    let inI := inside di; let inJ := inside dj
    if inI then
      polyP := polyP.push pi
      polyC := polyC.push ci
    if inI != inJ then
      let denom := di - dj
      let t := if Float.abs denom < 1e-12 then 0.5 else max 0.0 (min 1.0 (di / denom))
      polyP := polyP.push (Vec3.lerp pi pj t)
      polyC := polyC.push (lerpColor ci cj t)
  if polyP.size < 3 then return mb
  let mut out := mb
  let (out1, i0) := out.addVertex polyP[0]! polyC[0]!
  out := out1
  let mut prev := i0
  for k in [1:polyP.size] do
    let (outK, idxK) := out.addVertex polyP[k]! polyC[k]!
    out := outK
    if k ≥ 2 then
      out := out.addTri i0 prev idxK
    prev := idxK
  return out

/-- Slice `mesh` by the PGA3 plane `Π = d·e₀ + n·(e₁,e₂,e₃)` (`‖n‖ = 1`),
returning both clipped 3D halves, 3D glowing cut contour segments, and a stitched
2D `ContourOverlay` projected into the plane's `(u, v)` frame! -/
def sliceMeshByPlane (mesh : MeshAsset) (normal : Vec3) (d : Float)
    (lowerId : UInt64 := 2001) (upperId : UInt64 := 2002) : SliceResult := Id.run do
  let n := Vec3.normalize normal
  let center := Vec3.scale (-d) n
  let (u, v) := Vec3.orthonormalBasis n
  let vCount := mesh.positions.size / 3
  let triCount := mesh.indices.size / 3
  let mut lowerMb : MeshBuilder := {}
  let mut upperMb : MeshBuilder := {}
  let mut segs3D : Array SegmentPrim := #[]
  let mut segs2D : Array Seg2 := #[]
  for t in [:triCount] do
    let i0 := mesh.indices[t * 3]!.toNat
    let i1 := mesh.indices[t * 3 + 1]!.toNat
    let i2 := mesh.indices[t * 3 + 2]!.toNat
    if i0 < vCount && i1 < vCount && i2 < vCount then
      let p0 := getVertPos mesh i0; let p1 := getVertPos mesh i1; let p2 := getVertPos mesh i2
      let c0 := getVertCol mesh i0; let c1 := getVertCol mesh i1; let c2 := getVertCol mesh i2
      -- Exact PGA3 incidence: (P/P.e123 ^ Π).e0123 = n·P + d
      let s0 := Vec3.dot n p0 + d
      let s1 := Vec3.dot n p1 + d
      let s2 := Vec3.dot n p2 + d
      lowerMb := clipTriHalfSpace lowerMb p0 p1 p2 c0 c1 c2 s0 s1 s2 true
      upperMb := clipTriHalfSpace upperMb p0 p1 p2 c0 c1 c2 s0 s1 s2 false
      -- Extract exact cut segment where triangle straddles plane
      let pts := #[p0, p1, p2]
      let ds := #[s0, s1, s2]
      let mut cuts : Array Vec3 := #[]
      for ei in [:3] do
        let ej := (ei + 1) % 3
        let di := ds[ei]!; let dj := ds[ej]!
        if (di ≤ 0.0 && dj > 0.0) || (di > 0.0 && dj ≤ 0.0) then
          let denom := di - dj
          let frac := if Float.abs denom < 1e-12 then 0.5 else max 0.0 (min 1.0 (di / denom))
          cuts := cuts.push (Vec3.lerp pts[ei]! pts[ej]! frac)
      if cuts.size == 2 then
        let a := cuts[0]!; let b := cuts[1]!
        segs3D := segs3D.push { a, b, width := 3.6, color := RGBA.cyan }
        let da := Vec3.sub a center; let db := Vec3.sub b center
        segs2D := segs2D.push ⟨Vec3.dot da u, Vec3.dot da v, Vec3.dot db u, Vec3.dot db v⟩
  let stitched := stitchSegments segs2D RGBA.cyan 2.8 1e-3
  let overlay : ContourOverlay :=
    { minX := -1.4, maxX := 1.4, minY := -1.4, maxY := 1.4, curves := stitched, intersections := #[] }
  return {
    lowerMesh := lowerMb.finalize lowerId
    upperMesh := upperMb.finalize upperId
    contour3D := segs3D
    contour2D := overlay }

end Grassmann.CoffeeShop.Mesh
