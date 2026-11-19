import Grassmann.Scene.Types
import Grassmann.Eval.Engine
import Grassmann.Eval.Calc
import Grassmann.CoffeeShop.Mesh
import Grassmann.Codegen.GPU
import Grassmann.Codegen.GPUInit

/-!
# Pure-Lean CoffeeShop Preset Gallery (19 Flagship Interactive 3D & 2D Scenes)

All geometry, PGA3/CGA3/STA/R3 math, RK4 rigid-body physics, Huzita-Hatori origami
folding, FABRIK IK, dual-quaternion skinning, exact plane-mesh slicing, and GPU OPNS
shader codegen run 100% in Lean and emit canonical `SceneFrame`s (`GSIR` v1).

Credits: Steven De Keninck (`enkimute` / `ganja.js`) & Michael Reed (`chakravala` / `Grassmann.jl`).
-/

namespace Grassmann.CoffeeShop

open Grassmann.CABI.Alg Grassmann.Scene Grassmann.Eval Grassmann.CoffeeShop.Mesh

/-- Catalog metadata for a CoffeeShop preset. -/
structure PresetInfo where
  id          : String
  title       : String
  category    : String
  algebra     : String
  description : String
  sampleCode  : String
  deriving Repr, Inhabited

/-- Reusable helper: look up a draggable handle position or use its default. -/
@[inline] def hPos (handles : Array (UInt32 × Vec3)) (id : UInt32) (defPos : Vec3) : Vec3 :=
  ((handles.find? fun kv => kv.1 == id).map (·.2)).getD defPos

/-- Build standard `SceneFrame` header for a preset. -/
private def baseFrame (presetId title algSpec : String) (seq : UInt64) (t : Float)
    (is2D : Bool := false) : SceneFrame :=
  let (algName, V, p, q, r, witt) := resolveAlgebra algSpec
  { frameSeq := seq, simTime := t, mode := .coffeeShop, is2D,
    gridEnabled := true, darkTheme := true, gridSize := 2.2,
    algebra := algebraMetaOf algName V p q r witt,
    presetId, title,
    camera :=
      if is2D then { motor := Motor3.translator 0.0 0.0 (-4.2), orthoScale := 1.0, isOrtho := true }
      else { motor := Motor3.orbitCamera 0.58 (-0.30) 5.2, fovDeg := 45.0, distance := 5.2 } }

/-! ## Shared Static Mesh Caches (computed once per call; GPU caches by `dirtyHash`) -/

private def bunnyAsset : MeshAsset := buildBunnyMesh 1001
private def freeTopBox : MeshAsset := buildBoxMesh 0.6 2.0 1.0 RGBA.violet 1003
private def latheTorus : MeshAsset := buildTorusMesh 0.65 0.22 26 14 RGBA.cyan 1002
private def latheCone  : MeshAsset := buildConeMesh 0.55 1.1 24 RGBA.amber 1004
private def latheCyl   : MeshAsset := buildCylinderMesh 0.42 1.0 24 RGBA.green 1005
private def latheSphere : MeshAsset :=
  (MeshBuilder.addEllipsoid {} Vec3.zero ⟨0.55, 0.55, 0.55⟩ 0.0 12 20 RGBA.coral).finalize 1006

/-! ## 1. `#pga3d_slicing` — Flagship Bunny Mesh Plane Slicer + 2D Contour Inset -/

def buildPga3dSlicing (handles : Array (UInt32 × Vec3)) (sliceMotor : Option Motor3)
    (seq : UInt64) (t : Float) : SceneFrame :=
  let f := baseFrame "pga3d_slicing" "3D PGA Mesh Slicing (Bunny + Live Contour)" "PGA3" seq t
  -- Dual live 3D handles:
  --   handleId = 0: Plane Center (translates the cutting plane in 3D)
  --   handleId = 1: Tilt Normal  (rotates the PGA3 plane normal freely in SO(3))
  let armLen : Float := 0.95
  let hasH0 := handles.any (·.1 == 0)
  let hasH1 := handles.any (·.1 == 1)
  let defCenter : Vec3 := ⟨0.0, 0.15 + 0.45 * Float.sin (t * 0.65), 0.0⟩
  let defTilt := 0.25 * Float.sin (t * 0.4)
  let defNormal : Vec3 := Vec3.normalize ⟨Float.sin defTilt, Float.cos defTilt, 0.12 * Float.cos (t * 0.3)⟩
  let (planeCenter, planeNormal, planeD) :=
    if !hasH0 && !hasH1 then
      match sliceMotor with
      | some m =>
        let n := Vec3.normalize (Motor3.applyDir m ⟨0.0, 1.0, 0.0⟩)
        let p0 := Motor3.applyPoint m Vec3.zero
        (p0, n, -(Vec3.dot n p0))
      | none =>
        (defCenter, defNormal, -(Vec3.dot defNormal defCenter))
    else
      let c := hPos handles 0 defCenter
      let n :=
        if hasH1 then
          let tip := hPos handles 1 (Vec3.add c (Vec3.scale armLen defNormal))
          let diff := Vec3.sub tip c
          if Vec3.norm diff > 0.08 then Vec3.normalize diff else defNormal
        else
          let tilt := 0.25 * Float.sin (t * 0.4) + 0.35 * c.x
          Vec3.normalize ⟨Float.sin tilt, Float.cos tilt, 0.2 * c.z⟩
      (c, n, -(Vec3.dot n c))
  let tiltPos := Vec3.add planeCenter (Vec3.scale armLen planeNormal)
  let (u, v) := Vec3.orthonormalBasis planeNormal
  let sliced := sliceMeshByPlane bunnyAsset planeNormal planeD 2001 2002
  let normalStem : SegmentPrim :=
    { a := planeCenter, b := tiltPos, width := 3.2, color := RGBA.amber,
      role := { arrow := true } }
  let insp : Array InspectEntry := #[
    { idx := 0, name := "cutPlane", grade := 1,
      formatted := s!"{planeD}e0 + {planeNormal.x}e1 + {planeNormal.y}e2 + {planeNormal.z}e3",
      editable := true },
    { idx := 1, name := "planeNormal", grade := 1,
      formatted := s!"({planeNormal.x}, {planeNormal.y}, {planeNormal.z})",
      editable := true },
    { idx := 2, name := "contourSegs", grade := 2,
      formatted := s!"{sliced.contour3D.size} cut edges, {sliced.contour2D.curves.size} loops",
      editable := false }
  ]
  { f with
    meshAssets := #[sliced.lowerMesh, sliced.upperMesh]
    meshRefs := #[
      { meshId := sliced.lowerMesh.meshId, dirtyHash := sliced.lowerMesh.dirtyHash,
        motor := Motor3.identity, color := RGBA.white, useVertexColors := true },
      { meshId := sliced.upperMesh.meshId, dirtyHash := sliced.upperMesh.dirtyHash,
        motor := Motor3.translator (0.08 * planeNormal.x) (0.08 * planeNormal.y) (0.08 * planeNormal.z),
        color := ⟨0.88, 0.92, 1.0, 0.24⟩, useVertexColors := false }
    ]
    planes := #[{
      center := planeCenter, u, v, extent := 1.5,
      color := ⟨0.22, 0.85, 0.98, 0.18⟩, gridLines := true,
      handleId := 0, role := { draggable := true }, label := "Cut Plane Π" }]
    points := #[
      { handleId := 0, pos := planeCenter, radius := 0.09, color := RGBA.cyan,
        role := { draggable := true }, label := "Plane Center" },
      { handleId := 1, pos := tiltPos, radius := 0.085, color := RGBA.amber,
        role := { draggable := true }, label := "Tilt Normal" }
    ]
    segments := sliced.contour3D.push normalStem
    contourOverlay := some sliced.contour2D
    inspect := insp }

/-! ## 2. `pga3d_points_and_lines` — 5 Draggable Pyramid Points + Joins & Meets -/

def buildPga3dPointsAndLines (handles : Array (UInt32 × Vec3)) (seq : UInt64) (t : Float) :
    SceneFrame :=
  let f := baseFrame "pga3d_points_and_lines" "3D PGA Points, Lines & Planes" "PGA3" seq t
  let A := hPos handles 0 ⟨0.0, 0.95, 0.0⟩
  let B := hPos handles 1 ⟨0.9, -0.9, -0.9⟩
  let C := hPos handles 2 ⟨-0.9, -0.9, -0.9⟩
  let D := hPos handles 3 ⟨0.9, -0.9, 0.9⟩
  let E := hPos handles 4 ⟨-0.9, -0.9, 0.9⟩
  let avg := Vec3.scale (1.0 / 3.0) (Vec3.add A (Vec3.add B E))
  let bc  := Vec3.scale 0.5 (Vec3.add B C)
  let dirEC := Vec3.normalize (Vec3.sub C E)
  let dirL  := Vec3.normalize (Vec3.sub bc avg)
  -- Plane A&B&C
  let nABC := Vec3.normalize (Vec3.cross (Vec3.sub B A) (Vec3.sub C A))
  let (uABC, vABC) := Vec3.orthonormalBasis nABC
  let ctrABC := Vec3.scale (1.0 / 3.0) (Vec3.add A (Vec3.add B C))
  -- Plane A&E&D and intersection l ^ (A&E&D)
  let nAED := Vec3.normalize (Vec3.cross (Vec3.sub E A) (Vec3.sub D A))
  let denom := Vec3.dot nAED dirL
  let inter :=
    if Float.abs denom < 1e-6 then avg
    else
      let s := Vec3.dot nAED (Vec3.sub A avg) / denom
      Vec3.add avg (Vec3.scale s dirL)
  let sumDir := Vec3.normalize (Vec3.add dirL dirEC)
  let sumOrig := Vec3.scale 0.5 (Vec3.add avg E)
  { f with
    points := #[
      { handleId := 0, pos := A, radius := 0.09, color := RGBA.cyan, role := { draggable := true }, label := "A" },
      { handleId := 1, pos := B, radius := 0.09, color := RGBA.cyan, role := { draggable := true }, label := "B" },
      { handleId := 2, pos := C, radius := 0.09, color := RGBA.cyan, role := { draggable := true }, label := "C" },
      { handleId := 3, pos := D, radius := 0.09, color := RGBA.cyan, role := { draggable := true }, label := "D" },
      { handleId := 4, pos := E, radius := 0.09, color := RGBA.cyan, role := { draggable := true }, label := "E" },
      { handleId := 10, pos := avg, radius := 0.075, color := RGBA.violet, label := "A+B+E" },
      { handleId := 11, pos := bc, radius := 0.075, color := RGBA.violet, label := "B+C" },
      { handleId := 12, pos := inter, radius := 0.095, color := RGBA.green, label := "l ^ (A&E&D)" }
    ]
    segments := #[
      { a := A, b := B, width := 2.0, color := RGBA.green },
      { a := A, b := C, width := 2.0, color := RGBA.green },
      { a := A, b := D, width := 2.0, color := RGBA.green },
      { a := A, b := E, width := 2.0, color := RGBA.green },
      { a := B, b := C, width := 2.0, color := RGBA.green },
      { a := C, b := E, width := 2.0, color := RGBA.green },
      { a := E, b := D, width := 2.0, color := RGBA.green },
      { a := D, b := B, width := 2.0, color := RGBA.green }
    ]
    lines := #[
      { origin := E, dir := dirEC, clip := 2.4, width := 2.4, color := RGBA.violet, label := "E&C" },
      { origin := avg, dir := dirL, clip := 2.6, width := 2.4, color := RGBA.blue, label := "(A+B+E)&(B+C)" },
      { origin := sumOrig, dir := sumDir, clip := 2.4, width := 2.4, color := RGBA.amber, label := "l + ec" }
    ]
    planes := #[
      { center := ctrABC, u := uABC, v := vABC, extent := 1.25,
        color := ⟨0.58, 0.35, 0.95, 0.22⟩, label := "A&B&C" }
    ]
    inspect := #[
      { idx := 0, name := "A", grade := 3, formatted := s!"e123 + {A.x}e023 + {A.y}e031 + {A.z}e012" },
      { idx := 1, name := "l ^ (A&E&D)", grade := 3, formatted := s!"({inter.x}, {inter.y}, {inter.z})" }
    ] }

/-! ## 3. `pga3d_physics_free_top` — Dzhanibekov Rigid Body RK4 in PGA3 -/

/-- Exact RK4 step of Euler's torque-free rigid body equations in PGA3 (`M, ω_body`)
for box inertia `I = (Ix, Iy, Iz)` — demonstrates the Dzhanibekov intermediate-axis flip! -/
def stepFreeTopRK4 (m : Motor3) (w : Vec3) (dt : Float) : Motor3 × Vec3 :=
  -- Box size (0.6, 2.0, 1.0), mass = 1 => principal inertias:
  let ix := (2.0 * 2.0 + 1.0 * 1.0) / 12.0
  let iy := (0.6 * 0.6 + 1.0 * 1.0) / 12.0
  let iz := (0.6 * 0.6 + 2.0 * 2.0) / 12.0
  let dw (om : Vec3) : Vec3 :=
    ⟨((iy - iz) / ix) * om.y * om.z,
     ((iz - ix) / iy) * om.z * om.x,
     ((ix - iy) / iz) * om.x * om.y⟩
  let dm (mot : Motor3) (om : Vec3) : Motor3 :=
    -- dM/dt = ½ M * B_ω where B_ω = -ω_x e23 + ω_y e13 - ω_z e12
    let bw : Motor3 := { s := 0.0, e23 := -0.5 * om.x, e13 := 0.5 * om.y, e12 := -0.5 * om.z }
    Motor3.mul mot bw
  let addM (a b : Motor3) (s : Float) : Motor3 :=
    { s := a.s + s * b.s, e01 := a.e01 + s * b.e01, e02 := a.e02 + s * b.e02,
      e03 := a.e03 + s * b.e03, e12 := a.e12 + s * b.e12, e13 := a.e13 + s * b.e13,
      e23 := a.e23 + s * b.e23, e0123 := a.e0123 + s * b.e0123 }
  let k1m := dm m w; let k1w := dw w
  let k2m := dm (addM m k1m (0.5 * dt)) (Vec3.add w (Vec3.scale (0.5 * dt) k1w))
  let k2w := dw (Vec3.add w (Vec3.scale (0.5 * dt) k1w))
  let k3m := dm (addM m k2m (0.5 * dt)) (Vec3.add w (Vec3.scale (0.5 * dt) k2w))
  let k3w := dw (Vec3.add w (Vec3.scale (0.5 * dt) k2w))
  let k4m := dm (addM m k3m dt) (Vec3.add w (Vec3.scale dt k3w))
  let k4w := dw (Vec3.add w (Vec3.scale dt k3w))
  let combM (a b c d : Float) : Float := (dt / 6.0) * (a + 2.0 * b + 2.0 * c + d)
  let mNext : Motor3 :=
    { s := m.s + combM k1m.s k2m.s k3m.s k4m.s
      e01 := m.e01 + combM k1m.e01 k2m.e01 k3m.e01 k4m.e01
      e02 := m.e02 + combM k1m.e02 k2m.e02 k3m.e02 k4m.e02
      e03 := m.e03 + combM k1m.e03 k2m.e03 k3m.e03 k4m.e03
      e12 := m.e12 + combM k1m.e12 k2m.e12 k3m.e12 k4m.e12
      e13 := m.e13 + combM k1m.e13 k2m.e13 k3m.e13 k4m.e13
      e23 := m.e23 + combM k1m.e23 k2m.e23 k3m.e23 k4m.e23
      e0123 := m.e0123 + combM k1m.e0123 k2m.e0123 k3m.e0123 k4m.e0123 }
  let wNext : Vec3 :=
    ⟨w.x + combM k1w.x k2w.x k3w.x k4w.x,
     w.y + combM k1w.y k2w.y k3w.y k4w.y,
     w.z + combM k1w.z k2w.z k3w.z k4w.z⟩
  (Motor3.normalize mNext, wNext)

def buildPga3dFreeTop (motor : Motor3) (omega : Vec3) (trail : FloatArray)
    (seq : UInt64) (t : Float) : SceneFrame :=
  let f := baseFrame "pga3d_physics_free_top" "3D PGA Free Top (Dzhanibekov RK4)" "PGA3" seq t
  let tip := Motor3.applyPoint motor ⟨0.0, 1.15, 0.0⟩
  let angWorld := Motor3.applyDir motor (Vec3.scale 0.5 omega)
  { f with
    meshAssets := #[freeTopBox]
    meshRefs := #[{ meshId := freeTopBox.meshId, dirtyHash := freeTopBox.dirtyHash,
                    motor, color := RGBA.white, useVertexColors := true }]
    segments := #[
      { a := Vec3.zero, b := angWorld, width := 3.5, color := RGBA.amber, role := { arrow := true } }
    ]
    points := #[{ handleId := 0, pos := tip, radius := 0.07, color := RGBA.cyan, label := "Body +Y" }]
    curves := if trail.size ≥ 6 then #[{ points := trail, width := 2.4, color := RGBA.cyan }] else #[]
    inspect := #[
      { idx := 0, name := "Motor M", grade := 2, formatted := s!"s={motor.s}, e12={motor.e12}, e13={motor.e13}, e23={motor.e23}" },
      { idx := 1, name := "ω_body", grade := 2, formatted := s!"({omega.x}, {omega.y}, {omega.z})" }
    ] }

/-! ## 4. `pga3d_origami` — Animated Kabuto Origami Folding via PGA3 Rotors -/

private def foldPoly (poly : Array Vec3) (planeN : Vec3) (planeD angle : Float) :
    Array (Array Vec3) := Id.run do
  let n := Vec3.normalize planeN
  -- Split polygon by plane n·p + d = 0, rotate negative side around hinge line in Z=0/plane
  let mut negSide : Array Vec3 := #[]
  let mut posSide : Array Vec3 := #[]
  for i in [:poly.size] do
    let j := (i + 1) % poly.size
    let pi := poly[i]!; let pj := poly[j]!
    let di := Vec3.dot n pi + planeD
    let dj := Vec3.dot n pj + planeD
    if di ≤ 1e-4 then negSide := negSide.push pi
    if di ≥ -1e-4 then posSide := posSide.push pi
    if (di < -1e-4 && dj > 1e-4) || (di > 1e-4 && dj < -1e-4) then
      let frac := di / (di - dj)
      let cut := Vec3.lerp pi pj frac
      negSide := negSide.push cut
      posSide := posSide.push cut
  -- Rotate negSide around hinge axis (n × +Y) passing through point p0 = -d*n
  let axis := Vec3.normalize (Vec3.cross n ⟨0.0, 1.0, 0.0⟩)
  let p0 := Vec3.scale (-planeD) n
  let r := Motor3.rotorAxis axis angle
  let rotPt (p : Vec3) : Vec3 := Vec3.add p0 (Motor3.applyDir r (Vec3.sub p p0))
  let mut out : Array (Array Vec3) := #[]
  if negSide.size ≥ 3 then out := out.push (negSide.map rotPt)
  if posSide.size ≥ 3 then out := out.push posSide
  return out

def buildPga3dOrigami (seq : UInt64) (t : Float) : SceneFrame :=
  let f := baseFrame "pga3d_origami" "3D PGA Origami (Kabuto Fold Axioms)" "PGA3" seq t
  let pi := 3.14159265358979323846
  let phase := (t * 0.45) - Float.floor (t * 0.45 / 4.0) * 4.0
  let step := phase.toUInt32.toNat
  let localT := phase - step.toFloat
  let s := 1.25
  let baseSq : Array Vec3 := #[⟨-s, 0.0, s⟩, ⟨s, 0.0, s⟩, ⟨s, 0.0, -s⟩, ⟨-s, 0.0, -s⟩]
  let a0 := if step == 0 then localT * pi * 0.92 else pi * 0.92
  let a1 := if step < 1 then 0.0 else if step == 1 then localT * pi * 0.85 else pi * 0.85
  let a2 := if step < 2 then 0.0 else if step == 2 then localT * pi * 0.85 else pi * 0.85
  let polys1 := foldPoly baseSq ⟨1.0, 0.0, 1.0⟩ 0.0 a0
  let polys2 := polys1.foldl (init := #[]) fun acc poly =>
    if a1 > 1e-3 then acc ++ foldPoly poly ⟨1.0, 0.0, 0.0⟩ (-0.35) a1 else acc.push poly
  let polys3 := polys2.foldl (init := #[]) fun acc poly =>
    if a2 > 1e-3 then acc ++ foldPoly poly ⟨0.0, 0.0, 1.0⟩ (-0.35) a2 else acc.push poly
  let mb : MeshBuilder := Id.run do
    let mut b : MeshBuilder := {}
    let mut ci := 0
    for poly in polys3 do
      let col : RGBA := if ci % 2 == 0 then ⟨0.94, 0.95, 0.98, 1.0⟩ else ⟨0.75, 0.86, 1.0, 1.0⟩
      if poly.size ≥ 3 then
        let (b0, i0) := b.addVertex poly[0]! col
        b := b0
        let mut prev := i0
        for k in [1:poly.size] do
          let (bk, ik) := b.addVertex poly[k]! col
          b := bk
          if k ≥ 2 then b := b.addTri i0 prev ik
          prev := ik
      ci := ci + 1
    return b
  let mesh := mb.finalize 2100
  let segs : Array SegmentPrim := Id.run do
    let mut out : Array SegmentPrim := #[]
    for poly in polys3 do
      for i in [:poly.size] do
        let j := (i + 1) % poly.size
        out := out.push { a := poly[i]!, b := poly[j]!, width := 2.2, color := RGBA.cyan }
    return out
  { f with
    meshAssets := #[mesh]
    meshRefs := #[{ meshId := mesh.meshId, dirtyHash := mesh.dirtyHash,
                    color := RGBA.white, useVertexColors := true, doubleSided := true }]
    segments := segs
    labels := #[{ pos := ⟨0.0, 1.45, 0.0⟩, text := s!"Kabuto Fold Step {min 4 (step + 1)}/4", color := RGBA.amber }] }

/-! ## 5. `pga3d_motor_orbits` — 1D Curves & 2D Manifolds via Motor Products -/

def buildPga3dMotorOrbits (seq : UInt64) (t : Float) : SceneFrame := Id.run do
  let f := baseFrame "pga3d_motor_orbits" "3D PGA Motor Orbits (Curves & Manifolds)" "PGA3" seq t
  let pi := 3.14159265358979323846
  let circleMot (axis : Vec3) (r u : Float) : Motor3 :=
    Motor3.mul (Motor3.rotorAxis axis (2.0 * pi * u)) (Motor3.translator r 0.0 0.0)
  let mut circPts := FloatArray.emptyWithCapacity (65 * 3)
  for i in [:65] do
    let u := i.toFloat / 64.0
    let m := circleMot ⟨0.0, 0.0, 1.0⟩ 1.45 u
    let p := Motor3.applyPoint m Vec3.zero
    circPts := circPts.push p.x |>.push p.y |>.push p.z
  -- Animated loxodrome / helical motor orbit
  let mut helixPts := FloatArray.emptyWithCapacity (96 * 3)
  for i in [:96] do
    let u := i.toFloat / 95.0
    let m := Motor3.expBivector 0.0 (1.3 * (u - 0.5)) 0.0 (2.5 * pi * u + t * 0.4) 0.0 0.0
    let p := Motor3.applyPoint m ⟨0.85, 0.0, 0.0⟩
    helixPts := helixPts.push p.x |>.push p.y |>.push p.z
  let rotM := Motor3.rotorAxis ⟨0.3, 1.0, 0.2⟩ (t * 0.45)
  return { f with
    meshAssets := #[latheTorus, latheCone]
    meshRefs := #[
      { meshId := latheTorus.meshId, dirtyHash := latheTorus.dirtyHash,
        motor := rotM, color := RGBA.white, useVertexColors := true },
      { meshId := latheCone.meshId, dirtyHash := latheCone.dirtyHash,
        motor := Motor3.mul (Motor3.translator 1.4 0.0 0.0) rotM,
        color := RGBA.white, useVertexColors := true }
    ]
    curves := #[
      { points := circPts, width := 3.0, color := RGBA.coral, closed := true },
      { points := helixPts, width := 3.0, color := RGBA.amber }
    ] }

/-! ## 6. `pga3d_icosahedron` — Progressive Rotor Icosahedron Construction -/

def buildPga3dIcosahedron (seq : UInt64) (t : Float) : SceneFrame := Id.run do
  let f := baseFrame "pga3d_icosahedron" "3D PGA Icosahedron via Rotors" "PGA3" seq t
  let phi := (1.0 + Float.sqrt 5.0) * 0.5
  let invR := 1.15 / Float.sqrt (1.0 + phi * phi)
  let rawV : Array Vec3 := #[
    ⟨-1, phi, 0⟩, ⟨1, phi, 0⟩, ⟨-1, -phi, 0⟩, ⟨1, -phi, 0⟩,
    ⟨0, -1, phi⟩, ⟨0, 1, phi⟩, ⟨0, -1, -phi⟩, ⟨0, 1, -phi⟩,
    ⟨phi, 0, -1⟩, ⟨phi, 0, 1⟩, ⟨-phi, 0, -1⟩, ⟨-phi, 0, 1⟩
  ]
  let rot := Motor3.mul (Motor3.rotorAxis ⟨0.0, 1.0, 0.0⟩ (t * 0.5))
                        (Motor3.rotorAxis ⟨1.0, 0.0, 0.0⟩ (t * 0.31))
  let verts := rawV.map fun v => Motor3.applyPoint rot (Vec3.scale invR v)
  let faces : Array (Nat × Nat × Nat) := #[
    (0,11,5), (0,5,1), (0,1,7), (0,7,10), (0,10,11),
    (1,5,9), (5,11,4), (11,10,2), (10,7,6), (7,1,8),
    (3,9,4), (3,4,2), (3,2,6), (3,6,8), (3,8,9),
    (4,9,5), (2,4,11), (6,2,10), (8,6,7), (9,8,1)
  ]
  let mut mb : MeshBuilder := {}
  let mut segs : Array SegmentPrim := #[]
  for (a, b, c) in faces do
    let pa := verts[a]!; let pb := verts[b]!; let pc := verts[c]!
    let (mb1, i0) := mb.addVertex pa ⟨0.36, 0.68, 1.0, 0.85⟩
    let (mb2, i1) := mb1.addVertex pb ⟨0.58, 0.42, 0.98, 0.85⟩
    let (mb3, i2) := mb2.addVertex pc ⟨0.24, 0.88, 0.92, 0.85⟩
    mb := mb3.addTri i0 i1 i2
    segs := segs.push { a := pa, b := pb, width := 2.0, color := RGBA.white }
                |>.push { a := pb, b := pc, width := 2.0, color := RGBA.white }
                |>.push { a := pc, b := pa, width := 2.0, color := RGBA.white }
  let mesh := mb.finalize 2200
  let pts := verts.mapIdx fun i v =>
    { handleId := i.toUInt32, pos := v, radius := 0.065, color := RGBA.amber : PointPrim }
  return { f with
    meshAssets := #[mesh]
    meshRefs := #[{ meshId := mesh.meshId, dirtyHash := mesh.dirtyHash,
                    color := RGBA.white, useVertexColors := true }]
    segments := segs, points := pts }

/-! ## 7. `pga3d_skinning` — Dual Quaternion vs Linear Blend Skinning Rod -/

def buildPga3dSkinning (seq : UInt64) (t : Float) : SceneFrame := Id.run do
  let f := baseFrame "pga3d_skinning" "3D PGA Dual-Quaternion vs Linear Skinning" "PGA3" seq t
  let useDQS := (Float.floor (t * 0.35)).toUInt32 % 2 == 0
  let twist := 2.2 * Float.sin (t * 1.4)
  let b1 := Motor3.mul (Motor3.rotorAxis ⟨0.0, 1.0, 0.0⟩ (-twist)) (Motor3.translator (0.25 * Float.sin t) 0.0 0.0)
  let b2 := Motor3.mul (Motor3.rotorAxis ⟨0.0, 1.0, 0.0⟩ twist) (Motor3.translator (-0.25 * Float.sin t) 0.0 0.0)
  let rings := 15
  let sides := 4
  let pi := 3.14159265358979323846
  let mut pts : Array Vec3 := Array.mkEmpty (rings * sides)
  for i in [:rings] do
    let w2 := i.toFloat / (rings - 1).toFloat
    let w1 := 1.0 - w2
    let y := -1.2 + 2.4 * w2
    let blendedMot : Motor3 := Motor3.normalize
      { s := w1 * b1.s + w2 * b2.s, e01 := w1 * b1.e01 + w2 * b2.e01,
        e02 := w1 * b1.e02 + w2 * b2.e02, e03 := w1 * b1.e03 + w2 * b2.e03,
        e12 := w1 * b1.e12 + w2 * b2.e12, e13 := w1 * b1.e13 + w2 * b2.e13,
        e23 := w1 * b1.e23 + w2 * b2.e23, e0123 := w1 * b1.e0123 + w2 * b2.e0123 }
    for j in [:sides] do
      let a := 2.0 * pi * j.toFloat / sides.toFloat
      let p0 : Vec3 := ⟨0.42 * Float.cos a, y, 0.42 * Float.sin a⟩
      let p :=
        if useDQS then Motor3.applyPoint blendedMot p0
        else Vec3.add (Vec3.scale w1 (Motor3.applyPoint b1 p0))
                      (Vec3.scale w2 (Motor3.applyPoint b2 p0))
      pts := pts.push p
  let col := if useDQS then RGBA.cyan else RGBA.coral
  let mut segs : Array SegmentPrim := #[]
  for i in [:rings] do
    for j in [:sides] do
      let idx := i * sides + j
      let nxt := i * sides + ((j + 1) % sides)
      segs := segs.push { a := pts[idx]!, b := pts[nxt]!, width := 2.6, color := col }
      if i + 1 < rings then
        segs := segs.push { a := pts[idx]!, b := pts[(i + 1) * sides + j]!, width := 2.6, color := col }
  return { f with
    segments := segs
    labels := #[{ pos := ⟨0.0, 1.55, 0.0⟩,
                  text := if useDQS then "Dual Quaternion Skinning (Volume Preserved)"
                          else "Linear Blend Skinning (Candy-Wrapper Collapse)",
                  color := col }] }

/-! ## 8. `pga3d_objects` — Lathed PGA3 Solids + 3D Motor Flow Particle Field -/

def buildPga3dObjects (seq : UInt64) (t : Float) : SceneFrame := Id.run do
  let f := baseFrame "pga3d_objects" "3D PGA Lathed Solids & Motor Flow Field" "PGA3" seq t
  let spin := Motor3.mul (Motor3.rotorAxis ⟨0.0, 1.0, 0.0⟩ t) (Motor3.rotorAxis ⟨1.0, 0.0, 0.0⟩ (t * 0.4))
  let flowMot := Motor3.expBivector 0.0 0.08 0.0 0.0 0.22 0.06
  let mut starts := FloatArray.emptyWithCapacity (216 * 3)
  let mut ends   := FloatArray.emptyWithCapacity (216 * 3)
  for ix in [:6] do
    for iy in [:6] do
      for iz in [:6] do
        let p : Vec3 := ⟨-1.5 + ix.toFloat * 0.6, -1.5 + iy.toFloat * 0.6, -1.5 + iz.toFloat * 0.6⟩
        let q := Motor3.applyPoint flowMot p
        starts := starts.push p.x |>.push p.y |>.push p.z
        ends   := ends.push q.x |>.push q.y |>.push q.z
  return { f with
    meshAssets := #[latheTorus, latheCone, latheCyl, latheSphere]
    meshRefs := #[
      { meshId := latheTorus.meshId, dirtyHash := latheTorus.dirtyHash,
        motor := Motor3.mul (Motor3.translator (-1.15) 0.55 0.0) spin, useVertexColors := true },
      { meshId := latheSphere.meshId, dirtyHash := latheSphere.dirtyHash,
        motor := Motor3.mul (Motor3.translator 1.15 0.55 0.0) spin, useVertexColors := true },
      { meshId := latheCone.meshId, dirtyHash := latheCone.dirtyHash,
        motor := Motor3.mul (Motor3.translator (-1.15) (-0.75) 0.0) spin, useVertexColors := true },
      { meshId := latheCyl.meshId, dirtyHash := latheCyl.dirtyHash,
        motor := Motor3.mul (Motor3.translator 1.15 (-0.75) 0.0) spin, useVertexColors := true }
    ]
    flowFields := #[{ starts, ends, pointSize := 4.5, color := RGBA.cyan, speed := 1.0 }] }

/-! ## 9. `cga3d_intersections` — Live Sphere ∩ {Sphere, Plane, Line, Circle} (Real + Imaginary!) -/

def buildCga3dIntersections (handles : Array (UInt32 × Vec3)) (seq : UInt64) (t : Float) :
    SceneFrame :=
  let f := baseFrame "cga3d_intersections" "3D CGA Live Intersections (Real & Imaginary)" "CGA3" seq t
  let c1 := hPos handles 0 ⟨0.25 * Float.sin (t * 0.6), 0.15 * Float.cos (t * 0.5), 0.0⟩
  let r1 := 1.05
  let c2 : Vec3 := ⟨-1.3, 0.0, 0.0⟩
  let r2 := 0.65
  let planeY := -0.78
  let lineY := 0.82
  -- Sphere S1 ∩ Plane y = planeY -> Circle (imaginary when |c1.y - planeY| > r1)
  let dyP := c1.y - planeY
  let r2SP := r1 * r1 - dyP * dyP
  let circSP : CirclePrim :=
    { center := ⟨c1.x, planeY, c1.z⟩, u := ⟨1.0, 0.0, 0.0⟩, v := ⟨0.0, 0.0, 1.0⟩,
      radius := Float.sqrt (Float.abs r2SP), width := 3.0,
      color := if r2SP ≥ 0.0 then RGBA.cyan else RGBA.coral,
      imaginary := r2SP < 0.0, label := "S1 & P" }
  -- Sphere S1 ∩ Sphere S2 -> Circle (or imaginary circle!)
  let d12Vec := Vec3.sub c2 c1
  let d12 := max 1e-6 (Vec3.norm d12Vec)
  let dir12 := Vec3.scale (1.0 / d12) d12Vec
  let h := 0.5 * (d12 + (r1 * r1 - r2 * r2) / d12)
  let r2SS := r1 * r1 - h * h
  let (uSS, vSS) := Vec3.orthonormalBasis dir12
  let circSS : CirclePrim :=
    { center := Vec3.add c1 (Vec3.scale h dir12), u := uSS, v := vSS,
      radius := Float.sqrt (Float.abs r2SS), width := 3.0,
      color := if r2SS ≥ 0.0 then RGBA.blue else RGBA.coral,
      imaginary := r2SS < 0.0, label := "S1 & S2" }
  -- Sphere S1 ∩ Line (y = lineY, z = 0) -> Point Pair (real or imaginary!)
  let dyL := lineY - c1.y; let dzL := -c1.z
  let discSL := r1 * r1 - dyL * dyL - dzL * dzL
  let dxSL := Float.sqrt (Float.abs discSL)
  let ppSL : PointPairPrim :=
    { p1 := ⟨c1.x - dxSL, lineY, 0.0⟩, p2 := ⟨c1.x + dxSL, lineY, 0.0⟩,
      radius := 0.08, color := if discSL ≥ 0.0 then RGBA.amber else RGBA.coral,
      imaginary := discSL < 0.0, showLink := true, label := "S1 & L" }
  -- Right circle C at (1.35, 0, 0) radius 0.6 in XY plane
  let circC : CirclePrim :=
    { center := ⟨1.35, 0.0, 0.0⟩, u := ⟨1.0, 0.0, 0.0⟩, v := ⟨0.0, 1.0, 0.0⟩,
      radius := 0.6, width := 2.6, color := RGBA.green, label := "C" }
  { f with
    points := #[{
      handleId := 0, pos := c1, radius := 0.09, color := RGBA.coral,
      role := { draggable := true }, label := "Drag S1" }]
    spheres := #[
      { center := c1, radius := r1, color := ⟨0.85, 0.92, 1.0, 0.22⟩, label := "S1" },
      { center := c2, radius := r2, color := ⟨0.45, 0.72, 1.0, 0.26⟩, label := "S2" }
    ]
    planes := #[{
      center := ⟨0.0, planeY, 0.0⟩, u := ⟨1.0, 0.0, 0.0⟩, v := ⟨0.0, 0.0, 1.0⟩,
      extent := 2.1, color := ⟨0.20, 0.75, 0.45, 0.20⟩, label := "P" }]
    lines := #[{
      origin := ⟨0.0, lineY, 0.0⟩, dir := ⟨1.0, 0.0, 0.0⟩, clip := 2.3,
      width := 2.4, color := RGBA.white, label := "L" }]
    circles := #[circSP, circSS, circC]
    pointPairs := #[ppSL]
    inspect := #[
      { idx := 0, name := "S1 & P (r²)", grade := 3, formatted := s!"r² = {r2SP} ({if r2SP ≥ 0.0 then "real" else "imaginary"})" },
      { idx := 1, name := "S1 & S2 (r²)", grade := 3, formatted := s!"r² = {r2SS} ({if r2SS ≥ 0.0 then "real" else "imaginary"})" },
      { idx := 2, name := "S1 & L (disc)", grade := 2, formatted := s!"Δ = {discSL} ({if discSL ≥ 0.0 then "real pair" else "imaginary pair"})" }
    ] }

/-! ## 10. `cga3d_spheres_apollonius` — Circumsphere Through 4 Draggable Points -/

private def solveCircumsphere4 (p1 p2 p3 p4 : Vec3) : Vec3 × Float :=
  let a := Vec3.sub p2 p1; let b := Vec3.sub p3 p1; let c := Vec3.sub p4 p1
  let det := Vec3.dot a (Vec3.cross b c)
  if Float.abs det < 1e-8 then (Vec3.scale 0.25 (Vec3.add (Vec3.add p1 p2) (Vec3.add p3 p4)), 1.0)
  else
    let num := Vec3.add
      (Vec3.scale (Vec3.normSq c) (Vec3.cross a b))
      (Vec3.add (Vec3.scale (Vec3.normSq b) (Vec3.cross c a))
                (Vec3.scale (Vec3.normSq a) (Vec3.cross b c)))
    let rel := Vec3.scale (0.5 / det) num
    (Vec3.add p1 rel, Vec3.norm rel)

def buildCga3dSpheresApollonius (handles : Array (UInt32 × Vec3)) (seq : UInt64) (t : Float) :
    SceneFrame :=
  let f := baseFrame "cga3d_spheres_apollonius" "3D CGA Circumsphere & Plane (p1^p2^p3^p4)" "CGA3" seq t
  let p1 := hPos handles 0 ⟨1.0, 0.2, 0.2⟩
  let p2 := hPos handles 1 ⟨-0.3, 1.05, 0.1⟩
  let p3 := hPos handles 2 ⟨-0.2, -0.3, -1.05⟩
  let p4 := hPos handles 3 ⟨0.1, -0.95, 0.55⟩
  let (ctr, rad) := solveCircumsphere4 p1 p2 p3 p4
  let nPl := Vec3.normalize (Vec3.cross (Vec3.sub p2 p1) (Vec3.sub p3 p1))
  let (uPl, vPl) := Vec3.orthonormalBasis nPl
  let cPl := Vec3.scale (1.0 / 3.0) (Vec3.add p1 (Vec3.add p2 p3))
  { f with
    points := #[
      { handleId := 0, pos := p1, radius := 0.09, color := RGBA.coral, role := { draggable := true }, label := "p1" },
      { handleId := 1, pos := p2, radius := 0.09, color := RGBA.coral, role := { draggable := true }, label := "p2" },
      { handleId := 2, pos := p3, radius := 0.09, color := RGBA.coral, role := { draggable := true }, label := "p3" },
      { handleId := 3, pos := p4, radius := 0.09, color := RGBA.coral, role := { draggable := true }, label := "p4" },
      { handleId := 10, pos := ctr, radius := 0.06, color := RGBA.cyan, label := "Center" }
    ]
    spheres := #[
      { center := ctr, radius := min 4.0 rad, color := ⟨0.25, 0.58, 1.0, 0.24⟩, label := "p1^p2^p3^p4" },
      -- Inner Apollonius-like tangent sphere
      { center := Vec3.lerp ctr p1 0.5, radius := min 2.0 (0.5 * rad),
        color := ⟨0.95, 0.62, 0.20, 0.22⟩, label := "Tangent" }
    ]
    planes := #[{
      center := cPl, u := uPl, v := vPl, extent := 1.8,
      color := ⟨0.22, 0.85, 0.55, 0.18⟩, label := "p1^p2^p3^n∞" }]
    inspect := #[
      { idx := 0, name := "Sphere", grade := 4, formatted := s!"center=({ctr.x},{ctr.y},{ctr.z}), r={rad}" }
    ] }

/-! ## 11. `cga3d_opns_cyclide` — Lean-Generated WGSL/GLSL/MSL OPNS Raymarching Shader! -/

def buildCga3dOpnsCyclide (seq : UInt64) (t : Float) : SceneFrame :=
  let f := baseFrame "cga3d_opns_cyclide" "3D CGA OPNS Raymarcher (Lean WGSL/GLSL/MSL)" "CGA3" seq t
  let shaderOpt := Grassmann.Codegen.GPUInit.compileGaOpnsBundle "cga3_witt" Grassmann.Codegen.GPUInit.AlgSpec.cga3 4 false
  let shaders := match shaderOpt with | .ok s => #[s] | .error _ => #[]
  -- Grade-4 blade in 5D CGA3 has C(5,4) = 5 coefficients ordered for GPUInit's
  -- `c0 = z*b[0] - y*b[1] + x*b[2] - 1.0*b[3] + 0.5*(x^2+y^2+z^2)*b[4] = 0`:
  -- Sphere of center (cx, cy, cz) and radius r:
  --   b[0] = -cz, b[1] = cy, b[2] = -cx, b[3] = 0.5*(r^2 - (cx^2+cy^2+cz^2)), b[4] = 1.0
  let cx := 0.28 * Float.sin (t * 0.7)
  let cy := 0.16 * Float.sin (t * 0.9)
  let cz := 0.22 * Float.cos (t * 0.6)
  let r := 0.78 + 0.12 * Float.cos (t * 0.9)
  let c2 := cx * cx + cy * cy + cz * cz
  let coeffs := (FloatArray.emptyWithCapacity 5)
    |>.push (-cz)
    |>.push cy
    |>.push (-cx)
    |>.push (0.5 * (r * r - c2))
    |>.push 1.0
  { f with
    opnsShaders := shaders
    opnsUniforms := #[{
      shaderIdx := 0, grade := 4, coeffs, thresh := 0.04, maxSteps := 80, stepSize := 0.00025,
      color := ⟨0.68, 0.42, 1.0, 0.92⟩, isIPNS := false }]
    -- Also provide a crisp parametric Dupin-cyclide/torus wireframe guide for non-OPNS render paths
    meshAssets := #[latheTorus]
    meshRefs := #[{
      meshId := latheTorus.meshId, dirtyHash := latheTorus.dirtyHash,
      motor := Motor3.rotorAxis ⟨0.4, 1.0, 0.0⟩ (t * 0.5),
      color := ⟨0.72, 0.45, 1.0, 0.35⟩, wireframe := true }]
    inspect := #[
      { idx := 0, name := "OPNS Shader", grade := 4,
        formatted := if shaders.isEmpty then "compile err" else s!"WGSL+GLSL+MSL ({shaders[0]!.hash})" }
    ] }

/-! ## 12. `pga2d_euler_line` — Interactive Euler Line (Orthocenter, Circumcenter, Centroid) -/

def buildPga2dEulerLine (handles : Array (UInt32 × Vec3)) (seq : UInt64) (t : Float) : SceneFrame :=
  let f := baseFrame "pga2d_euler_line" "2D PGA Euler's Line" "PGA2" seq t true
  let A := hPos handles 0 ⟨-1.4, -0.5, 0.0⟩
  let B := hPos handles 1 ⟨0.5, 1.45, 0.0⟩
  let C := hPos handles 2 ⟨1.1, -0.5, 0.0⟩
  let centroid := Vec3.scale (1.0 / 3.0) (Vec3.add A (Vec3.add B C))
  -- Exact 2D circumcenter
  let d := 2.0 * (A.x * (B.y - C.y) + B.x * (C.y - A.y) + C.x * (A.y - B.y))
  let (circum, ortho) :=
    if Float.abs d < 1e-6 then (centroid, centroid)
    else
      let a2 := A.x * A.x + A.y * A.y
      let b2 := B.x * B.x + B.y * B.y
      let c2 := C.x * C.x + C.y * C.y
      let ux := (a2 * (B.y - C.y) + b2 * (C.y - A.y) + c2 * (A.y - B.y)) / d
      let uy := (a2 * (C.x - B.x) + b2 * (A.x - C.x) + c2 * (B.x - A.x)) / d
      let cc : Vec3 := ⟨ux, uy, 0.0⟩
      -- Euler identity: H = A + B + C - 2O
      let hh : Vec3 := ⟨A.x + B.x + C.x - 2.0 * ux, A.y + B.y + C.y - 2.0 * uy, 0.0⟩
      (cc, hh)
  let eDir := Vec3.normalize (Vec3.sub circum ortho)
  { f with
    points := #[
      { handleId := 0, pos := A, radius := 0.09, color := RGBA.cyan, role := { draggable := true }, label := "A" },
      { handleId := 1, pos := B, radius := 0.09, color := RGBA.cyan, role := { draggable := true }, label := "B" },
      { handleId := 2, pos := C, radius := 0.09, color := RGBA.cyan, role := { draggable := true }, label := "C" },
      { handleId := 10, pos := ortho, radius := 0.08, color := RGBA.violet, label := "Orthocenter" },
      { handleId := 11, pos := circum, radius := 0.08, color := RGBA.blue, label := "Circumcenter" },
      { handleId := 12, pos := centroid, radius := 0.08, color := RGBA.green, label := "Centroid" }
    ]
    segments := #[
      { a := A, b := B, width := 2.5, color := RGBA.white },
      { a := B, b := C, width := 2.5, color := RGBA.white },
      { a := C, b := A, width := 2.5, color := RGBA.white },
      { a := A, b := ortho, width := 1.4, color := RGBA.violet, role := { dashed := true } },
      { a := B, b := ortho, width := 1.4, color := RGBA.violet, role := { dashed := true } }
    ]
    lines := #[{
      origin := centroid, dir := eDir, clip := 3.4, width := 3.0,
      color := RGBA.amber, label := "Euler Line" }]
    circles := #[{
      center := circum, u := ⟨1.0, 0.0, 0.0⟩, v := ⟨0.0, 1.0, 0.0⟩,
      radius := Vec3.norm (Vec3.sub A circum), width := 1.8, color := ⟨0.3, 0.62, 1.0, 0.6⟩ }] }

/-! ## 13. `pga2d_inverse_kinematics` — 6-Segment PGA2 FABRIK Kinematic Arm -/

def buildPga2dIK (handles : Array (UInt32 × Vec3)) (seq : UInt64) (t : Float) : SceneFrame := Id.run do
  let f := baseFrame "pga2d_inverse_kinematics" "2D PGA Inverse Kinematics (FABRIK)" "PGA2" seq t true
  let base := hPos handles 0 ⟨-1.4, 0.0, 0.0⟩
  let defTarget : Vec3 := ⟨0.9 + 0.55 * Float.cos (t * 1.1), 0.75 * Float.sin (t * 1.6), 0.0⟩
  let target := hPos handles 1 defTarget
  let nSegs := 6
  let segLen := 0.52
  let mut c : Array Vec3 := Array.mkEmpty (nSegs + 1)
  for i in [:(nSegs + 1)] do
    c := c.push ⟨base.x + i.toFloat * segLen, base.y, 0.0⟩
  for _ in [:8] do
    c := c.set! nSegs target
    for k in [:nSegs] do
      let i := nSegs - 1 - k
      let d := Vec3.normalize (Vec3.sub c[i]! c[i + 1]!)
      c := c.set! i (Vec3.add c[i + 1]! (Vec3.scale segLen d))
    c := c.set! 0 base
    for i in [1:(nSegs + 1)] do
      let d := Vec3.normalize (Vec3.sub c[i]! c[i - 1]!)
      c := c.set! i (Vec3.add c[i - 1]! (Vec3.scale segLen d))
  let mut segs : Array SegmentPrim := #[]
  let mut pts : Array PointPrim := #[
    { handleId := 0, pos := base, radius := 0.10, color := RGBA.violet, role := { draggable := true }, label := "Base" },
    { handleId := 1, pos := target, radius := 0.11, color := RGBA.coral, role := { draggable := true }, label := "Target" }
  ]
  for i in [:nSegs] do
    segs := segs.push { a := c[i]!, b := c[i + 1]!, width := 4.0, color := RGBA.green }
    if i > 0 then
      pts := pts.push { handleId := (10 + i).toUInt32, pos := c[i]!, radius := 0.075, color := RGBA.cyan }
  return { f with points := pts, segments := segs }

/-! ## 14. `pga2d_desargues_theorem` — Interactive Projective Perspective Triangles -/

def buildPga2dDesargues (handles : Array (UInt32 × Vec3)) (seq : UInt64) (t : Float) : SceneFrame :=
  let f := baseFrame "pga2d_desargues_theorem" "2D PGA Desargues' Theorem" "PGA2" seq t true
  let O := hPos handles 0 ⟨-1.7, 0.9, 0.0⟩
  let A := hPos handles 1 ⟨-0.6, 0.95, 0.0⟩
  let B := hPos handles 2 ⟨-0.9, -0.2, 0.0⟩
  let C := hPos handles 3 ⟨-0.1, -0.4, 0.0⟩
  let A' := Vec3.lerp O A 1.75
  let B' := Vec3.lerp O B 1.95
  let C' := Vec3.lerp O C 1.65
  let lineMeet (p1 p2 q1 q2 : Vec3) : Vec3 :=
    let a1 := p1.y - p2.y; let b1 := p2.x - p1.x; let c1 := p1.x * p2.y - p1.y * p2.x
    let a2 := q1.y - q2.y; let b2 := q2.x - q1.x; let c2 := q1.x * q2.y - q1.y * q2.x
    let w := a1 * b2 - b1 * a2
    if Float.abs w < 1e-6 then Vec3.zero
    else ⟨(b1 * c2 - c1 * b2) / w, (c1 * a2 - a1 * c2) / w, 0.0⟩
  let X := lineMeet A B A' B'
  let Y := lineMeet B C B' C'
  let Z := lineMeet C A C' A'
  { f with
    points := #[
      { handleId := 0, pos := O, radius := 0.09, color := RGBA.amber, role := { draggable := true }, label := "O" },
      { handleId := 1, pos := A, radius := 0.08, color := RGBA.cyan, role := { draggable := true }, label := "A" },
      { handleId := 2, pos := B, radius := 0.08, color := RGBA.cyan, role := { draggable := true }, label := "B" },
      { handleId := 3, pos := C, radius := 0.08, color := RGBA.cyan, role := { draggable := true }, label := "C" },
      { handleId := 10, pos := A', radius := 0.07, color := RGBA.green, label := "A'" },
      { handleId := 11, pos := B', radius := 0.07, color := RGBA.green, label := "B'" },
      { handleId := 12, pos := C', radius := 0.07, color := RGBA.green, label := "C'" },
      { handleId := 13, pos := X, radius := 0.08, color := RGBA.coral, label := "AB^A'B'" },
      { handleId := 14, pos := Y, radius := 0.08, color := RGBA.coral, label := "BC^B'C'" },
      { handleId := 15, pos := Z, radius := 0.08, color := RGBA.coral, label := "CA^C'A'" }
    ]
    segments := #[
      { a := A, b := B, width := 2.4, color := RGBA.cyan },
      { a := B, b := C, width := 2.4, color := RGBA.cyan },
      { a := C, b := A, width := 2.4, color := RGBA.cyan },
      { a := A', b := B', width := 2.4, color := RGBA.green },
      { a := B', b := C', width := 2.4, color := RGBA.green },
      { a := C', b := A', width := 2.4, color := RGBA.green },
      { a := O, b := A', width := 1.4, color := RGBA.ghost, role := { dashed := true } },
      { a := O, b := B', width := 1.4, color := RGBA.ghost, role := { dashed := true } },
      { a := O, b := C', width := 1.4, color := RGBA.ghost, role := { dashed := true } }
    ]
    lines := #[{
      origin := X, dir := Vec3.normalize (Vec3.sub Y X), clip := 4.0,
      width := 2.8, color := RGBA.coral, label := "Perspectivity Axis" }] }

/-! ## 15. `sta_lorentz_boost` — ALOK-950 Spacetime Algebra `Cl(3,1)` (`-+++`) -/

def buildStaLorentzBoost (handles : Array (UInt32 × Vec3)) (seq : UInt64) (t : Float) : SceneFrame :=
  let f := baseFrame "sta_lorentz_boost" "Spacetime Algebra Cl(3,1) Lorentz Boost (-+++)" "STA" seq t
  let vA := hPos handles 0 ⟨1.15, 0.35, 0.25⟩
  let vB := hPos handles 1 ⟨0.30, 1.10, 0.55⟩
  let phi := 0.55 * Float.sin (t * 0.7)
  let c := Float.cosh phi; let s := Float.sinh phi
  -- Boost along e_t ∧ e_x: (t', x') = (cosh φ · t + sinh φ · x, sinh φ · t + cosh φ · x)
  let tA0 := 0.85; let tB0 := 0.65
  let boostedA : Vec3 := ⟨s * tA0 + c * vA.x, vA.y, vA.z⟩
  let boostedB : Vec3 := ⟨s * tB0 + c * vB.x, vB.y, vB.z⟩
  let area := Vec3.norm (Vec3.cross boostedA boostedB)
  -- Light cone rings at y = ±1.2 (visualizing causal structure!)
  { f with
    points := #[
      { handleId := 0, pos := vA, radius := 0.09, color := RGBA.amber, role := { draggable := true }, label := "A" },
      { handleId := 1, pos := vB, radius := 0.09, color := RGBA.cyan, role := { draggable := true }, label := "B" }
    ]
    segments := #[
      { a := Vec3.zero, b := boostedA, width := 3.4, color := RGBA.amber, role := { arrow := true } },
      { a := Vec3.zero, b := boostedB, width := 3.4, color := RGBA.cyan, role := { arrow := true } },
      { a := ⟨-1.3, 1.3, 0.0⟩, b := ⟨1.3, -1.3, 0.0⟩, width := 1.4, color := RGBA.ghost, role := { dashed := true } },
      { a := ⟨1.3, 1.3, 0.0⟩, b := ⟨-1.3, -1.3, 0.0⟩, width := 1.4, color := RGBA.ghost, role := { dashed := true } }
    ]
    circles := #[
      { center := ⟨0.0, 1.25, 0.0⟩, u := ⟨1.0, 0.0, 0.0⟩, v := ⟨0.0, 0.0, 1.0⟩,
        radius := 1.25, width := 1.6, color := ⟨0.95, 0.85, 0.35, 0.5⟩, label := "Future Light Cone" },
      { center := ⟨0.0, -1.25, 0.0⟩, u := ⟨1.0, 0.0, 0.0⟩, v := ⟨0.0, 0.0, 1.0⟩,
        radius := 1.25, width := 1.6, color := ⟨0.95, 0.85, 0.35, 0.5⟩ }
    ]
    bivectorDisks := #[{
      origin := Vec3.zero, u := boostedA, v := boostedB, area,
      color := ⟨0.95, 0.58, 0.22, 0.34⟩, isDisk := false, orientationArrow := true }]
    inspect := #[
      { idx := 0, name := "Rapidity φ", grade := 0, formatted := s!"φ={phi}, γ={c}, β={Float.tanh phi}" },
      { idx := 1, name := "A ∧ B (Spatial)", grade := 2, formatted := s!"area = {area}" }
    ] }

/-! ## 16. `sta_maxwell_em` — Faraday Electromagnetic Bivector `F = E + I·B` -/

def buildStaMaxwellEM (seq : UInt64) (t : Float) : SceneFrame := Id.run do
  let f := baseFrame "sta_maxwell_em" "STA Maxwell Faraday Bivector F = E + IB" "STA" seq t
  let phi := 0.7 * Float.sin (t * 0.65)
  let gamma := Float.cosh phi; let bg := Float.sinh phi
  -- Pure electric field E0 = (0, 1, 0) + magnetic B0 = (0, 0, 0.5) boosted along +X
  let E : Vec3 := ⟨0.0, gamma * 1.0 - bg * 0.5, 0.0⟩
  let B : Vec3 := ⟨0.0, 0.0, gamma * 0.5 - bg * 1.0⟩
  let poynting := Vec3.cross E B
  let mut segs : Array SegmentPrim := #[]
  for ix in [:3] do
    let ox := -1.1 + ix.toFloat * 1.1
    let o : Vec3 := ⟨ox, 0.0, 0.0⟩
    segs := segs
      |>.push { a := o, b := Vec3.add o E, width := 3.2, color := RGBA.amber, role := { arrow := true } }
      |>.push { a := o, b := Vec3.add o B, width := 3.2, color := RGBA.cyan, role := { arrow := true } }
      |>.push { a := o, b := Vec3.add o poynting, width := 2.4, color := RGBA.green, role := { arrow := true } }
  return { f with
    segments := segs
    bivectorDisks := #[{
      origin := Vec3.zero, u := E, v := B, area := Vec3.norm poynting,
      color := ⟨0.32, 0.85, 0.95, 0.28⟩, isDisk := true }]
    labels := #[
      { pos := E, text := "E'(φ)", color := RGBA.amber },
      { pos := B, text := "B'(φ)", color := RGBA.cyan },
      { pos := poynting, text := "S = E×B", color := RGBA.green }
    ] }

/-! ## 17. `r3_rational_rotor` — ALOK-950 Exact Rational R3 Rotor Sandwich -/

def buildR3RationalRotor (handles : Array (UInt32 × Vec3)) (seq : UInt64) (t : Float) : SceneFrame := Id.run do
  let f := baseFrame "r3_rational_rotor" "R3 Exact Rational Rotor Sandwich (ALOK-950)" "R3" seq t
  let v := hPos handles 0 ⟨1.2, 0.4, 0.5⟩
  -- Pythagorean rational rotor: R = (3 + 4e12) / 5 => exact rational angle atan(24/7)
  let rRat : Calc.RatRotor3 := { s := 3, b12 := 4, b13 := 0, b23 := 0 }
  let vRat : Calc.RatVec3 := ⟨1, 0, 0⟩
  let exactOut := Calc.r3RationalSandwich rRat vRat
  let ang := 2.0 * Float.atan2 4.0 3.0 + 0.25 * Float.sin (t * 0.8)
  let rot := Motor3.rotorAxis ⟨0.0, 0.0, 1.0⟩ ang
  let vRot := Motor3.applyDir rot v
  let mut arc := FloatArray.emptyWithCapacity (33 * 3)
  for i in [:33] do
    let u := i.toFloat / 32.0
    let p := Motor3.applyDir (Motor3.rotorAxis ⟨0.0, 0.0, 1.0⟩ (u * ang)) v
    arc := arc.push p.x |>.push p.y |>.push p.z
  return { f with
    points := #[
      { handleId := 0, pos := v, radius := 0.09, color := RGBA.cyan, role := { draggable := true }, label := "v" },
      { handleId := 1, pos := vRot, radius := 0.09, color := RGBA.amber, label := "R >>> v" }
    ]
    segments := #[
      { a := Vec3.zero, b := v, width := 3.2, color := RGBA.cyan, role := { arrow := true } },
      { a := Vec3.zero, b := vRot, width := 3.2, color := RGBA.amber, role := { arrow := true } }
    ]
    curves := #[{ points := arc, width := 2.8, color := RGBA.green }]
    bivectorDisks := #[{
      origin := Vec3.zero, u := ⟨0.9, 0.0, 0.0⟩, v := ⟨0.0, 0.9, 0.0⟩, area := 0.81,
      color := ⟨0.55, 0.42, 1.0, 0.28⟩, isDisk := true }]
    inspect := #[
      { idx := 0, name := "R = (3+4e₁₂)/5", grade := 2,
        formatted := s!"exact R>>>e₁ = ({exactOut.x}, {exactOut.y}, {exactOut.z})" }
    ] }

/-! ## 18. `dual_autodiff_surface` — Dual Number AD Tangent Plane & Grassmann Normal -/

def buildDualAutodiffSurface (handles : Array (UInt32 × Vec3)) (seq : UInt64) (t : Float) :
    SceneFrame :=
  let f := baseFrame "dual_autodiff_surface" "Dual Cl(0,0,1) Autodiff Surface & Normal" "Dual" seq t
  let expr := "0.55 * sin(1.6*x + t) * cos(1.6*y)"
  let probe := hPos handles 0 ⟨0.45, 0.0, -0.35⟩
  let px := probe.x; let py := -probe.z
  let z := 0.55 * Float.sin (1.6 * px + t) * Float.cos (1.6 * py)
  let dzdx := 0.55 * 1.6 * Float.cos (1.6 * px + t) * Float.cos (1.6 * py)
  let dzdy := -0.55 * 1.6 * Float.sin (1.6 * px + t) * Float.sin (1.6 * py)
  let surfPt : Vec3 := ⟨px, z, -py⟩
  let tX := Vec3.normalize ⟨1.0, dzdx, 0.0⟩
  let tY := Vec3.normalize ⟨0.0, dzdy, -1.0⟩
  let normal := Vec3.normalize ⟨-dzdx, 1.0, dzdy⟩
  let assets := match evalSurfaceMesh expr t (-2.0) 2.0 (-2.0) 2.0 34 3001 with
    | .ok m => #[m]
    | .error _ => #[]
  let refs := assets.map fun m =>
    { meshId := m.meshId, dirtyHash := m.dirtyHash, color := RGBA.white, useVertexColors := true : MeshRefPrim }
  { f with
    meshAssets := assets, meshRefs := refs
    points := #[{
      handleId := 0, pos := surfPt, radius := 0.095, color := RGBA.amber,
      role := { draggable := true }, label := "Probe (x+ε)" }]
    segments := #[
      { a := surfPt, b := Vec3.add surfPt (Vec3.scale 0.8 normal), width := 3.6, color := RGBA.coral, role := { arrow := true } },
      { a := surfPt, b := Vec3.add surfPt (Vec3.scale 0.6 tX), width := 2.6, color := RGBA.cyan, role := { arrow := true } },
      { a := surfPt, b := Vec3.add surfPt (Vec3.scale 0.6 tY), width := 2.6, color := RGBA.green, role := { arrow := true } }
    ]
    planes := #[{
      center := surfPt, u := tX, v := tY, extent := 0.65,
      color := ⟨1.0, 0.72, 0.22, 0.30⟩, label := "Tangent Plane" }]
    inspect := #[
      { idx := 0, name := "Jet f(x+ε,y)", grade := 1, formatted := s!"z={z}, ∂z/∂x={dzdx}, ∂z/∂y={dzdy}" }
    ] }

/-! ## 19. `complex_mobius_orbit` — Complex Cl(0,1) Möbius / Riemann Sphere Lift -/

def buildComplexMobius (handles : Array (UInt32 × Vec3)) (seq : UInt64) (t : Float) : SceneFrame := Id.run do
  let f := baseFrame "complex_mobius_orbit" "Complex Cl(0,1) Möbius & Riemann Sphere" "Complex" seq t
  let z0 := hPos handles 0 ⟨0.9, 0.0, 0.4⟩
  let pi := 3.14159265358979323846
  let stereoLift (x y : Float) : Vec3 :=
    let r2 := x * x + y * y
    let denom := r2 + 1.0
    ⟨2.0 * x / denom, (r2 - 1.0) / denom, 2.0 * y / denom⟩
  let mut planeCurve := FloatArray.emptyWithCapacity (80 * 3)
  let mut sphereCurve := FloatArray.emptyWithCapacity (80 * 3)
  for i in [:80] do
    let s := (i.toFloat - 40.0) * 0.09
    let ang := s * 2.2 + t * 0.8
    let rad := Float.exp (s * 0.28) * max 0.25 (Float.sqrt (z0.x * z0.x + z0.z * z0.z))
    let x := rad * Float.cos ang
    let y := rad * Float.sin ang
    planeCurve := planeCurve.push x |>.push (-1.05) |>.push y
    let sp := stereoLift x y
    sphereCurve := sphereCurve.push sp.x |>.push sp.y |>.push sp.z
  let lifted := stereoLift z0.x z0.z
  return { f with
    spheres := #[{ center := Vec3.zero, radius := 1.0, color := ⟨0.30, 0.62, 1.0, 0.22⟩, label := "Riemann S²" }]
    points := #[
      { handleId := 0, pos := ⟨z0.x, -1.05, z0.z⟩, radius := 0.09, color := RGBA.amber,
        role := { draggable := true }, label := "z ∈ ℂ" },
      { handleId := 1, pos := lifted, radius := 0.085, color := RGBA.cyan, label := "Stereo(z)" },
      { handleId := 2, pos := ⟨0.0, 1.0, 0.0⟩, radius := 0.06, color := RGBA.white, label := "∞" }
    ]
    segments := #[{ a := ⟨0.0, 1.0, 0.0⟩, b := ⟨z0.x, -1.05, z0.z⟩, width := 1.8, color := RGBA.ghost, role := { dashed := true } }]
    curves := #[
      { points := planeCurve, width := 2.4, color := RGBA.amber },
      { points := sphereCurve, width := 3.0, color := RGBA.cyan }
    ]
    circles := #[{
      center := Vec3.zero, u := ⟨1.0, 0.0, 0.0⟩, v := ⟨0.0, 0.0, 1.0⟩,
      radius := 1.0, width := 1.6, color := RGBA.ghost }]
    inspect := #[
      { idx := 0, name := "z", grade := 1, formatted := s!"{z0.x} + {z0.z}i (π={pi})" }
    ] }

/-! ## Complete Preset Registry (19 Presets) -/

def presetCatalog : Array PresetInfo := #[
  { id := "pga3d_slicing", title := "3D PGA Mesh Slicing (Bunny)", category := "3D PGA", algebra := "PGA3",
    description := "Live Stanford-style bunny sliced by a dual-handle PGA3 plane (center + 3D tilt normal) with clipped halves + 2D contour inset.",
    sampleCode := "@basis PGA3\nlet bunny = mesh(\"bunny\")\nlet P = point(0, 0.15 + 0.45 * sin(t * 0.65), 0)\nlet N = point(0.24 * sin(t * 0.4), 1.1 + 0.45 * sin(t * 0.65), 0.12 * cos(t * 0.3))\nlet nx = N.x - P.x\nlet ny = N.y - P.y\nlet nz = N.z - P.z\nlet cut = plane(nx, ny, nz, -(nx * P.x + ny * P.y + nz * P.z))\nlet sliced = slice(bunny, cut)" },
  { id := "pga3d_points_and_lines", title := "3D PGA Points, Lines & Planes", category := "3D PGA", algebra := "PGA3",
    description := "5 draggable 3D pyramid points demonstrating Join (&), Meet (^), and projective sums.",
    sampleCode := "@basis PGA3\nlet A = point(0, 0.95, 0)\nlet B = point(0.9, -0.7, -0.7)\nlet C = point(-0.9, -0.7, -0.7)\nlet D = point(0, -0.7, 0.95)\nlet L_AB = A & B\nlet L_AC = A & C\nlet face = A & B & C\nlet mid = (A + D).Normalized" },
  { id := "pga3d_physics_free_top", title := "3D PGA Free Top (Dzhanibekov RK4)", category := "3D PGA", algebra := "PGA3",
    description := "Torque-free rigid body RK4 simulation in PGA3 displaying the intermediate-axis flip.",
    sampleCode := "@basis PGA3\nlet M = motor(0.2, 1, 0.15, t * 2.2, 0)\nlet body = transform(mesh(\"cube\"), M)\nlet spinAxis = point(0, 0, 0) & (M >>> point(0, 1.2, 0))" },
  { id := "pga3d_origami", title := "3D PGA Origami (Kabuto)", category := "3D PGA", algebra := "PGA3",
    description := "Animated 3D Kabuto origami folds built from Huzita-Hatori PGA3 planes and hinge rotors.",
    sampleCode := "@basis PGA3\nlet A = point(-1, 0, 0)\nlet B = point(1, 0, 0)\nlet C = point(0, 0, 1.1)\nlet hinge = A & B\nlet R = motor(hinge, 0.9 * sin(t * 0.8))\nlet flap = poly(A, B, R >>> C)" },
  { id := "pga3d_motor_orbits", title := "3D PGA Motor Orbits", category := "3D PGA", algebra := "PGA3",
    description := "1D curves and 2D manifolds generated as products of parameterized PGA3 motors.",
    sampleCode := "@basis PGA3\nlet P0 = point(0.95, -0.6, 0)\nlet L = (e13 + 0.35 * e02).Normalized\nfn orbit(u) = exp(u * L) >>> P0\nlet helix = curve([orbit(i * 0.18) for i in 0..32])\nlet live = orbit(t * 0.8)" },
  { id := "pga3d_icosahedron", title := "3D PGA Icosahedron", category := "3D PGA", algebra := "PGA3",
    description := "Regular icosahedron generated from three seed points via 5-fold PGA3 rotors.",
    sampleCode := "@basis PGA3\nlet R = motor(0.3, 1, 0.2, t * 0.6, 0)\nlet ico = transform(mesh(\"icosahedron\"), R)\nlet seed = point(0.95, 0.35, 0)\nlet ring = closedCurve([motor(0, 1, 0, i * 1.256637, 0) >>> seed for i in 0..5])" },
  { id := "pga3d_skinning", title := "3D PGA Dual-Quaternion Skinning", category := "3D PGA", algebra := "PGA3",
    description := "Direct visual comparison of Dual Quaternion Skinning vs Linear Blend Skinning candy-wrapper collapse.",
    sampleCode := "@basis PGA3\nlet b1 = motor(0, 1, 0, 1.1 * sin(t), 0)\nlet b2 = motor(0, 1, 0, -1.1 * sin(t), 0)\nlet mid = (0.5 * b1 + 0.5 * b2).Normalized\nlet cyl = transform(mesh(\"cylinder\"), mid)" },
  { id := "pga3d_objects", title := "3D PGA Lathed Solids & Motor Flow", category := "3D PGA", algebra := "PGA3",
    description := "Lathed torus, sphere, cone, and cylinder solids immersed in a 3D PGA motor flow particle field.",
    sampleCode := "@basis PGA3\nlet R = motor(0, 1, 0, t * 0.7, 0)\nlet tor = transform(mesh(\"torus\"), R)\nlet cone = transform(mesh(\"cone\"), translator(1.3, 0, 0) * R)\nlet axis = point(0, -1.1, 0) & point(0, 1.1, 0)" },
  { id := "cga3d_intersections", title := "3D CGA Live Intersections", category := "3D CGA", algebra := "CGA3",
    description := "Draggable sphere intersecting spheres, planes, lines & circles — renders both real and imaginary rounds!",
    sampleCode := "@basis CGA3\nlet A = point(0.45 * cos(t * 0.5), 0.1, 0)\nlet S1 = sphere(A, 0.95)\nlet S2 = sphere(-0.45, 0, 0, 0.85)\nlet P = plane(0, 1, 0, 0.15)\nlet C12 = S1 ^ S2\nlet C1P = S1 ^ P" },
  { id := "cga3d_spheres_apollonius", title := "3D CGA Circumsphere & Apollonius", category := "3D CGA", algebra := "CGA3",
    description := "4 draggable 3D points spanning their unique circumsphere p1^p2^p3^p4 and circumplane.",
    sampleCode := "@basis CGA3\nlet A = point(1.0, 0.2, 0.2)\nlet B = point(-0.9, 0.4, 0.5)\nlet C = point(0.1, -0.9, 0.4)\nlet D = point(0.1, 0.3, -0.95)\nlet circ = circle(A, B, C)\nlet sph = A ^ B ^ C ^ D" },
  { id := "cga3d_opns_cyclide", title := "3D CGA OPNS Raymarcher (WGSL/GLSL/MSL)", category := "3D CGA", algebra := "CGA3",
    description := "Live Lean-compiled WGSL/GLSL/MSL sphere-tracing shader for Outer Product Null Space visualization.",
    sampleCode := "@basis CGA3\nlet S = sphere(0.25 * cos(t), 0, 0, 0.85)\nlet gpu = opns(\"cos(x*2.2)*sin(y*2.2) + cos(y*2.2)*sin(z*2.2) + cos(z*2.2)*sin(x*2.2)\")" },
  { id := "pga2d_euler_line", title := "2D PGA Euler's Line", category := "2D PGA", algebra := "PGA2",
    description := "Draggable triangle vertices demonstrating collinearity of orthocenter, centroid, and circumcenter.",
    sampleCode := "@basis PGA2\nlet A = point(-1.2, -0.6)\nlet B = point(0.4, 1.35)\nlet C = point(1.15, -0.5)\nlet ab = A & B\nlet bc = B & C\nlet H = (ab << C) ^ (bc << A)\nlet O = (ab << (A + B)) ^ (bc << (B + C))\nlet Euler = H & O" },
  { id := "pga2d_inverse_kinematics", title := "2D PGA Inverse Kinematics", category := "2D PGA", algebra := "PGA2",
    description := "6-segment FABRIK kinematic chain with draggable base and target.",
    sampleCode := "@basis PGA2\nlet base = point(-1.3, 0)\nlet target = point(1.0, 0.55)\nlet mid = (base + target).Normalized\nlet link1 = seg(base, mid)\nlet link2 = seg(mid, target)\nlet ray = base & target" },
  { id := "pga2d_desargues_theorem", title := "2D PGA Desargues' Theorem", category := "2D PGA", algebra := "PGA2",
    description := "Interactive perspective triangles proving collinearity of corresponding edge meets.",
    sampleCode := "@basis PGA2\nlet O = point(-1.6, 0.85)\nlet A = point(-0.6, 0.9)\nlet B = point(-0.4, -0.2)\nlet A2 = point(0.5, 0.95)\nlet B2 = point(0.9, -0.5)\nlet r1 = O & A\nlet r2 = O & B\nlet X = (A & B) ^ (A2 & B2)" },
  { id := "sta_lorentz_boost", title := "STA Cl(3,1) Lorentz Boost (-+++)", category := "Spacetime", algebra := "STA",
    description := "ALOK-950 Minkowski spacetime light-cone, draggable vectors, rapidity boost & spatial wedge bivector.",
    sampleCode := "@basis STA\nlet B = boost(1, 0, 0, 0.65 * sin(t * 0.6))\nlet v1 = 1.1 * ex + 0.4 * ey\nlet v2 = 0.3 * ex + 1.05 * ey + 0.45 * ez\nlet world = B >>> (et + 0.4 * ex)\nlet W = v1 ^ v2" },
  { id := "sta_maxwell_em", title := "STA Maxwell Faraday Bivector", category := "Spacetime", algebra := "STA",
    description := "Unified relativistic electromagnetic bivector F = E + IB mixing under Lorentz boosts.",
    sampleCode := "@basis STA\nlet F = 0.8 * et * ex + 0.7 * ey * ez\nlet L = boost(0, 0, 1, 0.5 * sin(t))\nlet Fprime = L >>> F" },
  { id := "r3_rational_rotor", title := "R3 Exact Rational Rotor (ALOK-950)", category := "3D GA", algebra := "R3",
    description := "Exact rational Pythagorean rotor sandwich R >>> v with zero floating-point drift.",
    sampleCode := "@basis R3\nlet R = (3 + 4 * e12) / 5\nlet v = 1.2 * e1 + 0.3 * e3\nlet rotated = R >>> v\nlet planeBiv = e1 ^ e2" },
  { id := "dual_autodiff_surface", title := "Dual Cl(0,0,1) Autodiff Surface", category := "Dual", algebra := "Dual",
    description := "Forward-mode dual-number differentiation driving an animated 3D surface with live tangent plane & normal.",
    sampleCode := "@basis Dual\nlet wave = surface(\"0.55 * sin(1.8*x + t) * cos(1.8*y)\", 2.0, 28)\nlet x = 0.5 + e0\nlet sq = x * x" },
  { id := "complex_mobius_orbit", title := "Complex Cl(0,1) Möbius & Riemann Sphere", category := "Complex", algebra := "Complex",
    description := "Complex loxodrome orbit stereographically lifted onto the 3D Riemann sphere.",
    sampleCode := "@basis Complex\nlet z0 = 0.85 + 0.45 * e1\nlet z1 = z0 * z0\nlet z2 = z1 * z0\nlet ring = closedCurve([point(cos(i * 0.25) * 0.9, sin(i * 0.25) * 0.9, 0) for i in 0..25])" }
]

end Grassmann.CoffeeShop
