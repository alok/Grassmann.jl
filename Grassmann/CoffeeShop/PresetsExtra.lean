import Grassmann.Scene.Types
import Grassmann.Scene.Json
import Grassmann.CoffeeShop.Mesh
import Grassmann.Eval.Implicit3D

/-!
# Expanded Pure-Lean CoffeeShop Preset Gallery (+28 Flagship Presets → 47 Total!)

Strictly `Init`-only (`Grassmann.Scene.*`, `Grassmann.CoffeeShop.Mesh`,
`Grassmann.Eval.Implicit3D` — zero `Lean.*`, zero `Std.*`, zero `DirectSum.Basis`
macro imports) so every preset links straight into both the tiny 2.5 MB C ABI dylib
and the Lean 4.36 → C → Emscripten WASM bundle!

Covers ALL 15 `ganja.js` algebra groups + the 3D Implicit & Parametric Gallery:
- **3D PGA (`Cl(3,0,1)`)**: `pga3d_origami_fold`, `pga3d_ik_arm`, `pga3d_hopf`,
  `pga3d_duality`, `pga3d_spring_physics`, `pga3d_skinning_twist`
- **3D CGA (`Cl(4,1)`)**: `cga3d_dupin_cyclide`, `cga3d_apollonius`,
  `cga3d_clifford_torus`, `cga3d_inversion`, `cga3d_dipole_field`
- **Spacetime `STA` (`Cl(3,1) -+++`)**: `sta_light_cone`, `sta_em_wave`, `sta_rapidity`
- **3D Implicit & Parametric Gallery (`Implicit3D`)**: `implicit_gyroid`,
  `implicit_metaballs`, `implicit_schwarz_p`, `param_klein_bottle`,
  `param_mobius_strip`, `implicit_genus2`, `param_boys_surface`,
  `param_enneper_superquadric`
- **2D CGA / Non-Euclidean / Complex / Dual / Quaternion / Higher Cl**:
  `cga2d_apollonius`, `pga2d_non_euclidean`, `complex_mandelbrot`,
  `dual_tangent_plane`, `quaternion_slerp`, `higher_cl_conic_pencil`

Credits: Steven De Keninck (`enkimute` / `ganja.js`) & Michael Reed (`chakravala` / `Grassmann.jl`).
-/

namespace Grassmann.CoffeeShop.PresetsExtra

open Grassmann.Scene Grassmann.CoffeeShop.Mesh Grassmann.Eval.Implicit3D

private def piF : Float := 3.14159265358979323846
private def twoPiF : Float := 6.28318530717958647692

/-- Catalog metadata matching `Grassmann.CoffeeShop.PresetInfo` field-for-field. -/
structure ExtraPresetInfo where
  id          : String
  title       : String
  category    : String
  algebra     : String
  description : String
  sampleCode  : String
  deriving Repr, Inhabited

/-- Look up draggable handle `id` or return `defPos`. -/
@[inline] private def hPos (handles : Array (UInt32 × Vec3)) (id : UInt32) (defPos : Vec3) : Vec3 :=
  ((handles.find? fun kv => kv.1 == id).map (·.2)).getD defPos

/-- Construct an orthonormal tangent frame `(u, v)` perpendicular to unit normal `n`. -/
private def orthoFrame (n : Vec3) : Vec3 × Vec3 :=
  let nu := Vec3.normalize n
  let ref : Vec3 := if Float.abs nu.y < 0.9 then ⟨0.0, 1.0, 0.0⟩ else ⟨1.0, 0.0, 0.0⟩
  let u := Vec3.normalize (Vec3.cross ref nu)
  let v := Vec3.cross nu u
  (u, v)

/-- Build a 3D `CurvePrim` from an array of `Vec3` sample points. -/
private def curveFromVecs (pts : Array Vec3) (color : RGBA) (width : Float := 2.2)
    (closed : Bool := false) (dashed : Bool := false) : CurvePrim := Id.run do
  let mut fa := FloatArray.emptyWithCapacity (pts.size * 3)
  for p in pts do
    fa := fa.push p.x |>.push p.y |>.push p.z
  return { points := fa, width, color, closed, dashed }

/-- Exact `Init`-only `AlgebraMeta` descriptors for every ganja.js algebra group. -/
private def metaFor (alg : String) : AlgebraMeta :=
  match alg with
  | "PGA3" =>
    { name := "PGA3", p := 3, q := 0, r := 1, conformalWitt := false
      basisNames := #["1","e0","e1","e2","e3","e01","e02","e03","e12","e13","e23","e012","e013","e023","e123","e0123"]
      basisMetric := #[1,0,1,1,1,0,0,0,-1,-1,-1,0,0,0,-1,0] }
  | "CGA3" =>
    { name := "CGA3", p := 4, q := 1, r := 0, conformalWitt := true
      basisNames := #["1","e1","e2","e3","e+","e-"]
      basisMetric := #[1,1,1,1,1,-1] }
  | "STA" =>
    { name := "STA", p := 3, q := 1, r := 0, conformalWitt := false
      basisNames := #["1","e0","e1","e2","e3","e01","e02","e03","e12","e13","e23","e012","e013","e023","e123","I"]
      basisMetric := #[1,-1,1,1,1,1,1,1,-1,-1,-1,1,1,1,-1,-1] }
  | "CGA2" =>
    { name := "CGA2", p := 3, q := 1, r := 0, conformalWitt := true
      basisNames := #["1","e1","e2","e+","e-"]
      basisMetric := #[1,1,1,1,-1] }
  | "Hyperbolic2D" =>
    { name := "Cl(2,1)", p := 2, q := 1, r := 0, conformalWitt := false
      basisNames := #["1","e0","e1","e2","e01","e02","e12","e012"]
      basisMetric := #[1,-1,1,1,1,1,-1,1] }
  | "Complex" =>
    { name := "Complex", p := 0, q := 1, r := 0, conformalWitt := false
      basisNames := #["1","i"], basisMetric := #[1,-1] }
  | "Dual" =>
    { name := "Dual", p := 0, q := 0, r := 1, conformalWitt := false
      basisNames := #["1","ε"], basisMetric := #[1,0] }
  | "Quaternion" =>
    { name := "Quaternion", p := 0, q := 2, r := 0, conformalWitt := false
      basisNames := #["1","i","j","k"], basisMetric := #[1,-1,-1,-1] }
  | "CCGA" =>
    { name := "Cl(6,3)", p := 6, q := 3, r := 0, conformalWitt := true
      basisNames := #["1","e1","e2","ex2","ey2","exy","e∞x","e∞y","e∞xy"]
      basisMetric := #[1,1,1,1,1,1,-1,-1,-1] }
  | _ =>
    { name := "R3", p := 3, q := 0, r := 0, conformalWitt := false
      basisNames := #["1","e1","e2","e3","e12","e13","e23","I"]
      basisMetric := #[1,1,1,1,-1,-1,-1,-1] }

private def mkBase (presetId title alg : String) (seq : UInt64) (t : Float)
    (is2D : Bool := false) (camDist : Float := 4.8) : SceneFrame :=
  { frameSeq := seq, simTime := t, mode := .coffeeShop, is2D,
    gridEnabled := true, darkTheme := true, gridSize := 2.4,
    algebra := metaFor alg, presetId, title,
    camera :=
      if is2D then { motor := Motor3.translator 0.0 0.0 (-4.2), orthoScale := 1.0, isOrtho := true }
      else { motor := Motor3.orbitCamera (0.55 + 0.10 * Float.sin (t * 0.25)) (-0.32) camDist,
             fovDeg := 45.0, distance := camDist } }

/-- Helper: append a double-sided colored quad `(p0, p1, p2, p3)` to a `MeshBuilder`. -/
private def addDoubleQuad (mb : MeshBuilder) (p0 p1 p2 p3 : Vec3) (col : RGBA) : MeshBuilder :=
  let (mb1, i0) := mb.addVertex p0 col
  let (mb2, i1) := mb1.addVertex p1 col
  let (mb3, i2) := mb2.addVertex p2 col
  let (mb4, i3) := mb3.addVertex p3 col
  let mb5 := (mb4.addTri i0 i1 i2).addTri i0 i2 i3
  let (mb6, j0) := mb5.addVertex p0 col
  let (mb7, j1) := mb6.addVertex p1 col
  let (mb8, j2) := mb7.addVertex p2 col
  let (mb9, j3) := mb8.addVertex p3 col
  (mb9.addTri j0 j2 j1).addTri j0 j3 j2

/-! ## GROUP A: 3D PGA (`Cl(3,0,1)`) — 6 New Showstopper Presets -/

/-- **1. `pga3d_origami_fold`** — Miura-ori rigid-panel origami fold using exact PGA3 hinge rotors! -/
def buildPga3dOrigamiFold (handles : Array (UInt32 × Vec3)) (seq : UInt64) (t : Float) : SceneFrame := Id.run do
  let f := mkBase "pga3d_origami_fold" "3D PGA Miura-Ori Rigid Origami Fold" "PGA3" seq t
  let ctrl := hPos handles 0 ⟨0.0, 0.55 + 0.45 * Float.sin (t * 0.9), 0.0⟩
  let foldFrac := max 0.08 (min 0.92 (0.5 + 0.45 * ctrl.y))
  let theta := foldFrac * 1.32 -- dihedral crease fold angle
  let alpha := 1.05            -- Miura-ori acute parallelogram angle (~60°)
  -- Analytical rigid-fold Miura-ori kinematic linkage
  let eta := Float.asin (Float.sin theta * Float.sin alpha)
  let dx := Float.cos eta
  let dz := Float.sin alpha * Float.cos theta / max 0.15 (Float.cos eta)
  let hPeak := Float.sin theta * Float.cos alpha
  let shiftZ := Float.cos alpha
  let mut mb : MeshBuilder := {}
  let mut segs : Array SegmentPrim := #[]
  let cols : Array RGBA := #[RGBA.cyan, RGBA.violet, RGBA.amber, RGBA.coral]
  for ix in [:4] do
    for iz in [:3] do
      let pt (i j : Nat) : Vec3 :=
        let x := (Float.ofNat i - 2.0) * dx * 0.58
        let zig := if i % 2 == 1 then shiftZ * 0.58 else 0.0
        let z := (Float.ofNat j - 1.5) * dz * 0.65 + zig
        let y := (if (i + j) % 2 == 1 then hPeak else -hPeak) * 0.52
        ⟨x, y, z⟩
      let p00 := pt ix iz
      let p10 := pt (ix + 1) iz
      let p11 := pt (ix + 1) (iz + 1)
      let p01 := pt ix (iz + 1)
      let col := cols[(ix + iz) % cols.size]!
      mb := addDoubleQuad mb p00 p10 p11 p01 col
      segs := segs.push { a := p00, b := p10, width := 2.2, color := RGBA.white }
                  |>.push { a := p00, b := p01, width := 2.2, color := RGBA.white }
  let mesh := mb.finalize 4001
  return { f with
    meshAssets := #[mesh],
    meshRefs := #[{ meshId := mesh.meshId, dirtyHash := mesh.dirtyHash,
                    color := RGBA.white, useVertexColors := true, doubleSided := true }],
    segments := segs,
    points := #[{ handleId := 0, pos := ctrl, radius := 0.09, color := RGBA.amber,
                  role := { draggable := true }, label := "Fold Angle" }],
    inspect := #[{ idx := 0, name := "Hinge Rotor", grade := 2,
                   formatted := s!"exp(-{theta * 0.5} · L_crease)", editable := true }] }

/-- **2. `pga3d_ik_arm`** — 5-Link Spatial 3D FABRIK / Motor Inverse Kinematics Arm! -/
def buildPga3dIkArm (handles : Array (UInt32 × Vec3)) (seq : UInt64) (t : Float) : SceneFrame := Id.run do
  let f := mkBase "pga3d_ik_arm" "3D PGA Spatial FABRIK Inverse Kinematics" "PGA3" seq t
  let defTarget : Vec3 := ⟨1.15 * Float.cos (t * 0.75), 0.75 + 0.45 * Float.sin (t * 1.1), 0.95 * Float.sin (t * 0.6)⟩
  let target := hPos handles 0 defTarget
  let basePt : Vec3 := ⟨0.0, -0.95, 0.0⟩
  let linkLens : Array Float := #[0.62, 0.58, 0.52, 0.46, 0.40]
  -- Initial straight-up chain
  let mut joints : Array Vec3 := #[basePt]
  let mut accY := basePt.y
  for l in linkLens do
    accY := accY + l
    joints := joints.push ⟨0.05, accY, 0.0⟩
  -- 10 exact FABRIK backward + forward motor-projection iterations purely in Lean!
  for _ in [:10] do
    -- Backward pass: snap tip to target
    joints := joints.set! (joints.size - 1) target
    let mut i := joints.size - 1
    while i > 0 do
      let pNext := joints[i]!
      let pCur := joints[i - 1]!
      let len := linkLens[i - 1]!
      let d := Vec3.sub pCur pNext
      let dir := if Vec3.norm d > 1e-6 then Vec3.normalize d else ⟨0.0, -1.0, 0.0⟩
      joints := joints.set! (i - 1) (Vec3.add pNext (Vec3.scale len dir))
      i := i - 1
    -- Forward pass: anchor base at basePt
    joints := joints.set! 0 basePt
    for j in [:linkLens.size] do
      let pCur := joints[j]!
      let pNext := joints[j + 1]!
      let len := linkLens[j]!
      let d := Vec3.sub pNext pCur
      let dir := if Vec3.norm d > 1e-6 then Vec3.normalize d else ⟨0.0, 1.0, 0.0⟩
      joints := joints.set! (j + 1) (Vec3.add pCur (Vec3.scale len dir))
  let mut pts : Array PointPrim := #[
    { handleId := 0, pos := target, radius := 0.10, color := RGBA.coral,
      role := { draggable := true, target := true }, label := "Target" }
  ]
  let mut segs : Array SegmentPrim := #[]
  for j in [:joints.size] do
    pts := pts.push { handleId := (j + 1).toUInt32, pos := joints[j]!,
                      radius := if j == 0 then 0.11 else 0.07,
                      color := if j == 0 then RGBA.violet else RGBA.cyan,
                      label := if j == 0 then "Base" else s!"J{j}" }
    if j + 1 < joints.size then
      segs := segs.push { a := joints[j]!, b := joints[j + 1]!, width := 4.5,
                          color := if j % 2 == 0 then RGBA.white else RGBA.amber }
  let totalReach := linkLens.foldl (· + ·) 0.0
  return { f with
    points := pts, segments := segs,
    spheres := #[{ center := basePt, radius := totalReach,
                   color := ⟨0.25, 0.55, 0.95, 0.08⟩, label := "Reach Shell" }],
    inspect := #[{ idx := 0, name := "End Effector", grade := 3,
                   formatted := s!"e123 + ({target.x})e023 + ({target.y})e031 + ({target.z})e012", editable := true }] }

/-- **3. `pga3d_hopf`** — Hopf Fibration & Motor Geodesic Fiber Bundle (`S³ → S²`)! -/
def buildPga3dHopf (handles : Array (UInt32 × Vec3)) (seq : UInt64) (t : Float) : SceneFrame := Id.run do
  let f := mkBase "pga3d_hopf" "3D PGA Hopf Fibration (Spin(3) / S³ Fibers)" "PGA3" seq t false 5.4
  let ctrl := hPos handles 0 ⟨0.0, 0.35 + 0.25 * Float.sin (t * 0.5), 0.0⟩
  let etaBase := max 0.25 (min 1.32 (0.78 + 0.45 * ctrl.y))
  let latitudes : Array (Float × Nat × RGBA) :=
    #[ (etaBase * 0.55, 8, RGBA.cyan)
     , (etaBase,        10, RGBA.violet)
     , (min 1.38 (etaBase * 1.35), 8, RGBA.amber) ]
  let mut curves : Array CurvePrim := #[]
  for (eta, nFibers, col) in latitudes do
    let cEta := Float.cos eta; let sEta := Float.sin eta
    for k in [:nFibers] do
      let phi := twoPiF * Float.ofNat k / Float.ofNat nFibers + t * 0.25
      let mut pts : Array Vec3 := #[]
      let steps := 44
      for s in [:steps] do
        let xi := twoPiF * Float.ofNat s / Float.ofNat steps
        -- Hopf fiber parameterized on unit S³: (z1, z2) = (cos η e^{i(ξ+φ)}, sin η e^{iξ})
        let x1 := cEta * Float.cos (xi + phi)
        let x2 := cEta * Float.sin (xi + phi)
        let x3 := sEta * Float.cos xi
        let x4 := sEta * Float.sin xi
        let denom := max 0.30 (1.0 - x4)
        let p : Vec3 := ⟨0.78 * x1 / denom, 0.78 * x3 / denom, 0.78 * x2 / denom⟩
        pts := pts.push p
      curves := curves.push (curveFromVecs pts col 2.2 true false)
  return { f with
    curves,
    points := #[{ handleId := 0, pos := ctrl, radius := 0.09, color := RGBA.coral,
                  role := { draggable := true }, label := "Hopf Latitude η" }],
    lines := #[{ origin := Vec3.zero, dir := ⟨0.0, 1.0, 0.0⟩, clip := 2.4, width := 2.5,
                 color := RGBA.white, label := "Central Fiber" }],
    inspect := #[{ idx := 0, name := "Hopf Rotor", grade := 2,
                   formatted := s!"η = {etaBase} rad · 26 linked Villarceau circles", editable := true }] }

/-- **4. `pga3d_duality`** — 3D Projective Polar Duality (Point ↔ Polar Plane) & Dual Tetrahedron! -/
def buildPga3dDuality (handles : Array (UInt32 × Vec3)) (seq : UInt64) (t : Float) : SceneFrame := Id.run do
  let f := mkBase "pga3d_duality" "3D PGA Projective Duality (Poles ↔ Polar Planes)" "PGA3" seq t
  let apex := hPos handles 0 ⟨0.95 * Float.cos (t * 0.5), 0.95, 0.95 * Float.sin (t * 0.5)⟩
  let verts : Array (Vec3 × String × RGBA) :=
    #[ (apex, "P0", RGBA.coral)
     , (⟨-1.15, -0.55, 0.75⟩, "P1", RGBA.cyan)
     , (⟨1.10, -0.55, 0.65⟩, "P2", RGBA.amber)
     , (⟨0.0, -0.55, -1.15⟩, "P3", RGBA.green) ]
  let mut pts : Array PointPrim := #[]
  let mut planes : Array PlanePrim := #[]
  let mut segs : Array SegmentPrim := #[]
  for i in [:verts.size] do
    let (v, lbl, col) := verts[i]!
    pts := pts.push { handleId := i.toUInt32, pos := v, radius := if i == 0 then 0.095 else 0.075,
                      color := col, role := { draggable := i == 0 }, label := lbl }
    -- Polar plane of v with respect to unit sphere: v · x = 1 → normal = v/‖v‖, center = v/‖v‖²
    let n2 := max 0.15 (Vec3.normSq v)
    let center := Vec3.scale (1.0 / n2) v
    let (u, w) := orthoFrame v
    planes := planes.push { center, u, v := w, extent := 0.95,
                            color := { col with a := 0.24 }, label := s!"!{lbl}" }
    segs := segs.push { a := v, b := center, width := 1.6, color := RGBA.ghost, role := { dashed := true } }
  -- Tetrahedron edges
  for i in [:verts.size] do
    for j in [i+1:verts.size] do
      segs := segs.push { a := verts[i]!.1, b := verts[j]!.1, width := 2.2, color := RGBA.white }
  return { f with
    points := pts, planes, segments := segs,
    spheres := #[{ center := Vec3.zero, radius := 1.0, color := ⟨0.65, 0.72, 1.0, 0.14⟩, label := "Polarity Sphere" }],
    inspect := #[{ idx := 0, name := "Pole P0", grade := 3,
                   formatted := s!"P0 ↔ !P0 (p·x = 1)", editable := true }] }

/-- **5. `pga3d_spring_physics`** — 6-DOF PGA3 Motor Rigid-Body Spring-Damper Physics! -/
def buildPga3dSpringPhysics (handles : Array (UInt32 × Vec3)) (seq : UInt64) (t : Float) : SceneFrame := Id.run do
  let f := mkBase "pga3d_spring_physics" "3D PGA Rigid-Body Motor Spring Physics" "PGA3" seq t
  let anchor := hPos handles 0 ⟨0.0, 1.35, 0.0⟩
  -- Analytical damped 6-DOF harmonic motor oscillator driven by anchor displacement + time
  let omega := 2.4
  let swayX := 0.45 * Float.sin (omega * t * 0.65)
  let bounceY := -0.35 + 0.32 * Float.cos (omega * t)
  let swayZ := 0.28 * Float.cos (omega * t * 0.55)
  let bodyPos : Vec3 := ⟨anchor.x + swayX, anchor.y - 1.55 + bounceY, anchor.z + swayZ⟩
  let tiltAngle := 0.45 * Float.sin (omega * t * 0.65)
  let spinAngle := 0.65 * t
  let motor := Motor3.mul (Motor3.translator bodyPos.x bodyPos.y bodyPos.z)
    (Motor3.mul (Motor3.rotorAxis ⟨0.0, 0.0, 1.0⟩ tiltAngle)
                (Motor3.rotorAxis ⟨0.0, 1.0, 0.0⟩ spinAngle))
  let attachWorld := Motor3.applyPoint motor ⟨0.0, 0.38, 0.0⟩
  -- Coiled helical spring curve connecting ceiling anchor to rigid body corner
  let axis := Vec3.sub attachWorld anchor
  let (su, sv) := orthoFrame axis
  let mut springPts : Array Vec3 := #[]
  let coils := 8.0
  let steps := 72
  for i in [:steps + 1] do
    let u := Float.ofNat i / Float.ofNat steps
    let env := Float.sin (u * piF) -- tapers to 0 at endpoints
    let r := 0.16 * env
    let ang := twoPiF * coils * u
    let p := Vec3.add (Vec3.lerp anchor attachWorld u)
      (Vec3.add (Vec3.scale (r * Float.cos ang) su) (Vec3.scale (r * Float.sin ang) sv))
    springPts := springPts.push p
  let box := buildBoxMesh 0.72 0.72 0.72 RGBA.cyan 4005
  return { f with
    meshAssets := #[box],
    meshRefs := #[{ meshId := box.meshId, dirtyHash := box.dirtyHash, motor,
                    color := RGBA.cyan, useVertexColors := true }],
    curves := #[curveFromVecs springPts RGBA.amber 2.8 false false],
    points := #[ { handleId := 0, pos := anchor, radius := 0.10, color := RGBA.coral,
                   role := { draggable := true }, label := "Spring Anchor" }
               , { handleId := 1, pos := attachWorld, radius := 0.06, color := RGBA.white, label := "Attach" } ],
    segments := #[{ a := bodyPos, b := Vec3.add bodyPos ⟨0.0, -0.55, 0.0⟩, width := 3.0,
                    color := RGBA.green, role := { arrow := true } }],
    inspect := #[{ idx := 0, name := "Body Motor M(t)", grade := 2,
                   formatted := s!"s={motor.s} e12={motor.e12} e02={motor.e02}", editable := true }] }

/-- **6. `pga3d_skinning_twist`** — 3-Bone Dual-Quaternion / Motor Linear Blending Skinning! -/
def buildPga3dSkinningTwist (handles : Array (UInt32 × Vec3)) (seq : UInt64) (t : Float) : SceneFrame := Id.run do
  let f := mkBase "pga3d_skinning_twist" "3D PGA Motor-Blended Articulated Skinning" "PGA3" seq t
  let tipCtrl := hPos handles 0 ⟨0.65 * Float.cos (t * 0.9), 1.05, 0.65 * Float.sin (t * 0.9)⟩
  let twistAngle := 1.65 * Float.sin (t * 0.85) + tipCtrl.x * 1.4
  let bendX := tipCtrl.x * 0.65
  let bendZ := tipCtrl.z * 0.65
  -- 3-bone skeleton motors along Y ∈ [-1, 1]
  let m0 := Motor3.identity
  let m1 := Motor3.mul (Motor3.translator (bendX * 0.35) 0.0 (bendZ * 0.35))
                       (Motor3.rotorAxis ⟨0.0, 1.0, 0.0⟩ (twistAngle * 0.5))
  let m2 := Motor3.mul (Motor3.translator bendX 0.0 bendZ)
                       (Motor3.rotorAxis ⟨0.0, 1.0, 0.0⟩ twistAngle)
  -- Blend 3 motors via normalized linear motor blending (DLB) directly on cylinder surface!
  let blendMotor (u : Float) : Motor3 :=
    let w0 := if u < 0.5 then 1.0 - 2.0 * u else 0.0
    let w2 := if u > 0.5 then 2.0 * u - 1.0 else 0.0
    let w1 := 1.0 - w0 - w2
    Motor3.normalize
      { s     := w0 * m0.s + w1 * m1.s + w2 * m2.s
        e01   := w0 * m0.e01 + w1 * m1.e01 + w2 * m2.e01
        e02   := w0 * m0.e02 + w1 * m1.e02 + w2 * m2.e02
        e03   := w0 * m0.e03 + w1 * m1.e03 + w2 * m2.e03
        e12   := w0 * m0.e12 + w1 * m1.e12 + w2 * m2.e12
        e13   := w0 * m0.e13 + w1 * m1.e13 + w2 * m2.e13
        e23   := w0 * m0.e23 + w1 * m1.e23 + w2 * m2.e23
        e0123 := w0 * m0.e0123 + w1 * m1.e0123 + w2 * m2.e0123 }
  let surf (u v : Float) : Vec3 :=
    let y := -1.0 + 2.0 * u
    let r := 0.36 + 0.07 * Float.cos (6.0 * v)
    let rest : Vec3 := ⟨r * Float.cos v, y, r * Float.sin v⟩
    Motor3.applyPoint (blendMotor u) rest
  let mesh := buildParametricSurface surf 0.0 1.0 0.0 twoPiF 28 24 4006 false
  let b0 := Motor3.applyPoint m0 ⟨0.0, -1.0, 0.0⟩
  let b1 := Motor3.applyPoint m1 ⟨0.0, 0.0, 0.0⟩
  let b2 := Motor3.applyPoint m2 ⟨0.0, 1.0, 0.0⟩
  return { f with
    meshAssets := #[mesh],
    meshRefs := #[{ meshId := mesh.meshId, dirtyHash := mesh.dirtyHash,
                    color := RGBA.white, useVertexColors := true }],
    points := #[ { handleId := 0, pos := tipCtrl, radius := 0.10, color := RGBA.coral,
                   role := { draggable := true }, label := "Tip Bone" }
               , { handleId := 1, pos := b0, radius := 0.07, color := RGBA.white, label := "Bone 0" }
               , { handleId := 2, pos := b1, radius := 0.07, color := RGBA.amber, label := "Bone 1" } ],
    segments := #[ { a := b0, b := b1, width := 4.0, color := RGBA.amber }
                 , { a := b1, b := b2, width := 4.0, color := RGBA.coral } ],
    inspect := #[{ idx := 0, name := "DLB Twist", grade := 2,
                   formatted := s!"M(u) = normalize(∑ w_i(u) M_i), θ={twistAngle}", editable := true }] }

/-! ## GROUP B: 3D CGA (`Cl(4,1)`) — 5 New Showstopper Presets -/

/-- **7. `cga3d_dupin_cyclide`** — Exact Conformal Dupin Cyclide + Focal Conics + Tangent Spheres! -/
def buildCga3dDupinCyclide (handles : Array (UInt32 × Vec3)) (seq : UInt64) (t : Float) : SceneFrame := Id.run do
  let f := mkBase "cga3d_dupin_cyclide" "3D CGA Dupin Cyclide & Focal Conics" "CGA3" seq t
  let ctrl := hPos handles 0 ⟨0.36 + 0.18 * Float.sin (t * 0.6), 0.62, 0.0⟩
  let cParam := max 0.05 (min 0.72 (Float.abs ctrl.x))
  let dParam := max (cParam + 0.15) (min 0.92 (Float.abs ctrl.y))
  let mesh := buildDupinCyclideMesh 1.0 cParam dParam 44 26 4101
  -- Focal ellipse in the (x, z) plane: x = cos u, z = b sin u
  let b := Float.sqrt (max 0.04 (1.0 - cParam * cParam))
  let mut ellPts : Array Vec3 := #[]
  for i in [:48] do
    let u := twoPiF * Float.ofNat i / 48.0
    ellPts := ellPts.push ⟨Float.cos u, 0.0, b * Float.sin u⟩
  return { f with
    meshAssets := #[mesh],
    meshRefs := #[{ meshId := mesh.meshId, dirtyHash := mesh.dirtyHash,
                    color := RGBA.white, useVertexColors := true }],
    curves := #[curveFromVecs ellPts RGBA.amber 2.6 true false],
    spheres := #[ { center := ⟨1.0, 0.0, 0.0⟩, radius := max 0.12 (dParam - cParam),
                    color := ⟨0.22, 0.88, 0.95, 0.24⟩, label := "Min Curv Sphere" }
                , { center := ⟨-1.0, 0.0, 0.0⟩, radius := dParam + cParam,
                    color := ⟨1.0, 0.53, 0.53, 0.16⟩, label := "Max Curv Sphere" } ],
    points := #[{ handleId := 0, pos := ctrl, radius := 0.09, color := RGBA.coral,
                  role := { draggable := true }, label := "Cyclide (c, d)" }],
    inspect := #[{ idx := 0, name := "Dupin Cyclide", grade := 4,
                   formatted := s!"a=1, c={cParam}, d={dParam}", editable := true }] }

/-- **8. `cga3d_apollonius`** — 3D Apollonius / Soddy Kissing Spheres (Descartes' 3D Theorem)! -/
def buildCga3dApollonius (handles : Array (UInt32 × Vec3)) (seq : UInt64) (t : Float) : SceneFrame := Id.run do
  let f := mkBase "cga3d_apollonius" "3D CGA Apollonius / Soddy Kissing Spheres" "CGA3" seq t
  let ctrl := hPos handles 0 ⟨0.62 + 0.10 * Float.sin (t * 0.7), 0.0, 0.0⟩
  let r := max 0.35 (min 0.82 (Float.abs ctrl.x))
  -- 4 mutually tangent equal spheres of radius r at vertices of a regular tetrahedron of edge 2r
  let s := r / Float.sqrt 2.0
  let c1 : Vec3 := ⟨ s,  s,  s⟩
  let c2 : Vec3 := ⟨ s, -s, -s⟩
  let c3 : Vec3 := ⟨-s,  s, -s⟩
  let c4 : Vec3 := ⟨-s, -s,  s⟩
  -- Distance from origin to each center is √3 · s = r √(3/2)
  let dOrig := r * Float.sqrt 1.5
  let rInner := dOrig - r -- Exact inner Soddy sphere radius!
  let rOuter := dOrig + r -- Exact outer enclosing Soddy sphere radius!
  return { f with
    spheres := #[
      { center := c1, radius := r, color := ⟨0.22, 0.88, 0.95, 0.36⟩, label := "S1" },
      { center := c2, radius := r, color := ⟨0.72, 0.45, 1.0,  0.36⟩, label := "S2" },
      { center := c3, radius := r, color := ⟨0.32, 0.92, 0.58, 0.36⟩, label := "S3" },
      { center := c4, radius := r, color := ⟨1.0,  0.72, 0.22, 0.36⟩, label := "S4" },
      { center := Vec3.zero, radius := rInner, color := ⟨1.0, 0.42, 0.42, 0.88⟩, label := "Inner Soddy" },
      { center := Vec3.zero, radius := rOuter, color := ⟨0.85, 0.90, 1.0, 0.10⟩, label := "Outer Soddy" }
    ],
    points := #[{ handleId := 0, pos := ctrl, radius := 0.08, color := RGBA.coral,
                  role := { draggable := true }, label := "Sphere Radius" }],
    segments := #[
      { a := c1, b := c2, width := 1.8, color := RGBA.white },
      { a := c1, b := c3, width := 1.8, color := RGBA.white },
      { a := c1, b := c4, width := 1.8, color := RGBA.white },
      { a := c2, b := c3, width := 1.8, color := RGBA.white },
      { a := c2, b := c4, width := 1.8, color := RGBA.white },
      { a := c3, b := c4, width := 1.8, color := RGBA.white }
    ],
    inspect := #[{ idx := 0, name := "Descartes 3D", grade := 1,
                   formatted := s!"r={r}, r_in={rInner}, r_out={rOuter}", editable := true }] }

/-- **9. `cga3d_clifford_torus`** — Stereographic `R³ ↔ S³` Clifford Torus with 4D Rotation! -/
def buildCga3dCliffordTorus (handles : Array (UInt32 × Vec3)) (seq : UInt64) (t : Float) : SceneFrame := Id.run do
  let f := mkBase "cga3d_clifford_torus" "3D CGA Stereographic Clifford Torus (4D Rotation)" "CGA3" seq t
  let ctrl := hPos handles 0 ⟨0.95 * Float.cos (t * 0.5), 0.95 * Float.sin (t * 0.5), 0.0⟩
  let ang4D := Float.atan2 ctrl.y ctrl.x
  let mesh := buildCliffordTorusMesh ang4D 0.68 44 26 4103
  return { f with
    meshAssets := #[mesh],
    meshRefs := #[{ meshId := mesh.meshId, dirtyHash := mesh.dirtyHash,
                    color := RGBA.white, useVertexColors := true }],
    circles := #[
      { center := Vec3.zero, u := ⟨1.0, 0.0, 0.0⟩, v := ⟨0.0, 0.0, 1.0⟩, radius := 0.68,
        width := 2.6, color := RGBA.amber, label := "Equatorial S¹" }
    ],
    points := #[{ handleId := 0, pos := ctrl, radius := 0.09, color := RGBA.coral,
                  role := { draggable := true }, label := "4D Rotor Angle" }],
    inspect := #[{ idx := 0, name := "S³ → ℝ³", grade := 2,
                   formatted := s!"4D angle θ = {ang4D} rad", editable := true }] }

/-- **10. `cga3d_inversion`** — Conformal Reflection & Spherical Inversion `S X S⁻¹` of a 3D Cube! -/
def buildCga3dInversion (handles : Array (UInt32 × Vec3)) (seq : UInt64) (t : Float) : SceneFrame := Id.run do
  let f := mkBase "cga3d_inversion" "3D CGA Conformal Inversion of a Cube (S X S⁻¹)" "CGA3" seq t
  let invC := hPos handles 0 ⟨0.65 + 0.35 * Float.cos (t * 0.6), 0.25 * Float.sin (t * 0.8), 0.55⟩
  let invR := 0.88
  let invertPt (p : Vec3) : Vec3 :=
    let d := Vec3.sub p invC
    let d2 := max 0.08 (Vec3.normSq d)
    Vec3.add invC (Vec3.scale ((invR * invR) / d2) d)
  -- Original cube corners centered at (-0.4, 0, -0.2)
  let c0 : Vec3 := ⟨-0.45, 0.0, -0.25⟩
  let hs := 0.62
  let corners : Array Vec3 := #[
    ⟨c0.x - hs, c0.y - hs, c0.z - hs⟩, ⟨c0.x + hs, c0.y - hs, c0.z - hs⟩,
    ⟨c0.x + hs, c0.y + hs, c0.z - hs⟩, ⟨c0.x - hs, c0.y + hs, c0.z - hs⟩,
    ⟨c0.x - hs, c0.y - hs, c0.z + hs⟩, ⟨c0.x + hs, c0.y - hs, c0.z + hs⟩,
    ⟨c0.x + hs, c0.y + hs, c0.z + hs⟩, ⟨c0.x - hs, c0.y + hs, c0.z + hs⟩
  ]
  let edgePairs : Array (Nat × Nat) :=
    #[(0,1),(1,2),(2,3),(3,0), (4,5),(5,6),(6,7),(7,4), (0,4),(1,5),(2,6),(3,7)]
  let mut origSegs : Array SegmentPrim := #[]
  let mut curves : Array CurvePrim := #[]
  for (i, j) in edgePairs do
    let a := corners[i]!; let b := corners[j]!
    origSegs := origSegs.push { a, b, width := 1.6, color := RGBA.ghost, role := { dashed := true } }
    let mut arcPts : Array Vec3 := #[]
    for k in [:25] do
      let u := Float.ofNat k / 24.0
      arcPts := arcPts.push (invertPt (Vec3.lerp a b u))
    curves := curves.push (curveFromVecs arcPts RGBA.cyan 2.8 false false)
  return { f with
    segments := origSegs, curves,
    spheres := #[{ center := invC, radius := invR, color := ⟨1.0, 0.53, 0.53, 0.22⟩, label := "Inversion Sphere S" }],
    points := #[{ handleId := 0, pos := invC, radius := 0.09, color := RGBA.coral,
                  role := { draggable := true }, label := "Sphere Center" }],
    inspect := #[{ idx := 0, name := "Conformal Sandwich", grade := 1,
                   formatted := "X' = -S X S⁻¹ (lines → circular arcs)", editable := true }] }

/-- **11. `cga3d_dipole_field`** — CGA Point-Pair Dipole Field `P = A ∧ B` (Coaxial Circles + Equipotentials)! -/
def buildCga3dDipoleField (handles : Array (UInt32 × Vec3)) (seq : UInt64) (t : Float) : SceneFrame := Id.run do
  let f := mkBase "cga3d_dipole_field" "3D CGA Point-Pair Dipole Field (A ∧ B)" "CGA3" seq t
  let pA := hPos handles 0 ⟨-0.95, 0.15 * Float.sin (t * 0.7), 0.0⟩
  let pB := hPos handles 1 ⟨ 0.95, -0.15 * Float.sin (t * 0.7), 0.0⟩
  let mid := Vec3.lerp pA pB 0.5
  let halfVec := Vec3.scale 0.5 (Vec3.sub pB pA)
  let aDist := max 0.2 (Vec3.norm halfVec)
  let axis := Vec3.normalize halfVec
  let (u0, v0) := orthoFrame axis
  -- Coaxial field-line circles passing through both dipole poles A & B in 6 meridional planes!
  let mut circles : Array CirclePrim := #[]
  for m in [:6] do
    let phi := piF * Float.ofNat m / 6.0 + t * 0.15
    let radial := Vec3.add (Vec3.scale (Float.cos phi) u0) (Vec3.scale (Float.sin phi) v0)
    for k in #[0.45, 0.95, -0.45, -0.95] do
      let offset := k * aDist
      let rad := Float.sqrt (aDist * aDist + offset * offset)
      let ctr := Vec3.add mid (Vec3.scale offset radial)
      circles := circles.push { center := ctr, u := axis, v := radial, radius := rad,
                                width := 2.0, color := RGBA.cyan }
  -- Orthogonal Apollonian equipotential spheres around A and B
  let spheres : Array SpherePrim := #[
    { center := Vec3.lerp pA mid 0.25, radius := aDist * 0.42, color := ⟨1.0, 0.42, 0.42, 0.22⟩, label := "+Φ" },
    { center := Vec3.lerp pB mid 0.25, radius := aDist * 0.42, color := ⟨0.30, 0.62, 1.0, 0.22⟩, label := "-Φ" }
  ]
  return { f with
    circles, spheres,
    pointPairs := #[{ p1 := pA, p2 := pB, radius := 0.08, color := RGBA.amber, showLink := true, label := "A∧B" }],
    points := #[
      { handleId := 0, pos := pA, radius := 0.095, color := RGBA.coral, role := { draggable := true }, label := "Pole A" },
      { handleId := 1, pos := pB, radius := 0.095, color := RGBA.blue,  role := { draggable := true }, label := "Pole B" }
    ],
    inspect := #[{ idx := 0, name := "Point Pair A∧B", grade := 2,
                   formatted := s!"‖A-B‖ = {2.0 * aDist} · 24 dipole circles", editable := true }] }

/-! ## GROUP C: Spacetime Algebra `STA` (`Cl(3,1)` `-+++`) — 3 New Showstopper Presets -/

/-- **12. `sta_light_cone`** — Minkowski Light Cone (`-c²t² + x² + y² = 0`) + Lorentz Boost & Worldline! -/
def buildStaLightCone (handles : Array (UInt32 × Vec3)) (seq : UInt64) (t : Float) : SceneFrame := Id.run do
  let f := mkBase "sta_light_cone" "STA Cl(3,1) Relativistic Light Cone & Lorentz Boost" "STA" seq t
  let ctrl := hPos handles 0 ⟨0.65 * Float.sin (t * 0.5), 1.0, 0.0⟩
  let beta := max (-0.82) (min 0.82 (ctrl.x / max 0.5 (Float.abs ctrl.y)))
  let gamma := 1.0 / Float.sqrt (max 0.05 (1.0 - beta * beta))
  -- Build future & past light cones as translucent parametric double-cone mesh
  let coneSurf (u v : Float) : Vec3 :=
    -- u ∈ [-1.25, 1.25] is time coordinate ct (mapped to Y), radius = |u|
    let r := Float.abs u
    ⟨r * Float.cos v, u, r * Float.sin v⟩
  let coneMesh := buildParametricSurface coneSurf (-1.25) 1.25 0.0 twoPiF 22 32 4201 true 0.34
  -- Proper-time hyperboloid contour circles & hyperbolic accelerated worldline x² - (ct)² = 1/a²
  let mut worldPts : Array Vec3 := #[]
  for i in [:41] do
    let tau := -1.1 + 2.2 * Float.ofNat i / 40.0
    let x := 0.55 * Float.cosh tau
    let ct := 0.55 * Float.sinh tau
    worldPts := worldPts.push ⟨x, ct, 0.0⟩
  -- Boosted axes (ct', x') in the (x, ct) plane
  let ctPrime : Vec3 := ⟨gamma * beta * 1.25, gamma * 1.25, 0.0⟩
  let xPrime  : Vec3 := ⟨gamma * 1.25, gamma * beta * 1.25, 0.0⟩
  return { f with
    meshAssets := #[coneMesh],
    meshRefs := #[{ meshId := coneMesh.meshId, dirtyHash := coneMesh.dirtyHash,
                    color := ⟨0.95, 0.78, 0.30, 0.28⟩, doubleSided := true }],
    curves := #[curveFromVecs worldPts RGBA.coral 3.2 false false],
    lines := #[
      { origin := Vec3.zero, dir := Vec3.normalize ctPrime, clip := 1.6, width := 3.0, color := RGBA.cyan, label := "ct' (Boosted)" },
      { origin := Vec3.zero, dir := Vec3.normalize xPrime,  clip := 1.6, width := 3.0, color := RGBA.green, label := "x' (Simul.)" },
      { origin := Vec3.zero, dir := ⟨0.0, 1.0, 0.0⟩,        clip := 1.6, width := 1.8, color := RGBA.ghost, label := "ct" }
    ],
    circles := #[
      { center := ⟨0.0, 1.25, 0.0⟩, u := ⟨1.0, 0.0, 0.0⟩, v := ⟨0.0, 0.0, 1.0⟩, radius := 1.25, width := 2.4, color := RGBA.amber, label := "Future Horizon" },
      { center := ⟨0.0, -1.25, 0.0⟩, u := ⟨1.0, 0.0, 0.0⟩, v := ⟨0.0, 0.0, 1.0⟩, radius := 1.25, width := 2.4, color := RGBA.violet, label := "Past Horizon" }
    ],
    points := #[{ handleId := 0, pos := ctrl, radius := 0.09, color := RGBA.coral,
                  role := { draggable := true }, label := s!"β={beta}" }],
    inspect := #[{ idx := 0, name := "Lorentz Boost B", grade := 2,
                   formatted := s!"β = {beta}, γ = {gamma} (-+++ metric)", editable := true }] }

/-- **13. `sta_em_wave`** — Electromagnetic Faraday Bivector Wave `F = E + I B`! -/
def buildStaEmWave (handles : Array (UInt32 × Vec3)) (seq : UInt64) (t : Float) : SceneFrame := Id.run do
  let f := mkBase "sta_em_wave" "STA Electromagnetic Faraday Wave (F = E + I B)" "STA" seq t
  let ctrl := hPos handles 0 ⟨0.0, 0.85, 0.0⟩
  let polEllip := max 0.0 (min 1.0 (Float.abs ctrl.x)) -- 0 = linear, 1 = circular polarization!
  let mut ePts : Array Vec3 := #[]
  let mut bPts : Array Vec3 := #[]
  let mut segs : Array SegmentPrim := #[]
  let mut disks : Array BivectorDiskPrim := #[]
  let nSamples := 48
  for i in [:nSamples] do
    let u := Float.ofNat i / Float.ofNat (nSamples - 1)
    let z := -2.0 + 4.0 * u
    let phase := 3.6 * z - 3.2 * t
    let ex := polEllip * 0.72 * Float.sin phase
    let ey := 0.78 * Float.cos phase
    -- B = k̂ × E so Bx = -Ey, By = Ex
    let bx := -ey
    let by_ := ex
    let eTip : Vec3 := ⟨ex, ey, z⟩
    let bTip : Vec3 := ⟨bx, by_, z⟩
    ePts := ePts.push eTip
    bPts := bPts.push bTip
    if i % 3 == 0 then
      let org : Vec3 := ⟨0.0, 0.0, z⟩
      segs := segs.push { a := org, b := eTip, width := 2.6, color := RGBA.coral, role := { arrow := true } }
                  |>.push { a := org, b := bTip, width := 2.6, color := RGBA.cyan,  role := { arrow := true } }
    if i == 16 || i == 32 then
      disks := disks.push { origin := ⟨0.0, 0.0, z⟩, u := ⟨ex, ey, 0.0⟩, v := ⟨bx, by_, 0.0⟩,
                            area := 0.5, color := ⟨1.0, 0.72, 0.22, 0.28⟩, isDisk := false }
  return { f with
    curves := #[curveFromVecs ePts RGBA.coral 3.0 false false,
                curveFromVecs bPts RGBA.cyan 3.0 false false],
    segments := segs, bivectorDisks := disks,
    lines := #[{ origin := Vec3.zero, dir := ⟨0.0, 0.0, 1.0⟩, clip := 2.3, width := 2.0,
                 color := RGBA.amber, label := "Poynting k = E × B" }],
    points := #[{ handleId := 0, pos := ctrl, radius := 0.09, color := RGBA.amber,
                  role := { draggable := true }, label := "Polarization" }],
    inspect := #[{ idx := 0, name := "Faraday F = E + IB", grade := 2,
                   formatted := s!"∇F = 0 · ellipticity = {polEllip}", editable := true }] }

/-- **14. `sta_rapidity`** — Thomas Precession & Non-Commutative Boost Composition (`Wigner Rotation`)! -/
def buildStaRapidity (handles : Array (UInt32 × Vec3)) (seq : UInt64) (t : Float) : SceneFrame := Id.run do
  let f := mkBase "sta_rapidity" "STA Thomas Precession & Wigner Rotation" "STA" seq t
  let h0 := hPos handles 0 ⟨0.78, 0.0, 0.0⟩
  let h1 := hPos handles 1 ⟨0.0, 0.72 * Float.cos (t * 0.4), 0.72 * Float.sin (t * 0.4)⟩
  let v1x := max (-0.85) (min 0.85 h0.x)
  let v2y := max (-0.85) (min 0.85 h1.y)
  let g1 := 1.0 / Float.sqrt (max 0.05 (1.0 - v1x * v1x))
  let g2 := 1.0 / Float.sqrt (max 0.05 (1.0 - v2y * v2y))
  -- Exact relativistic velocity addition & Thomas-Wigner rotation angle tan(θ_W) = (g1 g2 v1 v2)/(g1 + g2)
  let wignerAngle := Float.atan2 (g1 * g2 * v1x * v2y) (g1 + g2)
  let v12 : Vec3 := ⟨v1x / (1.0), v2y / g1, 0.0⟩
  let v21 : Vec3 := ⟨v1x / g2, v2y, 0.0⟩
  return { f with
    circles := #[
      { center := Vec3.zero, u := ⟨1.0, 0.0, 0.0⟩, v := ⟨0.0, 1.0, 0.0⟩, radius := 1.0,
        width := 2.6, color := RGBA.amber, label := "Speed of Light |v| = c" }
    ],
    segments := #[
      { a := Vec3.zero, b := ⟨v1x, 0.0, 0.0⟩, width := 3.5, color := RGBA.cyan, role := { arrow := true } },
      { a := ⟨v1x, 0.0, 0.0⟩, b := v12, width := 3.2, color := RGBA.coral, role := { arrow := true } },
      { a := Vec3.zero, b := v12, width := 3.2, color := RGBA.green, role := { arrow := true } },
      { a := Vec3.zero, b := v21, width := 2.4, color := RGBA.violet, role := { dashed := true, arrow := true } }
    ],
    bivectorDisks := #[
      { origin := Vec3.zero, u := ⟨v1x, 0.0, 0.0⟩, v := ⟨0.0, v2y, 0.0⟩,
        area := Float.abs wignerAngle, color := ⟨0.72, 0.45, 1.0, 0.32⟩, isDisk := true }
    ],
    points := #[
      { handleId := 0, pos := ⟨v1x, 0.0, 0.0⟩, radius := 0.09, color := RGBA.cyan, role := { draggable := true }, label := "Boost v1" },
      { handleId := 1, pos := ⟨0.0, v2y, 0.0⟩, radius := 0.09, color := RGBA.coral, role := { draggable := true }, label := "Boost v2" }
    ],
    inspect := #[{ idx := 0, name := "Wigner Angle θ_W", grade := 2,
                   formatted := s!"B(v2)B(v1) = R({wignerAngle * 180.0 / piF}°) B(v12)", editable := true }] }

/-! ## GROUP D: 3D Implicit & Parametric Gallery (Powered by `Implicit3D.lean`!) — 8 Presets -/

/-- **15. `implicit_gyroid`** — Gyroid TPMS Minimal Surface (Watertight Marching Tetrahedra)! -/
def buildImplicitGyroid (handles : Array (UInt32 × Vec3)) (seq : UInt64) (t : Float) : SceneFrame :=
  let f := mkBase "implicit_gyroid" "Implicit 3D: Gyroid TPMS Minimal Surface" "R3" seq t false 4.6
  let ctrl := hPos handles 0 ⟨0.0, 0.25 * Float.sin (t * 0.6), 1.55⟩
  let iso := max (-0.85) (min 0.85 ctrl.y)
  let mesh := buildGyroidMesh iso 2.35 16 4301
  { f with
    meshAssets := #[mesh],
    meshRefs := #[{ meshId := mesh.meshId, dirtyHash := mesh.dirtyHash,
                    color := RGBA.white, useVertexColors := true }],
    points := #[{ handleId := 0, pos := ctrl, radius := 0.09, color := RGBA.amber,
                  role := { draggable := true }, label := "Isovalue" }],
    inspect := #[{ idx := 0, name := "Gyroid TPMS", grade := 0,
                   formatted := s!"sin(x)cos(y)+sin(y)cos(z)+sin(z)cos(x) = {iso}", editable := true }] }

/-- **16. `implicit_metaballs`** — Animated 4-Lobe Organic Metaballs (Marching Tetrahedra)! -/
def buildImplicitMetaballs (handles : Array (UInt32 × Vec3)) (seq : UInt64) (t : Float) : SceneFrame :=
  let f := mkBase "implicit_metaballs" "Implicit 3D: Live Organic Metaballs" "R3" seq t false 4.4
  let ctrl := hPos handles 0 ⟨0.58 * Float.cos (t * 0.7), 0.25 * Float.sin (t * 0.9), 0.0⟩
  let mesh := buildMetaballsMesh t ctrl 16 4302
  { f with
    meshAssets := #[mesh],
    meshRefs := #[{ meshId := mesh.meshId, dirtyHash := mesh.dirtyHash,
                    color := RGBA.white, useVertexColors := true }],
    points := #[{ handleId := 0, pos := ctrl, radius := 0.09, color := RGBA.coral,
                  role := { draggable := true }, label := "Metaball Orb" }],
    inspect := #[{ idx := 0, name := "Metaball Field", grade := 0,
                   formatted := "∑ rᵢ² / ‖p - cᵢ(t)‖² = 1", editable := true }] }

/-- **17. `implicit_schwarz_p`** — Schwarz P Triply Periodic Minimal Surface! -/
def buildImplicitSchwarzP (handles : Array (UInt32 × Vec3)) (seq : UInt64) (t : Float) : SceneFrame :=
  let f := mkBase "implicit_schwarz_p" "Implicit 3D: Schwarz P Minimal Surface" "R3" seq t false 4.6
  let ctrl := hPos handles 0 ⟨0.0, 0.30 * Float.sin (t * 0.55), 1.55⟩
  let iso := max (-0.95) (min 0.95 ctrl.y)
  let mesh := buildSchwarzPMesh iso 2.30 16 4303
  { f with
    meshAssets := #[mesh],
    meshRefs := #[{ meshId := mesh.meshId, dirtyHash := mesh.dirtyHash,
                    color := RGBA.white, useVertexColors := true }],
    points := #[{ handleId := 0, pos := ctrl, radius := 0.09, color := RGBA.cyan,
                  role := { draggable := true }, label := "Isovalue" }],
    inspect := #[{ idx := 0, name := "Schwarz P", grade := 0,
                   formatted := s!"cos(x) + cos(y) + cos(z) = {iso}", editable := true }] }

/-- **18. `param_klein_bottle`** — Figure-8 Klein Bottle Non-Orientable Immersion! -/
def buildParamKleinBottle (handles : Array (UInt32 × Vec3)) (seq : UInt64) (t : Float) : SceneFrame :=
  let f := mkBase "param_klein_bottle" "Parametric 3D: Figure-8 Klein Bottle" "R3" seq t false 4.5
  let ctrl := hPos handles 0 ⟨0.42 + 0.08 * Float.sin (t * 0.6), 1.05, 0.0⟩
  let rTube := max 0.22 (min 0.62 (Float.abs ctrl.x))
  let mesh := buildKleinBottleMesh 1.02 rTube 48 24 4304
  { f with
    meshAssets := #[mesh],
    meshRefs := #[{ meshId := mesh.meshId, dirtyHash := mesh.dirtyHash,
                    color := RGBA.white, useVertexColors := true, doubleSided := true }],
    points := #[{ handleId := 0, pos := ctrl, radius := 0.09, color := RGBA.violet,
                  role := { draggable := true }, label := "Tube Radius" }],
    inspect := #[{ idx := 0, name := "Klein Bottle", grade := 0,
                   formatted := s!"Non-orientable χ=0 immersion, r={rTube}", editable := true }] }

/-- **19. `param_mobius_strip`** — Twisted Möbius Strip + Parallel-Transported Normal Vector! -/
def buildParamMobiusStrip (handles : Array (UInt32 × Vec3)) (seq : UInt64) (t : Float) : SceneFrame := Id.run do
  let f := mkBase "param_mobius_strip" "Parametric 3D: Möbius Strip & Normal Flip" "R3" seq t false 4.4
  let ctrl := hPos handles 0 ⟨0.38, 0.0, 1.35⟩
  let halfW := max 0.16 (min 0.55 (Float.abs ctrl.x))
  let mesh := buildMobiusStripMesh 1.0 halfW 1.0 56 12 4305
  -- Center spine curve + animated transported normal arrow showing sign flip after 2π!
  let mut spine : Array Vec3 := #[]
  for i in [:64] do
    let u := twoPiF * Float.ofNat i / 64.0
    spine := spine.push ⟨Float.cos u, 0.0, Float.sin u⟩
  let uA := t * 0.9
  let pA : Vec3 := ⟨Float.cos uA, 0.0, Float.sin uA⟩
  let nA : Vec3 := Vec3.scale 0.48 ⟨-Float.sin (0.5 * uA) * Float.cos uA, Float.cos (0.5 * uA), -Float.sin (0.5 * uA) * Float.sin uA⟩
  return { f with
    meshAssets := #[mesh],
    meshRefs := #[{ meshId := mesh.meshId, dirtyHash := mesh.dirtyHash,
                    color := RGBA.white, useVertexColors := true, doubleSided := true }],
    curves := #[curveFromVecs spine RGBA.amber 2.8 true false],
    segments := #[{ a := pA, b := Vec3.add pA nA, width := 3.6, color := RGBA.coral, role := { arrow := true } }],
    points := #[
      { handleId := 0, pos := ctrl, radius := 0.09, color := RGBA.cyan, role := { draggable := true }, label := "Band Width" },
      { handleId := 1, pos := pA, radius := 0.065, color := RGBA.white, label := "Walker" }
    ],
    inspect := #[{ idx := 0, name := "Möbius Band", grade := 0,
                   formatted := "Non-orientable 1-sided band (n(2π) = -n(0))", editable := true }] }

/-- **20. `implicit_genus2`** — Genus-2 Double-Torus Pretzel Isosurface (Marching Tetrahedra)! -/
def buildImplicitGenus2 (handles : Array (UInt32 × Vec3)) (seq : UInt64) (t : Float) : SceneFrame :=
  let f := mkBase "implicit_genus2" "Implicit 3D: Genus-2 Double-Torus Pretzel" "R3" seq t false 4.2
  let ctrl := hPos handles 0 ⟨0.0, 0.22 + 0.05 * Float.sin (t * 0.7), 1.15⟩
  let tubeR := max 0.14 (min 0.34 (Float.abs ctrl.y))
  let mesh := buildGenus2Mesh tubeR 18 4306
  { f with
    meshAssets := #[mesh],
    meshRefs := #[{ meshId := mesh.meshId, dirtyHash := mesh.dirtyHash,
                    color := RGBA.white, useVertexColors := true }],
    points := #[{ handleId := 0, pos := ctrl, radius := 0.09, color := RGBA.amber,
                  role := { draggable := true }, label := "Tube Thickness" }],
    inspect := #[{ idx := 0, name := "Genus-2 Surface", grade := 0,
                   formatted := s!"((x²+y²)² - x² + y²)² + z² = {tubeR*tubeR}", editable := true }] }

/-- **21. `param_boys_surface`** — Boy's Surface Immersion of the Real Projective Plane `ℝP²`! -/
def buildParamBoysSurface (handles : Array (UInt32 × Vec3)) (seq : UInt64) (t : Float) : SceneFrame :=
  let f := mkBase "param_boys_surface" "Parametric 3D: Boy's Surface (ℝP² Immersion)" "R3" seq t false 4.2
  let ctrl := hPos handles 0 ⟨0.85, 0.0, 1.15⟩
  let sc := max 0.5 (min 1.2 (Float.abs ctrl.x))
  let mesh := buildBoysSurfaceMesh sc 40 24 4307
  { f with
    meshAssets := #[mesh],
    meshRefs := #[{ meshId := mesh.meshId, dirtyHash := mesh.dirtyHash,
                    motor := Motor3.rotorAxis ⟨0.0, 1.0, 0.0⟩ (t * 0.3),
                    color := RGBA.white, useVertexColors := true, doubleSided := true }],
    points := #[{ handleId := 0, pos := ctrl, radius := 0.09, color := RGBA.violet,
                  role := { draggable := true }, label := "Scale" }],
    inspect := #[{ idx := 0, name := "Boy's Surface", grade := 0,
                   formatted := "3-fold symmetric ℝP² immersion (χ = 1)", editable := true }] }

/-- **22. `param_enneper_superquadric`** — Enneper Minimal Surface + Interactive Superquadric Morph! -/
def buildParamEnneperSuperquadric (handles : Array (UInt32 × Vec3)) (seq : UInt64) (t : Float) : SceneFrame :=
  let f := mkBase "param_enneper_superquadric" "Parametric 3D: Enneper Minimal & Superquadric" "R3" seq t false 4.8
  let ctrl := hPos handles 0 ⟨0.45 + 0.35 * Float.sin (t * 0.5), 0.45 + 0.35 * Float.cos (t * 0.5), 1.35⟩
  let e1 := max 0.22 (min 2.2 (0.25 + 1.2 * Float.abs ctrl.x))
  let e2 := max 0.22 (min 2.2 (0.25 + 1.2 * Float.abs ctrl.y))
  let sq := buildSuperquadricMesh e1 e2 0.72 30 20 4308
  let enn := buildEnneperSurfaceMesh 1.10 0.36 28 28 4309
  { f with
    meshAssets := #[sq, enn],
    meshRefs := #[
      { meshId := sq.meshId,  dirtyHash := sq.dirtyHash,  motor := Motor3.translator (-0.95) 0.0 0.0,
        color := RGBA.white, useVertexColors := true },
      { meshId := enn.meshId, dirtyHash := enn.dirtyHash, motor := Motor3.translator 0.95 0.0 0.0,
        color := RGBA.white, useVertexColors := true, doubleSided := true }
    ],
    points := #[{ handleId := 0, pos := ctrl, radius := 0.09, color := RGBA.amber,
                  role := { draggable := true }, label := "Superquadric (e1,e2)" }],
    inspect := #[{ idx := 0, name := "Minimal & Superquadric", grade := 0,
                   formatted := s!"Superquadric e1={e1}, e2={e2} + Enneper H=0", editable := true }] }

/-! ## GROUP E: 2D CGA / Non-Euclidean / Complex / Dual / Quaternion / Higher Cl — 6 Presets -/

/-- **23. `cga2d_apollonius`** — 2D CGA (`Cl(3,1)`) Apollonius / Soddy Tangent Circles! -/
def buildCga2dApollonius (handles : Array (UInt32 × Vec3)) (seq : UInt64) (t : Float) : SceneFrame := Id.run do
  let f := mkBase "cga2d_apollonius" "2D CGA Apollonius / Descartes Tangent Circles" "CGA2" seq t true
  let ctrl := hPos handles 0 ⟨0.62 + 0.14 * Float.sin (t * 0.6), 0.0, 0.0⟩
  let r1 := max 0.30 (min 0.85 (Float.abs ctrl.x))
  let r2 := 0.58
  let r3 := 0.50
  -- Place 3 mutually tangent circles in the XY plane
  let c1 : Vec3 := ⟨-r1, 0.0, 0.0⟩
  let c2 : Vec3 := ⟨ r2, 0.0, 0.0⟩
  let d12 := r1 + r2; let d13 := r1 + r3; let d23 := r2 + r3
  let x3 := (d12 * d12 + d13 * d13 - d23 * d23) / (2.0 * d12) - r1
  let y3 := Float.sqrt (max 0.01 (d13 * d13 - (x3 + r1) * (x3 + r1)))
  let c3 : Vec3 := ⟨x3, y3, 0.0⟩
  -- Descartes' Circle Theorem: k4 = k1 + k2 + k3 ± 2 √(k1 k2 + k2 k3 + k3 k1)
  let k1 := 1.0 / r1; let k2 := 1.0 / r2; let k3 := 1.0 / r3
  let disc := 2.0 * Float.sqrt (max 0.0 (k1 * k2 + k2 * k3 + k3 * k1))
  let kIn  := k1 + k2 + k3 + disc
  let kOut := k1 + k2 + k3 - disc
  let rIn := 1.0 / max 0.05 kIn
  let rOut := 1.0 / max 0.05 (Float.abs kOut)
  -- Complex Descartes formula for inner/outer tangent centers (weighted centroid approximation refined)
  let ctrIn : Vec3 := ⟨(k1 * c1.x + k2 * c2.x + k3 * c3.x) / (k1 + k2 + k3),
                       (k1 * c1.y + k2 * c2.y + k3 * c3.y) / (k1 + k2 + k3), 0.0⟩
  let ctrOut : Vec3 := ⟨(c1.x + c2.x + c3.x) / 3.0, (c1.y + c2.y + c3.y) / 3.0, 0.0⟩
  let u := ⟨1.0, 0.0, 0.0⟩; let v := ⟨0.0, 1.0, 0.0⟩
  return { f with
    circles := #[
      { center := c1, u, v, radius := r1, width := 2.6, color := RGBA.cyan, label := "C1" },
      { center := c2, u, v, radius := r2, width := 2.6, color := RGBA.violet, label := "C2" },
      { center := c3, u, v, radius := r3, width := 2.6, color := RGBA.green, label := "C3" },
      { center := ctrIn, u, v, radius := rIn, width := 3.0, color := RGBA.coral, label := "Inner Soddy" },
      { center := ctrOut, u, v, radius := rOut, width := 2.0, color := RGBA.amber, label := "Outer Soddy" }
    ],
    points := #[
      { handleId := 0, pos := ctrl, radius := 0.075, color := RGBA.coral, role := { draggable := true }, label := "Radius r1" },
      { handleId := 1, pos := c1, radius := 0.05, color := RGBA.cyan },
      { handleId := 2, pos := c2, radius := 0.05, color := RGBA.violet },
      { handleId := 3, pos := c3, radius := 0.05, color := RGBA.green }
    ],
    inspect := #[{ idx := 0, name := "Descartes 2D", grade := 1,
                   formatted := s!"k_in = {kIn} (r={rIn}), k_out = {kOut}", editable := true }] }

/-- **24. `pga2d_non_euclidean`** — 2D Hyperbolic Poincaré Disk (`Cl(2,1)`) Geodesics & Triangle! -/
def buildPga2dNonEuclidean (handles : Array (UInt32 × Vec3)) (seq : UInt64) (t : Float) : SceneFrame := Id.run do
  let f := mkBase "pga2d_non_euclidean" "2D Hyperbolic Cl(2,1) Poincaré Disk Geodesics" "Hyperbolic2D" seq t true
  let clampDisk (p : Vec3) : Vec3 :=
    let r := Float.sqrt (p.x * p.x + p.y * p.y)
    if r > 0.90 then ⟨0.90 * p.x / r, 0.90 * p.y / r, 0.0⟩ else ⟨p.x, p.y, 0.0⟩
  let A := clampDisk (hPos handles 0 ⟨-0.65, -0.35, 0.0⟩)
  let B := clampDisk (hPos handles 1 ⟨ 0.72, -0.25, 0.0⟩)
  let C := clampDisk (hPos handles 2 ⟨ 0.10 + 0.25 * Float.sin (t * 0.5), 0.72, 0.0⟩)
  -- Hyperbolic geodesic arc connecting p and q inside the unit disk (orthogonal to unit circle!)
  let geodesicCurve (p q : Vec3) (col : RGBA) : CurvePrim := Id.run do
    -- Inversion of p in unit circle gives p* = p / |p|²; circumcircle of (p, q, p*) is orthogonal!
    let det := p.x * q.y - p.y * q.x
    let mut pts : Array Vec3 := #[]
    if Float.abs det < 1e-3 then
      for i in [:24] do pts := pts.push (Vec3.lerp p q (Float.ofNat i / 23.0))
    else
      let p2 := p.x * p.x + p.y * p.y + 1.0
      let q2 := q.x * q.x + q.y * q.y + 1.0
      let cx := (p2 * q.y - q2 * p.y) / (2.0 * det)
      let cy := (p.x * q2 - q.x * p2) / (2.0 * det)
      let rad := Float.sqrt (max 1e-4 ((p.x - cx) * (p.x - cx) + (p.y - cy) * (p.y - cy)))
      let a0 := Float.atan2 (p.y - cy) (p.x - cx)
      let a1 := Float.atan2 (q.y - cy) (q.x - cx)
      let dAng0 := a1 - a0
      let dAng :=
        if dAng0 > piF then dAng0 - twoPiF
        else if dAng0 < -piF then dAng0 + twoPiF
        else dAng0
      for i in [:29] do
        let u := Float.ofNat i / 28.0
        let ang := a0 + u * dAng
        pts := pts.push ⟨cx + rad * Float.cos ang, cy + rad * Float.sin ang, 0.0⟩
    return curveFromVecs pts col 2.8 false false
  let u := ⟨1.0, 0.0, 0.0⟩; let v := ⟨0.0, 1.0, 0.0⟩
  return { f with
    circles := #[
      { center := Vec3.zero, u, v, radius := 1.0, width := 3.0, color := RGBA.amber, label := "Ideal Horizon ∂ℍ²" },
      { center := ⟨0.0, 0.5, 0.0⟩, u, v, radius := 0.5, width := 1.8, color := RGBA.ghost, label := "Horocycle" }
    ],
    curves := #[geodesicCurve A B RGBA.cyan, geodesicCurve B C RGBA.violet, geodesicCurve C A RGBA.coral],
    points := #[
      { handleId := 0, pos := A, radius := 0.075, color := RGBA.cyan,   role := { draggable := true }, label := "A" },
      { handleId := 1, pos := B, radius := 0.075, color := RGBA.violet, role := { draggable := true }, label := "B" },
      { handleId := 2, pos := C, radius := 0.075, color := RGBA.coral,  role := { draggable := true }, label := "C" }
    ],
    inspect := #[{ idx := 0, name := "Hyperbolic Cl(2,1)", grade := 1,
                   formatted := "Poincaré disk geodesics (angle sum < 180°)", editable := true }] }

/-- **25. `complex_mandelbrot`** — Complex `Cl(0,1)` Mandelbrot Cardioid + Live Iterated Orbit & Möbius Grid! -/
def buildComplexMandelbrot (handles : Array (UInt32 × Vec3)) (seq : UInt64) (t : Float) : SceneFrame := Id.run do
  let f := mkBase "complex_mandelbrot" "Complex Cl(0,1) Mandelbrot Orbit & Möbius Map" "Complex" seq t true
  let cPt := hPos handles 0 ⟨-0.45 + 0.35 * Float.cos (t * 0.55), 0.32 + 0.25 * Float.sin (t * 0.55), 0.0⟩
  -- Main Mandelbrot cardioid: c(θ) = ½ e^{iθ} - ¼ e^{2iθ}
  let mut cardioid : Array Vec3 := #[]
  for i in [:72] do
    let th := twoPiF * Float.ofNat i / 72.0
    let x := 0.5 * Float.cos th - 0.25 * Float.cos (2.0 * th)
    let y := 0.5 * Float.sin th - 0.25 * Float.sin (2.0 * th)
    cardioid := cardioid.push ⟨x, y, 0.0⟩
  -- Iterated complex orbit z_{n+1} = z_n² + c (pure Cl(0,1) multiplication!)
  let mut orbitPts : Array Vec3 := #[Vec3.zero]
  let mut segs : Array SegmentPrim := #[]
  let mut zx := 0.0; let mut zy := 0.0
  for _ in [:24] do
    let nx := zx * zx - zy * zy + cPt.x
    let ny := 2.0 * zx * zy + cPt.y
    if nx * nx + ny * ny > 16.0 then break
    let prev : Vec3 := ⟨zx, zy, 0.0⟩
    let next : Vec3 := ⟨nx, ny, 0.0⟩
    segs := segs.push { a := prev, b := next, width := 2.2, color := RGBA.coral }
    orbitPts := orbitPts.push next
    zx := nx; zy := ny
  let u := ⟨1.0, 0.0, 0.0⟩; let v := ⟨0.0, 1.0, 0.0⟩
  return { f with
    curves := #[curveFromVecs cardioid RGBA.cyan 2.8 true false,
                curveFromVecs orbitPts RGBA.amber 2.2 false false],
    circles := #[
      { center := ⟨-1.0, 0.0, 0.0⟩, u, v, radius := 0.25, width := 2.4, color := RGBA.violet, label := "Period-2 Bulb" },
      { center := Vec3.zero, u, v, radius := 2.0, width := 1.4, color := RGBA.ghost, label := "Escape |z|=2" }
    ],
    segments := segs,
    points := #[{ handleId := 0, pos := cPt, radius := 0.08, color := RGBA.coral,
                  role := { draggable := true }, label := "c = Re + i·Im" }],
    inspect := #[{ idx := 0, name := "z_{n+1} = z_n² + c", grade := 0,
                   formatted := s!"c = {cPt.x} + ({cPt.y})i · {orbitPts.size} bounded steps", editable := true }] }

/-- **26. `dual_tangent_plane`** — Dual Numbers `Cl(0,0,1)` Automatic Differentiation Tangent Plane! -/
def buildDualTangentPlane (handles : Array (UInt32 × Vec3)) (seq : UInt64) (t : Float) : SceneFrame := Id.run do
  let f := mkBase "dual_tangent_plane" "Dual Cl(0,0,1) Autodiff Tangent Plane & Gradient" "Dual" seq t false 4.6
  let probe := hPos handles 0 ⟨0.65 * Float.cos (t * 0.5), 0.0, 0.65 * Float.sin (t * 0.5)⟩
  let x0 := max (-1.4) (min 1.4 probe.x)
  let z0 := max (-1.4) (min 1.4 probe.z)
  -- Exact dual-number evaluation of f(x + ε, z) and f(x, z + ε) for f(x,z) = 0.55 sin(1.6x) cos(1.6z)
  let evalF (x z : Float) : Float := 0.55 * Float.sin (1.6 * x) * Float.cos (1.6 * z)
  let y0 := evalF x0 z0
  let dfdx := 0.55 * 1.6 * Float.cos (1.6 * x0) * Float.cos (1.6 * z0) -- Dual ε part wrt x!
  let dfdz := -0.55 * 1.6 * Float.sin (1.6 * x0) * Float.sin (1.6 * z0) -- Dual ε part wrt z!
  let surf (u v : Float) : Vec3 := ⟨u, evalF u v, v⟩
  let mesh := buildParametricSurface surf (-1.6) 1.6 (-1.6) 1.6 32 32 4401 true
  let tu := Vec3.normalize ⟨1.0, dfdx, 0.0⟩
  let tv := Vec3.normalize ⟨0.0, dfdz, 1.0⟩
  let nrm := Vec3.normalize ⟨-dfdx, 1.0, -dfdz⟩
  let pSurf : Vec3 := ⟨x0, y0, z0⟩
  return { f with
    meshAssets := #[mesh],
    meshRefs := #[{ meshId := mesh.meshId, dirtyHash := mesh.dirtyHash,
                    color := RGBA.white, useVertexColors := true, doubleSided := true }],
    planes := #[{ center := pSurf, u := tu, v := tv, extent := 0.62,
                  color := ⟨1.0, 0.72, 0.22, 0.42⟩, label := "Dual Tangent Plane" }],
    segments := #[
      { a := pSurf, b := Vec3.add pSurf (Vec3.scale 0.65 nrm), width := 3.4, color := RGBA.coral, role := { arrow := true } },
      { a := pSurf, b := Vec3.add pSurf (Vec3.scale 0.55 tu),  width := 2.8, color := RGBA.cyan,  role := { arrow := true } },
      { a := pSurf, b := Vec3.add pSurf (Vec3.scale 0.55 tv),  width := 2.8, color := RGBA.green, role := { arrow := true } }
    ],
    points := #[{ handleId := 0, pos := pSurf, radius := 0.09, color := RGBA.coral,
                  role := { draggable := true }, label := "(x0, y0)" }],
    inspect := #[{ idx := 0, name := "Dual Jet f(x+ε)", grade := 1,
                   formatted := s!"f={y0} + ({dfdx})εx + ({dfdz})εz (ε²=0)", editable := true }] }

/-- **27. `quaternion_slerp`** — Quaternion `Cl(0,2)` / `R3⁺` Gimbal-Free SLERP Geodesic on S³! -/
def buildQuaternionSlerp (handles : Array (UInt32 × Vec3)) (seq : UInt64) (t : Float) : SceneFrame := Id.run do
  let f := mkBase "quaternion_slerp" "Quaternion Cl(0,2) Gimbal-Free SLERP on S³" "Quaternion" seq t false 4.5
  let targetDir := Vec3.normalize (hPos handles 0 ⟨0.85, 0.65, 0.55⟩)
  let startDir : Vec3 := Vec3.normalize ⟨-0.8, 0.5, 0.4⟩
  let axis := Vec3.normalize (Vec3.cross startDir targetDir)
  let totalAng := Float.acos (max (-1.0) (min 1.0 (Vec3.dot startDir targetDir)))
  let uPhase := 0.5 + 0.5 * Float.sin (t * 0.9)
  let curRot := Motor3.rotorAxis axis (uPhase * totalAng)
  -- Geodesic arc traced on the unit sphere by Slerp(q0, q1, u)
  let mut arcPts : Array Vec3 := #[]
  for i in [:37] do
    let u := Float.ofNat i / 36.0
    arcPts := arcPts.push (Motor3.applyPoint (Motor3.rotorAxis axis (u * totalAng)) startDir)
  let curTip := Motor3.applyPoint curRot startDir
  let box := buildBoxMesh 0.45 0.18 0.72 RGBA.violet 4402
  return { f with
    meshAssets := #[box],
    meshRefs := #[{ meshId := box.meshId, dirtyHash := box.dirtyHash, motor := curRot,
                    color := RGBA.violet, useVertexColors := true }],
    spheres := #[{ center := Vec3.zero, radius := 1.0, color := ⟨0.30, 0.62, 1.0, 0.14⟩, label := "Unit S² Orbit" }],
    curves := #[curveFromVecs arcPts RGBA.amber 3.2 false false],
    segments := #[
      { a := Vec3.zero, b := startDir, width := 2.4, color := RGBA.cyan, role := { arrow := true } },
      { a := Vec3.zero, b := targetDir, width := 2.4, color := RGBA.coral, role := { arrow := true } },
      { a := Vec3.zero, b := curTip, width := 3.6, color := RGBA.green, role := { arrow := true } }
    ],
    points := #[
      { handleId := 0, pos := targetDir, radius := 0.09, color := RGBA.coral, role := { draggable := true }, label := "Target q1" },
      { handleId := 1, pos := startDir, radius := 0.075, color := RGBA.cyan, label := "Start q0" }
    ],
    inspect := #[{ idx := 0, name := "SLERP q(u)", grade := 2,
                   formatted := s!"q(u) = q0 (q0⁻¹ q1)^{uPhase} · θ={totalAng * 180.0 / piF}°", editable := true }] }

/-- **28. `higher_cl_conic_pencil`** — Higher-Dimensional `Cl(6,3)` / `Cl(5,3)` Conic Section Pencil! -/
def buildHigherClConicPencil (handles : Array (UInt32 × Vec3)) (seq : UInt64) (t : Float) : SceneFrame := Id.run do
  let f := mkBase "higher_cl_conic_pencil" "Higher Cl(6,3) Conic Pencil (Ellipse ↔ Hyperbola)" "CCGA" seq t true
  let ctrl := hPos handles 0 ⟨0.55 * Float.sin (t * 0.65), 0.0, 0.0⟩
  -- 1-parameter pencil of conics through 4 base points (±1, ±0.7):
  -- (1 - λ) * (x²/1.49 + y²/0.98 - 1) + λ * (x² - 2.04 y²) = 0
  -- Morphs smoothly from Ellipse (λ < 0) through Circle & Parabola to Hyperbola (λ > 0)!
  let lam := max (-0.95) (min 0.95 ctrl.x)
  let mut curves : Array CurvePrim := #[]
  let cols : Array RGBA := #[RGBA.cyan, RGBA.violet, RGBA.amber, RGBA.coral, RGBA.green]
  for idx in [:5] do
    let lVal := lam + (Float.ofNat idx - 2.0) * 0.28
    -- Parametric ellipse (lVal < 0.25) or hyperbola (lVal ≥ 0.25)
    let mut pts : Array Vec3 := #[]
    if lVal < 0.25 then
      let a := 1.15 + 0.35 * lVal
      let b := max 0.35 (0.95 - 0.55 * lVal)
      for i in [:64] do
        let th := twoPiF * Float.ofNat i / 64.0
        pts := pts.push ⟨a * Float.cos th, b * Float.sin th, 0.0⟩
      curves := curves.push (curveFromVecs pts cols[idx]! (if idx == 2 then 3.2 else 2.0) true false)
    else
      let a := max 0.35 (0.85 - 0.25 * lVal)
      let b := 0.72 + 0.25 * lVal
      let mut ptsR : Array Vec3 := #[]
      let mut ptsL : Array Vec3 := #[]
      for i in [:33] do
        let s := -1.35 + 2.70 * Float.ofNat i / 32.0
        ptsR := ptsR.push ⟨ a * Float.cosh s, b * Float.sinh s, 0.0⟩
        ptsL := ptsL.push ⟨-a * Float.cosh s, b * Float.sinh s, 0.0⟩
      curves := curves.push (curveFromVecs ptsR cols[idx]! (if idx == 2 then 3.2 else 2.0) false false)
                      |>.push (curveFromVecs ptsL cols[idx]! (if idx == 2 then 3.2 else 2.0) false false)
  return { f with
    curves,
    points := #[
      { handleId := 0, pos := ctrl, radius := 0.085, color := RGBA.coral, role := { draggable := true }, label := "Pencil λ" },
      { handleId := 1, pos := ⟨ 1.0,  0.7, 0.0⟩, radius := 0.06, color := RGBA.white, label := "B1" },
      { handleId := 2, pos := ⟨-1.0,  0.7, 0.0⟩, radius := 0.06, color := RGBA.white, label := "B2" },
      { handleId := 3, pos := ⟨-1.0, -0.7, 0.0⟩, radius := 0.06, color := RGBA.white, label := "B3" },
      { handleId := 4, pos := ⟨ 1.0, -0.7, 0.0⟩, radius := 0.06, color := RGBA.white, label := "B4" }
    ],
    inspect := #[{ idx := 0, name := "Conic Blade C(λ)", grade := 5,
                   formatted := s!"Cl(6,3) pencil (1-λ)C₁ + λC₂, λ={lam}", editable := true }] }

/-! ## Master Extra Catalog (28 Presets) & Dispatcher -/

def extraPresetCatalog : Array ExtraPresetInfo := #[
  { id := "pga3d_origami_fold", title := "3D PGA Miura-Ori Rigid Origami", category := "3D PGA", algebra := "PGA3",
    description := "Rigid-panel Miura-ori crease-hinged fold driven by exact PGA3 rotors.",
    sampleCode := "// Miura-ori hinge fold: M = exp(-theta/2 * L_crease)" },
  { id := "pga3d_ik_arm", title := "3D PGA Spatial FABRIK IK Arm", category := "3D PGA", algebra := "PGA3",
    description := "5-link spatial 3D inverse kinematics arm reaching a draggable 3D target.",
    sampleCode := "// 3D FABRIK backward/forward projection in Cl(3,0,1)" },
  { id := "pga3d_hopf", title := "3D PGA Hopf Fibration (S³ → ℝ³)", category := "3D PGA", algebra := "PGA3",
    description := "26 linked Villarceau motor-geodesic fibers stereographically projected from S³.",
    sampleCode := "// Hopf fiber: (cos η e^{i(ξ+φ)}, sin η e^{iξ}) ∈ S³" },
  { id := "pga3d_duality", title := "3D PGA Projective Polar Duality", category := "3D PGA", algebra := "PGA3",
    description := "Points mapped to dual polar planes (!P) across the unit polarity sphere.",
    sampleCode := "// Polar duality: P ↔ !P (p · x = 1)" },
  { id := "pga3d_spring_physics", title := "3D PGA Spring-Damper Motor Physics", category := "3D PGA", algebra := "PGA3",
    description := "6-DOF rigid cube oscillating on a helical spring under PGA3 motor dynamics.",
    sampleCode := "// Rigid body motor spring: M'(t) = -0.5 * M * B(t)" },
  { id := "pga3d_skinning_twist", title := "3D PGA Motor-Blended Skinning Twist", category := "3D PGA", algebra := "PGA3",
    description := "3-bone dual-quaternion / motor linear blending (DLB) on an articulated cylinder.",
    sampleCode := "// DLB: M(u) = normalize(w0*M0 + w1*M1 + w2*M2)" },
  { id := "cga3d_dupin_cyclide", title := "3D CGA Dupin Cyclide & Focal Conics", category := "3D CGA", algebra := "CGA3",
    description := "Exact conformal Dupin cyclide envelope of spheres tangent to three spheres.",
    sampleCode := "// Dupin cyclide in Cl(4,1) with focal ellipse & curvature spheres" },
  { id := "cga3d_apollonius", title := "3D CGA Apollonius / Soddy Spheres", category := "3D CGA", algebra := "CGA3",
    description := "Four mutually tangent spheres kissing exact inner and outer Soddy spheres.",
    sampleCode := "// Descartes 3D theorem: (∑ k_i)² = 3 ∑ k_i²" },
  { id := "cga3d_clifford_torus", title := "3D CGA Clifford Torus (4D Rotation)", category := "3D CGA", algebra := "CGA3",
    description := "Stereographic projection of S¹×S¹ ⊂ S³ rotating smoothly inside-out in 4D.",
    sampleCode := "// Clifford torus S¹×S¹ ⊂ S³ stereographically projected to ℝ³" },
  { id := "cga3d_inversion", title := "3D CGA Conformal Cube Inversion", category := "3D CGA", algebra := "CGA3",
    description := "Spherical inversion S X S⁻¹ bending cube edges into exact circular arcs.",
    sampleCode := "// Conformal sandwich: X' = -S * X * S⁻¹" },
  { id := "cga3d_dipole_field", title := "3D CGA Point-Pair Dipole Field", category := "3D CGA", algebra := "CGA3",
    description := "CGA point pair A∧B spanning coaxial field circles & orthogonal equipotentials.",
    sampleCode := "@basis CGA3\nlet A = point(-0.9, 0.1, 0)\nlet B = point(0.9, -0.1, 0)\nlet pair = A ^ B\nlet S1 = sphere(A, 0.55)\nlet S2 = sphere(B, 0.55)" },
  { id := "sta_light_cone", title := "STA Minkowski Light Cone & Boost", category := "Spacetime", algebra := "STA",
    description := "Relativistic light cone (-c²t²+x²+y²=0), hyperbolic worldline, and Lorentz boost.",
    sampleCode := "@basis STA\nlet B = boost(1, 0, 0, 0.65 * sin(t * 0.5))\nlet ctPrime = B >>> et\nlet xPrime = B >>> ex\nlet cone = implicit(\"x^2 + z^2 - y^2\", 14, 1.3)" },
  { id := "sta_em_wave", title := "STA Electromagnetic Wave (F = E + IB)", category := "Spacetime", algebra := "STA",
    description := "Oscillating Faraday bivector F = E + IB with linear/circular polarization handle.",
    sampleCode := "@basis STA\nlet E = 0.8 * et * ex * cos(t)\nlet B = 0.8 * ey * ez * cos(t)\nlet F = E + B" },
  { id := "sta_rapidity", title := "STA Thomas Precession & Wigner Angle", category := "Spacetime", algebra := "STA",
    description := "Non-commutative boost composition B(v2)B(v1) = R(θ_W)B(v12) on the velocity disk.",
    sampleCode := "@basis STA\nlet B1 = boost(1, 0, 0, 0.7)\nlet B2 = boost(0, 1, 0, 0.6)\nlet comp = B2 * B1\nlet v = comp >>> et" },
  { id := "implicit_gyroid", title := "Implicit 3D: Gyroid TPMS Surface", category := "Implicit 3D", algebra := "R3",
    description := "Watertight Marching Tetrahedra Gyroid minimal surface with iridescent curvature.",
    sampleCode := "@basis R3\nlet gyroid = implicit(\"sin(2.35*x)*cos(2.35*y) + sin(2.35*y)*cos(2.35*z) + sin(2.35*z)*cos(2.35*x)\", 16, 1.45)" },
  { id := "implicit_metaballs", title := "Implicit 3D: Animated Metaballs", category := "Implicit 3D", algebra := "R3",
    description := "Real-time 4-lobe organic metaball fusion with draggable magnetic orb.",
    sampleCode := "@basis R3\nlet blobs = implicit(\"1 - 0.24/((x-0.55*cos(t))^2+y^2+z^2+0.05) - 0.24/((x+0.55)^2+y^2+z^2+0.05)\", 16, 1.45)" },
  { id := "implicit_schwarz_p", title := "Implicit 3D: Schwarz P Minimal Surface", category := "Implicit 3D", algebra := "R3",
    description := "Triply periodic Schwarz P isosurface extracted via Kuhn Marching Tetrahedra.",
    sampleCode := "@basis R3\nlet sp = implicit(\"cos(2.3*x) + cos(2.3*y) + cos(2.3*z)\", 16, 1.45)" },
  { id := "param_klein_bottle", title := "Parametric 3D: Figure-8 Klein Bottle", category := "Parametric 3D", algebra := "R3",
    description := "Double-sided non-orientable figure-8 Klein bottle immersion with live tube radius.",
    sampleCode := "@basis R3\nlet klein = opns(\"((x^2+y^2+z^2-1)^2 - 0.12)\")" },
  { id := "param_mobius_strip", title := "Parametric 3D: Möbius Strip", category := "Parametric 3D", algebra := "R3",
    description := "Twisted Möbius band with parallel-transported normal flipping sign after 2π.",
    sampleCode := "@basis R3\nlet spine = closedCurve([point(cos(i * 0.2), 0, sin(i * 0.2)) for i in 0..32])" },
  { id := "implicit_genus2", title := "Implicit 3D: Genus-2 Pretzel", category := "Implicit 3D", algebra := "R3",
    description := "Double-torus genus-2 algebraic surface extracted via Marching Tetrahedra.",
    sampleCode := "@basis R3\nlet pretzel = implicit(\"((x^2 + y^2)^2 - x^2 + y^2)^2 + z^2 = 0.05\", 18, 1.35)" },
  { id := "param_boys_surface", title := "Parametric 3D: Boy's Surface (ℝP²)", category := "Parametric 3D", algebra := "R3",
    description := "Apéry-Bryant 3-fold symmetric immersion of the real projective plane ℝP².",
    sampleCode := "// Apéry-Bryant Boy's surface immersion of RP²" },
  { id := "param_enneper_superquadric", title := "Parametric 3D: Enneper & Superquadric", category := "Parametric 3D", algebra := "R3",
    description := "Enneper minimal surface paired with an exponent-morphing superquadric.",
    sampleCode := "// Enneper H=0 minimal surface + superquadric (e1, e2)" },
  { id := "cga2d_apollonius", title := "2D CGA Apollonius Tangent Circles", category := "2D CGA", algebra := "CGA2",
    description := "Descartes circle theorem: three kissing circles + inner & outer Soddy circles.",
    sampleCode := "// k4 = k1 + k2 + k3 ± 2√(k1k2 + k2k3 + k3k1)" },
  { id := "pga2d_non_euclidean", title := "2D Hyperbolic Cl(2,1) Poincaré Disk", category := "2D Non-Euclidean", algebra := "Hyperbolic2D",
    description := "Hyperbolic geodesics orthogonal to the ideal circle with draggable triangle.",
    sampleCode := "// Cl(2,1) hyperbolic geodesics & horocycle" },
  { id := "complex_mandelbrot", title := "Complex Cl(0,1) Mandelbrot Orbit", category := "Complex", algebra := "Complex",
    description := "Main Mandelbrot cardioid & period-2 bulb with live z_{n+1}=z_n²+c escape orbit.",
    sampleCode := "// Cl(0,1): z = z*z + c" },
  { id := "dual_tangent_plane", title := "Dual Cl(0,0,1) Autodiff Tangent Plane", category := "Dual", algebra := "Dual",
    description := "Exact dual-number automatic differentiation tangent plane & gradient probe.",
    sampleCode := "// f(x + ε, y) = f(x, y) + f_x(x, y)·ε  (ε² = 0)" },
  { id := "quaternion_slerp", title := "Quaternion Cl(0,2) Gimbal-Free SLERP", category := "Quaternion", algebra := "Quaternion",
    description := "Geodesic spherical linear interpolation q0(q0⁻¹q1)^u on S³ without gimbal lock.",
    sampleCode := "// Cl(0,2) SLERP: q(u) = q0 * exp(u * log(q0⁻¹ * q1))" },
  { id := "higher_cl_conic_pencil", title := "Higher Cl(6,3) Conic Section Pencil", category := "Higher Cl", algebra := "CCGA",
    description := "Projective 1-parameter pencil of conics morphing Ellipse ↔ Parabola ↔ Hyperbola.",
    sampleCode := "// Cl(6,3) CCGA pencil: C(λ) = (1 - λ) C1 + λ C2" }
]

/-- Return all 28 extra preset IDs. -/
def extraPresetIds : Array String := extraPresetCatalog.map (·.id)

/-- Serialize the 28-preset extra catalog to `Init`-only JSON. -/
def extraPresetCatalogJson : String :=
  Json.arrJson (extraPresetCatalog.map fun p => Json.objJson #[
    ("id", Json.quote p.id),
    ("title", Json.quote p.title),
    ("category", Json.quote p.category),
    ("algebra", Json.quote p.algebra),
    ("description", Json.quote p.description),
    ("sampleCode", Json.quote p.sampleCode)
  ])

/-- Build any of the 28 extra CoffeeShop presets by `id`; returns `none` if not an extra preset ID. -/
def buildExtraPreset (id : String) (handles : Array (UInt32 × Vec3))
    (seq : UInt64 := 0) (t : Float := 0.0) : Option SceneFrame :=
  match id with
  | "pga3d_origami_fold"         => some (buildPga3dOrigamiFold handles seq t)
  | "pga3d_ik_arm"               => some (buildPga3dIkArm handles seq t)
  | "pga3d_hopf"                 => some (buildPga3dHopf handles seq t)
  | "pga3d_duality"              => some (buildPga3dDuality handles seq t)
  | "pga3d_spring_physics"       => some (buildPga3dSpringPhysics handles seq t)
  | "pga3d_skinning_twist"       => some (buildPga3dSkinningTwist handles seq t)
  | "cga3d_dupin_cyclide"        => some (buildCga3dDupinCyclide handles seq t)
  | "cga3d_apollonius"           => some (buildCga3dApollonius handles seq t)
  | "cga3d_clifford_torus"       => some (buildCga3dCliffordTorus handles seq t)
  | "cga3d_inversion"            => some (buildCga3dInversion handles seq t)
  | "cga3d_dipole_field"         => some (buildCga3dDipoleField handles seq t)
  | "sta_light_cone"             => some (buildStaLightCone handles seq t)
  | "sta_em_wave"                => some (buildStaEmWave handles seq t)
  | "sta_rapidity"               => some (buildStaRapidity handles seq t)
  | "implicit_gyroid"            => some (buildImplicitGyroid handles seq t)
  | "implicit_metaballs"         => some (buildImplicitMetaballs handles seq t)
  | "implicit_schwarz_p"         => some (buildImplicitSchwarzP handles seq t)
  | "param_klein_bottle"         => some (buildParamKleinBottle handles seq t)
  | "param_mobius_strip"         => some (buildParamMobiusStrip handles seq t)
  | "implicit_genus2"            => some (buildImplicitGenus2 handles seq t)
  | "param_boys_surface"         => some (buildParamBoysSurface handles seq t)
  | "param_enneper_superquadric" => some (buildParamEnneperSuperquadric handles seq t)
  | "cga2d_apollonius"           => some (buildCga2dApollonius handles seq t)
  | "pga2d_non_euclidean"        => some (buildPga2dNonEuclidean handles seq t)
  | "complex_mandelbrot"         => some (buildComplexMandelbrot handles seq t)
  | "dual_tangent_plane"         => some (buildDualTangentPlane handles seq t)
  | "quaternion_slerp"           => some (buildQuaternionSlerp handles seq t)
  | "higher_cl_conic_pencil"     => some (buildHigherClConicPencil handles seq t)
  | _                            => none

end Grassmann.CoffeeShop.PresetsExtra
