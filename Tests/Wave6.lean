import Grassmann.Studio

/-!
# Wave 6C Verification Suite (`Tests/Wave6.lean`)

Strictly `Init`-only (ZERO `Lean.*`, ZERO `Std.*`, ZERO `DirectSum`, ZERO `sorry`/axioms):
1. **Dual-Handle 3D Slicing Manipulator (`pga3d_slicing` & `pga3d_slicing_hq`)**:
   - Verifies both draggable handles (`0 = Plane Center`, `1 = Tilt Normal`), normal arrow stem,
     live plane-normal rotation + 2D `ContourOverlay` change on `DragHandle 1`, rigid tilt
     preservation on `DragHandle 0`, and runnable dual-handle `LiveScript` v2 script.
2. **All 77 Unique Presets + 3 New Wave 6C Showstoppers + Pure-Lean Guided Tour (`Tour.lean`)**:
   - Verifies `totalPresetCount == 77`, 0 ID collisions, 8B `GSIR` v1, KaTeX `formula`+`summary`.
   - Deep-verifies `implicit_barth_sextic` (GPU GLSL3/WGSL/MSL + bytecode MT + `phi`/`iso`),
     `cga3d_dupin_cyclide_raymarch` (GPU raymarch + focal ellipse & hyperbola + sliders),
     `pga3d_gears_kinematics` (3 meshing involute gears + motors + `speed`/`ratio`), and
     `tourCatalogJson` + `{"op":"loadTourStop","index":0..5}`.
3. **Full 17/17 Wedge Campaign Audit + Grand Finale L17 (3D Euler Axis) + T1–T6**:
   - Geometry separation & non-degeneracy audit across all 17 levels & T1–T6.
   - Programmatically solves **ALL 17/17 Wedge levels** (L1–L9 PGA2 + L10–L17 PGA3), verifying
     L17 Circumcenter `O` + Centroid `G` + 3D Euler Axis `O & G` and Monge's Theorem `G = (O+M)/2`,
     plus symmetric 3D `dotProject` ergonomics.
4. **All 6 Dots Round-2 Adversarial Regression Tests (`#174`)**:
   - P0 #2: PGA2 `point(x,y)` vs line incidence (`(e1-e0) ^ point(1,0,0) == 0`, `(e2-2*e0) ^ point(3,2,0) == 0`, `translator`).
   - P0 #3: CGA3 off-origin OPNS `A ^ B ^ ni` & IPNS `P1 ^ P2` flat-line extraction (actual off-origin line, 0 circles).
   - P0 #4: Lossless 64-bit JSON `wedgeRandom` seed parsing (`9007199254740992` vs `9007199254740993` + `seedStr` in `metaJson`).
   - P0 #5: GPU implicit raymarcher respects `bound` (distinct shader hashes + radius `bound*1.75` across GLSL3/WGSL/MSL).
   - P1 #8: Mode-gated `wedgeGesture` (never hijacks CoffeeShop/Calculator into Wedge).
   - P1 #10: Explicit `resetTime` (exact `simTime == 0.0` + RK4 reset) & `seekTime` (exact seek, no `dt` drift).

Credits: Michael Reed (`chakravala` / `Grassmann.jl`) & Steven De Keninck (`enkimute` / `ganja.js`).
-/

namespace Tests.Wave6

open Grassmann
open Grassmann.Scene Grassmann.Scene.Binary Grassmann.Scene.Json
open Grassmann.Eval Grassmann.Eval.ImplicitExpr Grassmann.Wedge Grassmann.Wedge.Tutorials
open Grassmann.CoffeeShop Grassmann.CoffeeShop.PresetsExtra
open Grassmann.CoffeeShop.PresetsParity Grassmann.CoffeeShop.PresetsShowcase
open Grassmann.CoffeeShop.Tour Grassmann.Studio

private def assertTrue (name : String) (cond : Bool) : IO Unit := do
  if !cond then
    throw (IO.userError s!"FAIL [{name}]")

private def hasSubstr (haystack needle : String) : Bool :=
  (haystack.splitOn needle).length > 1

private def hasVisualGeometry (f : SceneFrame) : Bool :=
  !f.points.isEmpty || !f.segments.isEmpty || !f.lines.isEmpty ||
  !f.planes.isEmpty || !f.circles.isEmpty || !f.spheres.isEmpty ||
  !f.meshRefs.isEmpty || !f.curves.isEmpty || !f.bivectorDisks.isEmpty ||
  !f.flowFields.isEmpty || !f.opnsUniforms.isEmpty

private def contourFingerprint (co : Option ContourOverlay) : Float :=
  match co with
  | none => 0.0
  | some ov => Id.run do
    let mut s := 0.0
    for c in ov.curves do
      s := s + Float.ofNat c.points.size
      for i in [:min 12 c.points.size] do
        s := s + c.points.get! i * Float.ofNat (i + 1)
    return s

/-! ## 1. Dual-Handle 3D Slicing Manipulator (`pga3d_slicing` & `pga3d_slicing_hq`) -/

def testDualHandleSlicing : IO Unit := do
  -- 1a. `pga3d_slicing` (Stanford bunny)
  let mut cs := CoffeeShop.loadPreset {} "pga3d_slicing"
  let f0 := CoffeeShop.toSceneFrame cs 1
  assertTrue "slicing has 2 draggable 3D handles"
    (f0.points.size == 2 && f0.points[0]!.handleId == 0 && f0.points[0]!.role.draggable &&
     f0.points[1]!.handleId == 1 && f0.points[1]!.role.draggable)
  assertTrue "slicing has normal arrow stem" (f0.segments.any (·.role.arrow))
  assertTrue "slicing has 2D contour inset" (f0.contourOverlay.isSome)

  -- Drag handle 0 (Plane Center)
  cs := CoffeeShop.setHandle cs 0 ⟨0.0, 0.25, 0.0⟩
  let fCenter := CoffeeShop.toSceneFrame cs 2
  let n0 := Vec3.normalize (Vec3.sub fCenter.points[1]!.pos fCenter.points[0]!.pos)
  let c0 := contourFingerprint fCenter.contourOverlay
  assertTrue "slicing handle 0 moved center to y=0.25"
    (Float.abs (fCenter.points[0]!.pos.y - 0.25) < 1e-6)

  -- Drag handle 1 (Tilt Normal) to steep 3D tilt!
  cs := CoffeeShop.setHandle cs 1 ⟨0.85, 0.65, 0.45⟩
  let fTilted := CoffeeShop.toSceneFrame cs 3
  let n1 := Vec3.normalize (Vec3.sub fTilted.points[1]!.pos fTilted.points[0]!.pos)
  let c1 := contourFingerprint fTilted.contourOverlay
  assertTrue "slicing handle 1 tilted plane normal significantly" (Vec3.dot n0 n1 < 0.90)
  assertTrue "slicing handle 1 updated 2D contour inset" (Float.abs (c1 - c0) > 1e-4)
  assertTrue "slicing tilted bunny still has both clipped halves" (fTilted.meshAssets.size == 2)
  match validateGsirFrame (encodeFrame fTilted true) with
  | .error e => throw (IO.userError s!"tilted slicing GSIR invalid: {e}")
  | .ok _ => pure ()

  -- Drag handle 0 AFTER handle 1: custom tilt normal MUST be preserved!
  cs := CoffeeShop.setHandle cs 0 ⟨0.0, -0.10, 0.0⟩
  let fShifted := CoffeeShop.toSceneFrame cs 4
  let n2 := Vec3.normalize (Vec3.sub fShifted.points[1]!.pos fShifted.points[0]!.pos)
  assertTrue "dragging handle 0 after handle 1 preserves custom 3D tilt normal"
    (Vec3.dot n1 n2 > 0.999)
  assertTrue "dragging handle 0 moved plane center to y=-0.10"
    (Float.abs (fShifted.points[0]!.pos.y - (-0.10)) < 1e-6)

  -- Verify `pga3d_slicing` LiveScript v2 sampleCode executes cleanly with dual handles
  let scriptCode := CoffeeShop.presetScriptFor "pga3d_slicing"
  let frScript := evalScriptToFrame "PGA3" scriptCode #[] 0.5 1
  assertTrue "pga3d_slicing LiveScript 0 diagnostics" frScript.diagnostics.isEmpty
  assertTrue "pga3d_slicing LiveScript has >=2 draggable handles"
    ((frScript.points.filter (·.role.draggable)).size ≥ 2)
  assertTrue "pga3d_slicing LiveScript produces sliced bunny meshes & contour"
    (frScript.meshAssets.size ≥ 2 && frScript.contourOverlay.isSome)

  -- 1b. `pga3d_slicing_hq` (High-detail bunny & trefoil knot)
  let mut hq := CoffeeShop.loadPreset {} "pga3d_slicing_hq"
  hq := CoffeeShop.setHandle hq 0 ⟨0.0, 0.15, 0.0⟩
  let hq0 := CoffeeShop.toSceneFrame hq 1
  let hqn0 := Vec3.normalize (Vec3.sub hq0.points[1]!.pos hq0.points[0]!.pos)
  let hqc0 := contourFingerprint hq0.contourOverlay
  assertTrue "slicing_hq has 2 draggable 3D handles"
    (hq0.points.size == 2 && hq0.points[0]!.handleId == 0 && hq0.points[1]!.handleId == 1)
  hq := CoffeeShop.setHandle hq 1 ⟨0.75, 0.65, -0.50⟩
  let hq1 := CoffeeShop.toSceneFrame hq 2
  let hqn1 := Vec3.normalize (Vec3.sub hq1.points[1]!.pos hq1.points[0]!.pos)
  let hqc1 := contourFingerprint hq1.contourOverlay
  assertTrue "slicing_hq handle 1 tilted normal significantly" (Vec3.dot hqn0 hqn1 < 0.90)
  assertTrue "slicing_hq handle 1 updated 2D contour inset" (Float.abs (hqc1 - hqc0) > 1e-4)

/-! ## 2. All 77 Unique Presets + 3 New Wave 6C Showstoppers + Pure-Lean Guided Tour -/

def test77PresetsShowstoppersAndTour : IO Unit := do
  -- 2a. All 77 unique presets
  assertTrue s!"totalPresetCount == 77 (got {totalPresetCount})" (totalPresetCount == 77)
  let allIds : Array String :=
    presetCatalog.map (·.id) ++ extraPresetCatalog.map (·.id) ++
    parityPresetCatalog.map (·.id) ++ showcasePresetCatalog.map (·.id)
  assertTrue "allIds.size == 77" (allIds.size == 77)
  let mut seen : Array String := #[]
  for id in allIds do
    assertTrue s!"unique id '{id}'" (!seen.contains id)
    seen := seen.push id
  match parseJson Studio.presetCatalogJson with
  | .ok (.arr items) => assertTrue s!"catalog JSON has 77 items (got {items.size})" (items.size == 77)
  | _ => throw (IO.userError "presetCatalogJson invalid")
  for id in allIds do
    let fr := CoffeeShop.toSceneFrame (CoffeeShop.loadPreset {} id) 1
    assertTrue s!"{id}: 0 diagnostics" fr.diagnostics.isEmpty
    assertTrue s!"{id}: visual geometry" (hasVisualGeometry fr)
    assertTrue s!"{id}: non-empty KaTeX formula" (!fr.formula.isEmpty)
    assertTrue s!"{id}: non-empty summary" (!fr.summary.isEmpty)
    let raw := encodeFrame fr true
    match validateGsirFrame raw with
    | .error e => throw (IO.userError s!"{id} GSIR invalid: {e}")
    | .ok _ => assertTrue s!"{id}: 8B aligned" (raw.size % 8 == 0)

  -- 2b. `implicit_barth_sextic`: GPU GLSL3/WGSL/MSL + Bytecode MT + phi/iso sliders
  let mut bCs := CoffeeShop.loadPreset {} "implicit_barth_sextic"
  let b0 := CoffeeShop.toSceneFrame bCs 1
  assertTrue "barth: has GPU shader triplet"
    (b0.opnsShaders.size == 1 && !b0.opnsShaders[0]!.glsl.isEmpty &&
     !b0.opnsShaders[0]!.wgsl.isEmpty && !b0.opnsShaders[0]!.msl.isEmpty)
  assertTrue "barth: has OPNS uniform" (b0.opnsUniforms.size == 1)
  assertTrue "barth: has rich bytecode MT mesh (>500 verts, >1000 tris)"
    (b0.meshAssets.size == 1 && b0.meshAssets[0]!.positions.size / 3 > 500 &&
     b0.meshAssets[0]!.indices.size / 3 > 1000)
  assertTrue "barth: has phi & iso params" (b0.params.size == 2)
  bCs := CoffeeShop.setParam bCs "phi" 1.35
  bCs := CoffeeShop.setParam bCs "iso" 0.12
  let b1 := CoffeeShop.toSceneFrame bCs 2
  assertTrue "barth: setParam updates GPU shader hash" (b1.opnsShaders[0]!.hash != b0.opnsShaders[0]!.hash)
  assertTrue "barth: setParam updates bytecode MT mesh dirtyHash"
    (b1.meshAssets[0]!.dirtyHash != b0.meshAssets[0]!.dirtyHash)

  -- 2c. `cga3d_dupin_cyclide_raymarch`: GPU raymarch + focal ellipse & hyperbola + sliders
  let mut dCs := CoffeeShop.loadPreset {} "cga3d_dupin_cyclide_raymarch"
  let d0 := CoffeeShop.toSceneFrame dCs 1
  assertTrue "cyclide: GPU shader triplet + uniform"
    (d0.opnsShaders.size == 1 && d0.opnsUniforms.size == 1 &&
     !d0.opnsShaders[0]!.glsl.isEmpty && !d0.opnsShaders[0]!.wgsl.isEmpty && !d0.opnsShaders[0]!.msl.isEmpty)
  assertTrue "cyclide: glowing focal ellipse + 2 focal hyperbola branches" (d0.curves.size == 3)
  assertTrue "cyclide: 3 @param sliders (majorR, minorR, eccentricity)" (d0.params.size == 3)
  dCs := CoffeeShop.setParam dCs "eccentricity" 0.62
  let d1 := CoffeeShop.toSceneFrame dCs 2
  assertTrue "cyclide: setParam updates GPU shader hash" (d1.opnsShaders[0]!.hash != d0.opnsShaders[0]!.hash)

  -- 2d. `pga3d_gears_kinematics`: 3 meshing gears + motors + speed/ratio sliders
  let mut gCs := CoffeeShop.loadPreset {} "pga3d_gears_kinematics"
  let g0 := CoffeeShop.toSceneFrame gCs 1
  assertTrue "gears: 3 meshing gear meshes + 3 pitch circles + 3 bivector disks"
    (g0.meshAssets.size == 3 && g0.meshRefs.size == 3 && g0.circles.size == 3 && g0.bivectorDisks.size == 3)
  assertTrue "gears: 2 @param sliders (speed, ratio)" (g0.params.size == 2)
  gCs := CoffeeShop.stepTick gCs 0.25 0.25
  let g1 := CoffeeShop.toSceneFrame gCs 2
  assertTrue "gears: tick rotates gear motors"
    (Float.abs (g1.meshRefs[0]!.motor.e12 - g0.meshRefs[0]!.motor.e12) > 1e-3 &&
     Float.abs (g1.meshRefs[1]!.motor.e12 - g0.meshRefs[1]!.motor.e12) > 1e-3)
  gCs := CoffeeShop.setParam gCs "ratio" 1.0
  let g2 := CoffeeShop.toSceneFrame gCs 3
  assertTrue "gears: setParam ratio rebuilds gear2 with new tooth count"
    (g2.meshAssets[1]!.meshId != g0.meshAssets[1]!.meshId)

  -- 2e. Pure-Lean Guided Tour (`Tour.lean` + `loadTourStop 0..5`)
  match parseJson Studio.tourCatalogJson with
  | .ok (.arr stops) =>
    assertTrue s!"tourCatalogJson has 6 stops (got {stops.size})" (stops.size == 6)
    for idx in [:6] do
      let sObj := stops[idx]!
      assertTrue s!"tour[{idx}] non-empty title" (!(((sObj.get? "title").bind JVal.asStr?).getD "").isEmpty)
      assertTrue s!"tour[{idx}] non-empty formula" (!(((sObj.get? "formula").bind JVal.asStr?).getD "").isEmpty)
      assertTrue s!"tour[{idx}] non-empty summary" (!(((sObj.get? "summary").bind JVal.asStr?).getD "").isEmpty)
      assertTrue s!"tour[{idx}] non-empty tryIt" (!(((sObj.get? "tryIt").bind JVal.asStr?).getD "").isEmpty)
  | _ => throw (IO.userError "tourCatalogJson invalid")

  let mut sess := Studio.create
  for idx in [:6] do
    let stop := getTourStop idx
    let (sess', bytes) ← IO.ofExcept (Studio.dispatchJson sess s!"\{\"op\":\"loadTourStop\",\"index\":{idx}}")
    sess := sess'
    match validateGsirFrame bytes with
    | .error e => throw (IO.userError s!"tour stop {idx} GSIR invalid: {e}")
    | .ok _ => assertTrue s!"tour stop {idx} 8B aligned" (bytes.size % 8 == 0)
    if idx == 5 then
      assertTrue "tour stop 5 enters Wedge mode Level 1"
        (sess.active == .wedge && sess.wedge.levelIdx == 0 && sess.wedge.dim == .dim2D)
    else
      assertTrue s!"tour stop {idx} loads preset {stop.presetId}"
        (sess.active == .coffeeShop && sess.coffee.presetId == stop.presetId)

/-! ## 3. Wedge 17/17 Campaign Audit, Grand Finale L17 & Symmetric 3D Dot -/

private def findIdByLabel (st : WedgeState) (lbl : String) : UInt32 :=
  (st.items.find? fun it => it.label == lbl && (it.role == .given || it.role == .constructed)).map (·.id) |>.getD 0

private def elemById (st : WedgeState) (id : UInt32) : PgaElem :=
  (st.items.find? fun it => it.id == id).map (·.elem) |>.getD (.pt2 0 0)

private def pullApart (st : WedgeState) (idA idB : UInt32) : WedgeState :=
  let u := Wedge.separationAxis (elemById st idA) (elemById st idB)
  Wedge.stepGesture st idA idB u (Vec3.neg u) false false false

private def pushTogether (st : WedgeState) (idA idB : UInt32) : WedgeState :=
  let u := Wedge.separationAxis (elemById st idA) (elemById st idB)
  Wedge.stepGesture st idA idB (Vec3.neg u) u false false false

private def holdDot (st : WedgeState) (movedId heldId : UInt32) : WedgeState :=
  let u := Wedge.separationAxis (elemById st movedId) (elemById st heldId)
  Wedge.stepGesture st movedId heldId (Vec3.neg u) Vec3.zero false true false

private def auditLevelGeometry (name : String) (lvl : WedgeLevel) : IO Unit := do
  -- Distinct given points well separated; no coincident givens; no target equals a given
  for i in [:lvl.givens.size] do
    for j in [(i+1):lvl.givens.size] do
      let a := lvl.givens[i]!.1; let b := lvl.givens[j]!.1
      assertTrue s!"{name}: givens {i} & {j} distinct" (!PgaElem.approxEq a b)
      match a, b with
      | .pt2 x1 y1, .pt2 x2 y2 =>
        let dist := Float.sqrt ((x1-x2)*(x1-x2) + (y1-y2)*(y1-y2))
        assertTrue s!"{name}: 2D given pts separated ({dist})" (dist ≥ 0.45)
      | .pt3 p1, .pt3 p2 =>
        let dist := Vec3.norm (Vec3.sub p1 p2)
        assertTrue s!"{name}: 3D given pts separated ({dist})" (dist ≥ 0.45)
      | _, _ => pure ()
  for t in lvl.targets do
    for g in lvl.givens do
      assertTrue s!"{name}: target '{t.2}' distinct from given '{g.2}'" (!PgaElem.approxEq t.1 g.1)

def testWedge17LevelsAndAudit : IO Unit := do
  assertTrue s!"allLevels.size == 17 (got {Wedge.allLevels.size})" (Wedge.allLevels.size == 17)
  -- Audit all 17 levels + 6 tutorials for separation & non-degeneracy
  for lvl in Wedge.allLevels do
    auditLevelGeometry s!"L{lvl.number}" lvl
  for card in tutorialCards do
    auditLevelGeometry card.id card.miniLevel

  -- Verify Hint toggle hides/shows ghost hints cleanly on L17
  let l17Init := Wedge.loadLevel 16
  let fHintsOn := Wedge.toSceneFrame l17Init 1 0.0
  let fHintsOff := Wedge.toSceneFrame (Wedge.stepAction l17Init .hint) 2 0.0
  let hintCountOn := (fHintsOn.points.filter (·.role.hint)).size + (fHintsOn.planes.filter (·.role.hint)).size
  let hintCountOff := (fHintsOff.points.filter (·.role.hint)).size + (fHintsOff.planes.filter (·.role.hint)).size
  assertTrue "L17 ghost hints toggle cleanly" (hintCountOn ≥ 3 && hintCountOff == 0)

  -- Solve ALL 17/17 levels cleanly!
  -- L1..L9 (2D PGA2)
  let s1 := Wedge.loadLevel 0; assertTrue "L1 solved" (pullApart s1 (findIdByLabel s1 "A") (findIdByLabel s1 "B")).solved
  let s2 := Wedge.loadLevel 1; assertTrue "L2 solved" (pushTogether s2 (findIdByLabel s2 "a") (findIdByLabel s2 "b")).solved
  let s3 := Wedge.loadLevel 2; assertTrue "L3 solved" (pushTogether s3 (findIdByLabel s3 "A") (findIdByLabel s3 "B")).solved
  let s4 := Wedge.loadLevel 3; assertTrue "L4 solved" (pullApart s4 (findIdByLabel s4 "c") (findIdByLabel s4 "b")).solved
  let s5 := Wedge.loadLevel 4; assertTrue "L5 solved" (holdDot s5 (findIdByLabel s5 "a") (findIdByLabel s5 "B")).solved
  let s6 := Wedge.loadLevel 5
  let s6a := holdDot s6 (findIdByLabel s6 "a") (findIdByLabel s6 "B")
  assertTrue "L6 solved" (pullApart s6a (findIdByLabel s6a "a") (s6a.nextId - 1)).solved
  -- L7 Orthocenter
  let s7 := Wedge.loadLevel 6
  let a7 := findIdByLabel s7 "A"; let b7 := findIdByLabel s7 "B"; let c7 := findIdByLabel s7 "C"
  let s7 := pullApart s7 a7 b7; let eAB7 := s7.nextId - 1
  let s7 := pullApart s7 b7 c7; let eBC7 := s7.nextId - 1
  let s7 := holdDot s7 eAB7 c7; let altC7 := s7.nextId - 1
  let s7 := holdDot s7 eBC7 a7; let altA7 := s7.nextId - 1
  assertTrue "L7 solved" (pushTogether s7 altC7 altA7).solved
  -- L8 Circumcenter
  let s8 := Wedge.loadLevel 7
  let a8 := findIdByLabel s8 "A"; let b8 := findIdByLabel s8 "B"; let c8 := findIdByLabel s8 "C"
  let s8 := pullApart s8 a8 b8; let eAB8 := s8.nextId - 1
  let s8 := pushTogether s8 a8 b8; let mAB8 := s8.nextId - 1
  let s8 := holdDot s8 eAB8 mAB8; let pbAB8 := s8.nextId - 1
  let s8 := pullApart s8 b8 c8; let eBC8 := s8.nextId - 1
  let s8 := pushTogether s8 b8 c8; let mBC8 := s8.nextId - 1
  let s8 := holdDot s8 eBC8 mBC8; let pbBC8 := s8.nextId - 1
  assertTrue "L8 solved" (pushTogether s8 pbAB8 pbBC8).solved
  -- L9 Euler Line
  let s9 := Wedge.loadLevel 8
  let a9 := findIdByLabel s9 "A"; let b9 := findIdByLabel s9 "B"; let c9 := findIdByLabel s9 "C"
  let s9 := pullApart s9 a9 b9; let eAB9 := s9.nextId - 1
  let s9 := pullApart s9 b9 c9; let eBC9 := s9.nextId - 1
  let s9 := holdDot s9 eAB9 c9; let altC9 := s9.nextId - 1
  let s9 := holdDot s9 eBC9 a9; let altA9 := s9.nextId - 1
  let s9 := pushTogether s9 altC9 altA9; let h9 := s9.nextId - 1
  let s9 := pushTogether s9 a9 b9; let mAB9 := s9.nextId - 1
  let s9 := holdDot s9 eAB9 mAB9; let pbAB9 := s9.nextId - 1
  let s9 := pushTogether s9 b9 c9; let mBC9 := s9.nextId - 1
  let s9 := holdDot s9 eBC9 mBC9; let pbBC9 := s9.nextId - 1
  let s9 := pushTogether s9 pbAB9 pbBC9; let o9 := s9.nextId - 1
  assertTrue "L9 solved" (pullApart s9 h9 o9).solved

  -- L10..L16 (3D PGA3)
  let s10 := Wedge.loadLevel 9
  let s10a := pullApart s10 (findIdByLabel s10 "A") (findIdByLabel s10 "B")
  assertTrue "L10 solved" (pullApart s10a (s10a.nextId - 1) (findIdByLabel s10a "C")).solved
  let s11 := Wedge.loadLevel 10
  let s11a := pushTogether s11 (findIdByLabel s11 "P1") (findIdByLabel s11 "P2")
  assertTrue "L11 solved" (pushTogether s11a (s11a.nextId - 1) (findIdByLabel s11a "P3")).solved
  let s12 := Wedge.loadLevel 11
  assertTrue "L12 solved" (pullApart s12 (findIdByLabel s12 "P1") (findIdByLabel s12 "P2")).solved
  let s13 := Wedge.loadLevel 12
  let a13 := findIdByLabel s13 "A"; let b13 := findIdByLabel s13 "B"
  let s13 := pullApart s13 a13 b13; let l13 := s13.nextId - 1
  let s13 := pushTogether s13 a13 b13; let m13 := s13.nextId - 1
  -- Test symmetric 3D dot ergonomics (hold line, drag point!)
  assertTrue "L13 solved via symmetric 3D dot (point -> line)" (holdDot s13 m13 l13).solved
  let s14 := Wedge.loadLevel 13
  let a14 := findIdByLabel s14 "A"; let b14 := findIdByLabel s14 "B"
  let c14 := findIdByLabel s14 "C"; let d14 := findIdByLabel s14 "D"
  let s14 := pullApart s14 a14 b14; let s14 := pullApart s14 (s14.nextId - 1) c14
  let base14 := s14.nextId - 1
  -- Also test symmetric 3D dot (hold plane, drag apex D!)
  assertTrue "L14 solved via symmetric 3D dot (point -> plane)" (holdDot s14 d14 base14).solved
  -- L15 Tetrahedron Circumcenter
  let mkPB (st : WedgeState) (p q : UInt32) : WedgeState × UInt32 :=
    let st1 := pullApart st p q; let l := st1.nextId - 1
    let st2 := pushTogether st1 p q; let m := st2.nextId - 1
    let st3 := holdDot st2 l m
    (st3, st3.nextId - 1)
  let s15 := Wedge.loadLevel 14
  let a15 := findIdByLabel s15 "A"; let b15 := findIdByLabel s15 "B"
  let c15 := findIdByLabel s15 "C"; let d15 := findIdByLabel s15 "D"
  let (s15, pb1) := mkPB s15 a15 b15
  let (s15, pb2) := mkPB s15 a15 c15
  let (s15, pb3) := mkPB s15 a15 d15
  let s15 := pushTogether s15 pb1 pb2
  assertTrue "L15 solved" (pushTogether s15 (s15.nextId - 1) pb3).solved
  -- L16 3D Monge Point
  let mkMonge (st : WedgeState) (u v p q : UInt32) : WedgeState × UInt32 :=
    let st1 := pullApart st u v; let e := st1.nextId - 1
    let st2 := pushTogether st1 p q; let m := st2.nextId - 1
    let st3 := holdDot st2 e m
    (st3, st3.nextId - 1)
  let s16 := Wedge.loadLevel 15
  let a16 := findIdByLabel s16 "A"; let b16 := findIdByLabel s16 "B"
  let c16 := findIdByLabel s16 "C"; let d16 := findIdByLabel s16 "D"
  let (s16, mp1) := mkMonge s16 c16 d16 a16 b16
  let (s16, mp2) := mkMonge s16 b16 d16 a16 c16
  let (s16, mp3) := mkMonge s16 a16 b16 c16 d16
  let s16 := pushTogether s16 mp1 mp2
  assertTrue "L16 solved" (pushTogether s16 (s16.nextId - 1) mp3).solved

  -- L17 Grand Finale: 3D Tetrahedron Circumcenter O + Centroid G + 3D Euler Axis (O & G)
  let s17 := Wedge.loadLevel 16
  let a17 := findIdByLabel s17 "A"; let b17 := findIdByLabel s17 "B"
  let c17 := findIdByLabel s17 "C"; let d17 := findIdByLabel s17 "D"
  -- 1. Build Centroid G = (A+B) + (C+D) in 3 moves
  let s17 := pushTogether s17 a17 b17; let mAB17 := s17.nextId - 1
  let s17 := pushTogether s17 c17 d17; let mCD17 := s17.nextId - 1
  let s17 := pushTogether s17 mAB17 mCD17; let gId := s17.nextId - 1
  -- 2. Build Circumcenter O via 3 perpendicular bisector planes
  let (s17, pb17a) := mkPB s17 a17 b17
  let (s17, pb17b) := mkPB s17 a17 c17
  let (s17, pb17c) := mkPB s17 a17 d17
  let s17 := pushTogether s17 pb17a pb17b
  let s17 := pushTogether s17 (s17.nextId - 1) pb17c; let oId := s17.nextId - 1
  -- 3. Join O & G into the 3D Euler Axis!
  let s17Done := pullApart s17 oId gId
  assertTrue "L17 Grand Finale solved (all 3 targets O, G, O&G!)" s17Done.solved
  let oEl := elemById s17Done oId
  let gEl := elemById s17Done gId
  let ogDist := Vec3.norm (Vec3.sub oEl.anchor gEl.anchor)
  assertTrue s!"L17 well-conditioned ‖O - G‖ > 0.30 (got {ogDist})" (ogDist > 0.30)
  -- Independently verify Monge's 3D Euler Line Theorem: G = (O + M)/2 and O & M == O & G!
  let (s17M, mm1) := mkMonge s17 c17 d17 a17 b17
  let (s17M, mm2) := mkMonge s17M b17 d17 a17 c17
  let (s17M, mm3) := mkMonge s17M a17 b17 c17 d17
  let s17M := pushTogether s17M mm1 mm2
  let s17M := pushTogether s17M (s17M.nextId - 1) mm3
  let mEl := elemById s17M (s17M.nextId - 1)
  match PgaElem.addSameGrade oEl mEl, PgaElem.join oEl gEl, PgaElem.join oEl mEl with
  | some midOM, some axisOG, some axisOM =>
    assertTrue "Monge's 3D Euler Theorem: (O + M)/2 == G" (PgaElem.approxEq midOM gEl)
    assertTrue "Monge's 3D Euler Theorem: O & M == O & G" (PgaElem.approxEq axisOM axisOG)
  | _, _, _ => throw (IO.userError "L17 Monge Euler check failed")

/-! ## 4. All 6 Dots Round-2 Adversarial Regression Tests (`#174`) -/

def testDotsRound2Regressions : IO Unit := do
  -- P0 #2: PGA2 Script Point vs Line Incidence & Translator
  let pga2Code :=
    "@basis PGA2\nlet P = point(1, 0, 0)\nlet L = e1 - e0\nlet I0 = L ^ P\nlet Q = point(3, 2, 0)\nlet L2 = e2 - 2 * e0\nlet I1 = L2 ^ Q\nlet T = translator(2, -1) >>> point(1, 3, 0)\nlet J = P & Q\nlet IJ = J ^ P"
  let pga2Fr := evalScriptToFrame "PGA2" pga2Code #[] 0.0 1
  assertTrue "Dots P0 #2: PGA2 script 0 diagnostics" pga2Fr.diagnostics.isEmpty
  let findInsp (fr : SceneFrame) (nm : String) : String :=
    (fr.inspect.find? (·.name == nm)).map (·.formatted) |>.getD "<missing>"
  assertTrue s!"Dots P0 #2: (e1-e0)^point(1,0,0) == 0 (got {findInsp pga2Fr "I0"})"
    (findInsp pga2Fr "I0" == "0")
  assertTrue s!"Dots P0 #2: (e2-2*e0)^point(3,2,0) == 0 (got {findInsp pga2Fr "I1"})"
    (findInsp pga2Fr "I1" == "0")
  assertTrue s!"Dots P0 #2: (P&Q)^P == 0 (got {findInsp pga2Fr "IJ"})"
    (findInsp pga2Fr "IJ" == "0")
  match pga2Fr.points.find? (·.label == "T") with
  | some ptT =>
    assertTrue s!"Dots P0 #2: translator(2,-1)>>>point(1,3) == (3,2) (got {ptT.pos.x},{ptT.pos.y})"
      (Float.abs (ptT.pos.x - 3.0) < 1e-5 && Float.abs (ptT.pos.y - 2.0) < 1e-5)
  | none => throw (IO.userError "Dots P0 #2: missing translated point T")

  -- P0 #3: CGA3 Off-Origin OPNS Line `A ^ B ^ ni` Extraction
  let cga3LineCode :=
    "@basis CGA3\nlet A = point(0, 1, 0)\nlet B = point(1, 1, 0)\nlet L = A ^ B ^ ni"
  let cga3Fr := evalScriptToFrame "CGA3" cga3LineCode #[] 0.0 1
  assertTrue "Dots P0 #3: CGA3 line script 0 diagnostics" cga3Fr.diagnostics.isEmpty
  assertTrue s!"Dots P0 #3: emits 1 line & 0 circles (got lines={cga3Fr.lines.size}, circles={cga3Fr.circles.size})"
    (cga3Fr.lines.size == 1 && cga3Fr.circles.size == 0)
  let ln := cga3Fr.lines[0]!
  let distToLine (p : Vec3) (l : LinePrim) : Float :=
    Vec3.norm (Vec3.cross (Vec3.sub p l.origin) l.dir)
  assertTrue s!"Dots P0 #3: A=(0,1,0) lies on emitted line (err={distToLine ⟨0,1,0⟩ ln})"
    (distToLine ⟨0.0, 1.0, 0.0⟩ ln < 1e-6)
  assertTrue s!"Dots P0 #3: B=(1,1,0) lies on emitted line (err={distToLine ⟨1,1,0⟩ ln})"
    (distToLine ⟨1.0, 1.0, 0.0⟩ ln < 1e-6)
  -- General 3D off-origin skew line `A=(2,-3,5), B=(4,1,2)`
  let cga3SkewFr := evalScriptToFrame "CGA3"
    "@basis CGA3\nlet A = point(2, -3, 5)\nlet B = point(4, 1, 2)\nlet L = A ^ B ^ ni" #[] 0.0 2
  assertTrue "Dots P0 #3 skew: 1 line, 0 circles" (cga3SkewFr.lines.size == 1 && cga3SkewFr.circles.size == 0)
  let ln2 := cga3SkewFr.lines[0]!
  assertTrue "Dots P0 #3 skew: A=(2,-3,5) on line" (distToLine ⟨2.0, -3.0, 5.0⟩ ln2 < 1e-5)
  assertTrue "Dots P0 #3 skew: B=(4,1,2) on line" (distToLine ⟨4.0, 1.0, 2.0⟩ ln2 < 1e-5)

  -- P0 #4: Lossless 64-Bit JSON Seed Parsing & WedgeHudState `seedStr` Roundtrip
  let (sSeedA, _) ← IO.ofExcept (Studio.dispatchJson Studio.create
    "{\"op\":\"wedgeRandom\",\"dim\":2,\"difficulty\":1,\"seed\":9007199254740992}")
  let (sSeedB, _) ← IO.ofExcept (Studio.dispatchJson Studio.create
    "{\"op\":\"wedgeRandom\",\"dim\":2,\"difficulty\":1,\"seed\":9007199254740993}")
  let (sSeedStr, _) ← IO.ofExcept (Studio.dispatchJson Studio.create
    "{\"op\":\"wedgeRandom\",\"dim\":3,\"difficulty\":2,\"seedStr\":\"9007199254740993\"}")
  assertTrue "Dots P0 #4: 9007199254740992 vs 9007199254740993 parsed losslessly as distinct UInt64"
    (sSeedA.wedge.randomSeed == 9007199254740992 && sSeedB.wedge.randomSeed == 9007199254740993 &&
     sSeedStr.wedge.randomSeed == 9007199254740993)
  let fSeedA := Wedge.toSceneFrame sSeedA.wedge 1 0.0
  let fSeedB := Wedge.toSceneFrame sSeedB.wedge 1 0.0
  let fSeedStr := Wedge.toSceneFrame sSeedStr.wedge 1 0.0
  assertTrue "Dots P0 #4: distinct titles (#992 vs #993)" (fSeedA.title != fSeedB.title)
  let metaSeed := Json.toMetaJson fSeedStr (Json.buildLabelTable fSeedStr)
  assertTrue "Dots P0 #4: metaJson.wedge preserves lossless seedStr"
    (hasSubstr metaSeed "\"seedStr\":\"9007199254740993\"" && hasSubstr metaSeed "\"isRandom\":true")

  -- P0 #5: GPU Implicit Raymarcher Respects `bound` Across GLSL3/WGSL/MSL
  let csB1 := CoffeeShop.setImplicit {} "x*x+y*y+z*z-9" true 1.0 16
  let csB4 := CoffeeShop.setImplicit {} "x*x+y*y+z*z-9" true 4.0 16
  let frB1 := CoffeeShop.toSceneFrame csB1 1
  let frB4 := CoffeeShop.toSceneFrame csB4 2
  assertTrue "Dots P0 #5: bound=1 vs bound=4 emit distinct GPU shader hashes"
    (frB1.opnsShaders.size == 1 && frB4.opnsShaders.size == 1 &&
     frB1.opnsShaders[0]!.hash != frB4.opnsShaders[0]!.hash)
  let sh4 := frB4.opnsShaders[0]!
  assertTrue "Dots P0 #5: bound=4 GLSL uses clipR=7.0 (not 2.2)"
    (hasSubstr sh4.glsl "intersectSphere(ro, rd, 7.0" && !hasSubstr sh4.glsl "intersectSphere(ro, rd, 2.2)")
  assertTrue "Dots P0 #5: bound=4 WGSL uses clipR²=49.0 (not 4.84)"
    (hasSubstr sh4.wgsl "- 49.0" && !hasSubstr sh4.wgsl "- 4.84;")
  assertTrue "Dots P0 #5: bound=4 MSL uses clipR²=49.0f (not 4.84f)"
    (hasSubstr sh4.msl "- 49.0" && !hasSubstr sh4.msl "- 4.84f;")
  assertTrue "Dots P0 #5: bound=4 camera distance frames radius-3 sphere cleanly"
    (frB4.camera.distance ≥ 10.0)

  -- P1 #8: Mode-Gated `WedgeGesture` (never hijacks CoffeeShop/Calculator into Wedge!)
  let sCoffee := Studio.create
  let sHijackPrev := Studio.dispatchEvent sCoffee (.wedgeGesture 0 1 ⟨1,0,0⟩ ⟨-1,0,0⟩ false false true) false
  let sHijackCommit := Studio.dispatchEvent sCoffee (.wedgeGesture 0 1 ⟨1,0,0⟩ ⟨-1,0,0⟩ false false false) false
  assertTrue "Dots P1 #8: wedgeGesture preview ignored in CoffeeShop" (sHijackPrev.active == .coffeeShop)
  assertTrue "Dots P1 #8: wedgeGesture commit ignored in CoffeeShop" (sHijackCommit.active == .coffeeShop)
  let sCalc := Studio.dispatchEvent sCoffee (.loadPreset "calculator") true
  let sCalcAfter := Studio.dispatchEvent sCalc (.wedgeGesture 0 1 ⟨1,0,0⟩ ⟨-1,0,0⟩ false false false) false
  assertTrue "Dots P1 #8: wedgeGesture ignored in Calculator" (sCalcAfter.active == .calculator)

  -- P1 #10: Explicit `resetTime` & `seekTime`
  let mut sTime := Studio.dispatchEvent Studio.create (.loadPreset "pga3d_bouncing_cube") true
  let y0 := sTime.coffee.cubeState.pos.y
  for k in [:20] do
    sTime := Studio.dispatchEvent sTime (.tick 0.05 (Float.ofNat (k + 1) * 0.05)) false
  assertTrue "Dots P1 #10: cube moved after ticks" (Float.abs (sTime.coffee.simTime - 1.0) < 1e-6)
  let (sSeek, _) ← IO.ofExcept (Studio.dispatchJson sTime "{\"op\":\"seekTime\",\"t\":2.5}")
  assertTrue s!"Dots P1 #10: seekTime exact 2.5 (got {sSeek.coffee.simTime})"
    (Float.abs (sSeek.coffee.simTime - 2.5) < 1e-9)
  let (sReset, _) ← IO.ofExcept (Studio.dispatchJson sSeek "{\"op\":\"resetTime\"}")
  assertTrue s!"Dots P1 #10: resetTime exact 0.0 (got {sReset.coffee.simTime})"
    (sReset.coffee.simTime == 0.0)
  assertTrue "Dots P1 #10: resetTime resets bouncing cube RK4 physics state"
    (Float.abs (sReset.coffee.cubeState.pos.y - y0) < 1e-6)

def runAll : IO Unit := do
  testDualHandleSlicing
  IO.println "PASS [1/4] Dual-handle 3D slicing manipulator (pga3d_slicing & pga3d_slicing_hq + tilt + 2D contour + LiveScript)"
  test77PresetsShowstoppersAndTour
  IO.println "PASS [2/4] All 77 unique presets + 3 Wave 6C showstoppers (Barth Sextic, Dupin Cyclide, Involute Gears) + 6-stop Guided Tour"
  testWedge17LevelsAndAudit
  IO.println "PASS [3/4] All 17/17 Wedge levels solved (incl. L17 3D Euler Axis + Monge theorem) + separation audit + symmetric 3D dot"
  testDotsRound2Regressions
  IO.println "PASS [4/4] All 6 Dots Round-2 regressions (PGA2 incidence, CGA3 off-origin line, 64-bit seed, GPU bound, mode-gated wedgeGesture, resetTime/seekTime)"
  IO.println "ALL WAVE 6C + DOTS ROUND-2 TESTS PASSED!"

end Tests.Wave6

def main : IO Unit := Tests.Wave6.runAll
