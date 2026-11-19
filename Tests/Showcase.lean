import Grassmann.Studio

/-!
# Comprehensive Wave 4B Verification & Benchmark Suite (`Tests.Showcase`)

Strictly `Init`-only (ZERO `Lean.*`, ZERO `Std.*`, ZERO `DirectSum`, ZERO `sorry`/axioms):
1. **All 74 Unique Presets + KaTeX `formula` & `summary` Metadata**:
   - Verifies `totalPresetCount == 74`, 74 strictly unique IDs, valid 74-entry `presetCatalogJson`,
     valid 8B-aligned `GSIR` v1 frames, visual geometry, and non-empty KaTeX `formula` + `summary`
     across ALL 74 CoffeeShop presets AND ALL 16 Wedge 2D/3D levels!
2. **All 5 Wave 4B Showstopper Presets + Live `setParam` JSON Dispatch**:
   - `pga3d_bouncing_cube` (RK4 impulse + `gravity`/`restitution`/`spin`)
   - `pga3d_double_pendulum` (singularity-free constrained RK4 + exact rod length conservation + `length`/`damping`/`gravity`)
   - `sta_terrell_penrose` (past light-cone Terrell-Penrose rotation vs Lorentz contraction + `beta`/`distance`)
   - `sta_maxwell_streamlines` (320 RK4 `E`+`B` `0x0D FLOW_PARTICLES` streaks + Faraday `F = E + IB` disks + `frequency`/`dipole`/`bScale`)
   - `pga3d_hopf_streamlines` (324 RK4 Hopf+screw `0x0D FLOW_PARTICLES` streaks + Villarceau fibers + `pitch`/`twist`/`flowSpeed`)
3. **LiveScript v2 `slider(...)` & `@param` Directives + Live `setParam`**:
   - Verifies `slider(...)`, `@param name = def (lo..hi, step)`, `metaJson.params[]`, live `setParam`
     re-evaluation, and clean 0-diagnostic execution of all 5 showcase `sampleCode` scripts!
4. **Bytecode `ImplicitExpr` Exact Float Equivalence (`< 1e-12`)**:
   - Verifies `evalBytecode` vs reference `evalExpr` across 8 diverse expressions (including `t`-folding
     and deep `maxStack > 8` trees) over 512 sample points!
5. **Bytecode vs AST Marching Tetrahedra Speedup Benchmark**:
   - Direct apples-to-apples timing of bytecode vs AST on `16³` & `18³` Gyroid, Metaballs, and Genus-2!

Credits: Michael Reed (`chakravala` / `Grassmann.jl`) & Steven De Keninck (`enkimute` / `ganja.js`).
-/

namespace Tests.Showcase

open Grassmann Grassmann.Scene Grassmann.Scene.Binary Grassmann.Scene.Json
open Grassmann.Eval Grassmann.Eval.ImplicitExpr Grassmann.CoffeeShop
open Grassmann.CoffeeShop.PresetsExtra Grassmann.CoffeeShop.PresetsParity
open Grassmann.CoffeeShop.PresetsShowcase Grassmann.Wedge Grassmann.Studio

private def hasSubstr (s pat : String) : Bool := (s.splitOn pat).length > 1

private def assertTrue (name : String) (cond : Bool) : IO Unit := do
  if !cond then
    throw (IO.userError s!"FAIL [{name}]")

private def assertApprox (name : String) (a b : Float) (tol : Float := 1e-3) : IO Unit := do
  if Float.abs (a - b) > tol then
    throw (IO.userError s!"FAIL [{name}]: got {a}, expected {b} (tol={tol})")

private def hasVisualGeometry (f : SceneFrame) : Bool :=
  !f.points.isEmpty || !f.lines.isEmpty || !f.planes.isEmpty || !f.circles.isEmpty ||
  !f.spheres.isEmpty || !f.pointPairs.isEmpty || !f.bivectorDisks.isEmpty ||
  !f.segments.isEmpty || !f.curves.isEmpty || !f.meshRefs.isEmpty ||
  !f.flowFields.isEmpty || !f.opnsUniforms.isEmpty

/-! ## 1. All 77 Unique Presets + All 17 Wedge Levels KaTeX Metadata -/

def testAll74PresetsAndWedgeMeta : IO Unit := do
  assertTrue s!"totalPresetCount == 77 (got {totalPresetCount})" (totalPresetCount == 77)
  let allIds : Array String :=
    presetCatalog.map (·.id) ++
    extraPresetCatalog.map (·.id) ++
    parityPresetCatalog.map (·.id) ++
    showcasePresetCatalog.map (·.id)
  assertTrue "allIds.size == 77" (allIds.size == 77)
  -- Check strict uniqueness across all 77 preset IDs
  let mut seen : Array String := #[]
  for id in allIds do
    assertTrue s!"unique preset id '{id}'" (!seen.contains id)
    seen := seen.push id
  -- Verify `presetCatalogJson` parses as a 77-element JSON array
  match parseJson Studio.presetCatalogJson with
  | .error e => throw (IO.userError s!"presetCatalogJson invalid JSON: {e}")
  | .ok (.arr items) =>
    assertTrue s!"presetCatalogJson has 77 items (got {items.size})" (items.size == 77)
  | .ok _ => throw (IO.userError "presetCatalogJson is not a JSON array")

  -- Load & validate EVERY ONE of the 77 presets (GSIR v1 + geometry + KaTeX formula + summary!)
  for id in allIds do
    let cs := CoffeeShop.loadPreset {} id
    let fr := CoffeeShop.toSceneFrame cs 1
    assertTrue s!"preset {id}: 0 diagnostics" fr.diagnostics.isEmpty
    assertTrue s!"preset {id}: has visual geometry" (hasVisualGeometry fr)
    assertTrue s!"preset {id}: non-empty KaTeX formula" (!fr.formula.isEmpty)
    assertTrue s!"preset {id}: non-empty human summary" (!fr.summary.isEmpty)
    let metaStr := Json.toMetaJson fr (Json.buildLabelTable fr)
    assertTrue s!"preset {id}: metaJson contains formula" (hasSubstr metaStr "\"formula\":\"")
    assertTrue s!"preset {id}: metaJson contains summary" (hasSubstr metaStr "\"summary\":\"")
    assertTrue s!"preset {id}: metaJson contains params" (hasSubstr metaStr "\"params\":[")
    let raw := encodeFrame fr true
    match validateGsirFrame raw with
    | .error e => throw (IO.userError s!"preset {id} GSIR invalid: {e}")
    | .ok _ => assertTrue s!"preset {id}: 8B aligned" (raw.size % 8 == 0)

  -- Verify ALL 17 Wedge 2D/3D campaign levels emit non-empty KaTeX formula & summary!
  assertTrue "17 Wedge levels" (Wedge.allLevels.size == 17)
  for idx in [:Wedge.allLevels.size] do
    let ws := Wedge.loadLevel idx
    let wf := Wedge.toSceneFrame ws (idx + 1).toUInt64 0.5
    assertTrue s!"wedge L{idx+1}: non-empty KaTeX formula" (!wf.formula.isEmpty)
    assertTrue s!"wedge L{idx+1}: non-empty summary" (!wf.summary.isEmpty)
    match validateGsirFrame (encodeFrame wf true) with
    | .error e => throw (IO.userError s!"wedge L{idx+1} GSIR invalid: {e}")
    | .ok _ => pure ()

/-! ## 2. All 5 Wave 4B Showstopper Presets + Live `setParam` Dispatch -/

def testFiveShowcasePresetsAndSetParam : IO Unit := do
  -- 2a. `pga3d_bouncing_cube`: RK4 impulse + gravity/restitution/spin sliders
  let mut sess := Studio.create
  let (s1, _) ← IO.ofExcept (Studio.dispatchJson sess "{\"op\":\"loadPreset\",\"id\":\"pga3d_bouncing_cube\"}")
  sess := s1
  let fCube0 := CoffeeShop.toSceneFrame sess.coffee 1
  assertTrue "bouncing_cube has 3 @param sliders" (fCube0.params.size == 3)
  assertTrue "bouncing_cube has cube mesh + bivector disk + floor"
    (fCube0.meshRefs.size == 1 && fCube0.bivectorDisks.size == 1 && fCube0.planes.size == 1)
  let pos0 := sess.coffee.cubeState.pos
  for k in [:35] do
    sess := Studio.dispatchEvent sess (.tick 0.016 (Float.ofNat (k + 1) * 0.016)) false
  let pos1 := sess.coffee.cubeState.pos
  assertTrue "bouncing_cube moved under RK4" (Vec3.norm (Vec3.sub pos1 pos0) > 0.15)
  assertTrue "bouncing_cube stays above floor" (pos1.y ≥ -1.26)
  let (s2, _) ← IO.ofExcept (Studio.dispatchJson sess "{\"op\":\"setParam\",\"name\":\"gravity\",\"value\":18.5}")
  sess := s2
  let fCube1 := CoffeeShop.toSceneFrame sess.coffee 40
  assertApprox "bouncing_cube gravity updated to 18.5" fCube1.params[0]!.value 18.5 1e-4

  -- 2b. `pga3d_double_pendulum`: singularity-free constrained RK4 + exact rod conservation
  let (s3, _) ← IO.ofExcept (Studio.dispatchJson sess "{\"op\":\"loadPreset\",\"id\":\"pga3d_double_pendulum\"}")
  sess := s3
  let fDp0 := CoffeeShop.toSceneFrame sess.coffee 1
  assertTrue "double_pendulum has 3 @param sliders" (fDp0.params.size == 3)
  assertTrue "double_pendulum has 2 rod meshes + 3 spheres + chaotic trails"
    (fDp0.meshRefs.size == 2 && fDp0.spheres.size == 3 && fDp0.curves.size == 2)
  for k in [:30] do
    sess := Studio.dispatchEvent sess (.tick 0.016 (Float.ofNat (k + 1) * 0.016)) false
  let dp := sess.coffee.doublePendulum
  let pivot : Vec3 := ⟨0.0, 1.25, 0.0⟩
  assertApprox "double_pendulum rod 1 length exact" (Vec3.norm (Vec3.sub dp.p1 pivot)) 1.0 1e-3
  assertApprox "double_pendulum rod 2 length exact" (Vec3.norm (Vec3.sub dp.p2 dp.p1)) 0.9 1e-3
  let (s4, _) ← IO.ofExcept (Studio.dispatchJson sess "{\"op\":\"setParam\",\"name\":\"length\",\"value\":1.35}")
  sess := s4
  let dpLong := sess.coffee.doublePendulum
  assertApprox "double_pendulum setParam length=1.35 updates rod 1" (Vec3.norm (Vec3.sub dpLong.p1 pivot)) 1.35 1e-3
  assertApprox "double_pendulum setParam length=1.35 updates rod 2" (Vec3.norm (Vec3.sub dpLong.p2 dpLong.p1)) (0.9 * 1.35) 1e-3

  -- 2c. `sta_terrell_penrose`: relativistic optical rotation vs β slider
  let (s5, _) ← IO.ofExcept (Studio.dispatchJson sess "{\"op\":\"loadPreset\",\"id\":\"sta_terrell_penrose\"}")
  sess := s5
  let (s5a, _) ← IO.ofExcept (Studio.dispatchJson sess "{\"op\":\"setParam\",\"name\":\"beta\",\"value\":0.0}")
  let fTp0 := CoffeeShop.toSceneFrame s5a.coffee 1
  let (s5b, _) ← IO.ofExcept (Studio.dispatchJson s5a "{\"op\":\"setParam\",\"name\":\"beta\",\"value\":0.92}")
  let fTpHi := CoffeeShop.toSceneFrame s5b.coffee 2
  assertTrue "terrell_penrose has 2 @param sliders" (fTpHi.params.size == 2)
  assertApprox "terrell_penrose beta updated to 0.92" fTpHi.params[0]!.value 0.92 1e-4
  assertTrue "terrell_penrose mesh dirtyHash changes with beta (optical aberration!)"
    (fTp0.meshAssets[0]!.dirtyHash != fTpHi.meshAssets[0]!.dirtyHash)

  -- 2d. `sta_maxwell_streamlines`: 320 RK4 E+B streaks (`0x0D FLOW_PARTICLES`) + Faraday disks
  let (s6, _) ← IO.ofExcept (Studio.dispatchJson sess "{\"op\":\"loadPreset\",\"id\":\"sta_maxwell_streamlines\"}")
  let fMax0 := CoffeeShop.toSceneFrame s6.coffee 1
  assertTrue "maxwell_streamlines has 3 @param sliders" (fMax0.params.size == 3)
  assertTrue "maxwell_streamlines emits 2 FlowFieldPrims (E + B)" (fMax0.flowFields.size == 2)
  let totalMaxStreaks := fMax0.flowFields[0]!.starts.size / 3 + fMax0.flowFields[1]!.starts.size / 3
  assertTrue s!"maxwell_streamlines >= 300 RK4 streaks (got {totalMaxStreaks})" (totalMaxStreaks ≥ 300)
  assertTrue "maxwell_streamlines emits 6 Faraday bivector disks" (fMax0.bivectorDisks.size == 6)
  let (s6b, _) ← IO.ofExcept (Studio.dispatchJson s6 "{\"op\":\"setParam\",\"name\":\"bScale\",\"value\":0.0}")
  let fMaxNoB := CoffeeShop.toSceneFrame s6b.coffee 2
  assertTrue "maxwell_streamlines bScale=0 toggles off B flow field" (fMaxNoB.flowFields.size == 1)

  -- 2e. `pga3d_hopf_streamlines`: 324 RK4 Hopf+screw streaks (`0x0D FLOW_PARTICLES`) + pitch/twist sliders
  let (s7, _) ← IO.ofExcept (Studio.dispatchJson sess "{\"op\":\"loadPreset\",\"id\":\"pga3d_hopf_streamlines\"}")
  let fHopf0 := CoffeeShop.toSceneFrame s7.coffee 1
  assertTrue "hopf_streamlines has 3 @param sliders" (fHopf0.params.size == 3)
  assertTrue "hopf_streamlines emits 3 layered FlowFieldPrims" (fHopf0.flowFields.size == 3)
  let totalHopf := fHopf0.flowFields.foldl (fun acc fl => acc + fl.starts.size / 3) 0
  assertTrue s!"hopf_streamlines >= 320 RK4 streaks (got {totalHopf})" (totalHopf ≥ 320)
  let endY0 := fHopf0.flowFields[0]!.ends.get! 1
  let (s7b, _) ← IO.ofExcept (Studio.dispatchJson s7 "{\"op\":\"setParam\",\"name\":\"pitch\",\"value\":-1.1}")
  let fHopf1 := CoffeeShop.toSceneFrame s7b.coffee 2
  let endY1 := fHopf1.flowFields[0]!.ends.get! 1
  assertTrue "hopf_streamlines setParam pitch measurably alters RK4 streamlines"
    (Float.abs (endY1 - endY0) > 0.01)

/-! ## 3. LiveScript v2 `slider(...)`, `@param` & Showcase Scripts -/

def testLiveScriptSlidersAndShowcaseScripts : IO Unit := do
  -- Both `slider(...)` AND `@param` syntax inside LiveScript v2 + live `setParam` dispatch!
  let code := "
@basis PGA3
@param angle = 0.0 (0..3.14159, 0.01)
let rad = slider(\"radius\", 1.2, 0.2, 3.0, 0.05, \"Orbit Radius\")
let M = motor(0, 1, 0, angle, 0)
let P = M >>> point(rad, 0, 0)
"
  let mut sess := Studio.create
  sess := Studio.dispatchEvent sess (.evalScript "PGA3" code) true
  let f0 := CoffeeShop.toSceneFrame sess.coffee 1
  assertTrue "LiveScript @param + slider 0 diagnostics" f0.diagnostics.isEmpty
  assertTrue s!"LiveScript emitted 2 params (got {f0.params.size})" (f0.params.size == 2)
  assertTrue "slider label preserved" (f0.params[1]!.label == "Orbit Radius")
  assertApprox "initial P.x == 1.2" f0.points[0]!.pos.x 1.2 1e-2

  -- Dispatch JSON `setParam` for BOTH `@param angle` and `slider("radius", ...)`!
  let (s1, _) ← IO.ofExcept (Studio.dispatchJson sess "{\"op\":\"setParam\",\"name\":\"angle\",\"value\":1.57079632679}")
  let (s2, _) ← IO.ofExcept (Studio.dispatchJson s1 "{\"op\":\"setParam\",\"name\":\"radius\",\"value\":2.0}")
  let f1 := CoffeeShop.toSceneFrame s2.coffee 2
  assertApprox "after setParam angle=pi/2, P.x ≈ 0" f1.points[0]!.pos.x 0.0 1e-2
  assertApprox "after setParam radius=2.0, |P| ≈ 2.0" (Vec3.norm f1.points[0]!.pos) 2.0 1e-2
  let metaJson := Json.toMetaJson f1 (Json.buildLabelTable f1)
  assertTrue "metaJson serializes Orbit Radius label" (hasSubstr metaJson "\"label\":\"Orbit Radius\"")

  -- Verify ALL 5 showcase presets' runnable LiveScript v2 `sampleCode` execute cleanly!
  for p in showcasePresetCatalog do
    let fr := evalScriptToFrame p.algebra p.sampleCode #[] 0.6 1
    if !fr.diagnostics.isEmpty then
      throw (IO.userError s!"FAIL [showcase script {p.id}]: {fr.diagnostics[0]!}")
    assertTrue s!"showcase script {p.id} emits visual geometry" (hasVisualGeometry fr)
    assertTrue s!"showcase script {p.id} emits @param sliders" (!fr.params.isEmpty)
    match validateGsirFrame (encodeFrame fr true) with
    | .error e => throw (IO.userError s!"showcase script {p.id} GSIR invalid: {e}")
    | .ok _ => pure ()

/-! ## 4. Bytecode `ImplicitExpr` Exact Float Equivalence vs Reference AST (`< 1e-12`) -/

def testBytecodeEquivalence : IO Unit := do
  let exprs : Array String := #[
    "cos(x*2)*sin(y*2) + cos(y*2)*sin(z*2) + cos(z*2)*sin(x*2)",
    "cos(2.35*x) + cos(2.35*y) + cos(2.35*z)",
    "(sqrt(x^2 + z^2) - 0.85)^2 + y^2 - 0.28^2",
    "x^2 + y^2 + z^2 = 1",
    "1 - 0.22/((x-0.5*cos(t))^2 + y^2 + z^2 + 0.05) - 0.22/((x+0.5)^2 + y^2 + z^2 + 0.05)",
    "((x^2 + y^2)^2 - x^2 + y^2)^2 + z^2 - 0.0484",
    "atan2(y, x) + hypot(x, z) - min(abs(x), max(y, z)) + sin(t) / (r + 1.2)",
    -- Deep expression forcing `maxStack > 8` to exercise `evalBytecodeDeep` fallback!
    "(((((x+0.1)+(y+0.2))+((z+0.3)+(x-0.4)))+(((y-0.5)+(z-0.6))+((x+0.7)+(y+0.8))))+((((z+0.9)+(x-1.0))+((y-1.1)+(z-1.2)))+(((x+1.3)+(y+1.4))+((z+1.5)+(x-1.6)))))"
  ]
  let tVal : Float := 0.73
  for src in exprs do
    let ast ← IO.ofExcept (parseExpr src)
    let bc := compileToBytecode ast tVal
    assertTrue s!"bytecode non-empty for {src}" (!bc.ops.isEmpty)
    for ix in [:4] do
      let x := -1.1 + 0.73 * Float.ofNat ix
      for iy in [:4] do
        let y := -0.95 + 0.67 * Float.ofNat iy
        for iz in [:4] do
          let z := -1.05 + 0.71 * Float.ofNat iz
          let ref := evalExpr ast x y z 0.25 0.6 tVal
          let got := evalBytecode bc x y z 0.25 0.6
          assertApprox s!"bytecode == AST on ({x},{y},{z}) for {src}" got ref 1e-12

/-! ## 5. Bytecode vs AST Marching Tetrahedra Benchmark -/

def benchBytecodeVsAst : IO Unit := do
  let gyroid := "cos(x*2)*sin(y*2)+cos(y*2)*sin(z*2)+cos(z*2)*sin(x*2)"
  let metaEq := "1 - 0.22/((x-0.5*cos(t))^2 + y^2 + z^2 + 0.05) - 0.22/((x+0.5)^2 + y^2 + z^2 + 0.05)"
  let bmin : Vec3 := ⟨-1.6, -1.6, -1.6⟩
  let bmax : Vec3 := ⟨ 1.6,  1.6,  1.6⟩

  -- Pure 50,000-sample evaluator benchmark (isolating bytecode VM vs recursive AST!)
  let gyrAst ← IO.ofExcept (parseExpr gyroid)
  let gyrBc := compileToBytecode gyrAst 0.0
  let p0 ← IO.monoNanosNow
  let mut accAst : Float := 0.0
  for i in [:50000] do
    let u := Float.ofNat i * 0.0001
    accAst := accAst + evalExpr gyrAst u (u * 0.7 - 0.5) (0.3 - u * 0.4) 0.0 0.0 0.0
  let p1 ← IO.monoNanosNow
  let mut accBc : Float := 0.0
  for i in [:50000] do
    let u := Float.ofNat i * 0.0001
    accBc := accBc + evalBytecodeXYZ gyrBc u (u * 0.7 - 0.5) (0.3 - u * 0.4)
  let p2 ← IO.monoNanosNow
  assertApprox "50k pure eval sum AST == Bytecode" accBc accAst 1e-8
  let evalAstUs := Float.ofNat (p1 - p0) / 50000.0
  let evalBcUs  := Float.ofNat (p2 - p1) / 50000.0

  -- Warm up & verify exact vertex/triangle count match between Bytecode and AST!
  let mBc16 ← IO.ofExcept (evalImplicitExprMesh gyroid 0.0 bmin bmax 16 9101 true)
  let mAst16 ← IO.ofExcept (evalImplicitExprMeshAst gyroid 0.0 bmin bmax 16 9102 true)
  assertTrue "16³ Gyroid bytecode & AST emit identical vertex count" (mBc16.positions.size == mAst16.positions.size)
  assertTrue "16³ Gyroid bytecode & AST emit identical triangle count" (mBc16.indices.size == mAst16.indices.size)

  let iters := 10
  let t0 ← IO.monoNanosNow
  let mut sinkAst : Nat := 0
  for k in [:iters] do
    let eps := 1e-6 * Float.ofNat k
    let m ← IO.ofExcept (evalImplicitExprMeshAst gyroid eps ⟨-1.6 - eps, -1.6, -1.6⟩ ⟨1.6 + eps, 1.6, 1.6⟩ 16 (9102 + k.toUInt64) true)
    sinkAst := sinkAst + m.indices.size
  let t1 ← IO.monoNanosNow
  let mut sinkBc : Nat := 0
  for k in [:iters] do
    let eps := 1e-6 * Float.ofNat k
    let m ← IO.ofExcept (evalImplicitExprMesh gyroid eps ⟨-1.6 - eps, -1.6, -1.6⟩ ⟨1.6 + eps, 1.6, 1.6⟩ 16 (9101 + k.toUInt64) true)
    sinkBc := sinkBc + m.indices.size
  let t2 ← IO.monoNanosNow

  let astMs := Float.ofNat (t1 - t0) / (Float.ofNat iters * 1e6)
  let bcMs  := Float.ofNat (t2 - t1) / (Float.ofNat iters * 1e6)
  let speedup := astMs / max 0.001 bcMs

  let t3 ← IO.monoNanosNow
  let mBc18 ← IO.ofExcept (evalImplicitExprMesh gyroid 0.0 bmin bmax 18 9103 true)
  let t4 ← IO.monoNanosNow
  let mMeta ← IO.ofExcept (evalImplicitExprMesh metaEq 0.7 ⟨-1.5,-1.2,-1.2⟩ ⟨1.5,1.2,1.2⟩ 16 9104 true)
  let t5 ← IO.monoNanosNow

  assertTrue "benchmark sinks > 0" (sinkAst > 0 && sinkBc > 0 && mBc18.indices.size > 0 && mMeta.indices.size > 0)
  IO.println s!"  [bench] Pure Gyroid eval (50k): AST {evalAstUs} ns/pt -> Bytecode {evalBcUs} ns/pt ({evalAstUs / max 0.1 evalBcUs}x)"
  IO.println s!"  [bench] Gyroid 16³ AST vs Bytecode ({iters}x): {astMs} ms -> {bcMs} ms ({speedup}x! {mBc16.positions.size/3} verts, {mBc16.indices.size/3} tris)"
  IO.println s!"  [bench] Gyroid 18³ Bytecode:        {Float.ofNat (t4 - t3) / 1e6} ms ({mBc18.positions.size/3} verts, {mBc18.indices.size/3} tris)"
  IO.println s!"  [bench] Metaballs 16³ Bytecode:     {Float.ofNat (t5 - t4) / 1e6} ms ({mMeta.positions.size/3} verts, {mMeta.indices.size/3} tris)"

def runAll : IO Unit := do
  testAll74PresetsAndWedgeMeta
  IO.println "PASS [1/5] All 77 unique CoffeeShop presets + 17 Wedge levels emit valid 8B GSIR v1 + non-empty KaTeX formula & summary"
  testFiveShowcasePresetsAndSetParam
  IO.println "PASS [2/5] All 5 Wave 4B showstopper presets (Bouncing Cube, Double Pendulum, Terrell-Penrose, Maxwell & Hopf RK4 streamlines) + live setParam"
  testLiveScriptSlidersAndShowcaseScripts
  IO.println "PASS [3/5] LiveScript v2 slider() & @param directives + setParam overrides + 5 showcase runnable scripts"
  testBytecodeEquivalence
  IO.println "PASS [4/5] Bytecode ImplicitExpr exact float equivalence (< 1e-12) vs reference AST across 8 expressions (512 samples)"
  benchBytecodeVsAst
  IO.println "PASS [5/5] Bytecode vs AST Marching Tetrahedra benchmark complete"
  IO.println "ALL WAVE 4B SHOWCASE TESTS PASSED!"

end Tests.Showcase

def main : IO Unit := Tests.Showcase.runAll
