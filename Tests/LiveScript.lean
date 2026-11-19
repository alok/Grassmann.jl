import Grassmann.Studio

/-!
# Comprehensive Verification & Benchmark Suite for LiveScript v2 (`Tests.LiveScript`)

Strictly `Init`-only (zero `Lean.*`, zero `Std.*`, zero `DirectSum`, zero `sorry`/axioms):
1. **Language & Safety**: `@basis`/`Algebra(p,q,r)`, `fn`/lambdas, `for i in lo..hi`,
   `[expr for i in lo..hi]`, `if/else` & ternary, exact `Line L, Col C:` diagnostics,
   512-iter loop guard, 32-depth recursion guard, and error-resilient last-valid-scene retention!
2. **Reactive Handles, Animation & `EditCoeff`**: `DragHandle` re-evaluates derived lines/midpoints
   live, `Tick` drives time-parameterized motors, and `EditCoeff` patches script multivector blades live!
3. **Rich Geometry & Multi-Algebra Classification**: `graph([0xRRGGBB, ..., "label"])`,
   `seg`, `poly`, `curve`, `mesh` + `slice` (live bunny slicing + 2D contour!), `implicit`,
   `surface`, `opns`, CGA3 OPNS (`A^B`, `A^B^C`, `A^B^C^D`) + IPNS (`S1^S2`), STA `-+++` boosts,
   R3 rational rotors, Complex, Dual, and `Cl(2,1,1)`!
4. **Live Round-Trip on 27 Flagship Preset Scripts**: Every single preset in `presetCatalog` (19) +
   key `PresetsExtra` scripts (8) parses, executes with 0 diagnostics, renders geometry, and
   encodes valid 8-byte aligned `GSIR` v1 frames!
5. **Re-Evaluation Latency Benchmark**: Measures multi-statement PGA3 LiveScript re-eval µs/frame!
-/

namespace Tests.LiveScript

open Grassmann Grassmann.Scene Grassmann.Scene.Binary Grassmann.Scene.Json
open Grassmann.Eval Grassmann.CoffeeShop Grassmann.CoffeeShop.PresetsExtra Grassmann.Studio

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
  !f.segments.isEmpty || !f.curves.isEmpty || !f.meshRefs.isEmpty || !f.opnsUniforms.isEmpty

/-! ## 1. Language Constructs, Exact Line:Col Diagnostics & Safety Guards -/

def testLanguageAndSafety : IO Unit := do
  -- Algebra header override (`Algebra(2,0,1)` overrides caller's `"PGA3"`)
  let fAlg := evalScriptToFrame "PGA3" "Algebra(2, 0, 1)\nlet A = point(-1, 0)\nlet B = point(1, 0.5)\nlet L = A & B"
  assertTrue "Algebra(2,0,1) switches to PGA2 2D" (fAlg.algebra.name == "PGA2" && fAlg.is2D)
  assertTrue "Algebra(2,0,1) diagnostics empty" fAlg.diagnostics.isEmpty
  assertTrue "Algebra(2,0,1) emits 2 pts + 1 line" (fAlg.points.size == 2 && fAlg.lines.size == 1)

  -- User functions, arrow lambdas, conditionals, bounded loops & list comprehensions!
  let scriptLoop := "
@basis PGA3
fn stepPt(k) = point(cos(k * 0.5), sin(k * 0.5), k * 0.1)
let dbl = (x) => x > 2 ? x * 2 : x + 1
let pts = [stepPt(i) for i in 0..10]
let spiral = curve(pts)
let acc = 0
for j in 0..5 {
  acc = acc + dbl(j)
}
let pLast = pts[9]
"
  let fLoop := evalScriptToFrame "R3" scriptLoop
  assertTrue "fn + lambda + for + listComp no errors" fLoop.diagnostics.isEmpty
  assertTrue "listComp curve emitted" (fLoop.curves.size == 1 && fLoop.curves[0]!.points.size == 30)
  assertTrue "indexed pt extracted" (fLoop.points.size ≥ 1)

  -- Safety guard: > 512 loop iterations rejected cleanly without hanging!
  let fBigLoop := evalScriptToFrame "PGA3" "for i in 0..1000 { let x = i }"
  assertTrue "loop safety limit triggers diagnostic"
    (!fBigLoop.diagnostics.isEmpty && hasSubstr fBigLoop.diagnostics[0]! "512")

  -- Safety guard: infinite recursion caught cleanly!
  let fInfRec := evalScriptToFrame "PGA3" "fn boom(x) = boom(x + 1)\nlet y = boom(0)"
  assertTrue "recursion depth limit triggers diagnostic"
    (!fInfRec.diagnostics.isEmpty && hasSubstr fInfRec.diagnostics[0]! "recursion")

  -- Exact Line:Col syntax diagnostic!
  let fBad := evalScriptToFrame "PGA3" "let A = point(1, 0, 0)\nlet B = (1 + )\n"
  assertTrue "syntax error reports Line 2"
    (!fBad.diagnostics.isEmpty && hasSubstr fBad.diagnostics[0]! "Line 2")

  -- Error resilience in CoffeeShop: bad edit preserves last valid scene geometry!
  let cs0 := CoffeeShop.setScript {} "PGA3" "let A = point(1, 0, 0); let B = point(0, 1, 0); let L = A & B"
  let cs1 := CoffeeShop.setScript cs0 "PGA3" "let A = point(1, 0, 0)\nlet broken = ("
  let fRes := CoffeeShop.toSceneFrame cs1 2
  assertTrue "error-resilient frame keeps diagnostics" (!fRes.diagnostics.isEmpty)
  assertTrue "error-resilient frame preserves last valid 2 pts + 1 line"
    (fRes.points.size == 2 && fRes.lines.size == 1)

/-! ## 2. Reactive Draggable Script Handles, Time Animation (`Tick`) & Live `EditCoeff` -/

def testReactiveHandlesAndEditCoeff : IO Unit := do
  let code := "
@basis PGA3
let A = point(1, 0, 0)
let B = point(0, 1, 0)
let L = A & B
let M = (A + B).Normalized
"
  let f0 := evalScriptToFrame "PGA3" code #[] 0.0 1
  assertTrue "initial script 0 diagnostics" f0.diagnostics.isEmpty
  assertTrue "initial script 3 points (A, B, M) + 1 line (L)" (f0.points.size == 3 && f0.lines.size == 1)
  assertTrue "A is draggable handle 0" (f0.points[0]!.role.draggable && f0.points[0]!.handleId == 0)
  assertTrue "B is draggable handle 1" (f0.points[1]!.role.draggable && f0.points[1]!.handleId == 1)
  assertApprox "initial M.x == 0.5" f0.points[2]!.pos.x 0.5
  assertApprox "initial M.y == 0.5" f0.points[2]!.pos.y 0.5

  -- Drag handle 0 (`A`) to `(3.0, 0.0, 0.0)` -> `A`, `M`, AND `L` update reactively!
  let fDragged := evalScriptToFrame "PGA3" code #[(0, ⟨3.0, 0.0, 0.0⟩)] 0.0 2
  assertApprox "dragged A.x == 3.0" fDragged.points[0]!.pos.x 3.0
  assertApprox "derived midpoint M.x == 1.5" fDragged.points[2]!.pos.x 1.5
  assertApprox "derived midpoint M.y == 0.5" fDragged.points[2]!.pos.y 0.5
  -- Verify StudioSession dispatch flow (`evalScript` -> `dragHandle` -> `tick` -> `editCoeff`)
  let mut sess := Studio.create
  sess := Studio.dispatchEvent sess (.evalScript "PGA3" code) true
  sess := Studio.dispatchEvent sess (.dragHandle 0 ⟨3.0, 0.0, 0.0⟩) false
  match validateGsirFrame (Studio.getLastFrame sess) with
  | .error e => throw (IO.userError s!"Dragged script GSIR invalid: {e}")
  | .ok _ => pure ()
  -- Live `EditCoeff` on script variable 0 (`A`): patch `e023` (blade index 13 in PGA3 grade-major!)
  -- In PGA3 grade-major: 0=1; 1..4=e0..e3; 5..10=bivs; 11=e012(bit7), 12=e013(bit11), 13=e023(bit13), 14=e123(bit14)
  sess := Studio.dispatchEvent sess (.editCoeff 0 13 (-4.0)) true
  let fEdited := CoffeeShop.toSceneFrame sess.coffee 5
  assertApprox "EditCoeff patched A.x to 4.0" fEdited.points[0]!.pos.x 4.0
  assertApprox "EditCoeff propagated to derived midpoint M.x == 2.0" fEdited.points[2]!.pos.x 2.0

  -- Live `Tick` animation in script mode
  let animCode := "@basis PGA3\nlet R = motor(0, 1, 0, t, 0)\nlet P = R >>> point(1, 0, 0)"
  let fT0 := evalScriptToFrame "PGA3" animCode #[] 0.0 1
  let fT1 := evalScriptToFrame "PGA3" animCode #[] 1.57079632679 2
  assertApprox "anim t=0 P.x == 1" fT0.points[0]!.pos.x 1.0 1e-2
  assertApprox "anim t=pi/2 P.x == 0" fT1.points[0]!.pos.x 0.0 1e-2

/-! ## 3. Rich Constructors, `graph([...])`, Bunny Slicing, CGA3 OPNS+IPNS & STA -/

def testRichConstructorsAndAlgebras : IO Unit := do
  -- `graph([...])` with hex colors, labels, seg, poly & live Inspect Stash!
  let gCode := "
@basis PGA3
let A = point(-1, 0, 0)
let B = point(1, 0, 0)
let C = point(0, 1, 0)
let L = A & B
graph([0x44aaff, A, B, C, 0xff5566, L, \"Base Line\", seg(A, C), poly(A, B, C)])
"
  let fG := evalScriptToFrame "PGA3" gCode
  assertTrue "graph() 0 diagnostics" fG.diagnostics.isEmpty
  assertTrue "graph() 3 pts + 1 line + 1 seg + 1 poly mesh/curve"
    (fG.points.size == 3 && fG.lines.size == 1 && fG.segments.size == 1 &&
     fG.meshAssets.size == 1 && fG.curves.size == 1)
  assertTrue "graph() attached label 'Base Line'" (fG.lines[0]!.label == "Base Line")
  assertApprox "graph() applied hex color 0xff5566 R" fG.lines[0]!.color.r 1.0 1e-2
  assertTrue "graph() populated Inspect Stash for A, B, C, L" (fG.inspect.size == 4)

  -- Live Bunny Slicing inside user script!
  let sCode := "@basis PGA3\nlet b = mesh(\"bunny\")\nlet cut = plane(0, 1, 0, -0.1)\nlet res = slice(b, cut)"
  let fS := evalScriptToFrame "PGA3" sCode
  assertTrue "script bunny slice 0 diagnostics" fS.diagnostics.isEmpty
  assertTrue "script bunny slice produces 2 clipped meshes + cut segs + 2D contour"
    (fS.meshAssets.size == 2 && fS.segments.size > 10 && fS.contourOverlay.isSome)

  -- Live `implicit`, `surface`, and `opns` inside user scripts!
  let fImp := evalScriptToFrame "R3" "let m = implicit(\"x^2 + y^2 + z^2 = 1\", 12, 1.4)"
  assertTrue "script implicit() produces mesh" (fImp.diagnostics.isEmpty && fImp.meshAssets.size == 1)
  let fSurf := evalScriptToFrame "R3" "let s = surface(\"0.5*sin(x)*cos(y)\", 2, 14)"
  assertTrue "script surface() produces mesh" (fSurf.diagnostics.isEmpty && fSurf.meshAssets.size == 1)
  let fOpns := evalScriptToFrame "R3" "let g = opns(\"cos(x)*sin(y)+cos(y)*sin(z)+cos(z)*sin(x)\")"
  assertTrue "script opns() emits GLSL3/WGSL/MSL shader + uniform"
    (fOpns.diagnostics.isEmpty && fOpns.opnsShaders.size == 1 && fOpns.opnsUniforms.size == 1)

  -- CGA3 BOTH IPNS (`S1 ^ S2` -> circle!) AND OPNS (`A ^ B` -> pointPair, `circle(A,B,C)` -> circle, `A^B^C^D` -> sphere!)
  let cgaCode := "
@basis CGA3
let A = point(1, 0, 0)
let B = point(-1, 0, 0)
let C = point(0, 1, 0)
let D = point(0, 0, 1)
let pp = A ^ B
let opnsCircle = circle(A, B, C)
let opnsSphere = A ^ B ^ C ^ D
let S1 = sphere(0.4, 0, 0, 0.9)
let S2 = sphere(-0.4, 0, 0, 0.9)
let ipnsCircle = S1 ^ S2
"
  let fCga := evalScriptToFrame "CGA3" cgaCode
  assertTrue "CGA3 OPNS+IPNS 0 diagnostics" fCga.diagnostics.isEmpty
  assertTrue s!"CGA3 pointPair emitted (got {fCga.pointPairs.size})" (fCga.pointPairs.size == 1)
  assertTrue s!"CGA3 2 circles emitted: OPNS + IPNS (got {fCga.circles.size})" (fCga.circles.size == 2)
  assertTrue s!"CGA3 3 spheres emitted: S1, S2, OPNS (got {fCga.spheres.size})" (fCga.spheres.size == 3)

  -- STA `-+++` exact Lorentz boost preserving Minkowski interval `-t'² + x'² = -1`!
  let staCode := "@basis STA\nlet B = boost(1, 0, 0, 0.7)\nlet u = B >>> et"
  let fSta := evalScriptToFrame "STA" staCode
  assertTrue "STA boost 0 diagnostics" fSta.diagnostics.isEmpty
  let uEntry := fSta.inspect[1]!
  let ct := uEntry.coeffs.get! 1 -- et
  let vx := uEntry.coeffs.get! 2 -- ex
  assertApprox "STA boost Minkowski interval -(ct)^2 + x^2 == -1" (-ct * ct + vx * vx) (-1.0) 1e-4

/-! ## 4. Live Round-Trip of ALL 19 Base Flagship Presets + 8 Extra Presets (= 27 Live Scripts!) -/

def testFlagshipPresetScripts : IO Unit := do
  -- Verify every base preset's `sampleCode` executes cleanly with 0 diagnostics & emits valid GSIR!
  for p in presetCatalog do
    let fr := evalScriptToFrame p.algebra p.sampleCode #[] 0.5 1
    if !fr.diagnostics.isEmpty then
      throw (IO.userError s!"FAIL [preset script {p.id}]: {fr.diagnostics[0]!}")
    assertTrue s!"preset script {p.id} emits visual geometry" (hasVisualGeometry fr)
    let raw := encodeFrame fr true
    match validateGsirFrame raw with
    | .error e => throw (IO.userError s!"FAIL [preset script {p.id}] GSIR invalid: {e}")
    | .ok _ => assertTrue s!"preset script {p.id} 8B aligned" (raw.size % 8 == 0)

  -- Verify `toSceneFrame` populates `metaJson.script` on normal preset loads!
  let cs := CoffeeShop.loadPreset {} "pga3d_slicing"
  let frP := CoffeeShop.toSceneFrame cs 1
  assertTrue "pga3d_slicing frame populates script" (hasSubstr frP.script "slice(bunny")
  let metaStr := Json.toMetaJson frP (Json.buildLabelTable frP)
  assertTrue "metaJson includes \"script\" key" (hasSubstr metaStr "\"script\":")

  -- Verify key `PresetsExtra` live scripts (`implicit_gyroid`, `sta_light_cone`, etc.)
  let extraCheckIds := #["cga3d_dipole_field", "sta_light_cone", "sta_em_wave", "sta_rapidity",
                         "implicit_gyroid", "implicit_metaballs", "implicit_schwarz_p", "implicit_genus2"]
  for eid in extraCheckIds do
    match extraPresetCatalog.find? (·.id == eid) with
    | none => throw (IO.userError s!"Missing extra preset {eid}")
    | some ep =>
      let fr := evalScriptToFrame ep.algebra ep.sampleCode #[] 0.4 1
      if !fr.diagnostics.isEmpty then
        throw (IO.userError s!"FAIL [extra script {eid}]: {fr.diagnostics[0]!}")
      assertTrue s!"extra script {eid} emits visual geometry" (hasVisualGeometry fr)
      match validateGsirFrame (encodeFrame fr true) with
      | .error e => throw (IO.userError s!"FAIL [extra script {eid}] GSIR invalid: {e}")
      | .ok _ => pure ()

/-! ## 5. Re-Evaluation Latency Benchmark (µs/frame) -/

def benchLiveScript : IO Unit := do
  let benchCode := "
@basis PGA3
let A = point(0, 0.95, 0)
let B = point(0.9, -0.7, -0.7)
let C = point(-0.9, -0.7, -0.7)
let L = A & B
let P = A & B & C
let M = motor(0, 1, 0, t * 0.5, 0)
let A2 = M >>> A
"
  let iters := 200
  let t0 ← IO.monoNanosNow
  let mut sink : Nat := 0
  for k in [:iters] do
    let fr := evalScriptToFrame "PGA3" benchCode #[(0, ⟨0.1, 0.95, 0.0⟩)] (Float.ofNat k * 0.016) k.toUInt64
    let bytes := encodeFrame fr false
    sink := sink + bytes.size
  let t1 ← IO.monoNanosNow
  assertTrue "benchmark sink > 0" (sink > 0)
  let usPerEval := Float.ofNat (t1 - t0) / (Float.ofNat iters * 1000.0)
  IO.println s!"  [bench] LiveScript PGA3 (parse+eval+classify+GSIR, {iters}x): {usPerEval} µs/frame"

def runAll : IO Unit := do
  testLanguageAndSafety
  IO.println "PASS [1/5] LiveScript v2 syntax (@basis, Algebra, fn, loops, comps), Line:Col diagnostics & safety guards"
  testReactiveHandlesAndEditCoeff
  IO.println "PASS [2/5] Reactive draggable script handles, Tick animation & live EditCoeff multivector overrides"
  testRichConstructorsAndAlgebras
  IO.println "PASS [3/5] graph([0xHex, ...]), live bunny slice, implicit/surface/opns, CGA3 OPNS+IPNS & STA -+++ boosts"
  testFlagshipPresetScripts
  IO.println "PASS [4/5] All 27 flagship preset scripts (19 base + 8 extra) execute cleanly & emit valid 8B GSIR v1"
  benchLiveScript
  IO.println "PASS [5/5] LiveScript v2 re-evaluation benchmark complete"
  IO.println "ALL LIVESCRIPT V2 TESTS PASSED!"

end Tests.LiveScript

def main : IO Unit := Tests.LiveScript.runAll
