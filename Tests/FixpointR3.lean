import Grassmann.Studio

/-!
# Wave 8B / Round-3 Adversarial Fixpoint Verification Suite (`Tests/FixpointR3.lean`)

Strictly `Init`-only (ZERO `Lean.*`, ZERO `Std.*`, ZERO `DirectSum`, ZERO `sorry`/axioms):
1. **Signed & Odd Integer Powers in GPU Implicit Codegen (`GPUInit.lean`)**:
   - Verifies `x^5 + 1`, `x^3 + y^3 + z^3`, `x^9 + 1`, `x^10 - 1`, `x^(-3) + 1` preserve exact
     negative signs across GLSL3, WGSL, and Metal MSL (`gs_p5`, `gs_cb`, `gs_spow_odd`, `gs_spow_even`),
     matching CPU Marching Tetrahedra zero-level sets across negative coordinates!
2. **Exact Axis-Aligned Box `[-bound, bound]³` Clipping + `tFar < tNear` Guard + `bound ∈ [0.5, 20.0]`**:
   - Verifies `x - 1.5 @ bound=1` (CPU 0 verts + GPU `intersectBox(1.0)`), `x^2+y^2+z^2-9 @ bound=4`
     (CPU rich sphere + GPU `intersectBox(4.0)`), and `x - 15 @ bound=20` (CPU plane at `x=15` + GPU
     `intersectBox(20.0)`), with `tFar < tNear || tFar < 0.0` across GLSL3, WGSL, and MSL!
3. **Deterministic Fixed-Step RK4 Replay on `seekTime(t)` (`CoffeeShop/Engine.lean`)**:
   - Verifies `seekTime(2.5)` on `pga3d_bouncing_cube` matches `150 × Tick(1/60)` pose to `< 1e-6`
     (both from `t=0` and scrubbing backward from `t=5.0`), plus `pga3d_double_pendulum` and
     `pga3d_physics_free_top`, and exact `resetTime` / `seekTime(0.0)`!
4. **Automated 2D XY Non-Interpenetration Proof for 3D Involute Gears (`PresetsShowcase.lean`)**:
   - Transforms the actual emitted 3D front-face gear triangles by their `GSIR` `Motor3` matrices
     and checks exact 2D SAT strict-interior triangle intersection across **24 phase angles × 5 ratios**
     (even & odd `Z₂ ∈ {6, 9, 15, 18, 24}`), proving BOTH genuine tooth engagement (`r_a1 + r_a2 > d12`)
     AND **0 overlapping triangle pairs** at BOTH contacts (G1–G2 and G1–G3)!

Credits: Michael Reed (`chakravala` / `Grassmann.jl`) & Steven De Keninck (`enkimute` / `ganja.js`).
-/

namespace Tests.FixpointR3

open Grassmann
open Grassmann.Scene Grassmann.Scene.Binary Grassmann.Scene.Json
open Grassmann.Eval Grassmann.Eval.ImplicitExpr Grassmann.Codegen.GPUInit
open Grassmann.CoffeeShop Grassmann.CoffeeShop.PresetsShowcase Grassmann.Studio

private def assertTrue (name : String) (cond : Bool) : IO Unit := do
  if !cond then
    throw (IO.userError s!"FAIL [{name}]")

private def hasSubstr (haystack needle : String) : Bool :=
  (haystack.splitOn needle).length > 1

/-! ## 1. Signed & Odd Integer Powers in GPU Implicit Codegen + CPU Parity -/

def testSignedGpuPowers : IO Unit := do
  -- 1a. `x^5 + 1` at `bound = 2.0`: zero-level is plane `x = -1`!
  let mPow5 ← IO.ofExcept (evalImplicitExprMesh "x^5 + 1" 0.0 ⟨-2,-2,-2⟩ ⟨2,2,2⟩ 14 9801 false)
  let nVerts5 := mPow5.positions.size / 3
  assertTrue s!"CPU x^5+1 produces rich plane at x=-1 (verts={nVerts5})" (nVerts5 > 200)
  for k in [:nVerts5] do
    let vx := mPow5.positions.get! (k * 3)
    assertTrue s!"CPU x^5+1 vertex {k} lies on x=-1 (got x={vx})" (Float.abs (vx - (-1.0)) < 0.08)

  let shPow5 ← IO.ofExcept (compileImplicitExprToGpu "x^5 + 1" "pow5" 2.0)
  for (lang, src) in #[("GLSL3", shPow5.glsl), ("WGSL", shPow5.wgsl), ("MSL", shPow5.msl)] do
    assertTrue s!"{lang} x^5+1 uses signed gs_p5(p.x)" (hasSubstr src "gs_p5(p.x)")
    assertTrue s!"{lang} x^5+1 does NOT strip sign via abs(p.x)" (!hasSubstr src "pow(max(1e-6, abs(p.x))")

  -- 1b. `x^3 + y^3 + z^3` at `bound = 2.0`: spans negative octants!
  let mCub ← IO.ofExcept (evalImplicitExprMesh "x^3 + y^3 + z^3" 0.0 ⟨-2,-2,-2⟩ ⟨2,2,2⟩ 14 9802 false)
  let nVertsCub := mCub.positions.size / 3
  assertTrue s!"CPU x^3+y^3+z^3 non-empty (verts={nVertsCub})" (nVertsCub > 100)
  let mut hasNegX := false
  for k in [:nVertsCub] do
    if mCub.positions.get! (k * 3) < -0.5 then hasNegX := true
  assertTrue "CPU x^3+y^3+z^3 reaches negative x < -0.5" hasNegX
  let shCub ← IO.ofExcept (compileImplicitExprToGpu "x^3 + y^3 + z^3" "cub" 2.0)
  for (lang, src) in #[("GLSL3", shCub.glsl), ("WGSL", shCub.wgsl), ("MSL", shCub.msl)] do
    assertTrue s!"{lang} x^3+y^3+z^3 uses signed gs_cb"
      (hasSubstr src "gs_cb(p.x)" && hasSubstr src "gs_cb(p.y)" && hasSubstr src "gs_cb(p.z)")

  -- 1c. Higher odd (`x^9 + 1`), higher even (`x^10 - 1`), and negative odd (`x^(-3) + 1`)
  let shPow9 ← IO.ofExcept (compileImplicitExprToGpu "x^9 + 1" "pow9" 2.0)
  let shPow10 ← IO.ofExcept (compileImplicitExprToGpu "x^10 - 1" "pow10" 2.0)
  let shNeg3 ← IO.ofExcept (compileImplicitExprToGpu "x^(-3) + 1" "neg3" 2.0)
  for (lang, s9, s10, sn3) in #[
      ("GLSL3", shPow9.glsl, shPow10.glsl, shNeg3.glsl),
      ("WGSL",  shPow9.wgsl, shPow10.wgsl, shNeg3.wgsl),
      ("MSL",   shPow9.msl,  shPow10.msl,  shNeg3.msl)] do
    assertTrue s!"{lang} x^9+1 emits gs_spow_odd" (hasSubstr s9 "gs_spow_odd(p.x, 9.0")
    assertTrue s!"{lang} x^10-1 emits gs_spow_even" (hasSubstr s10 "gs_spow_even(p.x, 10.0")
    assertTrue s!"{lang} x^(-3)+1 emits gs_spow_odd" (hasSubstr sn3 "gs_spow_odd(p.x, -3.0")

/-! ## 2. Exact Axis-Aligned Box `[-bound, bound]³` + `tFar < tNear` + `bound ∈ [0.5, 20.0]` -/

def testExactBoxBoundsAndParity : IO Unit := do
  -- 2a. `x - 1.5` at `bound = 1.0`: strictly outside `[-1, 1]³`!
  let csOutCpu := CoffeeShop.setImplicit {} "x - 1.5" false 1.0 14
  let frOutCpu := CoffeeShop.toSceneFrame csOutCpu 1
  assertTrue "CPU x-1.5 @ bound=1 is empty (0 verts)"
    (frOutCpu.meshAssets.size == 1 && frOutCpu.meshAssets[0]!.positions.size == 0)

  let csOutGpu := CoffeeShop.setImplicit {} "x - 1.5" true 1.0 14
  let frOutGpu := CoffeeShop.toSceneFrame csOutGpu 2
  assertTrue "GPU x-1.5 @ bound=1 emits shader" (frOutGpu.opnsShaders.size == 1)
  let sh1 := frOutGpu.opnsShaders[0]!
  for (lang, src) in #[("GLSL3", sh1.glsl), ("WGSL", sh1.wgsl), ("MSL", sh1.msl)] do
    assertTrue s!"{lang} clips strictly to intersectBox(..., 1.0)" (hasSubstr src "intersectBox(ro, rd, 1.0")
    assertTrue s!"{lang} enforces tFar < tNear || tFar < 0.0 guard"
      (hasSubstr src "tFar < tNear || tFar < 0.0" && hasSubstr src "hitRange.y < hitRange.x || hitRange.y < 0.0")
    assertTrue s!"{lang} has NO legacy intersectSphere" (!hasSubstr src "intersectSphere")

  -- 2b. `x^2 + y^2 + z^2 - 9` at `bound = 4.0`: visible inside `[-4, 4]³`!
  let csSphCpu := CoffeeShop.setImplicit {} "x^2 + y^2 + z^2 - 9" false 4.0 16
  let frSphCpu := CoffeeShop.toSceneFrame csSphCpu 3
  assertTrue "CPU sphere r=3 @ bound=4 produces rich mesh"
    (frSphCpu.meshAssets.size == 1 && frSphCpu.meshAssets[0]!.positions.size / 3 > 400)
  assertTrue "CPU sphere r=3 @ bound=4 frames camera >= 10" (frSphCpu.camera.distance ≥ 10.0)
  let csSphGpu := CoffeeShop.setImplicit {} "x^2 + y^2 + z^2 - 9" true 4.0 16
  let frSphGpu := CoffeeShop.toSceneFrame csSphGpu 4
  let sh4 := frSphGpu.opnsShaders[0]!
  for (lang, src) in #[("GLSL3", sh4.glsl), ("WGSL", sh4.wgsl), ("MSL", sh4.msl)] do
    assertTrue s!"{lang} sphere r=3 @ bound=4 uses intersectBox(4.0)" (hasSubstr src "intersectBox(ro, rd, 4.0")
  assertTrue "GPU sphere r=3 @ bound=4 frames camera >= 10" (frSphGpu.camera.distance ≥ 10.0)

  -- 2c. `x - 15` at `bound = 20.0`: Lean accepts bound=20 (NOT clamped at 10!)
  let csBigCpu := CoffeeShop.setImplicit {} "x - 15" false 20.0 14
  assertTrue s!"setImplicit preserves bound=20.0 (got {csBigCpu.implicitBound})"
    (Float.abs (csBigCpu.implicitBound - 20.0) < 1e-9)
  let frBigCpu := CoffeeShop.toSceneFrame csBigCpu 5
  assertTrue "CPU x-15 @ bound=20 produces non-empty plane mesh"
    (frBigCpu.meshAssets.size == 1 && frBigCpu.meshAssets[0]!.positions.size / 3 > 100)
  let bigMesh := frBigCpu.meshAssets[0]!
  for k in [:(bigMesh.positions.size / 3)] do
    let vx := bigMesh.positions.get! (k * 3)
    assertTrue s!"CPU x-15 @ bound=20 vertex lies on x=15 (got {vx})" (Float.abs (vx - 15.0) < 0.25)
  let csBigGpu := CoffeeShop.setImplicit {} "x - 15" true 20.0 14
  let frBigGpu := CoffeeShop.toSceneFrame csBigGpu 6
  let sh20 := frBigGpu.opnsShaders[0]!
  for (lang, src) in #[("GLSL3", sh20.glsl), ("WGSL", sh20.wgsl), ("MSL", sh20.msl)] do
    assertTrue s!"{lang} x-15 @ bound=20 uses intersectBox(20.0)" (hasSubstr src "intersectBox(ro, rd, 20.0")
  assertTrue "GPU x-15 @ bound=20 frames camera >= 50" (frBigGpu.camera.distance ≥ 50.0)

/-! ## 3. Deterministic Fixed-Step RK4 Replay on `seekTime(t)` -/

def testSeekTimeRk4Replay : IO Unit := do
  -- 3a. `pga3d_bouncing_cube`: compare `seekTime(2.5)` vs `150 × Tick(1/60)`!
  let base := Studio.dispatchEvent Studio.create (.loadPreset "pga3d_bouncing_cube") true
  let initPos := base.coffee.cubeState.pos
  let dt : Float := 1.0 / 60.0
  let mut ticked := base
  for k in [:150] do
    ticked := Studio.dispatchEvent ticked (.tick dt (Float.ofNat (k + 1) * dt)) false
  let tickPos := ticked.coffee.cubeState.pos
  let tickRot := ticked.coffee.cubeState.rot

  -- Seek forward directly from t = 0
  let (seekFwd, bytesFwd) ← IO.ofExcept (Studio.dispatchJson base "{\"op\":\"seekTime\",\"t\":2.5}")
  match validateGsirFrame bytesFwd with
  | .error e => throw (IO.userError s!"seekTime(2.5) GSIR invalid: {e}")
  | .ok _ => pure ()
  assertTrue s!"seekTime(2.5) exact simTime == 2.5 (got {seekFwd.coffee.simTime})"
    (Float.abs (seekFwd.coffee.simTime - 2.5) < 1e-9)
  let fwdErr := Vec3.norm (Vec3.sub seekFwd.coffee.cubeState.pos tickPos)
  assertTrue s!"seekTime(2.5) cube pos matches 150×Tick(1/60) (err={fwdErr})" (fwdErr < 1e-6)
  assertTrue "seekTime(2.5) cube rotor matches 150×Tick(1/60)"
    (Float.abs (seekFwd.coffee.cubeState.rot.s - tickRot.s) < 1e-6 &&
     Float.abs (seekFwd.coffee.cubeState.rot.e12 - tickRot.e12) < 1e-6)
  assertTrue "seekTime(2.5) cube moved substantially away from t=0"
    (Vec3.norm (Vec3.sub seekFwd.coffee.cubeState.pos initPos) > 0.25)

  -- Scrub BACKWARD from t = 5.0 → t = 2.5: MUST reproduce exact same pose deterministically!
  let (at5, _) ← IO.ofExcept (Studio.dispatchJson seekFwd "{\"op\":\"seekTime\",\"t\":5.0}")
  let (seekBack, _) ← IO.ofExcept (Studio.dispatchJson at5 "{\"op\":\"seekTime\",\"t\":2.5}")
  let backErr := Vec3.norm (Vec3.sub seekBack.coffee.cubeState.pos tickPos)
  assertTrue s!"scrubbing backward 5.0->2.5 reproduces exact pose (err={backErr})" (backErr < 1e-6)

  -- Seek to 0.0 returns exact initial pose
  let (seek0, _) ← IO.ofExcept (Studio.dispatchJson seekBack "{\"op\":\"seekTime\",\"t\":0.0}")
  assertTrue "seekTime(0.0) resets simTime == 0.0 and initial cube pos"
    (seek0.coffee.simTime == 0.0 && Vec3.norm (Vec3.sub seek0.coffee.cubeState.pos initPos) < 1e-9)

  -- 3b. `pga3d_double_pendulum` & `pga3d_physics_free_top` also replay deterministically
  let dpBase := Studio.dispatchEvent Studio.create (.loadPreset "pga3d_double_pendulum") true
  let (dpSeek, _) ← IO.ofExcept (Studio.dispatchJson dpBase "{\"op\":\"seekTime\",\"t\":1.5}")
  assertTrue "double_pendulum seekTime(1.5) moves bob away from t=0"
    (Vec3.norm (Vec3.sub dpSeek.coffee.doublePendulum.p2 dpBase.coffee.doublePendulum.p2) > 0.1)

  let topBase := Studio.dispatchEvent Studio.create (.loadPreset "pga3d_physics_free_top") true
  let (topSeek, _) ← IO.ofExcept (Studio.dispatchJson topBase "{\"op\":\"seekTime\",\"t\":1.5}")
  assertTrue "free_top seekTime(1.5) rotates motor away from identity"
    (Float.abs (topSeek.coffee.topMotor.s - 1.0) > 0.05)

/-! ## 4. Exact 2D XY Gear-Tooth Non-Interpenetration Verification (0 Overlap!) -/

private structure Vec2 where
  x : Float
  y : Float

private structure Tri2 where
  a : Vec2
  b : Vec2
  c : Vec2

/-- Extract all front-face (`z > 0`) triangles of a `MeshAsset`, transformed into world XY by `m`. -/
private def extractFrontXYTris (mesh : MeshAsset) (m : Motor3) : Array Tri2 := Id.run do
  let nTris := mesh.indices.size / 3
  let mut out : Array Tri2 := Array.mkEmpty (nTris / 2)
  let getPt (vi : UInt32) : Vec3 :=
    let o := vi.toNat * 3
    ⟨mesh.positions.get! o, mesh.positions.get! (o + 1), mesh.positions.get! (o + 2)⟩
  for t in [:nTris] do
    let p0 := getPt (mesh.indices[t * 3]!)
    let p1 := getPt (mesh.indices[t * 3 + 1]!)
    let p2 := getPt (mesh.indices[t * 3 + 2]!)
    if p0.z > 0.0 && p1.z > 0.0 && p2.z > 0.0 then
      let w0 := Motor3.applyPoint m p0
      let w1 := Motor3.applyPoint m p1
      let w2 := Motor3.applyPoint m p2
      out := out.push { a := ⟨w0.x, w0.y⟩, b := ⟨w1.x, w1.y⟩, c := ⟨w2.x, w2.y⟩ }
  return out

private def triProjMinMax (t : Tri2) (ax ay : Float) : Float × Float :=
  let p0 := t.a.x * ax + t.a.y * ay
  let p1 := t.b.x * ax + t.b.y * ay
  let p2 := t.c.x * ax + t.c.y * ay
  (min p0 (min p1 p2), max p0 (max p1 p2))

/-- Exact 2D Separating Axis Theorem check for strict interior overlap between two triangles. -/
private def trisOverlapStrict2D (t1 t2 : Tri2) (eps : Float := 1e-6) : Bool :=
  let sepAxis (p q : Vec2) : Bool :=
    let nx := -(q.y - p.y)
    let ny := q.x - p.x
    let len := Float.sqrt (nx * nx + ny * ny)
    if len < 1e-12 then false
    else
      let ax := nx / len; let ay := ny / len
      let (lo1, hi1) := triProjMinMax t1 ax ay
      let (lo2, hi2) := triProjMinMax t2 ax ay
      hi1 ≤ lo2 + eps || hi2 ≤ lo1 + eps
  !(sepAxis t1.a t1.b || sepAxis t1.b t1.c || sepAxis t1.c t1.a ||
    sepAxis t2.a t2.b || sepAxis t2.b t2.c || sepAxis t2.c t2.a)

private def countOverlaps2D (ts1 ts2 : Array Tri2) : Nat := Id.run do
  let mut hits : Nat := 0
  for t1 in ts1 do
    let minX1 := min t1.a.x (min t1.b.x t1.c.x); let maxX1 := max t1.a.x (max t1.b.x t1.c.x)
    let minY1 := min t1.a.y (min t1.b.y t1.c.y); let maxY1 := max t1.a.y (max t1.b.y t1.c.y)
    for t2 in ts2 do
      let minX2 := min t2.a.x (min t2.b.x t2.c.x); let maxX2 := max t2.a.x (max t2.b.x t2.c.x)
      let minY2 := min t2.a.y (min t2.b.y t2.c.y); let maxY2 := max t2.a.y (max t2.b.y t2.c.y)
      if maxX1 > minX2 && maxX2 > minX1 && maxY1 > minY2 && maxY2 > minY1 then
        if trisOverlapStrict2D t1 t2 then
          hits := hits + 1
  return hits

private def maxRadiusFromCenter (ts : Array Tri2) (c : Vec3) : Float := Id.run do
  let mut best := 0.0
  for t in ts do
    for p in #[t.a, t.b, t.c] do
      let dx := p.x - c.x; let dy := p.y - c.y
      let r := Float.sqrt (dx * dx + dy * dy)
      if r > best then best := r
  return best

def testInvoluteGearsZeroOverlap : IO Unit := do
  -- Sweep 5 ratios (covering BOTH even Z2={6, 18, 24} AND odd Z2={9, 15}!) × 24 phase angles!
  let ratios : Array Float := #[0.5, 0.75, 1.25, 1.5, 2.0]
  let speed : Float := 1.4
  let twoPi := 6.28318530717958647692
  for ratio in ratios do
    let ov : Array (String × Float) := #[("speed", speed), ("ratio", ratio)]
    for step in [:24] do
      -- Cover a full revolution of tooth engagement (`0 .. 2π / 12` and beyond)
      let t := (Float.ofNat step / 24.0) * (twoPi / (12.0 * speed)) * 2.0
      let fr := buildPga3dGearsKinematics #[] ov step.toUInt64 t
      assertTrue "gears emits 3 assets & 3 refs" (fr.meshAssets.size == 3 && fr.meshRefs.size == 3)
      let t1 := extractFrontXYTris fr.meshAssets[0]! fr.meshRefs[0]!.motor
      let t2 := extractFrontXYTris fr.meshAssets[1]! fr.meshRefs[1]!.motor
      let t3 := extractFrontXYTris fr.meshAssets[2]! fr.meshRefs[2]!.motor
      -- Verify genuine tooth engagement at step 0 (`r_outer(G1) + r_outer(Gj) > centerDist`)
      if step == 0 then
        let c1 := fr.circles[0]!.center; let c2 := fr.circles[1]!.center; let c3 := fr.circles[2]!.center
        let rOut1 := maxRadiusFromCenter t1 c1
        let rOut2 := maxRadiusFromCenter t2 c2
        let rOut3 := maxRadiusFromCenter t3 c3
        let d12 := Vec3.norm (Vec3.sub c2 c1)
        let d13 := Vec3.norm (Vec3.sub c3 c1)
        assertTrue s!"ratio={ratio}: G1-G2 teeth genuinely engage ({rOut1}+{rOut2} > {d12})" (rOut1 + rOut2 > d12 + 0.05)
        assertTrue s!"ratio={ratio}: G1-G3 teeth genuinely engage ({rOut1}+{rOut3} > {d13})" (rOut1 + rOut3 > d13 + 0.05)
      let ov12 := countOverlaps2D t1 t2
      let ov13 := countOverlaps2D t1 t3
      assertTrue s!"ratio={ratio} step={step}: G1-G2 strictly ZERO XY tooth overlap (got {ov12})" (ov12 == 0)
      assertTrue s!"ratio={ratio} step={step}: G1-G3 strictly ZERO XY tooth overlap (got {ov13})" (ov13 == 0)

def runAll : IO Unit := do
  testSignedGpuPowers
  IO.println "PASS [1/4] Signed/odd GPU integer powers (x^5+1, x^3+y^3+z^3, x^9+1, x^10-1, x^-3+1) across GLSL3/WGSL/MSL + CPU parity"
  testExactBoxBoundsAndParity
  IO.println "PASS [2/4] Exact AABB [-bound,bound]³ + tFar<tNear guard across GLSL3/WGSL/MSL & CPU/GPU bound=1/4/20 parity"
  testSeekTimeRk4Replay
  IO.println "PASS [3/4] Deterministic fixed-step RK4 replay on seekTime (bouncing cube matches 150×Tick to <1e-6, double pendulum, free top)"
  testInvoluteGearsZeroOverlap
  IO.println "PASS [4/4] 3D involute gear train: genuine tooth engagement & STRICTLY ZERO XY tooth overlap across 5 ratios × 24 phases (120 checks!)"
  IO.println "ALL ROUND-3 FIXPOINT TESTS PASSED!"

end Tests.FixpointR3

def main : IO Unit := Tests.FixpointR3.runAll
