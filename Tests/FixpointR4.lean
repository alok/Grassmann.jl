import Grassmann.Studio

/-!
# Round-4 Final Fixpoint Verification Suite (`Tests/FixpointR4.lean`)

Strictly `Init`-only (ZERO `Lean.*`, ZERO `Std.*`, ZERO `DirectSum`, ZERO `sorry`/axioms):
1. **Exact Face-Parallel Ray–AABB Slab (`intersectBox`) Across GLSL3, WGSL, and Metal MSL**:
   - Eliminates the `1e-8` `safeRd` substitution bug so face-parallel rays such as
     `ro = (1, 0, 3), rd = (0, 0, -1), bound = 1` yield exact `[2.0, 4.0]` rather than false
     rejections (`tFar = 0 < tNear = 2`).
   - Verifies exact per-axis `abs(rd.axis) < 1e-12` slab logic across GLSL3, WGSL, and MSL
     and mirrors the exact shader algorithm numerically on face-parallel, edge-parallel,
     interior-face, outside-face, and away-facing rays.
2. **Strictly Scale-Invariant Zero-Set Hit Detection (`f → c·f`, `c > 0`)**:
   - Eliminates the unscaled `abs(fCur) < max(0.001, uThresh)` false-hit shortcut across
     GLSL3, WGSL, and MSL so `0.001*(x - 1.5) @ bound=1` produces **0 hits** (matching CPU
     Marching Tetrahedra `0` vertices) while `0.001*(x - 0.25)` and `x - 0.25` produce
     identical hit distances and shading normals (`gMax > 1e-20`).
   - Verifies exact boundary roots (`fPrev == 0` / `fCur == 0`) hit without bisection drift.
3. **Explicit `SetCamera` Override in Wedge Mode (3D & 2D, Binary `0x09` & JSON)**:
   - Decodes the actual emitted binary `GSIR` v1 `0x01 CAMERA` section bytes from
     `Studio.dispatchBin` / `Studio.dispatchJson` / `Studio.getLastFrame`, proving that
     `SetCamera(distance=6.8, fovDeg=52.0, translated+rotated Motor3)` in Wedge 3D and
     Wedge 2D is preserved verbatim (rather than overwritten with default `5.4`/`4.2`),
     survives `Tick` and `Snapshot`, and resets cleanly on level change (`wedgeAction .next`).

Credits: Michael Reed (`chakravala` / `Grassmann.jl`) & Steven De Keninck (`enkimute` / `ganja.js`).
-/

namespace Tests.FixpointR4

open Grassmann
open Grassmann.Scene Grassmann.Scene.Binary Grassmann.Scene.Json
open Grassmann.Eval Grassmann.Eval.ImplicitExpr Grassmann.Codegen.GPUInit
open Grassmann.CoffeeShop Grassmann.Wedge Grassmann.Studio

private def assertTrue (name : String) (cond : Bool) : IO Unit := do
  if !cond then
    throw (IO.userError s!"FAIL [{name}]")

private def hasSubstr (haystack needle : String) : Bool :=
  (haystack.splitOn needle).length > 1

private def near (a b tol : Float) : Bool :=
  Float.abs (a - b) < tol

private def motorNear (a b : Motor3) (tol : Float) : Bool :=
  near a.s b.s tol && near a.e01 b.e01 tol && near a.e02 b.e02 tol && near a.e03 b.e03 tol &&
  near a.e12 b.e12 tol && near a.e13 b.e13 tol && near a.e23 b.e23 tol && near a.e0123 b.e0123 tol

/-! ## Binary `GSIR` v1 `0x01 CAMERA` Section Decoder -/

private def decodeGsirCamera (buf : ByteArray) : Except String CameraState := do
  let (secCount, _, _) ← validateGsirFrame buf
  for i in [:secCount.toNat] do
    let dOff := 64 + i * 16
    let kind := readU32LE buf dOff
    let sOff := (readU32LE buf (dOff + 8)).toNat
    let sLen := (readU32LE buf (dOff + 12)).toNat
    if kind == secCamera then
      if sLen < 112 then throw s!"0x01 CAMERA section too short ({sLen} B)"
      let motor      := readMotor3 buf sOff
      -- Skip 16×f32 (64 B) column-major mat4 at sOff + 32 .. sOff + 96
      let fovDeg     := readF32LE buf (sOff + 96)
      let distance   := readF32LE buf (sOff + 100)
      let orthoScale := readF32LE buf (sOff + 104)
      let flags      := readU32LE buf (sOff + 108)
      return { motor, fovDeg, distance, orthoScale, isOrtho := (flags &&& 1) != 0 }
  throw "0x01 CAMERA section not found in GSIR frame"

/-! ## Exact Lean Mirror of Emitted `intersectBox` & Scale-Invariant Raymarch -/

private def mirrorIntersectBox (ro rd : Vec3) (b : Float) : Float × Float := Id.run do
  let mut tNear := -1e30
  let mut tFar  :=  1e30
  if Float.abs rd.x < 1e-12 then
    if ro.x < -b || ro.x > b then return (1.0, -1.0)
  else
    let invX := 1.0 / rd.x
    let t0x := (-b - ro.x) * invX
    let t1x := ( b - ro.x) * invX
    tNear := max tNear (min t0x t1x)
    tFar  := min tFar  (max t0x t1x)
  if Float.abs rd.y < 1e-12 then
    if ro.y < -b || ro.y > b then return (1.0, -1.0)
  else
    let invY := 1.0 / rd.y
    let t0y := (-b - ro.y) * invY
    let t1y := ( b - ro.y) * invY
    tNear := max tNear (min t0y t1y)
    tFar  := min tFar  (max t0y t1y)
  if Float.abs rd.z < 1e-12 then
    if ro.z < -b || ro.z > b then return (1.0, -1.0)
  else
    let invZ := 1.0 / rd.z
    let t0z := (-b - ro.z) * invZ
    let t1z := ( b - ro.z) * invZ
    tNear := max tNear (min t0z t1z)
    tFar  := min tFar  (max t0z t1z)
  if tFar < tNear || tFar < 0.0 then return (1.0, -1.0)
  return (max 0.0 tNear, tFar)

private def mirrorRaymarch (f : Vec3 → Float) (ro rd : Vec3) (b : Float) (steps : Nat := 96) :
    Option Float := Id.run do
  let (tNear, tFar) := mirrorIntersectBox ro rd b
  if tFar < tNear || tFar < 0.0 then return none
  let dt := (tFar - tNear) / Float.ofNat steps
  let mut tPrev := tNear
  let mut fPrev := f (Vec3.add ro (Vec3.scale tPrev rd))
  if fPrev == 0.0 then return some tPrev
  for i in [1:steps + 1] do
    let tCur := if i == steps then tFar else tNear + dt * Float.ofNat i
    let fCur := f (Vec3.add ro (Vec3.scale tCur rd))
    if fCur == 0.0 then return some tCur
    if (fPrev < 0.0 && fCur > 0.0) || (fPrev > 0.0 && fCur < 0.0) then
      let mut lo := tPrev
      let mut hi := tCur
      let mut fLo := fPrev
      for _ in [:6] do
        let mid := 0.5 * (lo + hi)
        let fMid := f (Vec3.add ro (Vec3.scale mid rd))
        if (fLo < 0.0 && fMid < 0.0) || (fLo > 0.0 && fMid > 0.0) then
          lo := mid; fLo := fMid
        else
          hi := mid
      return some (0.5 * (lo + hi))
    tPrev := tCur
    fPrev := fCur
  return none

/-! ## 1. Face-Parallel Slab & Scale-Invariant GPU Implicit Codegen -/

def testFaceParallelAndScaleInvariantGpu : IO Unit := do
  -- 1a. Codegen structure audit across GLSL3, WGSL, and Metal MSL
  let shScaled ← IO.ofExcept (compileImplicitExprToGpu "0.001*(x - 1.5)" "scaled_out" 1.0)
  let shFace   ← IO.ofExcept (compileImplicitExprToGpu "x - 1.0" "face_hit" 1.0)
  let shPow5   ← IO.ofExcept (compileImplicitExprToGpu "x^5 + 1" "pow5_r4" 2.0)

  for (tag, sh) in #[("0.001*(x-1.5)", shScaled), ("x-1.0", shFace), ("x^5+1", shPow5)] do
    for (lang, src) in #[("GLSL3", sh.glsl), ("WGSL", sh.wgsl), ("MSL", sh.msl)] do
      assertTrue s!"{tag}/{lang} has per-axis abs(rd.x) < 1e-12 slab check"
        (hasSubstr src "abs(rd.x) < 1e-12" && hasSubstr src "ro.x < -b || ro.x > b")
      assertTrue s!"{tag}/{lang} has per-axis abs(rd.y) < 1e-12 slab check"
        (hasSubstr src "abs(rd.y) < 1e-12" && hasSubstr src "ro.y < -b || ro.y > b")
      assertTrue s!"{tag}/{lang} has per-axis abs(rd.z) < 1e-12 slab check"
        (hasSubstr src "abs(rd.z) < 1e-12" && hasSubstr src "ro.z < -b || ro.z > b")
      assertTrue s!"{tag}/{lang} has NO legacy 1e-8 safeRd hack"
        (!hasSubstr src "safeRd" && !hasSubstr src "1e-8")
      assertTrue s!"{tag}/{lang} has NO unscaled abs(fCur) < max(0.001 false-hit shortcut"
        (!hasSubstr src "abs(fCur) < max(0.001" && !hasSubstr src "abs(fCur) <")
      assertTrue s!"{tag}/{lang} uses strictly scale-invariant sign-change crossing"
        (hasSubstr src "fPrev < 0.0" && hasSubstr src "fCur > 0.0")
      assertTrue s!"{tag}/{lang} hits exact boundary roots (fPrev == 0.0 / fCur == 0.0)"
        (hasSubstr src "fPrev == 0.0" && hasSubstr src "fCur == 0.0")
      assertTrue s!"{tag}/{lang} uses scale-invariant gradient normalization (gMax > 1e-20)"
        (hasSubstr src "gMax > 1e-20")

  -- 1b. Exact CPU Marching Tetrahedra parity for scaled outside/inside planes
  let csScaledOut := CoffeeShop.setImplicit {} "0.001*(x - 1.5)" false 1.0 14
  let frScaledOut := CoffeeShop.toSceneFrame csScaledOut 1
  assertTrue "CPU 0.001*(x-1.5) @ bound=1 produces 0 vertices"
    (frScaledOut.meshAssets.size == 1 && frScaledOut.meshAssets[0]!.positions.size == 0)

  let csScaledIn := CoffeeShop.setImplicit {} "0.001*(x - 0.25)" false 1.0 14
  let frScaledIn := CoffeeShop.toSceneFrame csScaledIn 2
  assertTrue "CPU 0.001*(x-0.25) @ bound=1 produces non-empty plane mesh"
    (frScaledIn.meshAssets.size == 1 && frScaledIn.meshAssets[0]!.positions.size / 3 > 100)

  -- 1c. Exact numerical mirror of intersectBox on Dots' face-parallel counterexamples
  let (tN1, tF1) := mirrorIntersectBox ⟨1.0, 0.0, 3.0⟩ ⟨0.0, 0.0, -1.0⟩ 1.0
  assertTrue s!"face-parallel ro=(1,0,3), rd=(0,0,-1), b=1 yields [2,4] (got [{tN1},{tF1}])"
    (near tN1 2.0 1e-12 && near tF1 4.0 1e-12)

  let (tN2, tF2) := mirrorIntersectBox ⟨-1.0, 1.0, 3.0⟩ ⟨0.0, 0.0, -1.0⟩ 1.0
  assertTrue s!"edge-parallel ro=(-1,1,3), rd=(0,0,-1), b=1 yields [2,4] (got [{tN2},{tF2}])"
    (near tN2 2.0 1e-12 && near tF2 4.0 1e-12)

  let (tN3, tF3) := mirrorIntersectBox ⟨1.0001, 0.0, 3.0⟩ ⟨0.0, 0.0, -1.0⟩ 1.0
  assertTrue "just-outside face-parallel ray ro=(1.0001,0,3) rejects" (tF3 < tN3)

  let (tN4, tF4) := mirrorIntersectBox ⟨0.0, 1.0, 0.0⟩ ⟨1.0, 0.0, 0.0⟩ 1.0
  assertTrue s!"interior top-face ray ro=(0,1,0), rd=(1,0,0), b=1 yields [0,1] (got [{tN4},{tF4}])"
    (near tN4 0.0 1e-12 && near tF4 1.0 1e-12)

  let (tN5, tF5) := mirrorIntersectBox ⟨0.0, 0.0, 3.0⟩ ⟨0.0, 0.0, 1.0⟩ 1.0
  assertTrue "away-facing ray ro=(0,0,3), rd=(0,0,1), b=1 rejects" (tF5 < tN5)

  -- 1d. Exact numerical mirror of scale-invariant raymarch
  let mut falseHits : Nat := 0
  for ix in [:9] do
    for iy in [:9] do
      let u := (Float.ofNat ix - 4.0) * 0.25
      let v := (Float.ofNat iy - 4.0) * 0.25
      let rd := Vec3.normalize ⟨u, v, -1.5⟩
      if (mirrorRaymarch (fun p => 0.001 * (p.x - 1.5)) ⟨0.0, 0.0, 3.0⟩ rd 1.0).isSome then
        falseHits := falseHits + 1
      if (mirrorRaymarch (fun p => 1e-6 * (p.x - 1.5)) ⟨0.0, 0.0, 3.0⟩ rd 1.0).isSome then
        falseHits := falseHits + 1
  assertTrue s!"0.001*(x-1.5) and 1e-6*(x-1.5) @ bound=1 produce 0 hits (got {falseHits})"
    (falseHits == 0)

  match mirrorRaymarch (fun p => p.x - 1.0) ⟨1.0, 0.0, 3.0⟩ ⟨0.0, 0.0, -1.0⟩ 1.0 with
  | some tHit =>
    assertTrue s!"face-parallel x-1.0 @ bound=1 hits at exact t=2.0 (got {tHit})"
      (near tHit 2.0 1e-12)
  | none =>
    throw (IO.userError "FAIL [face-parallel x-1.0 @ bound=1 missed]")

  let rdDiag := Vec3.normalize ⟨0.15, 0.1, -1.0⟩
  match mirrorRaymarch (fun p => p.x - 0.5) ⟨0.0, 0.0, 3.0⟩ rdDiag 1.0,
        mirrorRaymarch (fun p => 0.001 * (p.x - 0.5)) ⟨0.0, 0.0, 3.0⟩ rdDiag 1.0 with
  | some t1, some t2 =>
    assertTrue s!"scale-invariant hit distance: x-0.5 vs 0.001*(x-0.5) ({t1} vs {t2})"
      (near t1 t2 1e-12)
  | _, _ =>
    throw (IO.userError "FAIL [x-0.5 or 0.001*(x-0.5) missed]")

/-! ## 2. Explicit `SetCamera` Override in Wedge Mode (Decoded `GSIR` `0x01 CAMERA`) -/

def testWedgeSetCameraOverride : IO Unit := do
  -- 2a. Wedge 3D: switch to wedge_3d and verify default distance=5.4
  let s0 := Studio.create
  let (s1, f1) ← IO.ofExcept (Studio.dispatchJson s0 "{\"op\":\"loadPreset\",\"id\":\"wedge_3d\"}")
  assertTrue "session switched to wedge mode" (s1.active == .wedge && s1.wedge.dim == .dim3D)
  let camDefault3D ← IO.ofExcept (decodeGsirCamera f1)
  assertTrue s!"Wedge 3D default camera distance ≈ 5.4 (got {camDefault3D.distance})"
    (near camDefault3D.distance 5.4 1e-4 && !camDefault3D.isOrtho)

  -- Dispatch binary 0x09 SetCamera with distance=6.8, fovDeg=52.0, and non-zero translated+rotated motor!
  let customMot3D := Motor3.normalize
    (Motor3.mul (Motor3.translator 0.4 (-0.25) 0.6) (Motor3.orbitCamera 1.1 (-0.4) 6.8))
  let evBin ← IO.ofExcept (encodeInputEventBin (.setCamera customMot3D 52.0 6.8) false)
  let (s2, f2) ← IO.ofExcept (Studio.dispatchBin s1 evBin)
  let camSet3D ← IO.ofExcept (decodeGsirCamera f2)
  assertTrue s!"Wedge 3D binary SetCamera preserves distance=6.8 (got {camSet3D.distance})"
    (near camSet3D.distance 6.8 1e-4)
  assertTrue s!"Wedge 3D binary SetCamera preserves fovDeg=52.0 (got {camSet3D.fovDeg})"
    (near camSet3D.fovDeg 52.0 1e-4)
  assertTrue "Wedge 3D binary SetCamera preserves all 8 Motor3 blades verbatim"
    (motorNear camSet3D.motor customMot3D 1e-4)
  assertTrue "Wedge 3D binary SetCamera stays perspective (isOrtho == false)"
    (!camSet3D.isOrtho)

  -- Verify camera persists across Tick and Snapshot (idempotent cached frame too!)
  let tickBin ← IO.ofExcept (encodeInputEventBin (.tick 0.016 0.016) false)
  let (s3, f3) ← IO.ofExcept (Studio.dispatchBin s2 tickBin)
  let camAfterTick ← IO.ofExcept (decodeGsirCamera f3)
  assertTrue s!"Wedge 3D SetCamera persists after Tick (dist={camAfterTick.distance})"
    (near camAfterTick.distance 6.8 1e-4 && motorNear camAfterTick.motor customMot3D 1e-4)

  let snapBin ← IO.ofExcept (encodeInputEventBin .snapshot true)
  let (s4, f4) ← IO.ofExcept (Studio.dispatchBin s3 snapBin)
  let camAfterSnap ← IO.ofExcept (decodeGsirCamera f4)
  assertTrue s!"Wedge 3D SetCamera persists after Snapshot (dist={camAfterSnap.distance})"
    (near camAfterSnap.distance 6.8 1e-4 && motorNear camAfterSnap.motor customMot3D 1e-4)

  -- Verify JSON control path `setCamera` also updates Wedge camera verbatim
  let jsonCam :=
    "{\"op\":\"setCamera\",\"fovDeg\":58.5,\"distance\":7.25,\"motor\":[0.92,0.12,-0.08,0.15,0.22,-0.14,0.25,0.03]}"
  let (s5, f5) ← IO.ofExcept (Studio.dispatchJson s4 jsonCam)
  let camJson3D ← IO.ofExcept (decodeGsirCamera f5)
  assertTrue s!"Wedge 3D JSON SetCamera preserves distance=7.25 & fov=58.5 (got dist={camJson3D.distance}, fov={camJson3D.fovDeg})"
    (near camJson3D.distance 7.25 1e-4 && near camJson3D.fovDeg 58.5 1e-4)
  assertTrue "Wedge 3D JSON SetCamera preserves translation blades (e01,e02,e03,e0123)"
    (near camJson3D.motor.e01 0.12 1e-4 && near camJson3D.motor.e02 (-0.08) 1e-4 &&
     near camJson3D.motor.e03 0.15 1e-4 && near camJson3D.motor.e0123 0.03 1e-4)

  -- Advancing level resets customCamera cleanly back to level default (distance=5.4)
  let nextBin ← IO.ofExcept (encodeInputEventBin (.wedgeAction .next 0) false)
  let (_, fNext) ← IO.ofExcept (Studio.dispatchBin s5 nextBin)
  let camNext ← IO.ofExcept (decodeGsirCamera fNext)
  assertTrue s!"Wedge 3D level change resets camera to default 5.4 (got {camNext.distance})"
    (near camNext.distance 5.4 1e-4)

  -- 2b. Wedge 2D: preserves distance=6.8, motor, isOrtho=true, and orthoScale=6.8/4.2
  let (s2d0, f2d0) ← IO.ofExcept (Studio.dispatchJson s0 "{\"op\":\"loadPreset\",\"id\":\"wedge_2d\"}")
  assertTrue "session switched to Wedge 2D" (s2d0.active == .wedge && s2d0.wedge.dim == .dim2D)
  let camDef2D ← IO.ofExcept (decodeGsirCamera f2d0)
  assertTrue "Wedge 2D default isOrtho == true" camDef2D.isOrtho

  let customMot2D := Motor3.translator 0.5 (-0.3) (-6.8)
  let ev2d ← IO.ofExcept (encodeInputEventBin (.setCamera customMot2D 45.0 6.8) false)
  let (_, f2d1) ← IO.ofExcept (Studio.dispatchBin s2d0 ev2d)
  let camSet2D ← IO.ofExcept (decodeGsirCamera f2d1)
  assertTrue s!"Wedge 2D SetCamera preserves distance=6.8, isOrtho=true, orthoScale≈6.8/4.2 (got dist={camSet2D.distance}, ortho={camSet2D.orthoScale})"
    (near camSet2D.distance 6.8 1e-4 && camSet2D.isOrtho && near camSet2D.orthoScale (6.8 / 4.2) 1e-4)
  assertTrue "Wedge 2D SetCamera preserves Motor3 verbatim"
    (motorNear camSet2D.motor customMot2D 1e-4)

def main : IO Unit := do
  testFaceParallelAndScaleInvariantGpu
  IO.println "PASS: 1. Face-parallel slab intersectBox + scale-invariant zero-set GPU codegen & CPU parity"
  testWedgeSetCameraOverride
  IO.println "PASS: 2. Wedge 3D/2D explicit SetCamera override preserved verbatim in decoded GSIR 0x01 CAMERA"
  IO.println "ALL FIXPOINT ROUND-4 TESTS PASSED"

end Tests.FixpointR4

def main : IO Unit := Tests.FixpointR4.main
