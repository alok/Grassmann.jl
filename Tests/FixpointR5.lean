import Grassmann.Studio

/-!
# Round-5 Mathematical Fixpoint Verification Suite (`Tests/FixpointR5.lean`)

Strictly `Init`-only (ZERO `Lean.*`, ZERO `Std.*`, ZERO `DirectSum`, ZERO `sorry`/axioms):
1. **P1 — IEEE Float32-Safe Scientific Literal Formatting (`GPUInit.fmtFloat`)**:
   - Eliminates fixed-6-decimal underflow (`0.0000001` → `0.000000`) across GLSL3, WGSL, and MSL
     by emitting clean scientific notation (`1.000000e-7`, `-2.500000e-7`, `1.000000e-20`, `1.000000e12`)
     for nonzero `|v| < 1e-4 || |v| >= 1e7`, clamped safely to normal IEEE-754 float32 range.
   - Verifies `0.0000001*(x - 1.5) @ bound=1` emits `1.000000e-7` (zero `0.000000 *`) across
     all 3 GPU backends AND produces 0 vertices on CPU Marching Tetrahedra.
2. **P2 — Repeated-Root & Thin Two-Sheet Implicit Surfaces (`gs_refine_min`)**:
   - Verifies GLSL3, WGSL, and MSL emit the 3-point local-minimum stencil + 16-step golden-section
     minimizer `gs_refine_min` (with early-exit sign-flip bisection for sub-step thin two-sheets
     AND strictly interior scale-invariant acceptance `gMin < g0 && gMin < g2 && gMin <= 1e-5 * gMaxEnd`
     for repeated roots), plus 2nd-derivative diagonal normal fallback (`h2`) & `-rd` unit fallback.
   - Numerically mirrors the exact emitted raymarcher on:
     - `0.0000001*(x - 1.5) @ bound=1` & `1e-20*(x - 1.000001) @ bound=1` → **0/81 hits**
     - `x^2 + 0.01 @ bound=1` & `x^2 + 1e-7 @ bound=1` → **0/81 hits** (positive paraboloids never false-hit)
     - `(x - 0.12345)^2 @ bound=1` & `1e-7*(x - 0.12345)^2 @ bound=1` → **hits at `x ≈ 0.12345`** with exact unit normal `|N.x| ≈ 1`
     - `100*(x - 0.115)*(x - 0.107) @ bound=1` (width `0.008 < dt = 0.0208`) → **hits front sheet at `x ≈ 0.107` (+x ray) & `x ≈ 0.115` (-x ray)**
     - `(x - 0.995)^2 @ bound=1` (first-step boundary valley) → **hits at `x ≈ 0.995`**
     - Preserves Round-3/4 invariants (`x^5 + 1 @ bound=2`, `x - 15 @ bound=20`, `0.001*(x - 1.5) @ bound=1`, face-parallel `ro=(1,0,3), rd=(0,0,-1)`).

Credits: Michael Reed (`chakravala` / `Grassmann.jl`) & Steven De Keninck (`enkimute` / `ganja.js`).
-/

namespace Tests.FixpointR5

open Grassmann
open Grassmann.Scene Grassmann.Eval Grassmann.Eval.ImplicitExpr
open Grassmann.Codegen.GPUInit Grassmann.CoffeeShop

private def assertTrue (name : String) (cond : Bool) : IO Unit := do
  if !cond then
    throw (IO.userError s!"FAIL [{name}]")

private def hasSubstr (haystack needle : String) : Bool :=
  (haystack.splitOn needle).length > 1

private def near (a b tol : Float) : Bool :=
  Float.abs (a - b) < tol

/-! ## Exact Lean Mirror of Emitted Round-5 Raymarcher (`intersectBox` + `gs_refine_min` + `N`) -/

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

private def mirrorRefineMin (f : Vec3 → Float) (ro rd : Vec3)
    (ta tb tMidInit gMidInit s g0 g2 : Float) : Option Float := Id.run do
  let mut ga := ta
  let mut gb := tb
  let invPhi : Float := 0.61803398875
  let mut gc := gb - (gb - ga) * invPhi
  let mut gd := ga + (gb - ga) * invPhi
  let mut fc := s * f (Vec3.add ro (Vec3.scale gc rd))
  let mut fd := s * f (Vec3.add ro (Vec3.scale gd rd))
  let mut flipped := false
  let mut tFlip := ta
  if fc <= 0.0 then
    flipped := true; tFlip := gc
  else if fd <= 0.0 then
    flipped := true; tFlip := gd
  else
    for _ in [:32] do
      if !flipped then
        if fc < fd then
          gb := gd; gd := gc; fd := fc
          gc := gb - (gb - ga) * invPhi
          fc := s * f (Vec3.add ro (Vec3.scale gc rd))
          if fc <= 0.0 then flipped := true; tFlip := gc
        else
          ga := gc; gc := gd; fc := fd
          gd := ga + (gb - ga) * invPhi
          fd := s * f (Vec3.add ro (Vec3.scale gd rd))
          if fd <= 0.0 then flipped := true; tFlip := gd
  if flipped then
    let mut lo := if tMidInit > ta && tFlip > tMidInit then tMidInit else ta
    let mut hi := tFlip
    for _ in [:6] do
      let mid := 0.5 * (lo + hi)
      if s * f (Vec3.add ro (Vec3.scale mid rd)) > 0.0 then lo := mid else hi := mid
    return some (0.5 * (lo + hi))
  let mut tMin := if fc < fd then gc else gd
  let mut gMin := min fc fd
  if tMidInit > ta && gMidInit < gMin then
    gMin := gMidInit; tMin := tMidInit
  let gMaxEnd := max g0 g2
  if gMaxEnd > 0.0 && gMin < g0 && gMin < g2 && gMin <= 1e-8 * gMaxEnd then
    let delta := 0.01 * (tb - ta)
    let gL := s * f (Vec3.add ro (Vec3.scale (max ta (tMin - delta)) rd))
    let gR := s * f (Vec3.add ro (Vec3.scale (min tb (tMin + delta)) rd))
    let gLoc := max gL gR
    if gL <= 0.0 || gR <= 0.0 || (gLoc > 0.0 && gMin <= 1e-5 * gLoc) then
      return some tMin
  return none

private def mirrorRaymarchR5 (f : Vec3 → Float) (ro rd : Vec3) (b : Float) (steps : Nat := 96) :
    Option (Float × Vec3) := Id.run do
  let (tNear, tFar) := mirrorIntersectBox ro rd b
  if tFar < tNear || tFar < 0.0 then return none
  let dt := (tFar - tNear) / Float.ofNat steps
  let mut tPrev2 := tNear
  let mut fPrev2 := 0.0
  let mut tPrev := tNear
  let mut fPrev := f (Vec3.add ro (Vec3.scale tPrev rd))
  let mut hitOpt : Option Float := if fPrev == 0.0 then some tPrev else none
  if hitOpt.isNone then
    for i in [1:steps + 1] do
      if hitOpt.isNone then
        let tCur := if i == steps then tFar else tNear + dt * Float.ofNat i
        let fCur := f (Vec3.add ro (Vec3.scale tCur rd))
        if fCur == 0.0 then
          hitOpt := some tCur
        else if (fPrev < 0.0 && fCur > 0.0) || (fPrev > 0.0 && fCur < 0.0) then
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
          hitOpt := some (0.5 * (lo + hi))
        else
          let s := if fPrev > 0.0 then 1.0 else -1.0
          let gPrev := s * fPrev
          let gCur  := s * fCur
          if i == 1 && gPrev < gCur then
            hitOpt := mirrorRefineMin f ro rd tPrev tCur tPrev gPrev s gPrev gCur
          if hitOpt.isNone && i >= 2 then
            let gPrev2 := s * fPrev2
            if gPrev <= gPrev2 && gPrev <= gCur && (gPrev < gPrev2 || gPrev < gCur) then
              hitOpt := mirrorRefineMin f ro rd tPrev2 tCur tPrev gPrev s gPrev2 gCur
          if hitOpt.isNone && i == steps && gCur < gPrev then
            hitOpt := mirrorRefineMin f ro rd tPrev tCur tPrev gPrev s gPrev gCur
        tPrev2 := tPrev
        fPrev2 := fPrev
        tPrev := tCur
        fPrev := fCur
  match hitOpt with
  | none => return none
  | some tHit =>
    let pos := Vec3.add ro (Vec3.scale tHit rd)
    let h := max 0.0015 (b * 0.001)
    let f0 := f pos
    let fpx := f (Vec3.add pos ⟨h, 0, 0⟩); let fmx := f (Vec3.sub pos ⟨h, 0, 0⟩)
    let fpy := f (Vec3.add pos ⟨0, h, 0⟩); let fmy := f (Vec3.sub pos ⟨0, h, 0⟩)
    let fpz := f (Vec3.add pos ⟨0, 0, h⟩); let fmz := f (Vec3.sub pos ⟨0, 0, h⟩)
    let g : Vec3 := ⟨fpx - fmx, fpy - fmy, fpz - fmz⟩
    let gMax := max (Float.abs g.x) (max (Float.abs g.y) (Float.abs g.z))
    let mut n := Vec3.scale (-1.0) rd
    if gMax > 1e-20 then
      n := Vec3.normalize (Vec3.scale (1.0 / gMax) g)
    else
      let h2 : Vec3 := ⟨fpx + fmx - 2.0 * f0, fpy + fmy - 2.0 * f0, fpz + fmz - 2.0 * f0⟩
      let h2Max := max (Float.abs h2.x) (max (Float.abs h2.y) (Float.abs h2.z))
      if h2Max > 1e-20 then
        n := Vec3.normalize (Vec3.scale (1.0 / h2Max) h2)
    if Vec3.dot n (Vec3.scale (-1.0) rd) < 0.0 then n := Vec3.scale (-1.0) n
    return some (tHit, n)

/-! ## 1. P1: 9-Sig-Digit Float32-Safe Literal Formatting Across GLSL3, WGSL, and MSL -/

def testScientificFloatFormatting : IO Unit := do
  let shTiny ← IO.ofExcept (compileImplicitExprToGpu "0.0000001*(x - 1.5)" "tiny_e7" 1.0)
  for (lang, src) in #[("GLSL3", shTiny.glsl), ("WGSL", shTiny.wgsl), ("MSL", shTiny.msl)] do
    assertTrue s!"{lang} 0.0000001*(x-1.5) emits scientific literal 1.0e-7"
      (hasSubstr src "1.0e-7")
    assertTrue s!"{lang} 0.0000001*(x-1.5) does NOT underflow literal to 0.0 *"
      (!hasSubstr src "0.0 *" && !hasSubstr src "0.000000 *" && !hasSubstr src "e0")

  let shNeg ← IO.ofExcept (compileImplicitExprToGpu "-0.00000025*(x - 1.5)" "neg_e7" 1.0)
  for (lang, src) in #[("GLSL3", shNeg.glsl), ("WGSL", shNeg.wgsl), ("MSL", shNeg.msl)] do
    assertTrue s!"{lang} -0.00000025 emits 2.5e-7" (hasSubstr src "2.5e-7")

  let shBig ← IO.ofExcept (compileImplicitExprToGpu "100000000*(x - 0.5)" "big_e8" 1.0)
  for (lang, src) in #[("GLSL3", shBig.glsl), ("WGSL", shBig.wgsl), ("MSL", shBig.msl)] do
    assertTrue s!"{lang} 1e8 emits 1.0e8" (hasSubstr src "1.0e8")

  -- Dots Round-6 P1a: tiny outside plane 0.0000002*x - 0.000001 @ bound=1 (exact exponents, NO e0!)
  let shR6Out ← IO.ofExcept (compileImplicitExprToGpu "0.0000002*x - 0.000001" "r6_tiny_out" 1.0)
  for (lang, src) in #[("GLSL3", shR6Out.glsl), ("WGSL", shR6Out.wgsl), ("MSL", shR6Out.msl)] do
    assertTrue s!"{lang} R6 0.0000002*x - 0.000001 emits 2.0e-7 and 1.0e-6"
      (hasSubstr src "2.0e-7" && hasSubstr src "1.0e-6" && !hasSubstr src "e0")

  -- Dots Round-6 P1a: tiny inside plane 0.0000001*x - 0.00000005 @ bound=1 (root x=0.5)
  let shR6In ← IO.ofExcept (compileImplicitExprToGpu "0.0000001*x - 0.00000005" "r6_tiny_in" 1.0)
  for (lang, src) in #[("GLSL3", shR6In.glsl), ("WGSL", shR6In.wgsl), ("MSL", shR6In.msl)] do
    assertTrue s!"{lang} R6 0.0000001*x - 0.00000005 emits 1.0e-7 and 5.0e-8"
      (hasSubstr src "1.0e-7" && hasSubstr src "5.0e-8" && !hasSubstr src "e0")

  -- Dots Round-6/7 P1b: Float64 like-term combining eliminates float32 cancellation on
  -- 1000000*(0.5000004*x - 0.5000001*x) - 0.15 -> (0.3 * p.x) - 0.15 (hits EXACT x = 0.500000!),
  -- while unlike variables 0.5000004*x - 0.5000001*y - 0.15 preserve full 9-sig-digit literals!
  let shR6Diff ← IO.ofExcept (compileImplicitExprToGpu "1000000*(0.5000004*x - 0.5000001*x) - 0.15" "r6_9sig" 1.0)
  for (lang, src) in #[("GLSL3", shR6Diff.glsl), ("WGSL", shR6Diff.wgsl), ("MSL", shR6Diff.msl)] do
    assertTrue s!"{lang} R7 Float64 simplifyExpr folds 1000000*(0.5000004*x - 0.5000001*x) - 0.15 to return ((0.3 * p.x) - 0.15);"
      (hasSubstr src "return ((0.3 * p.x) - 0.15);")
  let shR6Unlike ← IO.ofExcept (compileImplicitExprToGpu "0.5000004*x - 0.5000001*y - 0.15" "r6_unlike" 1.0)
  for (lang, src) in #[("GLSL3", shR6Unlike.glsl), ("WGSL", shR6Unlike.wgsl), ("MSL", shR6Unlike.msl)] do
    assertTrue s!"{lang} R7 preserves distinct 9-sig-digit 0.5000004 and 0.5000001 on unlike variables"
      (hasSubstr src "0.5000004" && hasSubstr src "0.5000001" && hasSubstr src "0.15")

  -- Verifier R7 adversarial regressions: Float64 overflow never drops terms; (-1)^1e20 is +1.0 (even); div linear fold!
  for ovfExpr in #["1e308 + 1e308 + x", "1e308 + x + 1e308", "1e308*x + 1e308*x"] do
    let shOverflow ← IO.ofExcept (compileImplicitExprToGpu ovfExpr "r7_ovf" 1.0)
    for (lang, src) in #[("GLSL3", shOverflow.glsl), ("WGSL", shOverflow.wgsl), ("MSL", shOverflow.msl)] do
      assertTrue s!"{lang} R7 overflow '{ovfExpr}' keeps 3.4e38 (never drops to 0.0 / return p.x;)"
        (hasSubstr src "3.4e38" && !hasSubstr src "return p.x;" && !hasSubstr src "(0.0 + p.x)")
  let shEvenBigPow ← IO.ofExcept (compileImplicitExprToGpu "(-1)^1e20 + x" "r7_evenpow" 1.0)
  for (lang, src) in #[("GLSL3", shEvenBigPow.glsl), ("WGSL", shEvenBigPow.wgsl), ("MSL", shEvenBigPow.msl)] do
    assertTrue s!"{lang} R7 (-1)^1e20 + x folds even parity to (p.x + 1.0)"
      (hasSubstr src "return (p.x + 1.0);")
  let shDivFold ← IO.ofExcept (compileImplicitExprToGpu "2000000*((0.5000004*x)/2 - (0.5000001*x)/2) - 0.15" "r7_divfold" 1.0)
  for (lang, src) in #[("GLSL3", shDivFold.glsl), ("WGSL", shDivFold.wgsl), ("MSL", shDivFold.msl)] do
    assertTrue s!"{lang} R7 div linear fold reduces 2000000*((0.5000004*x)/2 - (0.5000001*x)/2) - 0.15 to ((0.3 * p.x) - 0.15)"
      (hasSubstr src "return ((0.3 * p.x) - 0.15);")

  -- CPU Marching Tetrahedra parity for tiny outside vs inside & 9-sig-digit diff
  let csTiny := CoffeeShop.setImplicit {} "0.0000001*(x - 1.5)" false 1.0 14
  let frTiny := CoffeeShop.toSceneFrame csTiny 1
  assertTrue "CPU 0.0000001*(x-1.5) @ bound=1 produces 0 vertices"
    (frTiny.meshAssets.size == 1 && frTiny.meshAssets[0]!.positions.size == 0)

  let csR6Out := CoffeeShop.setImplicit {} "0.0000002*x - 0.000001" false 1.0 14
  let frR6Out := CoffeeShop.toSceneFrame csR6Out 1
  assertTrue "CPU R6 0.0000002*x - 0.000001 @ bound=1 produces 0 vertices"
    (frR6Out.meshAssets.size == 1 && frR6Out.meshAssets[0]!.positions.size == 0)

  let csR6In := CoffeeShop.setImplicit {} "0.0000001*x - 0.00000005" false 1.0 14
  let frR6In := CoffeeShop.toSceneFrame csR6In 1
  assertTrue "CPU R6 0.0000001*x - 0.00000005 @ bound=1 produces non-empty plane at x=0.5"
    (frR6In.meshAssets.size == 1 && frR6In.meshAssets[0]!.positions.size > 100)

  let csR6Diff := CoffeeShop.setImplicit {} "1000000*(0.5000004*x - 0.5000001*x) - 0.15" false 1.0 14
  let frR6Diff := CoffeeShop.toSceneFrame csR6Diff 1
  assertTrue "CPU R6 1000000*(0.5000004*x - 0.5000001*x) - 0.15 @ bound=1 produces non-empty plane at x=0.5"
    (frR6Diff.meshAssets.size == 1 && frR6Diff.meshAssets[0]!.positions.size > 100)

/-! ## 2. P2: Repeated-Root, Positive-Minimum Rejection & Thin Two-Sheet Surfaces -/

def testRepeatedRootAndThinTwoSheet : IO Unit := do
  -- 2a. Shader codegen audit across all 3 backends
  let shRep  ← IO.ofExcept (compileImplicitExprToGpu "(x - 0.12345)^2" "rep_root" 1.0)
  let shThin ← IO.ofExcept (compileImplicitExprToGpu "100*(x - 0.115)*(x - 0.107)" "thin_sheet" 1.0)

  for (tag, sh) in #[("(x-0.12345)^2", shRep), ("100*(x-0.115)*(x-0.107)", shThin)] do
    for (lang, src) in #[("GLSL3", sh.glsl), ("WGSL", sh.wgsl), ("MSL", sh.msl)] do
      assertTrue s!"{tag}/{lang} defines gs_refine_min 32-step golden-section helper"
        (hasSubstr src "gs_refine_min(" && hasSubstr src "0.61803398875" && hasSubstr src "k < 32")
      assertTrue s!"{tag}/{lang} tracks 3-point stencil (tPrev2/fPrev2)"
        (hasSubstr src "tPrev2" && hasSubstr src "fPrev2")
      assertTrue s!"{tag}/{lang} enforces tightened R6 outer (1e-8) + local (1e-5) repeated-root gate"
        (hasSubstr src "gMin < g0 && gMin < g2 && gMin <= 1e-8" && hasSubstr src "gMin <= 1e-5")
      assertTrue s!"{tag}/{lang} includes 2nd-derivative normal fallback + -rd unit fallback"
        (hasSubstr src "h2Max > 1e-20" && hasSubstr src "N = -rd")
      assertTrue s!"{tag}/{lang} does NOT use WGSL-reserved identifier 'ref'"
        (!hasSubstr src "let ref " && !hasSubstr src "vec2 ref " && !hasSubstr src "float2 ref ")

  -- 2b. Zero false hits on scaled outside planes & strictly positive paraboloids (incl. Dots R6 1e-9 min!)
  let fnR6PosMin (p : Vec3) : Float :=
    (p.x - 0.12345) * (p.x - 0.12345) + 0.0001 * (0.0001 + p.x * p.x * 0.0001) * 0.1
  let mut falseHits : Nat := 0
  for ix in [:9] do
    for iy in [:9] do
      let u := (Float.ofNat ix - 4.0) * 0.25
      let v := (Float.ofNat iy - 4.0) * 0.25
      let rd := Vec3.normalize ⟨u, v, -1.5⟩
      let rdSide := Vec3.normalize ⟨1.5, u * 0.4, v * 0.4⟩
      if (mirrorRaymarchR5 (fun p => 1e-7 * (p.x - 1.5)) ⟨0, 0, 3⟩ rd 1.0).isSome then falseHits := falseHits + 1
      if (mirrorRaymarchR5 (fun p => 2e-7 * p.x - 1e-6) ⟨-2, 0, 0⟩ rdSide 1.0).isSome then falseHits := falseHits + 1
      if (mirrorRaymarchR5 (fun p => 1e-20 * (p.x - 1.000001)) ⟨0, 0, 3⟩ rd 1.0).isSome then falseHits := falseHits + 1
      if (mirrorRaymarchR5 (fun p => p.x * p.x + 0.01) ⟨0, 0, 3⟩ rd 1.0).isSome then falseHits := falseHits + 1
      if (mirrorRaymarchR5 (fun p => p.x * p.x + 1e-7) ⟨0, 0, 3⟩ rd 1.0).isSome then falseHits := falseHits + 1
      if (mirrorRaymarchR5 fnR6PosMin ⟨-2, 0, 0⟩ rdSide 1.0).isSome then falseHits := falseHits + 1
      if (mirrorRaymarchR5 fnR6PosMin ⟨-25, 0, 0⟩ rdSide 20.0).isSome then falseHits := falseHits + 1
  assertTrue s!"0 false hits across 7 empty/positive surfaces (incl. Dots R6 1e-9 min @ b=1 & b=20) × 81 rays (got {falseHits})" (falseHits == 0)

  -- Dots R6 tiny inside plane & 9-sig-digit diff plane hit accurately at x ≈ 0.5
  match mirrorRaymarchR5 (fun p => 1e-7 * p.x - 5e-8) ⟨-2, 0, 0⟩ ⟨1, 0, 0⟩ 1.0 with
  | some (tHit, _) => assertTrue s!"R6 1e-7*x - 5e-8 hits x≈0.5 (got x={-2.0 + tHit})" (near (-2.0 + tHit) 0.5 5e-4)
  | none => throw (IO.userError "FAIL [R6 1e-7*x - 5e-8 missed]")
  match mirrorRaymarchR5 (fun p => 0.3 * p.x - 0.15) ⟨-2, 0, 0⟩ ⟨1, 0, 0⟩ 1.0 with
  | some (tHit, _) => assertTrue s!"R7 folded 0.3*x - 0.15 hits exact x=0.5 (|x-0.5|<1e-4, got x={-2.0 + tHit})" (near (-2.0 + tHit) 0.5 1e-4)
  | none => throw (IO.userError "FAIL [R7 folded 0.3*x - 0.15 plane missed]")

  -- 2c. Repeated root (x - 0.12345)^2 (@ b=1 & b=20) & scaled 1e-7*(x - 0.12345)^2 @ bound=1
  match mirrorRaymarchR5 (fun p => (p.x - 0.12345) * (p.x - 0.12345)) ⟨-2, 0, 0⟩ ⟨1, 0, 0⟩ 1.0 with
  | some (tHit, n) =>
    let xHit := -2.0 + tHit
    assertTrue s!"(x-0.12345)^2 side ray hits x≈0.12345 (got x={xHit})" (near xHit 0.12345 5e-4)
    assertTrue s!"(x-0.12345)^2 normal is finite unit along x (got N=({n.x},{n.y},{n.z}))"
      (n.x.isFinite && Float.abs (Float.abs n.x - 1.0) < 1e-3)
  | none => throw (IO.userError "FAIL [(x-0.12345)^2 side ray missed]")

  match mirrorRaymarchR5 (fun p => (p.x - 0.12345) * (p.x - 0.12345)) ⟨-25, 0, 0⟩ ⟨1, 0, 0⟩ 20.0 with
  | some (tHit, n) =>
    let xHit := -25.0 + tHit
    assertTrue s!"(x-0.12345)^2 @ b=20 hits x≈0.12345 (got x={xHit})" (near xHit 0.12345 5e-4)
    assertTrue s!"(x-0.12345)^2 @ b=20 normal finite unit along x (got N.x={n.x})"
      (n.x.isFinite && Float.abs (Float.abs n.x - 1.0) < 1e-3)
  | none => throw (IO.userError "FAIL [(x-0.12345)^2 @ b=20 missed]")

  match mirrorRaymarchR5 (fun p => 1e-7 * (p.x - 0.12345) * (p.x - 0.12345)) ⟨-2, 0, 0⟩ ⟨1, 0, 0⟩ 1.0 with
  | some (tHit, _) =>
    let xHit := -2.0 + tHit
    assertTrue s!"1e-7*(x-0.12345)^2 scale-invariant repeated root hits x≈0.12345 (got x={xHit})"
      (near xHit 0.12345 5e-4)
  | none => throw (IO.userError "FAIL [1e-7*(x-0.12345)^2 missed]")

  -- First-step boundary valley (x - 0.995)^2 @ bound=1 entering at x=1.0
  match mirrorRaymarchR5 (fun p => (p.x - 0.995) * (p.x - 0.995)) ⟨2, 0, 0⟩ ⟨-1, 0, 0⟩ 1.0 with
  | some (tHit, _) =>
    let xHit := 2.0 - tHit
    assertTrue s!"first-step boundary valley (x-0.995)^2 hits x≈0.995 (got x={xHit})"
      (near xHit 0.995 5e-4)
  | none => throw (IO.userError "FAIL [(x-0.995)^2 boundary valley missed]")

  -- 2d. Thin two-sheet 100*(x - 0.115)*(x - 0.107) @ bound=1 (gap 0.008 < step 0.0208!)
  match mirrorRaymarchR5 (fun p => 100.0 * (p.x - 0.115) * (p.x - 0.107)) ⟨-2, 0, 0⟩ ⟨1, 0, 0⟩ 1.0 with
  | some (tHit, n) =>
    let xHit := -2.0 + tHit
    assertTrue s!"thin two-sheet +x ray hits front sheet x≈0.107 (got x={xHit})" (near xHit 0.107 5e-4)
    assertTrue s!"thin two-sheet normal finite unit along x (got N.x={n.x})"
      (n.x.isFinite && Float.abs (Float.abs n.x - 1.0) < 1e-3)
  | none => throw (IO.userError "FAIL [100*(x-0.115)*(x-0.107) +x ray missed]")

  match mirrorRaymarchR5 (fun p => 100.0 * (p.x - 0.115) * (p.x - 0.107)) ⟨2, 0, 0⟩ ⟨-1, 0, 0⟩ 1.0 with
  | some (tHit, _) =>
    let xHit := 2.0 - tHit
    assertTrue s!"thin two-sheet -x ray hits front sheet x≈0.115 (got x={xHit})" (near xHit 0.115 5e-4)
  | none => throw (IO.userError "FAIL [100*(x-0.115)*(x-0.107) -x ray missed]")

  -- 2e. Preserve Round-3/4 invariants: x^5+1 @ b=2, x-15 @ b=20, face-parallel x-1 @ b=1
  match mirrorRaymarchR5 (fun p => p.x * p.x * p.x * p.x * p.x + 1.0) ⟨-4, 0, 0⟩ ⟨1, 0, 0⟩ 2.0 with
  | some (tHit, _) => assertTrue "x^5+1 @ b=2 hits x=-1" (near (-4.0 + tHit) (-1.0) 1e-3)
  | none => throw (IO.userError "FAIL [x^5+1 @ b=2 missed]")

  match mirrorRaymarchR5 (fun p => p.x - 15.0) ⟨0, 0, 0⟩ ⟨1, 0, 0⟩ 20.0 with
  | some (tHit, _) => assertTrue "x-15 @ b=20 hits x=15" (near tHit 15.0 1e-2)
  | none => throw (IO.userError "FAIL [x-15 @ b=20 missed]")

  match mirrorRaymarchR5 (fun p => p.x - 1.0) ⟨1, 0, 3⟩ ⟨0, 0, -1⟩ 1.0 with
  | some (tHit, _) => assertTrue "face-parallel ro=(1,0,3), rd=(0,0,-1) hits t=2.0" (near tHit 2.0 1e-12)
  | none => throw (IO.userError "FAIL [face-parallel x-1 missed]")

def main : IO Unit := do
  testScientificFloatFormatting
  IO.println "PASS: 1. P1 9-sig-digit float32-safe literal formatting (0.0000001 -> 1.0e-7, 0.5000004 vs 0.5000001, 0 underflow) across GLSL3/WGSL/MSL"
  testRepeatedRootAndThinTwoSheet
  IO.println "PASS: 2. P2 Repeated-root ((x-0.12345)^2), positive-min rejection (1e-9 min @ b=1 & b=20) & thin two-sheet 32-step golden-section across GLSL3/WGSL/MSL"
  IO.println "ALL FIXPOINT ROUND-5 & ROUND-6 TESTS PASSED"

end Tests.FixpointR5

def main : IO Unit := Tests.FixpointR5.main
