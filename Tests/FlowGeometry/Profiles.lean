import Tests.FlowGeometry.Common

/-!
# Profiles (`oracle/golden/flowgeometry/profiles.json`, `internals.json`)

Every profile family at 540 chord fractions (a fixed grid with the edge cases, 400 uniform random
and 20 tiny ones): the value, the slope, the angle, the scaled forms `profile(p, x, c, x0)`, the
sampled fields over `interval(p)`, the intervals and the homogeneous points; and the coefficient
fits (`internals`) that localise errors. Bit for bit.
-/

open Lean Tests.Small Tests.CartanTests JuliaBase FlowGeometry

namespace Tests.FlowGeometryTests.Profiles

/-- A `FloatArray` from a list. -/
def fa (xs : List Float) : FloatArray := xs.foldl FloatArray.push .empty

/-- The profiles of the golden, in the generator's order. -/
def profiles : List Profile :=
  [.flatPlate 5, .flatPlate 2,
   .parabolicArc 6 5, .parabolicArc 10 5, Profile.parabolicArcDefault 5, .parabolicArc 2.5 7,
   .circularArc 6 5, .circularArc 10 5, .circularArc 2 5, Profile.circularArcDefault 21, .circularArc 7.5 6,
   Profile.clarkYDefault 12 5, Profile.clarkYDefault 6 5, .clarkY 12 0.0 5, .clarkY 15 0.5 5,
   Profile.clarkYDefault 12.5 5, Profile.clarkYDefault 12 150,
   Profile.thicknessDefault 12 5, Profile.thicknessX 12 4 5, .thickness 9 2 0.1 5, Profile.thicknessX 15 5 5,
   .thickness 10.5 3 0.2 6,
   Profile.modifiedDefault 12 5, Profile.modifiedM 12 63 5, Profile.modifiedM 12 64 5, Profile.modifiedM 12 33 5,
   Profile.modifiedM 12 34 5, Profile.modifiedM 10 93 5, .modified 12 65 0.5 5, Profile.modifiedM 6 12 5,
   Profile.modifiedM 5 12 5, Profile.modifiedM 8.25 63.5 5, Profile.modifiedM 15 95 5, Profile.modifiedM 12 64 150,
   .naca4 24 5, .naca4 0 5, .naca4 44 5, .naca4 64 5, .naca4 25 5, .naca4 65 5, .naca4 99 6, .naca4 24 150,
   .naca5 210 5, .naca5 220 5, .naca5 230 5, .naca5 240 5, .naca5 250 5, .naca5 430 5,
   .naca5 221 5, .naca5 231 5, .naca5 241 5, .naca5 251 5, .naca5 230 150,
   Profile.naca6Default 2 5, Profile.naca6Default 4 5, Profile.naca6Default 0 5, Profile.naca6Default 2.5 6,
   Profile.naca6Default 3 9,
   .naca6 (fa [0.5, 1.0]) (fa [0.1, 0.2]) 5, .naca6 (fa [0.8]) (fa [0.3]) 5,
   .naca6 (fa [0.3, 0.6, 1.0]) (fa [0.05, 0.1, 0.25]) 7,
   .naca6A 2 5, .naca6A 0 5, .naca6A 4 6]

/-- Check one golden profile record against the Lean profile. -/
def checkProfile (p : Profile) (d : Json) (xs xsc : FloatArray) : TestM Unit := do
  let n := p.typeString
  let e := p.eval
  checkFs s!"{n} y" (Cartan.buildFlat xs.size fun i => e.value xs[i]!) (← jField d "y")
  checkFs s!"{n} dy" (Cartan.buildFlat xs.size fun i => e.slope xs[i]!) (← jField d "dy")
  checkFs s!"{n} angle" (Cartan.buildFlat xs.size fun i => p.angleAt xs[i]! 1 0) (← jField d "angle")
  checkFs s!"{n} y_c2_x0h" (Cartan.buildFlat xsc.size fun i => p.valueAt xsc[i]! 2 0.5) (← jField d "y_c2_x0h")
  checkFs s!"{n} dy_c2_x0h" (Cartan.buildFlat xsc.size fun i => p.slopeAt xsc[i]! 2 0.5) (← jField d "dy_c2_x0h")
  checkFs s!"{n} angle_c2_x0h" (Cartan.buildFlat xsc.size fun i => p.angleAt xsc[i]! 2 0.5)
    (← jField d "angle_c2_x0h")
  checkFs s!"{n} y_c3_x0m1" (Cartan.buildFlat xsc.size fun i => p.valueAt xsc[i]! 3 (-1)) (← jField d "y_c3_x0m1")
  checkFs s!"{n} adjoint" (Cartan.buildFlat xsc.size fun i => p.slope xsc[i]!) (← jField d "adjoint")
  checkFs s!"{n} field" p.field.data (← jField d "field")
  checkFs s!"{n} slopefield" p.slopeField.data (← jField d "slopefield")
  checkFs s!"{n} anglefield" p.angleField.data (← jField d "anglefield")
  checkS s!"{n} interval" (toString (p.interval 1 0)) (← jField d "interval")
  checkS s!"{n} interval_c2_x01" (toString (p.interval 2 1)) (← jField d "interval_c2_x01")
  checkFs s!"{n} interval_vals" (p.interval 2.5 (-0.5)).toFloatArray (← jField d "interval_vals")
  checkFs s!"{n} points" (p.points).points (← jField d "points")
  checkFs s!"{n} points_c2_x01" (p.points 2 1).points (← jField d "points_c2_x01")
  checkFs s!"{n} initpoints" p.initpoints.points (← jField d "initpoints")
  checkFs s!"{n} chord" p.chord.toFloatArray (← jField d "chord")

/-- Run the profile value checks. -/
def run : TestM Unit := do
  let j ← load "profiles"
  let xs ← gFloats (← jField j "x")
  let xsc ← gFloats (← jField j "xsc")
  let recs ← jArr (← jField j "profiles")
  check "profiles: count" (recs.size == profiles.length) fun _ => s!"{recs.size} vs {profiles.length}"
  for (p, d) in profiles.zip recs.toList do
    checkS s!"type {p.typeString}" p.typeString (← jField d "type")
    checkProfile p d xs xsc

/-- The coefficient fits. -/
def runInternals : TestM Unit := do
  let j ← jField (← load "internals") "internals"
  for c in ← jArr (← jField j "clarky") do
    checkFs "clarky" (fa (clarky (← gFloat (← jField c "te"))).toList) (← jField c "a")
  for c in ← jArr (← jField j "clarky5") do
    checkFs "clarky5" (fa (clarky5 (← gFloat (← jField c "te")) (← gFloat (← jField c "x"))).toList)
      (← jField c "a")
  for c in ← jArr (← jField j "tailslope") do
    let a ← jArr c
    checkF "tailslope" (tailslope (← gFloat a[0]!)) a[1]!
  for c in ← jArr (← jField j "riegel") do
    let a ← jArr c
    checkF "riegel" (riegel (← gFloat a[0]!)) a[1]!
  for c in ← jArr (← jField j "radius") do
    let a ← jArr c
    checkF "radius" (radius (← gFloat a[0]!)) a[1]!
  let mods : List Profile := [Profile.modifiedM 12 63 5, Profile.modifiedM 12 64 5, Profile.modifiedM 12 33 5,
    Profile.modifiedM 10 93 5, Profile.modifiedM 6 12 5, Profile.modifiedM 5 12 5, .modified 12 65 0.5 5,
    Profile.modifiedM 8.25 63.5 5, Profile.modifiedM 15 95 5, Profile.modifiedM 12 34 5]
  for (p, c) in mods.zip (← jArr (← jField j "modified")).toList do
    checkS "modified type" p.typeString (← jField c "type")
    match p with
    | .modified t m te _ =>
      let (t, i, x, te) := modifiedParams t m te
      checkFs s!"modified params {p}" (fa [t, i.toFloat, x, te]) (← jField c "params")
      let (a, d) := modifiedCoeffs t i x te
      checkFs s!"modified a {p}" (fa a.toList) (← jField c "a")
      checkFs s!"modified d {p}" (fa d.toList) (← jField c "d")
    | _ => pure ()
  for c in ← jArr (← jField j "naca4") do
    let n ← gNat c "n"
    let (m, p) := naca4Decode n
    checkF s!"naca4 m {n}" m (← jField c "m")
    checkF s!"naca4 p {n}" p (← jField c "p")
    let (f, r) := naca4Coeffs m p
    checkFs s!"naca4 front {n}" (fa f.toList) (← jField c "front")
    checkFs s!"naca4 rear {n}" (fa r.toList) (← jField c "rear")
  for c in ← jArr (← jField j "naca5") do
    let n ← gNat c "n"
    let want ← jField c "decode"
    match naca5Decode n, errMsg? want with
    | some (a, b, k), _ => checkFs s!"naca5 {n}" (fa [a, b, k]) want
    | none, some _ => check s!"naca5 {n} error" true
    | none, none => check s!"naca5 {n}" false fun _ => "Lean has no decode"
  for c in ← jArr (← jField j "naca6") do
    let a ← gFloats (← jField c "a")
    let cl ← gFloats (← jField c "cl")
    checkS "naca6 type" (Profile.naca6 a cl 9).typeString (← jField c "type")
    let (cla, h, g) := naca6Decode a cl
    checkFs "naca6 cla" cla (← jField c "cla")
    checkFs "naca6 h" h (← jField c "h")
    checkFs "naca6 g" g (← jField c "g")

end Tests.FlowGeometryTests.Profiles
