import Tests.FlowGeometry.Common

/-!
# Airfoils (`parse.json`, `airfoils.json`, `small.json`)

The NACA grammar on 460 strings (Julia's type string or its `not valid` error), and for the NACA
designations at `p = 150` and the small explicit constructions at `p = 9`: the surfaces at three
`(c, x0)`, their bases, the closed outline and its base, the homogeneous points, the Joukowski
curves, and `UpperArc`/`LowerArc` as profiles. Broken upstream constructions (British, the
`interval` of `SymmetricArc`/`DoubleArc`) are compared with the `*_patched` goldens.
-/

open Lean Tests.Small Tests.CartanTests JuliaBase FlowGeometry

namespace Tests.FlowGeometryTests.Airfoils

/-- The NACA grammar. -/
def runParse : TestM Unit := do
  let j ← load "parse"
  for c in ← jArr (← jField j "cases") do
    let s ← gStr c "s"
    match NACA.parse? s, errMsg? c with
    | .ok a, none => checkS s!"parse {s}" a.typeString (← jField c "type")
    | .error _, some _ => check s!"parse {s}" true
    | .ok a, some e => check s!"parse {s}" false fun _ => s!"Lean {a.typeString}, Julia {e}"
    | .error _, none => check s!"parse {s}" false fun _ => "Lean: not valid"

/-- Compare a golden key, or its `_patched` intent when Julia errors. -/
def checkOrPatched (label : String) (got : FloatArray) (d : Json) (key : String) : TestM Unit := do
  let w ← jField d key
  match errMsg? w with
  | none => checkFs label got w
  | some _ =>
    match d.getObjVal? (key ++ "_patched") with
    | .ok p => checkFs s!"{label} (patched)" got p
    | .error _ => skip

/-- Check one airfoil record. -/
def checkAirfoil (a : Airfoil) (d : Json) : TestM Unit := do
  let n ← gStr d "name"
  checkS s!"{n} type" a.typeString (← jField d "type")
  check s!"{n} p" (a.samples == (← gNat d "p")) fun _ => s!"{a.samples}"
  -- the interval of an arc-based airfoil is a field in Julia (its values are checked with the arcs)
  let iv ← jField d "interval"
  let ivp ← jField d "interval_patched"
  let iv := if (errMsg? iv).isSome then ivp else iv
  if !((iv.getStr?.toOption.getD "").startsWith "LocalTensor") then
    checkS s!"{n} interval" (toString (a.interval 1 0)) iv
  for (c, x0, tag) in [((1 : Float), (0 : Float), ""), (2, 1, "_c2_x01"), (0.5, -0.25, "_ch_x0q")] do
    checkOrPatched s!"{n} upper{tag}" (a.upper c x0).data d s!"upper{tag}"
    checkOrPatched s!"{n} lower{tag}" (a.lower c x0).data d s!"lower{tag}"
    if let .ok b := d.getObjVal? s!"upper_base{tag}" then checkS s!"{n} upper_base{tag}" (toString a.upperAxis) b
    if let .ok b := d.getObjVal? s!"lower_base{tag}" then checkS s!"{n} lower_base{tag}" (toString a.lowerAxis) b
  checkOrPatched s!"{n} complex" a.complex.data d "complex"
  if let .ok b := d.getObjVal? "complex_base" then checkS s!"{n} complex_base" (toString a.outlineAxis) b
  else if let .ok b := d.getObjVal? "complex_base_patched" then
    -- Julia's patched base of a DoubleArc of two sample counts has the wrong length (the port's
    -- explicit base is its own choice, FG-B6)
    if a.upperSamples == a.lowerSamples then
      checkS s!"{n} complex_base (patched)" (toString a.outlineAxis) b
  checkFs s!"{n} points" a.points.points (← jField d "points")

/-- A `FloatArray` from a list. -/
def fa (xs : List Float) : FloatArray := xs.foldl FloatArray.push .empty

/-- The small constructions of `small.json`, in the generator's order. -/
def small : List Airfoil :=
  let am := Airfoil.american (.naca4 24 9) (Profile.clarkYDefault 12 9)
  [am, .american (.naca4 0 9) (Profile.modifiedM 12 64 9), .american (Profile.naca6Default 2 9) (Profile.clarkYDefault 12 9),
   .american (.naca5 230 9) (Profile.thicknessDefault 12 9), .american (.circularArc 4 9) (Profile.clarkYDefault 9 9),
   .american (.naca6A 2 9) (Profile.modifiedDefault 12 9),
   .british (.naca5 230 9) (Profile.clarkYDefault 12 9), .british (.naca4 24 9) (Profile.modifiedM 12 64 9),
   .symmetric (.circularArc 6 9), .symmetric (Profile.clarkYDefault 12 9), .symmetric (.flatPlate 9),
   .double (.circularArc 6 9) (.parabolicArc 4 9), .double (.circularArc 6 9) (.parabolicArc 4 5),
   .american (.upperArc am) (Profile.clarkYDefault 6 9), .symmetric (.upperArc am),
   .symmetric (.lowerArc (.symmetric (.circularArc 6 9)))]

/-- The Joukowski airfoils of `small.json`. -/
def joukowskis : List Joukowski :=
  [⟨1.1, 0.1, 0.1, 1.0, 5⟩, ⟨1.1, 0.1, 0.0, 1.0, 9⟩, ⟨1.2, 0.15, 0.05, 1.0, 17⟩, ⟨1.0, 0.0, 0.0, 1.0, 5⟩,
   ⟨1.1, 0.1, 0, 1, 5⟩, ⟨1.3, -0.2, -0.1, 1.1, 7⟩, ⟨1.1, 0.1, 0.1, 1.0, 75⟩]

/-- The arc profiles of `small.json`. -/
def arcs : List Profile :=
  let am := Airfoil.american (.naca4 24 9) (Profile.clarkYDefault 12 9)
  [.upperArc am, .lowerArc am, .upperArc (.symmetric (.circularArc 6 9)),
   .lowerArc (.double (.circularArc 6 9) (.parabolicArc 4 7)),
   .upperArc (.american (.naca4 24 5) (Profile.clarkYDefault 12 5))]

/-- Run the airfoil checks. -/
def run : TestM Unit := do
  runParse
  let j ← load "airfoils"
  for d in ← jArr (← jField j "airfoils") do
    let s ← gStr d "name"
    match NACA.parse? s with
    | .ok a => checkAirfoil a d
    | .error e => check s!"airfoil {s}" false fun _ => e
  -- plot data: the outline series is the golden outline split into coordinates
  let d2412 := (← jArr (← jField j "airfoils")).find? fun d => (d.getObjValAs? String "name").toOption == some "2412"
  if let some d := d2412 then
    let z ← gFloats (← jField d "complex")
    let sr := (NACA.parse! "2412").outlineSeries
    checkFloats "outlineSeries 2412 x" sr.xs (reParts z)
    checkFloats "outlineSeries 2412 y" sr.ys (imParts z)
    let dbl := (Airfoil.double (.circularArc 6 9) (.parabolicArc 4 9)).doubleArcSeries
    let (u, l) := (Airfoil.double (.circularArc 6 9) (.parabolicArc 4 9)).surfaces 1 0
    check "doubleArcSeries mean line" (dbl.size == 3 && (List.range 9).all fun i =>
      dbl[1]!.ys[i]! == ((imParts u)[i]! + (imParts l)[i]!) / 2)
  let sm ← load "small"
  let recs ← jArr (← jField sm "airfoils")
  check "small: count" (recs.size == small.length)
  for (a, d) in small.zip recs.toList do checkAirfoil a d
  let jr ← jArr (← jField sm "joukowski")
  check "joukowski: count" (jr.size == joukowskis.length)
  for (jk, d) in joukowskis.zip jr.toList do
    let n := jk.typeString
    checkS s!"{n} type" n (← jField d "type")
    checkS s!"{n} interval" (toString jk.interval) (← jField d "interval")
    checkFs s!"{n} complex" jk.complex.data (← jField d "complex")
    checkS s!"{n} complex_base" (toString jk.interval) (← jField d "complex_base")
    checkFs s!"{n} points" jk.points.points (← jField d "points")
  let ar ← jArr (← jField sm "arcs")
  check "arcs: count" (ar.size == arcs.length)
  for (p, d) in arcs.zip ar.toList do
    let n := p.typeString
    checkS s!"{n} type" n (← jField d "type")
    checkFs s!"{n} interval" (p.interval 1 0).toFloatArray (← jField d "interval")
    checkFs s!"{n} interval_c2_x01" (p.interval 2 1).toFloatArray (← jField d "interval_c2_x01")
    checkFs s!"{n} field" p.field.data (← jField d "field")
    checkFs s!"{n} slopefield" p.slopeField.data (← jField d "slopefield")
    checkFs s!"{n} upper" (p.upper 1 0).data (← jField d "upper")
    checkFs s!"{n} lower" (p.lower 1 0).data (← jField d "lower")
    checkFs s!"{n} upper_c2_x01" (p.upper 2 1).data (← jField d "upper_c2_x01")
    checkF s!"{n} eval" (p.value 0.5) (← jField d "eval")

end Tests.FlowGeometryTests.Airfoils
