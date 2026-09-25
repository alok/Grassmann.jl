import Tests.Geophysics.Common

/-!
# Standard-atmosphere goldens

One file per standard weather (`weather_<name>.json`) plus custom columns
(`weather_custom.json`). Each checks the integrated layer tables, the dense
geometric-altitude grid (every layer base, its neighbours and the gravity-model
switch included) for all 21 functions, their 20 ratios, gravity, geopotential,
the altitude conversions, `layer`, the fluid state `W(h)`, the layer-level
primitives around every base, evaluation in two foreign unit systems, the
four-argument cross-unit forms, and Julia's display.
-/

namespace Tests.GeophysicsTests

open Lean Tests.Units Geophysics UnitSystems StaticVectors

/-- Compare `f` over a golden grid of `Op`s, and their ratios. -/
def Tally.ops (t : Tally) (d : Json) (hs : List Float) (f : Op → Float → Float)
    (r : Op → Float → Float) (what : String) : Tally :=
  Op.all.foldl (fun t o =>
    let t := t.fs (hs.map (f o)) (fld d o.name) fun _ => s!"{what} {o.name}"
    if o.hasRatio then t.fs (hs.map (r o)) (fld d (o.name ++ "ratio")) fun _ => s!"{what} {o.name}ratio"
    else t) t

/-- The 1-based Julia layer of a `Fin`. -/
def jl {n : Nat} (i : Fin n) : Int := i.1 + 1

/-- All checks of one weather dump. -/
def weatherChecks {n : Nat} (W : Weather n) (d : Json) (label : String) (t : Tally) : Tally := Id.run do
  let mut t := t
  let U0 := W.units
  let U2 := sysOf (str (fld d "other"))
  let w (k : String) := s!"{label} {k}"
  t := t.ok (U0.name == str (fld d "units")) fun _ => w "units"
  t := t.f W.latitude (fld d "latitude") fun _ => w "latitude"
  t := t.f W.Tc (fld d "Tc") fun _ => w "Tc"
  t := t.f W.ha (fld d "ha") fun _ => w "ha"
  t := t.fs W.atm.a.toList (fld d "a") fun _ => w "a"
  t := t.fs W.atm.h.toList (fld d "h") fun _ => w "h"
  t := t.fs W.atm.m.toList (fld d "m") fun _ => w "m"
  t := t.fs W.T.toList (fld d "T") fun _ => w "T"
  t := t.fs W.p.toList (fld d "p") fun _ => w "p"
  t := t.fs W.rho.toList (fld d "rho") fun _ => w "rho"
  t := t.f W.radius (fld d "radius") fun _ => w "radius"
  t := t.f W.gravitySea (fld d "gravitySea") fun _ => w "gravitySea"
  t := t.f W.gasconstant (fld d "gasconstant") fun _ => w "gasconstant"
  t := t.f W.molecularmass (fld d "molecularmass") fun _ => w "molecularmass"
  t := t.f (W.radius U2) (fld d "radiusOther") fun _ => w "radiusOther"
  t := t.f (W.gravitySea U2) (fld d "gravitySeaOther") fun _ => w "gravitySeaOther"
  for (key, U) in [("getindex", U0), ("getindexOther", U2)] do
    for (row, i) in (arr (fld d key)).toList.zipIdx do
      if h : i < n then
        let (a, b, c, e, f) := W.get ⟨i, h⟩ U
        t := t.fs [a, b, c, e, f] row fun _ => w s!"{key}[{i}]"
      else t := t.ok false fun _ => w s!"{key}: too many layers"
  t := t.string W.display (fld d "display") fun _ => w "display"
  t := t.string W.typeString (fld d "type") fun _ => w "typeof"
  for (key, U) in [("seaMetric", Sys.Metric), ("seaNative", U0), ("seaOther", U2)] do
    let C := W.column U
    for o in Op.all do
      t := t.f (C.seaLevel o) (fld (fld d key) o.name) fun _ => w s!"{key} {o.name}"
  t := t.f W.geopotentialSea (fld d "geopotentialSea") fun _ => w "geopotentialSea"
  let lh := (floats (fld d "layerH")).toList
  for (x, g) in lh.zip (arr (fld d "layer")).toList do
    t := t.int (jl (W.layer x)) g fun _ => w s!"layer {fmt x}"
  t := t.fs (lh.map W.lapserate) (fld d "lapserate") fun _ => w "lapserate"
  -- the dense grid in W's units
  let C := W.native
  let hs := (floats (fld d "hs")).toList
  let hG := hs.map C.altgeopotent
  t := t.fs hG (fld d "hG") fun _ => w "altgeopotent"
  t := t.fs (hG.map (W.altgeometric ·)) (fld d "altgeometric") fun _ => w "altgeometric"
  t := t.fs (hs.map (W.altabs ·)) (fld d "altabs") fun _ => w "altabs"
  for (x, g) in hG.zip (arr (fld d "layerOf")).toList do
    t := t.int (jl (W.layer x)) g fun _ => w s!"layer(hG={fmt x})"
  t := t.fs (hs.map C.gravity) (fld d "gravity") fun _ => w "gravity"
  t := t.fs (hs.map C.geopotential) (fld d "geopotential") fun _ => w "geopotential"
  for (h, g) in hs.zip (arr (fld d "state")).toList do
    let F := W.state h
    t := t.fs [F.T, F.P] g fun _ => w s!"W({fmt h})"
  t := t.ops (fld d "ops") hs C.eval C.ratio (w "grid")
  -- layer-level primitives
  for r in arr (fld d "primitive") do
    let i := (int (fld r "i")).toNat - 1
    let x := float1 (fld r "hG")
    if h : i < n then
      let ii : Fin n := ⟨i, h⟩
      let wp := w s!"primitive i={i + 1} hG={fmt x}"
      for o in Op.all do
        t := t.f (C.opAt o x ii) (fld r o.name) fun _ => s!"{wp} {o.name}"
        if o.hasRatio then
          t := t.f (C.ratioAt o x ii) (fld r (o.name ++ "ratio")) fun _ => s!"{wp} {o.name}ratio"
      let F := W.stateAt x ii
      t := t.fs [F.T, F.P] (fld r "state") fun _ => w s!"W(hG={fmt x}, {i + 1})"
    else t := t.ok false fun _ => w "primitive layer out of range"
  -- foreign unit systems
  for key in ["cross", "british"] do
    let c := fld d key
    let U := sysOf (str (fld c "units"))
    let CU := W.column U
    let hx := (floats (fld c "hs")).toList
    let wk (k : String) := w s!"{key}({U.name}) {k}"
    t := t.fs (hx.map (W.altgeopotent · U)) (fld c "altgeopotent") fun _ => wk "altgeopotent"
    t := t.fs (hx.map fun h => W.altgeometric (W.altgeopotent h U) U) (fld c "altgeometric")
      fun _ => wk "altgeometric"
    t := t.fs (hx.map (W.altabs · U)) (fld c "altabs") fun _ => wk "altabs"
    for (h, g) in hx.zip (arr (fld c "layerOf")).toList do
      t := t.int (jl (CU.layer (CU.altgeopotent h))) g fun _ => wk s!"layer {fmt h}"
    t := t.fs (hx.map CU.gravity) (fld c "gravity") fun _ => wk "gravity"
    t := t.fs (hx.map CU.geopotential) (fld c "geopotential") fun _ => wk "geopotential"
    t := t.ops c hx CU.eval CU.ratio (wk "grid")
  -- four-argument forms
  for r in arr (fld d "four") do
    let U := sysOf (str (fld r "U"))
    let S := sysOf (str (fld r "S"))
    let h4 := (floats (fld r "hs")).toList
    let wk (k : String) := w s!"four({U.name},{S.name}) {k}"
    t := t.fs (h4.map (W.altabsFrom · U S)) (fld r "altabs") fun _ => wk "altabs"
    t := t.fs (h4.map (W.altgeopotentFrom · U S)) (fld r "altgeopotent") fun _ => wk "altgeopotent"
    t := t.fs (h4.map (W.altgeometricFrom · U S)) (fld r "altgeometric") fun _ => wk "altgeometric"
    t := t.fs (h4.map (W.gravityFrom · U S)) (fld r "gravity") fun _ => wk "gravity"
    t := t.fs (h4.map (W.geopotentialFrom · U S)) (fld r "geopotential") fun _ => wk "geopotential"
    let CU := W.column U
    let hU := h4.map (convert .length · U S)
    t := t.ops r hU CU.eval CU.ratio (wk "grid")
  return t

/-- One standard weather. -/
def weatherSuite (name : String) : IO Tally := do
  let d ← load s!"weather_{name}"
  let t := Tally.new s!"weather {name}"
  match weathers.lookup name with
  | some ⟨_, W⟩ => return weatherChecks W d name t
  | none => return t.ok false fun _ => s!"no Lean weather {name}"

/-- The custom columns of `weather_custom.json`, rebuilt in Lean. -/
def customWeathers : List (String × AnyWeather) :=
  let marsA : Atmosphere 3 := .make (vals [-2.5e-3, 0.0, 1.5e-3]) (vals [-0.0, 20.0e3, 40.0e3]) Mars
  [("US59_300_90000_0.3", ⟨_, US59.weather 300.0 90000.0 0.3⟩),
   ("US62_N2", ⟨_, Weather.integrate US62 ((N2 : Mole).state 288.15 101325.0) 0.5⟩),
   ("US76_Nested", ⟨_, Weather.integrate US76
      (((0.5 * Nitrox + 0.5 * N2 : Mixture) : Mole).state 288.15 101325.0) (π₀ / 4.0)⟩),
   ("Metric_US59E", ⟨_, (US59E.toUnits .Metric).weather 288.16⟩),
   ("English_US59", ⟨_, (US59.toUnits .English).weather 518.69 2116.2⟩),
   ("Mars", ⟨_, marsA.weather 210.0 610.0⟩),
   ("US56_CO2_English", ⟨_, Weather.integrate (US56.toUnits .English)
      ((CO2 : Mole).state 500.0 3000.0 .English) 0.2⟩)]

/-- `weather_custom.json`. -/
def customSuite : IO Tally := do
  let d ← load "weather_custom"
  let mut t := Tally.new "weather custom"
  for (nm, ⟨_, W⟩) in customWeathers do
    t := weatherChecks W (fld d nm) nm t
  let ct := fld d "convertedTables"
  t := t.fs (US59E.toUnits .Metric).a.toList (fld (fld ct "Metric_US59E") "a") fun _ => "Metric(US59E).a"
  t := t.fs (US59E.toUnits .Metric).h.toList (fld (fld ct "Metric_US59E") "h") fun _ => "Metric(US59E).h"
  t := t.fs (US76.toUnits .English).a.toList (fld (fld ct "English_US76") "a") fun _ => "English(US76).a"
  t := t.fs (US76.toUnits .English).h.toList (fld (fld ct "English_US76") "h") fun _ => "English(US76).h"
  return t

end Tests.GeophysicsTests
