import Tests.Geophysics.Common

/-!
# Planet goldens

All 13 bodies: shape constants, rotation, the zonal functions, normal gravity on
dense latitude grids, and gravity with altitude on an altitude × latitude grid,
in Metric, English, British, Gauss and IPS (`planets.json`).
-/

namespace Tests.GeophysicsTests

open Lean Tests.Units Geophysics UnitSystems

/-- Compare `f θ` over a golden latitude grid. -/
def Tally.grid (t : Tally) (xs : FloatArray) (f : Float → Float) (want : Json)
    (what : String) : Tally :=
  t.fs (xs.toList.map f) want fun _ => what

/-- Compare `f h θ` over a golden altitude × latitude grid. -/
def Tally.grid2 (t : Tally) (hs θs : FloatArray) (f : Float → Float → Float) (want : Json)
    (what : String) : Tally :=
  (hs.toList.zip (arr want).toList).zipIdx.foldl (fun t ((h, row), i) =>
    t.fs (θs.toList.map (f h)) row fun _ => s!"{what} h[{i}]") t

/-- `planets.json`. -/
def planetsSuite : IO Tally := do
  let j ← load "planets"
  let mut t := Tally.new "planets"
  let θfine := floats (fld j "theta_fine")
  for (nm, P) in planets do
    let d := fld j nm
    t := t.f P.flattening (fld d "flattening") fun _ => s!"{nm} flattening"
    t := t.f P.eccentricity (fld d "eccentricity") fun _ => s!"{nm} eccentricity"
    t := t.f P.eccentricity2 (fld d "eccentricity2") fun _ => s!"{nm} eccentricity2"
    t := t.f P.aspectratio (fld d "aspectratio") fun _ => s!"{nm} aspectratio"
    t := t.f P.q0 (fld d "q0") fun _ => s!"{nm} q0"
    t := t.f P.q01 (fld d "q01") fun _ => s!"{nm} q01"
    t := t.f P.dynamicformfactor (fld d "dynamicformfactor") fun _ => s!"{nm} J2"
    t := t.f P.secondzonalharmonic (fld d "secondzonalharmonic") fun _ => s!"{nm} C20"
    t := t.grid θfine P.latitudegeodetic (fld d "latitudegeodetic") s!"{nm} latitudegeodetic"
    t := t.grid θfine P.deflectiongeodetic (fld d "deflectiongeodetic") s!"{nm} deflectiongeodetic"
    t := t.grid θfine P.latitudegeocentric (fld d "latitudegeocentric") s!"{nm} latitudegeocentric"
    t := t.grid θfine P.deflectiongeocentric (fld d "deflectiongeocentric")
      s!"{nm} deflectiongeocentric"
    t := t.grid θfine P.latitudeparametric (fld d "latitudeparametric") s!"{nm} latitudeparametric"
    for un in ["Metric", "English", "British", "Gauss", "IPS"] do
      let U := sysOf un
      let s := fld d un
      let w (k : String) := s!"{nm} {un} {k}"
      t := t.f (P.semimajor U) (fld s "semimajor") fun _ => w "semimajor"
      t := t.f (P.period U) (fld s "period") fun _ => w "period"
      t := t.f (P.gravitation U) (fld s "gravitation") fun _ => w "gravitation"
      t := t.f (P.mass U) (fld s "mass") fun _ => w "mass"
      t := t.f (P.frequency U) (fld s "frequency") fun _ => w "frequency"
      t := t.f (P.angularfrequency U) (fld s "angularfrequency") fun _ => w "angularfrequency"
      t := t.f (P.meanradius U) (fld s "meanradius") fun _ => w "meanradius"
      t := t.f (P.semiminor U) (fld s "semiminor") fun _ => w "semiminor"
      t := t.f (P.lineareccentricity U) (fld s "lineareccentricity") fun _ => w "lineareccentricity"
      t := t.f (P.authalicradius U) (fld s "authalicradius") fun _ => w "authalicradius"
      t := t.f (P.gravitySpherical U) (fld s "gravitySpherical") fun _ => w "gravitySpherical"
      t := t.f (P.oblateness U) (fld s "oblateness") fun _ => w "oblateness"
      let us := floats (fld s "u")
      t := t.grid us (P.q · U) (fld s "q") (w "q")
      t := t.grid us (P.q1 · U) (fld s "q1") (w "q1")
      let θs := floats (fld s "thetas")
      t := t.grid θs (P.radiusFast · U) (fld s "radiusFast") (w "radiusFast")
      t := t.grid θs (P.radius · U) (fld s "radius") (w "radius")
      t := t.grid θs (P.radiusgeodetic · U) (fld s "radiusgeodetic") (w "radiusgeodetic")
      t := t.grid θs (P.speedRadial · U) (fld s "speedRadial") (w "speedRadial")
      t := t.grid θs (P.speed · U) (fld s "speed") (w "speed")
      t := t.grid θs (P.centripetalRadial · U) (fld s "centripetalRadial") (w "centripetalRadial")
      t := t.grid θs (P.centripetal · U) (fld s "centripetal") (w "centripetal")
      t := t.grid θs (P.oblatenessAt · U) (fld s "oblatenessAt") (w "oblatenessAt")
      t := t.grid θs (P.gravityNormal · U) (fld s "gravityNormal") (w "gravityNormal")
      t := t.grid θs (P.gravity · U) (fld s "gravity") (w "gravity")
      let hs := floats (fld s "hs")
      let θh := floats (fld s "thetaH")
      t := t.grid2 hs θh (P.deflection · · U) (fld s "deflection") (w "deflection")
      t := t.grid2 hs θh (P.latitudegeocentricAt · · U) (fld s "latitudegeocentricAt")
        (w "latitudegeocentricAt")
      t := t.grid2 hs θh (P.gravitygeodetic · · U) (fld s "gravitygeodetic") (w "gravitygeodetic")
      t := t.grid2 hs θh (P.gravityNorm · · U) (fld s "gravityNorm") (w "gravityNorm")
      t := t.grid2 hs θh (P.gravityAt · · U) (fld s "gravityAt") (w "gravityAt")
      for (h, row) in hs.toList.zip (arr (fld s "gravitycomponents")).toList do
        for (θ, c) in θh.toList.zip (arr row).toList do
          let (x, y) := P.gravitycomponents h θ U
          t := t.fs [x, y] c fun _ => w s!"gravitycomponents {fmt h} {fmt θ}"
  return t

end Tests.GeophysicsTests
