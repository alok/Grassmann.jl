import Tests.UnitSystems.Common

/-!
# UnitSystems: conversion fast paths

Exhaustive consistency of the fast paths of `UnitSystems/Convert.lean` with the
reference chains (which the golden suites check against Julia):

* `Conv.factorSys` (per-pair tables) is `===` to `q.factor U S` for all
  131 × 48 × 48 factors, and `Conv.convertSys`/`Conv.convertF` agree bit for bit
  with `Conv.convert` on a plain `Float64` value;
* `Sys.ofSystem?` recognises every named system (ties to an earlier system with
  the same Julia type are reported), and `Conv.factorAny` agrees with the chains;
* `UnitAlg NumF` (bare `Float64` chains) agrees with the `Num` chains bit for bit on
  all 131 × 48 × 48 factors of the named systems (the count and the largest
  relative error are printed; a relative bound of `1e-14` is the tolerance check).
-/

namespace Tests.UnitSystemsTests

open Lean Tests.Units FieldConstants UnitSystems

/-- `===` of two `Num`s (kind, payload bits and `Constant` flag). -/
def numIdent (a b : Num) : Bool := a.ident b

/-- Relative difference, `0` for identical values. -/
def relDiff (a b : Float) : Float :=
  if a == b || sameBits a b then 0 else (a - b).abs / max a.abs b.abs

/-- Largest relative error of the `UnitAlg Float` chains allowed by the tests. -/
def floatPathTol : Float := 1.0e-14

/-- The fast-path consistency checks. -/
def fastPathSuite : IO (Suite × Suite) := do
  let mut s : Suite := { name := "fast paths" }
  let mut e : Suite := { name := "fast paths (bit-exact)" }
  let sys := Sys.all.toArray
  let nums := sys.map (·.sys Num)
  let flts := sys.map (·.sys NumF)
  let mut exactF := 0
  let mut worst := 0.0
  let mut worstAt := ""
  for hu : iu in [0:sys.size] do
    for hs : is in [0:sys.size] do
      let (u, s') := (sys[iu], sys[is])
      let (U, S) := (nums[iu]!, nums[is]!)
      for q in Conv.all do
        let x := q.factor U S
        e := e.check (numIdent (q.factorSys u s') x) fun _ =>
          s!"factorSys {q.name}({u.name},{s'.name}) = {q.factorSys u s'}, chain {x}"
        -- a plain Float64 value through the three conversion paths
        let v : Float := 2.718281828459045
        let want := (q.convert (.p (.float v)) U S).toFloat
        e := e.check (sameBits (q.convertSys v u s') want) fun _ =>
          s!"convertSys {q.name}({u.name},{s'.name}): {q.convertSys v u s'} vs {want}"
        -- the unboxed chains
        let y := (q.factor flts[iu]! flts[is]!).x
        let d := relDiff y x.toFloat
        if d == 0 then exactF := exactF + 1
        if d > worst then
          worst := d
          worstAt := s!"{q.name}({u.name},{s'.name}): {y} vs {x}"
        s := s.check (d ≤ floatPathTol) fun _ =>
          s!"NumF chain {q.name}({u.name},{s'.name}) = {y}, Num {x} (rel {d})"
        e := e.check (d == 0) fun _ =>
          s!"NumF chain {q.name}({u.name},{s'.name}) = {y}, Num {x} (not bit-identical)"
  let total := sys.size * sys.size * 131
  IO.println s!"    UnitAlg NumF: {exactF}/{total} factors bit-identical to Num, worst rel. error {worst} at {worstAt}"
  -- literal systems: convertF with closed-term factors
  for q in Conv.all do
    let v : Float := 0.3
    e := e.check (sameBits (q.convertF v (English Num) (Metric Num))
        (q.convert (.p (.float v)) (English Num) (Metric Num)).toFloat) fun _ =>
      s!"convertF {q.name}(0.3, English, Metric)"
  -- named systems recognised by their parameters
  for h : i in [0:sys.size] do
    let u := sys[i]
    match Sys.ofSystem? nums[i]! with
    | some w =>
      s := s.check (Sys.identFull (w.sys Num) nums[i]!) fun _ => s!"ofSystem? {u.name} = {w.name}"
      if w != u then IO.println s!"    {u.name} has the Julia type of {w.name}"
    | none => s := s.check false fun _ => s!"ofSystem? {u.name} = none"
  -- a system that is not named: Metric with another coupling
  let M := Metric Num
  let custom : UnitSystem Num := { M with C := { M.C with ΩΛ := .c (.float 0.7) } }
  s := s.check (Sys.ofSystem? custom).isNone fun _ => "ofSystem? of a perturbed Metric"
  for q in Conv.all do
    for (a, b) in [(custom, M), (M, custom), (English Num, M), (custom, custom)] do
      e := e.check (numIdent (q.factorAny a b) (q.factor a b)) fun _ => s!"factorAny {q.name}"
  return (s, e)

end Tests.UnitSystemsTests
