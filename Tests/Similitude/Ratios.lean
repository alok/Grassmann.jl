import Tests.Similitude.Common
import Tests.Util.Random

/-!
# Similitude: conversion ratios and per-system constants

Against `oracle/golden/similitude/{ratios,system_constants}.json`: exact ratios
`ratio(d, U, S)` for a random sample of system pairs and quantities plus eight
complete pairs, their `ConvertUnit` display, and every defining and physical
constant of every system as a quantity (value, dimension and display).
-/

namespace Tests.SimilitudeTests

open Lean Tests.Units FieldConstants FieldAlgebra UnitSystems Similitude

/-- Conversion ratios and `ConvertUnit` display. -/
def ratiosSuite : IO Suite := do
  let j ← loadJson "similitude/ratios.json"
  let mut s : Suite := { name := "ratios" }
  for r in arr j do
    let (a, b) := (sysOf! (str (idx r 0)), sysOf! (str (idx r 1)))
    let some q := Conv.ofName? (str (idx r 2)) | s := s.check false fun _ => s!"no Conv {str (idx r 2)}"
    let d := q.dim.toGroup.v
    let what := s!"{q.name}({a.name},{b.name})"
    let some x := ratio? d a b
      | s := s.check (str (idx r 3) == "nothing") fun _ => s!"{what}: Julia does not throw"
    s := s.check (str (idx r 3) != "nothing") fun _ => s!"{what}: Julia throws, got {x}"
    s := s.check (x.toString == str (idx r 3)) fun _ => s!"{what}: got {x}, want {str (idx r 3)}"
    if let some f := goldFloat? (idx r 4) then
      s := s.check (sameBits x.toFloat f) fun _ => s!"{what}: {hexOf x.toFloat} want {hexOf f}"
    let c := showConvert d a b
    s := s.check (c == str (idx r 5)) fun _ => s!"{what}: got {c}, want {str (idx r 5)}"
  return s

/-- Constants and physics of every system as quantities. -/
def systemConstantsSuite : IO Suite := do
  let j ← loadJson "similitude/system_constants.json"
  let mut s : Suite := { name := "system constants" }
  let exact := scalarFunctions (α := Scalar)
  let model := scalarFunctions (α := HalfDim)
  for r in arr j do
    let U := sysOf! (str (idx r 0))
    let nm := str (idx r 1)
    -- `gaussgravitation` is a derived quantity in Similitude (checked with the derived units)
    if nm == "gaussgravitation" then continue
    match exact.lookup nm, model.lookup nm with
    | some f, some g =>
      let dims := (dimOf g).toExps
      -- Similitude binds each constant to its SI2019 quantity; `c(U)` converts it
      -- (`derived.jl:157-159`)
      let some rt := ratio? dims .SI2019 U
        | s := s.check (str (idx r 2) == "nothing") fun _ => s!"{nm}({U.name}): Julia does not throw"
      let v := f Sys.SI2019.consts * rt
      let shown := s!"{v} [{U.showDim dims}] {U.name}"
      s := s.check (shown == str (idx r 2)) fun _ => s!"{nm}({U.name}): got {shown}, want {str (idx r 2)}"
      if let some x := goldFloat? (idx r 3) then
        s := s.check (sameBits v.toFloat x) fun _ => s!"{nm}({U.name}): {hexOf v.toFloat} want {hexOf x}"
      s := s.check (ratsOfStr (str (idx r 4)) == (List.finRange 11).map fun i =>
          match dims.get i with | .int k => (k : Rat) | .rat q => q | .float _ => 0)
        fun _ => s!"{nm}({U.name}) dims"
    | _, _ => s := s.check false fun _ => s!"no function {nm}"
  return s

/-- Exponent vectors of two exact values agree and their coefficients are close. -/
def groupClose (a b : Scalar) : Bool :=
  match a, b with
  | .grp g, .grp h => g.v.beq h.v && JuliaBase.F64.isapprox g.c.toFloat h.c.toFloat (rtol := 1e-13)
  | a, b => JuliaBase.F64.isapprox a.toFloat b.toFloat (rtol := 1e-13)

/-- Property tests of the exact ratios (no oracle): `ratio(d,U,U) = 𝟏`, the
cocycle law `ratio(d,U,S)·ratio(d,S,V) = ratio(d,U,V)` on exponents (coefficients
within rounding), and `ratio(d,U,S)·ratio(d,S,U) = 𝟏`, for random systems and
quantities (FFF, whose permeability is zero, excluded). -/
def ratioPropertySuite : IO Suite := do
  let mut s : Suite := { name := "ratio properties" }
  let sys := (Sys.all.filter (· != .FFF)).toArray
  let convs := Conv.all.toArray
  let mut g := Tests.Rng.ofSeed 20260924
  for _ in [0:600] do
    let (i, g1) := g.nat sys.size
    let (j, g2) := g1.nat sys.size
    let (k, g3) := g2.nat sys.size
    let (c, g4) := g3.nat convs.size
    g := g4
    let (U, S, V, q) := (sys[i]!, sys[j]!, sys[k]!, convs[c]!)
    let d := q.dim.toGroup.v
    let one := Scalar.grp Consts.one
    s := s.check (groupClose (ratio d U U) one) fun _ => s!"{q.name}({U.name},{U.name}) = {ratio d U U}"
    s := s.check (groupClose (ratio d U S * ratio d S V) (ratio d U V)) fun _ =>
      s!"{q.name}: {U.name}→{S.name}→{V.name} = {ratio d U S * ratio d S V}, direct {ratio d U V}"
    s := s.check (groupClose (ratio d U S * ratio d S U) one) fun _ =>
      s!"{q.name}: {U.name}↔{S.name} = {ratio d U S * ratio d S U}"
  return s

end Tests.SimilitudeTests
