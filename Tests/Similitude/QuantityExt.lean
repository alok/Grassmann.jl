import Tests.Similitude.Common

/-!
# Similitude: powers, conversion factors, dimensionless sums, logarithms

Against `oracle/golden/similitude/quantity_ext.json`
(`oracle/similitude/quantity_ext.jl`), with the dimensions supplied at run time:

* literal powers `q^-2`, `q^-1`, `q^3` (`Quantity.zpow`) and rational powers
  `q^(1//2)`, `q^(1//3)`, `q^(-3//2)` (`Quantity.qpow`, where the root is exact);
* `q * d(U, English)` (a quantity times a `ConvertUnit`), the quotient of
  quantities of two systems (a `ConvertUnit`), products and quotients of
  conversion factors;
* a dimensionless quantity plus or minus a `Constant` (`Quantity.addNum`, …);
* `log`, `log2`, `log10`, `logdb` of quantities, their sums, scalings and `exp`;
* `neper`, `bel`, `decibel` in all 48 systems.
-/

namespace Tests.SimilitudeTests

open Lean Tests.Units FieldConstants FieldAlgebra UnitSystems Similitude

/-- Compile-time checks: `Metric(4.0, area)^(1//2)` is a length. -/
example : Quantity .Metric Dim.length Float := (Sys.Metric.qty Dim.area (4.0 : Float)).qpow 1 2
example : Quantity .Metric (Dim.length.zpow (-2)) Float := (Sys.Metric.qty Dim.length (2.0 : Float)).zpow (-2)
example : ConvertUnit .Metric .English Dim.energy :=
  Sys.Metric.qty Dim.energy (1.0 : Float) / Sys.English.qty Dim.energy (2.0 : Float)
example : Quantity .English Dim.energy Float :=
  Sys.Metric.qty Dim.energy (1.0 : Float) * Dim.energy.conv .Metric .English
#guard (neper .Metric).display == "𝟏 = 1.0 [log(𝟙)] Metric"

/-! Julia `d(v, U, S)` (values from the oracle) and the intended `morphism(U)`. -/
#guard (Dim.energy.convert (.ofFloat 2.0) .Metric .English).toString == "g₀⋅ft⋅lb⋅2 = 2.7116358966628007"
#guard (Dim.energy.convert (.ofInt 2) .English .Metric).toString == "g₀⁻¹ft⁻¹lb⁻¹2 = 1.4751242985545305"
#guard (Dim.energy.convert (.ofFloat 0.5) .Gauss .Metric).toString == "2⁷5⁷/2 = 5.0e6"
#guard (Dim.energy.convert (.ofInt 3) .Metric .Metric).toString == "3 = 3.0"
#guard (Dim.length.convert (.ofFloat 0.5) .English).toString == "ft⁻¹/2 = 1.6404199475065615"
-- Metric sets `g₀ = 1`: a force is a mass times an acceleration, `F ↦ M L T⁻²`
#guard ((Sys.Metric.morphism.map fun r => r[0]!.print).toList) ==
  ["0", "1", "1", "-2", "0", "0", "0", "0", "0", "0", "0"]

/-- The extended quantity algebra against the oracle. -/
def quantityExtSuite : IO Suite := do
  let j ← loadJson "similitude/quantity_ext.json"
  let mut s : Suite := { name := "quantity powers, factors, logarithms" }
  for r in arr (fld j "powers") do
    let U := sysOf! (str (fld r "sys"))
    let some q := Conv.ofName? (str (fld r "q")) | s := s.check false fun _ => "unknown quantity"
    let a : Q U q.dim := ⟨scalarOf (fld r "x")⟩
    let b : Q .English q.dim := ⟨scalarOf (fld r "y")⟩
    let tag := s!"{U.name}: {q.name} {toString a}"
    let chk (s : Suite) (k : String) (got : String) : Suite :=
      let w := str (fld r k)
      if w == "ERROR" then s else s.check (got == w) fun _ => s!"{tag} {k}: got {got}, want {w}"
    s := chk s "show" (toString a)
    s := chk s "pow_m2" (toString (a.zpow (-2)))
    s := chk s "pow_m1" (toString (a.zpow (-1)))
    s := chk s "pow3" (toString (a.zpow 3))
    if h : q.dim.HasRoot 2 then
      s := chk s "pow_half" (toString (a.qpow 1 2 h))
      s := chk s "pow_m3half" (toString (a.qpow (-3) 2 h))
    if h : q.dim.HasRoot 3 then s := chk s "pow_third" (toString (a.qpow 1 3 h))
    s := chk s "times_conv" (toString (a * q.dim.conv U .English))
    -- one system on both sides divides as quantities (in Julia and here)
    if U != .English then s := chk s "quotient" (toString (a / b))
    let c : ConvertUnit U .English q.dim := ⟨⟩
    let cl : ConvertUnit U .English Dim.length := ⟨⟩
    let c2 := c.mul c
    let c3 := c.div cl
    s := chk s "conv_sq" (toString c2)
    s := chk s "conv_div" (toString c3)
  for r in arr (fld j "dimensionless") do
    let U := sysOf! (str (fld r "sys"))
    let some q := Conv.ofName? (str (fld r "q")) | s := s.check false fun _ => "unknown quantity"
    let a : Quantity U q.dim Float := ⟨2.5⟩
    let tag := s!"{U.name}: {q.name}"
    if h : U.hom.halfDim q.dim = U.hom.halfDim Dim.one then
      s := s.check (toString (a.addNum 1.5 h) == str (fld r "add")) fun _ => s!"{tag} add"
      s := s.check (toString (Quantity.numAdd 1.5 a h) == str (fld r "radd")) fun _ => s!"{tag} radd"
      s := s.check (toString (a.subNum 1.5 h) == str (fld r "sub")) fun _ => s!"{tag} sub"
    else s := s.check false fun _ => s!"{tag}: not dimensionless in Lean"
  for r in arr (fld j "logs") do
    let U := sysOf! (str (fld r "sys"))
    let some q := Conv.ofName? (str (fld r "q")) | s := s.check false fun _ => "unknown quantity"
    let a : Quantity U q.dim Float := ⟨(scalarOf (fld r "x")).toFloat⟩
    let l := a.log
    let tag := s!"{U.name}: {q.name}"
    let chk (s : Suite) (k : String) (got : String) : Suite :=
      let w := str (fld r k)
      if w == "ERROR" then s else s.check (got == w) fun _ => s!"{tag} {k}: got {got}, want {w}"
    s := chk s "log" (toString l)
    s := chk s "log2" (toString a.log2)
    s := chk s "log10" (toString a.log10)
    s := chk s "logdb" (toString a.logdb)
    s := chk s "add" (toString (l + l))
    s := chk s "sub" (toString (l - l))
    s := chk s "mul2" (toString (l * (2.0 : Float)))
    s := chk s "div2" (toString (l / (2.0 : Float)))
    s := chk s "exp" (toString l.exp)
    s := chk s "exp10" (toString a.log10.exp10)
  for r in arr (fld j "neper") do
    let U := sysOf! (str (idx r 0))
    s := s.check ((neper U).display == str (idx r 1)) fun _ => s!"neper({U.name})"
    s := s.check ((bel U).display == str (idx r 2)) fun _ => s!"bel({U.name})"
    s := s.check ((decibel U).display == str (idx r 3)) fun _ => s!"decibel({U.name})"
  return s

end Tests.SimilitudeTests
