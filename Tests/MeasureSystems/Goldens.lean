import MeasureSystems
import Tests.Similitude.Common

/-!
# MeasureSystems golden tests

Against `oracle/golden/measuresystems/` (`oracle/measuresystems/gen.jl`):

* `measures.json`: the 44 generators, random monomials and named constants of
  `Group{:Measures}`: MeasureSystems' display and the measured `product`
  (value and uncertainty bit for bit);
* `measurements.json`: `measurement("…")` parsing, `show`, `print_special`,
  `special_print`, and arithmetic with correlated inputs;
* `system_constants.json`, `ratios.json`: constants of 28 systems and the
  conversion factors of 10 system pairs, with uncertainties.
-/

namespace Tests.MeasureSystemsTests

open Lean Tests.Units FieldConstants FieldAlgebra UnitSystems Similitude MeasureSystems
open Tests.SimilitudeTests (constsOf goldFloat? sysOf!)

/-- Check a measured value's bits against `[…, valBits, errBits]` at positions `i`, `i+1`. -/
def checkMNum (s : Suite) (what : String) (x : MNum) (r : Json) (i : Nat) : Suite :=
  match goldFloat? (idx r i), goldFloat? (idx r (i + 1)) with
  | some v, some e =>
    let s := s.check (sameBits x.val v) fun _ => s!"{what}: val {hexOf x.val}, want {hexOf v}"
    s.check (sameBits x.err e) fun _ => s!"{what}: err {hexOf x.err}, want {hexOf e}"
  | _, _ => s

/-- The measured constants group. -/
def measuresSuite : IO Suite := do
  let j ← loadJson "measuresystems/measures.json"
  let mut s : Suite := { name := "measured constants group" }
  for r in arr (fld j "basis") do
    let i := (int (idx r 0)).toNat - 1
    if h : i < 44 then
      let g := Consts.gen i h
      s := s.check (showMeasures g == str (idx r 1)) fun _ => s!"basis {i + 1}: got {showMeasures g}, want {str (idx r 1)}"
      s := checkMNum s s!"basis {i + 1}" (productM g) r 2
  for r in arr (fld j "random") do
    let g := constsOf r
    s := s.check (showMeasures g == str (idx r 2)) fun _ => s!"random: got {showMeasures g}, want {str (idx r 2)}"
    s := checkMNum s s!"random {str (idx r 0)}" (productM g) r 3
  for r in arr (fld j "named") do
    let g := constsOf (Json.arr #[idx r 1, idx r 2])
    s := s.check (showMeasures g == str (idx r 3)) fun _ => s!"{str (idx r 0)}: got {showMeasures g}, want {str (idx r 3)}"
    s := checkMNum s (str (idx r 0)) (productM g) r 4
  return s

/-- Parsing, printing and arithmetic of measurements. -/
def measurementsSuite : IO Suite := do
  let j ← loadJson "measuresystems/measurements.json"
  let mut s : Suite := { name := "measurements" }
  for r in arr (fld j "parse") do
    let inp := str (idx r 0)
    match Measurement.parse? inp 1 with
    | none => s := s.check false fun _ => s!"cannot parse {inp}"
    | some m =>
      s := checkMNum s inp (.meas m) r 1
      s := s.check (m.display == str (idx r 3)) fun _ => s!"show {inp}: got {m.display}, want {str (idx r 3)}"
      s := s.check (m.printSpecial == str (idx r 4)) fun _ => s!"print_special {inp}: got {m.printSpecial}, want {str (idx r 4)}"
      s := s.check (m.specialPrint == str (idx r 5)) fun _ => s!"special_print {inp}: got {m.specialPrint}, want {str (idx r 5)}"
  let p (t : String) (id : Nat) : Measurement := (Measurement.parse? t id).getD default
  let a := p "1.5(1)" 1
  let b := p "2.25(20)" 2
  let c := p "0.75(5)" 3
  let cases : List (String × Measurement) :=
    [("a+b", a + b), ("a-b", a - b), ("a*b", a * b), ("a/b", a / b), ("a-a", a - a), ("a/a", a / a),
     ("a*a", a * a), ("a^2", a.powInt 2), ("a^-3", a.powInt (-3)), ("a^(1//2)", a.powRat (mkRat 1 2)),
     ("a^0.75", a.powFloat 0.75), ("sqrt(a)", a.sqrt), ("cbrt(b)", b.cbrt), ("inv(c)", c.inv),
     ("2.5*a", Measurement.scale 2.5 a), ("a*3", a.mulReal 3.0), ("a/4.0", a.divReal 4.0),
     ("1.0/a", Measurement.realDiv 1.0 a), ("a+1.0", Measurement.result1 (a.val + 1.0) 1.0 a),
     ("1.0-a", Measurement.realSub 1.0 a), ("-a", -a), ("(a*b+c)/(a-c)", (a * b + c) / (a - c)),
     ("a*b*c-b*c*a", a * b * c - b * c * a), ("(a+b)*(a-b)", (a + b) * (a - b)),
     ("sqrt(a*a+b*b)", (a * a + b * b).sqrt)]
  for r in arr (fld j "arith") do
    let nm := str (idx r 0)
    match cases.lookup nm with
    | none => s := s.check false fun _ => s!"no case {nm}"
    | some m =>
      s := checkMNum s nm (.meas m) r 1
      s := s.check (m.display == str (idx r 3)) fun _ => s!"{nm}: got {m.display}, want {str (idx r 3)}"
  return s

/-- Constants of the selected systems with uncertainties. -/
def systemConstantsSuite : IO Suite := do
  let j ← loadJson "measuresystems/system_constants.json"
  let mut s : Suite := { name := "measured system constants" }
  let exact := scalarFunctions (α := Scalar)
  let model := scalarFunctions (α := HalfDim)
  for r in arr j do
    let U := sysOf! (str (idx r 0))
    let nm := str (idx r 1)
    match exact.lookup nm, model.lookup nm with
    | some f, some g =>
      let dims := (dimOf g).toExps
      let v := MValue.exact (f Sys.SI2019.consts * ratio dims .SI2019 U)
      let shown := s!"{v.jprint} [{U.showDim dims}] {U.name}"
      s := s.check (shown == str (idx r 2)) fun _ => s!"{nm}({U.name}): got {shown}, want {str (idx r 2)}"
      s := checkMNum s s!"{nm}({U.name})" v.toMNum r 3
    | _, _ => s := s.check false fun _ => s!"no function {nm}"
  return s

/-- Conversion factors with uncertainties. -/
def ratiosSuite : IO Suite := do
  let j ← loadJson "measuresystems/ratios.json"
  let mut s : Suite := { name := "measured ratios" }
  for r in arr j do
    let (a, b) := (sysOf! (str (idx r 0)), sysOf! (str (idx r 1)))
    let some q := Conv.ofName? (str (idx r 2)) | s := s.check false fun _ => "unknown quantity"
    let d := q.dim.toGroup.v
    let shown := showConvertM d a b
    s := s.check (shown == str (idx r 3)) fun _ => s!"{q.name}({a.name},{b.name}): got {shown}, want {str (idx r 3)}"
    s := checkMNum s s!"{q.name}({a.name},{b.name})" (MValue.exact (ratio d a b)).toMNum r 4
  return s

/-- Derived units with uncertainties, in their own system and in Metric
(`derived.json`), and `δμ₀`, `μE☾` (`constants.json`). -/
def derivedSuite : IO Suite := do
  let j ← loadJson "measuresystems/derived.json"
  let mut s : Suite := { name := "measured derived units" }
  for r in arr j do
    let nm := str (idx r 0)
    match MeasureSystems.Units.derivedTable.lookup nm with
    | none => s := s.check false fun _ => s!"no unit {nm}"
    | some ⟨_, _, q⟩ =>
      if !(str (idx r 1)).startsWith "Similitude." then
        s := s.check (toString q == str (idx r 1)) fun _ => s!"{nm}: got {q}, want {str (idx r 1)}"
      let m := q.to .Metric
      s := s.check (toString m == str (idx r 2)) fun _ => s!"{nm}(Metric): got {m}, want {str (idx r 2)}"
      s := checkMNum s s!"{nm}(Metric)" m.val.toMNum r 3
  let c ← loadJson "measuresystems/constants.json"
  for r in arr c do
    match str (idx r 0) with
    | "δμ₀" =>
      s := s.check (δμ₀.toMeas.display == str (idx r 1)) fun _ => s!"δμ₀: got {δμ₀.toMeas.display}"
      s := checkMNum s "δμ₀" δμ₀ r 2
    | "μE☾" =>
      s := s.check (μE.toMeas.display == str (idx r 1)) fun _ => s!"μE☾: got {μE.toMeas.display}"
      s := checkMNum s "μE☾" μE.toMNum r 2
    | nm =>
      if nm.startsWith "sackurtetrode(" then
        let U := sysOf! ((nm.drop 14).dropEnd 1).toString
        let (shown, m) := MeasureSystems.sackurtetrode U
        s := s.check (shown == str (idx r 1)) fun _ => s!"{nm}: got {shown}, want {str (idx r 1)}"
        s := checkMNum s nm m r 2
      else match MeasureSystems.Constants.table.lookup nm with
      | some (shown, m) =>
        s := s.check (shown == str (idx r 1)) fun _ => s!"{nm}: got {shown}, want {str (idx r 1)}"
        s := checkMNum s nm m r 2
      | none => s := s.check false fun _ => s!"no constant {nm}"
  return s

end Tests.MeasureSystemsTests
