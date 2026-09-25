import FieldAlgebra
import Tests.FieldAlgebra.Harness

/-!
# FieldAlgebra golden tests

Against `oracle/golden/similitude/fieldalgebra.json`
(`oracle/similitude/fieldalgebra.jl`): superscript printing primitives,
`makeint`/`findpower`, group algebra and display on a character-named basis
(`@group2 XYZ x y z w`) and a string-named basis (`@group2 Named ab cd …`), and
`LogGroup`/`ExpGroup` display.
-/

namespace Tests.FieldAlgebra.GroupTests

open Lean Tests.Units FieldConstants FieldConstants.Julia _root_.FieldAlgebra

/-- Julia `@group2 XYZ x y z w`. -/
def xyz : Basis := { name := "XYZ", n := 4, text := #["x", "y", "z", "w"], charNames := true }
/-- Julia `@group2 Named ab cd ef gh ij`. -/
def named : Basis := { name := "Named", n := 5, text := #["ab", "cd", "ef", "gh", "ij"], charNames := false }

/-! Compile-time spot checks (evaluated during elaboration). -/
#guard printExpoInt (-12) == "⁻¹²"
#guard printExpoRat (Rat.divInt (-3) 2) == "⁻³ᐟ²"
#guard printExpoBased "10" (.float (-3.0)) == "/10³"
#guard (Group.ofInts (B := xyz) [1, 2, 0, -1]).print == "xy²w⁻¹"
#guard (Group.ofInts (B := named) [1, 1, 0, 0, 2]).print == "ab⋅cd⋅ij²"
#guard (Group.ofInts (B := xyz) [0, 0, 0, 0] (.float 0.5)).print == "𝟙/2"
#guard ((Group.gen (B := xyz) ⟨0, by decide⟩).log.mulNum 2).print == "log(1.6487212707001282,x)"

/-- Decode `["I", "3"]`, `["R", "1/2"]`, `["F", "0x…"]`. -/
def expoOf (j : Json) : Expo :=
  match str (idx j 0) with
  | "I" => .int ((str (idx j 1)).toInt?.getD 0)
  | "R" =>
    match (str (idx j 1)).splitOn "/" with
    | [a, b] => .rat (Rat.divInt (a.toInt?.getD 0) (b.toInt?.getD 1))
    | _ => .int 0
  | _ => .float (hexFloat (idx j 1))

/-- Decode a coefficient. -/
def coefOf (j : Json) : Coef :=
  match expoOf j with
  | .int n => .int n
  | .rat q => .rat q
  | .float x => .float x

/-- Decode an exponent vector (all entries share one kind in Julia). -/
def expsOf (B : Basis) (j : Json) : Exps B.n :=
  let es := (arr j).map expoOf
  if es.any (fun e => match e with | .float _ => true | _ => false) then
    .float (FVec.ofFn fun i => (es[i.1]?.getD (.int 0)).toFloat)
  else
    .exact (Vector.ofFn fun i => match es[i.1]?.getD (.int 0) with
      | .int n => (n : Rat) | .rat q => q | .float _ => 0)

/-- Decode an encoded group element. -/
def groupOf (B : Basis) (j : Json) : Group B := ⟨expsOf B (fld j "v"), coefOf (fld j "c")⟩

/-- Same Julia kind and value for an exponent. -/
def expoSame : Expo → Expo → Bool
  | .int a, .int b => a == b
  | .rat a, .rat b => a == b
  | .float a, .float b => sameBits a b || a == b
  | _, _ => false

/-- Same Julia kind and value for a coefficient. -/
def coefSame : Coef → Coef → Bool
  | .int a, .int b => a == b
  | .rat a, .rat b => a == b
  | .float a, .float b => sameBits a b
  | _, _ => false

/-- Compare a Lean group with its Julia encoding: exponents (kind and value),
coefficient (kind and bits) and printed form. -/
def groupMatches {B : Basis} (g : Group B) (j : Json) : Bool × String :=
  let want := groupOf B j
  let okV := (List.finRange B.n).all fun i => expoSame (g.v.get i) (want.v.get i)
  let okC := coefSame g.c want.c
  let s := g.print
  let okS := s == str (fld j "show")
  (okV && okC && okS, s!"got {s}, want {str (fld j "show")} (v {okV}, c {okC})")

/-- Tests for one basis. -/
def groupRows (B : Basis) (rows : Array Json) (s0 : Suite) : Suite := Id.run do
  let mut s := s0
  for r in rows do
    let a := groupOf B (fld r "a")
    let b := groupOf B (fld r "b")
    -- decoding round trip: the printed form of the inputs
    s := s.check (a.print == str (fld (fld r "a") "show")) fun _ =>
      s!"show {str (fld (fld r "a") "show")}: got {a.print}"
    let e := int (fld r "e")
    let rr := match expoOf (fld r "r") with | .rat q => q | _ => 0
    let f := (expoOf (fld r "f")).toFloat
    let ops : List (String × Group B) :=
      [("mul", a * b), ("div", a / b), ("inv", a⁻¹), ("pow", a ^ e), ("powr", a ^ rr),
       ("sqrt", a.sqrt), ("powf", a.fpow f)]
    for (nm, g) in ops do
      let w := fld r nm
      if str w != "ERROR" then
        let (ok, msg) := groupMatches g w
        s := s.check ok fun _ => s!"{B.name} {nm} of {str (fld (fld r "a") "show")}: {msg}"
  return s

/-- Run the FieldAlgebra golden checks. -/
def run : IO Suite := do
  let j ← loadJson "similitude/fieldalgebra.json"
  let mut s : Suite := { name := "FieldAlgebra" }
  for r in arr (fld j "prims") do
    let kind := str (idx r 0)
    match kind with
    | "printexpo" =>
      let got := printExpo (expoOf (idx r 1))
      s := s.check (got == str (idx r 2)) fun _ => s!"printexpo {idx r 1}: got {got}, want {str (idx r 2)}"
    | "printexpo_based" =>
      let got := printExpoBased (str (idx r 1)) (expoOf (idx r 2))
      s := s.check (got == str (idx r 3)) fun _ =>
        s!"printexpo({str (idx r 1)}, {idx r 2}): got {got}, want {str (idx r 3)}"
    | "latexpo_based" =>
      let got := latexpoBased (str (idx r 1)) (expoOf (idx r 2))
      s := s.check (got == str (idx r 3)) fun _ =>
        s!"latexpo({str (idx r 1)}, {idx r 2}): got {got}, want {str (idx r 3)}"
    | "makeint" =>
      let x := (expoOf (idx r 1)).toFloat
      let got : Expo := match makeint x with | .int n => .int n.toInt | .float y => .float y
      s := s.check (expoSame got (expoOf (idx r 2))) fun _ => s!"makeint {showFloat x}: got {got.print}"
    | "findpower" =>
      let got := findpower (int (idx r 1)).toNat
      s := s.check (got == (int (idx r 2)).toNat) fun _ => s!"findpower {int (idx r 1)}: got {got}"
    | "print_special" =>
      let got := printSpecialFloat (expoOf (idx r 1)).toFloat
      s := s.check (got == str (idx r 2)) fun _ => s!"print_special: got {got}, want {str (idx r 2)}"
    | "special_print" =>
      let got := specialPrintFloat (expoOf (idx r 1)).toFloat
      s := s.check (got == str (idx r 2)) fun _ => s!"special_print: got {got}, want {str (idx r 2)}"
    | _ => pure ()
  let groups := arr (fld j "groups")
  s := groupRows xyz (groups.filter fun r => str (fld r "basis") == "XYZ") s
  s := groupRows named (groups.filter fun r => str (fld r "basis") == "Named") s
  -- LogGroup / ExpGroup display
  for r in arr (fld j "loggroups") do
    let check (B : Basis) (s : Suite) : Suite := Id.run do
      let mut s := s
      let a := groupOf B (fld r "a")
      let b := groupOf B (fld r "b")
      let cases : List (String × String) :=
        [("log", a.log.print), ("log2", a.log2.print), ("log10", a.log10.print),
         ("log3", (a.logb 3).print), ("logdb", a.logdb.print), ("exp", a.exp.print),
         ("exp2", a.exp2.print), ("exp10", a.exp10.print), ("pow3", (a.expb 3).print),
         ("logmul2", (a.log.mulNum 2).print), ("logdiv2", (a.log.divNum 2).print),
         ("logadd", ((a.log.add b.log).map (·.print)).getD "?"),
         ("logsub", ((a.log.sub b.log).map (·.print)).getD "?")]
      for (nm, got) in cases do
        let want := str (fld r nm)
        s := s.check (got == want) fun _ => s!"{nm}: got {got}, want {want}"
      return s
    s := if str (fld r "basis") == "XYZ" then check xyz s else check named s
  return s

end Tests.FieldAlgebra.GroupTests
