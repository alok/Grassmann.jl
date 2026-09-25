import Lean.Data.Json
import AbstractAnalysis.JuliaFloat

/-!
# Golden-test harness (shared by the AbstractAnalysis and Wilkinson suites)

Loads the committed JSON goldens, parses Julia's float `repr` strings exactly
(`Float.ofScientific` is correctly rounded), and tallies checks in a
`StateT` over `IO` so a suite reports `(passed, failed)`.
-/

open Lean

namespace Tests.Golden

/-- Pass/fail tally with the first few failure messages. -/
structure Tally where
  /-- Passed checks. -/
  pass : Nat := 0
  /-- Failed checks. -/
  fail : Nat := 0
  /-- Recorded failure messages (capped). -/
  msgs : Array String := #[]

/-- Test monad. -/
abbrev TestM := StateT Tally IO

/-- Record one check. -/
def check (name : String) (ok : Bool) (detail : String := "") : TestM Unit :=
  modify fun t =>
    if ok then { t with pass := t.pass + 1 }
    else { t with fail := t.fail + 1,
                  msgs := if t.msgs.size < 40 then t.msgs.push s!"FAIL {name}: {detail}" else t.msgs }

/-- Equality check with both sides in the message. -/
def checkEq {α : Type} [BEq α] [ToString α] (name : String) (got expected : α) : TestM Unit :=
  check name (got == expected) s!"got {got}, expected {expected}"

/-- Bitwise float equality (`NaN` equals `NaN`; `±0` distinguished). -/
def sameFloat (a b : Float) : Bool := a.toBits == b.toBits || (a.isNaN && b.isNaN)

/-- Float check: bitwise, or within `ulps` units in the last place, or within
relative tolerance `rtol`. -/
def checkFloat (name : String) (got expected : Float) (rtol : Float := 0) (ulps : Nat := 0) : TestM Unit :=
  let ok := sameFloat got expected ||
    (got.isFinite && expected.isFinite &&
      (AbstractAnalysis.IEEEFloat.ulpDistance got expected ≤ ulps ||
       (got - expected).abs ≤ rtol * max got.abs expected.abs))
  check name ok s!"got {AbstractAnalysis.Float.toJulia got}, expected {AbstractAnalysis.Float.toJulia expected}"

/-- Run a suite, print its summary and failures, return `(passed, failed)`. -/
def runSuite (label : String) (m : TestM Unit) : IO (Nat × Nat) := do
  let (_, t) ← (m.run {})
  for msg in t.msgs do IO.eprintln s!"  [{label}] {msg}"
  IO.println s!"{label}: {t.pass} passed, {t.fail} failed"
  return (t.pass, t.fail)

/-- Read and parse a golden JSON file (path relative to the package root). -/
def loadJson (path : System.FilePath) : IO Json := do
  let s ← IO.FS.readFile path
  match Json.parse s with
  | .ok j => return j
  | .error e => throw <| IO.userError s!"{path}: {e}"

/-- Parse Julia's `repr(::Float64)` (`Inf`, `-0.0`, `3.26592e6`, `1.0f0`, …). -/
def parseFloat (s : String) : Option Float :=
  match s with
  | "Inf" | "Inf32" => some (1.0 / 0.0)
  | "-Inf" | "-Inf32" => some (-1.0 / 0.0)
  | "NaN" | "NaN32" => some (0.0 / 0.0)
  | "-0.0" | "-0.0f0" => some (-0.0)
  | _ =>
    let s := s.replace "f" "e"
    match Json.parse s with
    | .ok (.num n) => some n.toFloat
    | _ => none

/-- A float field stored as a `repr` string. -/
def jFloat (j : Json) : Float :=
  match j with
  | .str s => (parseFloat s).getD (0.0 / 0.0)
  | .num n => n.toFloat
  | _ => 0.0 / 0.0

/-- Array of floats stored as `repr` strings. -/
def jFloats (j : Json) : Array Float :=
  match j with
  | .arr a => a.map jFloat
  | _ => #[]

/-- Integer field. -/
def jInt (j : Json) : Int :=
  match j.getInt? with
  | .ok i => i
  | .error _ => 0

/-- Natural-number field. -/
def jNat (j : Json) : Nat := (jInt j).toNat

/-- Boolean field. -/
def jBool (j : Json) : Bool :=
  match j.getBool? with
  | .ok b => b
  | .error _ => false

/-- String field. -/
def jStr (j : Json) : String :=
  match j.getStr? with
  | .ok s => s
  | .error _ => ""

/-- Array field. -/
def jArr (j : Json) : Array Json :=
  match j.getArr? with
  | .ok a => a
  | .error _ => #[]

/-- Object member (null when missing). -/
def jGet (j : Json) (k : String) : Json := (j.getObjVal? k).toOption.getD .null

/-- Rational `[num, den]`. -/
def jRat (j : Json) : Rat :=
  let a := jArr j
  (jInt a[0]! : Rat) / (jInt a[1]! : Rat)

/-- Integer list. -/
def jInts (j : Json) : Array Int := (jArr j).map jInt

/-- Natural list. -/
def jNats (j : Json) : Array Nat := (jArr j).map jNat

end Tests.Golden
