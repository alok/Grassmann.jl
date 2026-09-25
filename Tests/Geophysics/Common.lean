import Geophysics
import Geophysics.Show
import Tests.FieldAlgebra.Harness

/-!
# Shared helpers for the Geophysics golden tests

Goldens live in `oracle/golden/geophysics/*.json` (written by
`oracle/geophysics/gen.jl`). Floats are IEEE bit patterns `"0x…"` and must match
**bit for bit**; a Julia exception is `{"E": "<Type>: …"}`. A `DomainError`
(Julia's `sqrt`/`^` of a negative number) must be `NaN` in Lean; any other Julia
error (a `MethodError`, the `SutherlandGas` stack overflow, …) marks a Julia
defect that Lean fixes or replaces by its intent, and is counted as skipped.
-/

namespace Tests.GeophysicsTests

open Lean Tests.Units Geophysics UnitSystems

/-- A golden float: its bits, a Julia error, or malformed. -/
inductive Gold where
  | val (x : Float)
  | err (msg : String)
  | bad

/-- Decode a golden float. -/
def gold (j : Json) : Gold :=
  match j with
  | .str s => if s.startsWith "0x" then .val (Float.ofBits (hexU64 s)) else .bad
  | .obj _ => .err (str (fld j "E"))
  -- a Julia `Int` result (the integer `0` flattening of a sphere, `Tμ = 107`, …)
  | .num n => .val n.toFloat
  | _ => .bad

/-- A float for failure messages: Julia digits and bits. -/
def fmt (x : Float) : String := s!"{JuliaBase.F64.showString x} ({hexOf x})"

/-- A tally: the checks and the Julia-defect entries that were skipped. -/
structure Tally where
  /-- the checks -/
  s : Suite
  /-- golden entries recording a non-domain Julia error (not compared) -/
  skipped : Nat := 0

namespace Tally

/-- A new tally. -/
def new (name : String) : Tally := ⟨{ name }, 0⟩

/-- Record a boolean check. -/
def ok (t : Tally) (b : Bool) (msg : Unit → String) : Tally := { t with s := t.s.check b msg }

/-- Compare a Lean float with a golden float, bit for bit. -/
def f (t : Tally) (got : Float) (want : Json) (what : Unit → String) : Tally :=
  match gold want with
  | .val x => t.ok (sameBits got x) fun _ => s!"{what ()}: got {fmt got}, want {fmt x}"
  | .err m =>
    if m.startsWith "DomainError" then
      t.ok got.isNaN fun _ => s!"{what ()}: Julia DomainError, got {fmt got}"
    else { t with skipped := t.skipped + 1 }
  | .bad => t.ok false fun _ => s!"{what ()}: malformed golden {want.compress}"

/-- Compare a list of floats with a golden array. -/
def fs (t : Tally) (gots : List Float) (want : Json) (what : Unit → String) : Tally :=
  match gold want with
  | .err m =>
    if m.startsWith "DomainError" then
      t.ok (gots.any (·.isNaN)) fun _ => s!"{what ()}: Julia DomainError, got {gots.map fmt}"
    else { t with skipped := t.skipped + 1 }
  | _ =>
    let ws := arr want
    let t := t.ok (gots.length == ws.size) fun _ => s!"{what ()}: length {gots.length} vs {ws.size}"
    (gots.zip ws.toList).zipIdx.foldl
      (fun t ((g, w), i) => t.f g w fun _ => s!"{what ()}[{i}]") t

/-- Compare a Lean integer with a golden integer. -/
def int (t : Tally) (got : Int) (want : Json) (what : Unit → String) : Tally :=
  match want with
  | .obj _ => { t with skipped := t.skipped + 1 }
  | _ => t.ok (want.getInt?.toOption == some got) fun _ => s!"{what ()}: got {got}, want {want.compress}"

/-- Compare a string with a golden string (skipping a golden Julia error). -/
def string (t : Tally) (got : String) (want : Json) (what : Unit → String) : Tally :=
  match want with
  | .str w => t.ok (got == w) fun _ => s!"{what ()}:\n got  {got}\n want {w}"
  | _ => { t with skipped := t.skipped + 1 }

/-- Print the report; returns `(passed, failed)`. -/
def report (t : Tally) : IO (Nat × Nat) := do
  let r ← t.s.report
  if t.skipped > 0 then IO.println s!"    ({t.skipped} Julia-defect entries skipped)"
  return r

end Tally

/-- Decode a golden float array (non-floats become `NaN`). -/
def floats (j : Json) : FloatArray :=
  (arr j).foldl (fun acc x => acc.push (match gold x with | .val v => v | _ => JMath.nan)) .empty

/-- A golden float (`NaN` if it is not one). -/
def float1 (j : Json) : Float := match gold j with | .val v => v | _ => JMath.nan

/-- Julia system names used by the goldens. -/
def sysOf (s : String) : Sys := (Sys.ofName? s).getD .Metric

/-- Load a Geophysics golden. -/
def load (name : String) : IO Json := loadJson s!"geophysics/{name}.json"

end Tests.GeophysicsTests
