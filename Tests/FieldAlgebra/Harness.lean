import Lean.Data.Json

/-!
# Golden-test harness for the units packages

Shared by the FieldAlgebra, UnitSystems, Similitude and MeasureSystems suites.
Goldens are JSON files under `oracle/golden/<pkg>/` produced by the Julia
generators in `oracle/<pkg>/*.jl`; tests run from the package root (`lake test`).
Floats in goldens are either IEEE bit patterns (`"0x…"`) or Julia `repr`
strings; both are decoded exactly.
-/

namespace Tests.Units

open Lean

/-- A named tally of checks with the first few failure messages. -/
structure Suite where
  /-- suite name for the report -/
  name : String
  /-- passed checks -/
  pass : Nat := 0
  /-- failed checks -/
  fail : Nat := 0
  /-- first failure messages (at most `maxShown`) -/
  failures : Array String := #[]

/-- Failure messages kept per suite (printing is further limited by the
`UNITS_TEST_SHOW` environment variable, default 12). -/
def maxShown : Nat := 5000

/-- Record one check. The message is only built on failure. -/
def Suite.check (s : Suite) (ok : Bool) (msg : Unit → String) : Suite :=
  if ok then { s with pass := s.pass + 1 }
  else { s with fail := s.fail + 1,
                failures := if s.failures.size < maxShown then s.failures.push (msg ()) else s.failures }

/-- Merge the counts of another suite into this one. -/
def Suite.merge (s t : Suite) : Suite :=
  { s with pass := s.pass + t.pass, fail := s.fail + t.fail,
           failures := s.failures ++ (t.failures.map (s!"[{t.name}] " ++ ·)) }

/-- Print a one-line summary plus the stored failures; return `(passed, failed)`. -/
def Suite.report (s : Suite) : IO (Nat × Nat) := do
  IO.println s!"  {s.name}: {s.pass} passed, {s.fail} failed"
  let shown := ((← IO.getEnv "UNITS_TEST_SHOW").bind String.toNat?).getD 12
  for f in s.failures.extract 0 shown do IO.println s!"    FAIL {f}"
  return (s.pass, s.fail)

/-- Root of the committed goldens. -/
def goldenDir : System.FilePath := "oracle" / "golden"

/-- Load and parse a golden JSON file (path relative to `oracle/golden`). -/
def loadJson (rel : String) : IO Json := do
  let s ← IO.FS.readFile (goldenDir / rel)
  match Json.parse s with
  | .ok j => pure j
  | .error e => throw (IO.userError s!"{rel}: {e}")

/-- Array view of a JSON value (empty if not an array). -/
def arr (j : Json) : Array Json := (j.getArr?).toOption.getD #[]

/-- String view of a JSON value (`""` if not a string). -/
def str (j : Json) : String := (j.getStr?).toOption.getD ""

/-- Field of a JSON object (`null` if absent). -/
def fld (j : Json) (k : String) : Json := j.getObjValD k

/-- Integer view of a JSON number (0 if not an integer). -/
def int (j : Json) : Int := (j.getInt?).toOption.getD 0

/-- `j[i]` for arrays. -/
def idx (j : Json) (i : Nat) : Json := (arr j)[i]?.getD Json.null

/-- Parse `"0x…"` hexadecimal into a `UInt64`. -/
def hexU64 (s : String) : UInt64 :=
  let s := if s.startsWith "0x" then (s.drop 2).toString else s
  s.foldl (fun acc c =>
    let d := if c.isDigit then c.toNat - '0'.toNat
      else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10
      else if 'A' ≤ c && c ≤ 'F' then c.toNat - 'A'.toNat + 10 else 0
    acc * 16 + d.toUInt64) 0

/-- A float stored as its IEEE bit pattern `"0x…"`. -/
def hexFloat (j : Json) : Float := Float.ofBits (hexU64 (str j))

/-- Bitwise float identity (NaNs are identified). -/
def sameBits (x y : Float) : Bool := x.toBits == y.toBits || (x.isNaN && y.isNaN)

/-- Hex rendering of a float for failure messages. -/
def hexOf (x : Float) : String :=
  let b := x.toBits.toNat
  "0x" ++ String.ofList (Nat.toDigits 16 b)

end Tests.Units
