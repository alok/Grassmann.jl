import JuliaBase
import Lean.Data.Json

/-!
Shared helpers for the JuliaBase test suites: hex parsing, a pass/fail tally, and helpers
for the oracle golden files (`Tests/JuliaBase/*.json`, written by
`Tests/JuliaBase/gen_golden.jl` from the pinned oracle environment).
-/

namespace Tests.JuliaBase

/-- Parse a lowercase or uppercase hexadecimal string (no `0x` prefix). -/
def parseHex (s : String) : Option Nat :=
  s.foldl (fun acc c => acc.bind fun n =>
    if '0' ≤ c && c ≤ '9' then some (16 * n + (c.toNat - '0'.toNat))
    else if 'a' ≤ c && c ≤ 'f' then some (16 * n + (c.toNat - 'a'.toNat + 10))
    else if 'A' ≤ c && c ≤ 'F' then some (16 * n + (c.toNat - 'A'.toNat + 10))
    else none) (some 0)

/-- A `Float` from its hexadecimal bit pattern. -/
def floatOfHex (s : String) : Option Float := (parseHex s).map fun n => Float.ofBits n.toUInt64

/-- A `Float32` from its hexadecimal bit pattern. -/
def float32OfHex (s : String) : Option Float32 :=
  (parseHex s).map fun n => Float32.ofBits n.toUInt32

/-- Hexadecimal bit pattern of a `Float` (lowercase, no leading zeros, like Julia's
`string(reinterpret(UInt64, x), base = 16)`). -/
def hexOfFloat (x : Float) : String :=
  let n := x.toBits.toNat
  if n == 0 then "0" else String.ofList (Nat.toDigits 16 n)

/-- Bitwise float equality, treating every NaN as equal: Julia `isequal`. -/
@[inline] def sameFloat (x y : Float) : Bool := JuliaBase.F64.isequal x y

/-- Running tally of a test suite: passes, failures, and the first few failure messages. -/
structure Tally where
  /-- number of passed checks -/
  passed : Nat := 0
  /-- number of failed checks -/
  failed : Nat := 0
  /-- the first failure messages (capped) -/
  msgs : Array String := #[]

namespace Tally

/-- Record one check. -/
def check (t : Tally) (ok : Bool) (msg : Unit → String) : Tally :=
  if ok then { t with passed := t.passed + 1 }
  else
    { t with failed := t.failed + 1,
             msgs := if t.msgs.size < 20 then t.msgs.push (msg ()) else t.msgs }

/-- Combine two tallies. -/
def merge (a b : Tally) : Tally :=
  { passed := a.passed + b.passed, failed := a.failed + b.failed,
    msgs := (a.msgs ++ b.msgs).extract 0 20 }

/-- Print the failures under a suite name and return `(passed, failed)`. -/
def report (t : Tally) (name : String) : IO (Nat × Nat) := do
  for m in t.msgs do IO.eprintln s!"  [{name}] FAIL {m}"
  if t.failed > t.msgs.size then
    IO.eprintln s!"  [{name}] … {t.failed - t.msgs.size} more failures"
  IO.println s!"  {name}: {t.passed} passed, {t.failed} failed"
  return (t.passed, t.failed)

end Tally

/-- Read and parse a golden JSON file from `Tests/JuliaBase/` (paths are relative to the
package root, where `lake test` runs). -/
def loadGolden (name : String) : IO Lean.Json := do
  let path : System.FilePath := "Tests" / "JuliaBase" / name
  let txt ← IO.FS.readFile path
  match Lean.Json.parse txt with
  | .ok j => pure j
  | .error e => throw (IO.userError s!"{path}: {e}")

/-- The array under `key` of a JSON object (empty if absent). -/
def jArr (j : Lean.Json) (key : String) : Array Lean.Json :=
  ((j.getObjValD key).getArr?.toOption).getD #[]

/-- A JSON string (or `""`). -/
def jStr (j : Lean.Json) : String := (j.getStr?.toOption).getD ""

/-- A JSON array of strings, as a list (the row format of the golden files). -/
def jRow (j : Lean.Json) : List String := ((j.getArr?.toOption).getD #[]).toList.map jStr

/-- A JSON array of integers. -/
def jInts (j : Lean.Json) : List Int :=
  ((j.getArr?.toOption).getD #[]).toList.map fun x => (x.getInt?.toOption).getD 0

/-- Lines of a TSV file, split on tabs (blank lines dropped). -/
def readTsv (path : System.FilePath) : IO (Array (List String)) := do
  let txt ← IO.FS.readFile path
  return ((txt.splitOn "\n").filter (!·.isEmpty)).toArray.map (·.splitOn "\t")

end Tests.JuliaBase
