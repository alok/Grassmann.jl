import AbstractAnalysis
import Tests.AbstractAnalysis.Harness

/-!
Julia's shortest float printing, fuzzed against 7000+ `Float64` and 2000
`Float32` values printed by Julia (`oracle/golden/abstractanalysis/floatprint.json`).
-/

open Lean AbstractAnalysis Tests.Golden

namespace Tests.AbstractAnalysis.FloatPrint

/-- Parse a lowercase hexadecimal string. -/
def hexNat (s : String) : Nat :=
  s.foldl (fun acc c => acc * 16 + (if c.isDigit then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10)) 0

/-- The suite: all strings must match exactly. -/
def suite : TestM Unit := do
  let j ← loadJson "oracle/golden/abstractanalysis/floatprint.json"
  let mut bad64 := 0
  let mut first64 := ""
  let mut n64 := 0
  for e in jArr (jGet j "f64") do
    let x := Float.ofBits (hexNat (jStr (jGet e "bits"))).toUInt64
    let s := jStr (jGet e "str")
    n64 := n64 + 1
    if Float.toJulia x != s then
      if bad64 == 0 then first64 := s!"{s} printed as {Float.toJulia x}"
      bad64 := bad64 + 1
  check s!"Float64 string ({n64} values)" (bad64 == 0) s!"{bad64} mismatches, first: {first64}"
  let mut bad32 := 0
  let mut first32 := ""
  let mut n32 := 0
  for e in jArr (jGet j "f32") do
    let x := Float32.ofBits (hexNat (jStr (jGet e "bits"))).toUInt32
    n32 := n32 + 1
    let r := jStr (jGet e "repr")
    let s := jStr (jGet e "str")
    if JuliaFloat.float32Repr x != r || Float32.toJulia x != s then
      if bad32 == 0 then first32 := s!"{r} printed as {JuliaFloat.float32Repr x}"
      bad32 := bad32 + 1
  check s!"Float32 repr/string ({n32} values)" (bad32 == 0) s!"{bad32} mismatches, first: {first32}"

end Tests.AbstractAnalysis.FloatPrint
