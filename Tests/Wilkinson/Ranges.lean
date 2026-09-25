import Tests.Wilkinson.Util

/-!
Wilkinson's sample grids against Julia (`oracle/golden/wilkinson/ranges.json`):
`floatset(T, N; scale)` for `Float64` and `Float32`, every element bit for bit,
plus `Float32` and `Float64` `start:step:stop` ranges with exact rational
endpoints (the `floatrange` path) and without.
-/

open Lean Wilkinson Tests.Golden

namespace Tests.Wilkinson.Ranges

/-- Compare a grid with a golden `{first, last, step, len, bits}` record
(`f32` selects `Float32` bit patterns). -/
def checkSet (name : String) (s : FloatSet) (g : Json) (f32 : Bool) : TestM Unit := do
  let dec (j : Json) : Float := if f32 then (hexF32 j).toFloat else hexF64 j
  checkEq s!"{name}.len" s.len (jNat (jGet g "len"))
  check s!"{name}.first" (sameFloat s.first (dec (jGet g "first")))
  check s!"{name}.last" (sameFloat s.last (dec (jGet g "last")))
  check s!"{name}.step" (sameFloat s.stepValue (dec (jGet g "step")))
    s!"got {s.stepValue}, expected {dec (jGet g "step")}"
  let bits := jArr (jGet g "bits")
  let bad := (List.range bits.size).filter fun i => !sameFloat (s.get (i + 1)) (dec bits[i]!)
  check s!"{name}.elements ({bits.size})" bad.isEmpty
    s!"{bad.length} differ, first at {bad.head?.getD 0}: got {s.get (bad.head?.getD 0 + 1)}"

/-- The suite. -/
def suite : TestM Unit := do
  let j ← loadJson "oracle/golden/wilkinson/ranges.json"
  checkSet "floatset(Float64, 3000; scale = log)" (logset .f64) (jGet j "logset64") false
  checkSet "floatset(Float32, 3000; scale = log)" (logset .f32) (jGet j "logset32") true
  for (n, g) in [10, 100, 2999].zip (jArr (jGet j "logset64_n")).toList do
    checkSet s!"floatset(Float64, {n}; scale = log)" (floatset n JuliaBase.F64.log) g false
  checkSet "floatset(Float64, 10)" (floatset 10) (jGet j "idset64") false
  for g in jArr (jGet j "colon32") do
    let a := jArr (jGet g "args")
    let (x, st, y) := (hexF32 a[0]!, hexF32 a[1]!, hexF32 a[2]!)
    checkSet s!"{x}f0:{st}f0:{y}f0" (.f32 (colon32 x st y)) g true
  for g in jArr (jGet j "colon64") do
    let a := jArr (jGet g "args")
    let (x, st, y) := (hexF64 a[0]!, hexF64 a[1]!, hexF64 a[2]!)
    checkSet s!"{x}:{st}:{y}" (.f64 (JuliaBase.colon x st y)) g false

end Tests.Wilkinson.Ranges
