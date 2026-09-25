import Tests.Cartan.Common

/-!
# Range fields: Julia's lazy range arithmetic (`oracle/golden/cartan/ranges.json`)

The identity field of a range keeps the range as its fiber in Julia, and `x .* r`, `r ./ x`, `-r`,
`r₁ ± r₂` stay ranges with `TwicePrecision` elements; `t + 1` (a `Ref` broadcast) and `t * t`
materialize. The goldens record every element bit for bit and whether the fiber is still a range.
-/

open Lean Tests.Small Cartan JuliaBase

namespace Tests.CartanTests.Ranges

/-- The ranges of the goldens. -/
def axes : List (String × Axis) :=
  [("0:0.1:1", Axis.colon 0 0.1 1), ("0:0.25:2", Axis.colon 0 0.25 2), ("-1:0.3:2", Axis.colon (-1) 0.3 2),
   ("range(0,1,length=7)", Axis.range 0 1 7), ("LinRange(0,2π,7)", Axis.linRange 0 twoPiF 7),
   ("LinRange(-1,3,9)", Axis.linRange (-1) 3 9)]

/-- The field operations of the goldens on the identity field of `a`. -/
def ops (a : Axis) : List (String × FieldOut) :=
  let t := TensorField.ofAxis a
  let t2 := TensorField.ofAxisFn a ((0.5 : Float) * ·)
  let three : Float := 3
  [("t", out t), ("3t", out (three * t)), ("t*3", out (t * three)), ("2πt", out (twoPiF * t)),
   ("t/3", out (t / three)), ("-t", out (-t)), ("t+t", out (t + t)), ("t+3t", out (t + three * t)),
   ("t-3t", out (t - three * t)), ("t/3+t*7", out (t / three + t * (7 : Float))),
   ("t+1", out (t + (1 : Float))), ("1-t", out ((1 : Float) - t)), ("t*t", out (t * t)),
   ("t+t2", out (t + t2)), ("-(t/3)", out (-(t / three)))]

/-- The sums of the goldens (range closed forms, or Julia's pairwise vector sum). -/
def sums (a : Axis) : List (String × Float) :=
  let t := TensorField.ofAxis a
  let three : Float := 3
  [("sum(t)", t.sumF), ("sum(3t)", (three * t).sumF), ("sum(t/3)", (t / three).sumF),
   ("sum(t+1)", (t + (1 : Float)).sumF)]

/-- Run the range-field checks. -/
def run : TestM Unit := do
  let j ← load "ranges"
  let cases ← jField j "cases"
  for (name, a) in axes do
    let c ← jField cases name
    for (op, o) in ops a do
      checkField s!"ranges {name} {op}" o (← jField c op)
    for (op, x) in sums a do
      checkFloat s!"ranges {name} {op}" x (← jField c op)

end Tests.CartanTests.Ranges
