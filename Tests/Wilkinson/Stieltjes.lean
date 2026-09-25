import Tests.Wilkinson.Util

/-!
The Stieltjes bound against Julia (`oracle/golden/wilkinson/stieltjes.json`,
using verbatim copies of Wilkinson's kernels): for each form, `Ω` (first
overflow) exactly, and `simpson`, `geonorm` and sampled `stieltjes` values for
`Float64`, `BigFloat` (with `eps(Float64)`) and `Float32` evaluation, all bit for bit
(the grid, `exp`, `log`, powers and `sum` are Julia's own kernels).
-/

open Lean Wilkinson Tests.Golden

namespace Tests.Wilkinson.Stieltjes

/-- The suite. -/
def suite : TestM Unit := do
  let j ← loadJson "oracle/golden/wilkinson/stieltjes.json"
  let set64 := logset .f64
  let set32 := logset .f32
  for c in jArr (jGet j "cases") do
    let e := jExpr (jGet c "expr")
    let name := s!"stieltjes[{jExprStr (jGet c "expr")}]"
    let st := stieltjes set64 e .f64
    let n := Ω st
    checkEq s!"{name}.Ω" n (jNat (jGet c "omega"))
    let smp := simpson set64 st n
    check s!"{name}.simpson" (sameFloat smp (hexF64 (jGet c "smp"))) s!"got {smp}, expected {hexF64 (jGet c "smp")}"
    check s!"{name}.geonorm" (sameFloat (geonorm smp) (hexF64 (jGet c "geonorm")))
    let stb := stieltjes set64 e .big .f64
    let smpb := simpson set64 stb n
    check s!"{name}.simpson(BigFloat)" (sameFloat smpb (hexF64 (jGet c "smp_big")))
      s!"got {smpb}, expected {hexF64 (jGet c "smp_big")}"
    let st32 := stieltjes set32 e .f32
    let n32 := Ω st32
    checkEq s!"{name}.Ω(Float32)" n32 (jNat (jGet c "omega32"))
    let smp32 := simpson set32 st32 n32
    check s!"{name}.simpson(Float32)" (sameFloat smp32 (hexF64 (jGet c "smp32")))
      s!"got {smp32}, expected {hexF64 (jGet c "smp32")}"
    for smpl in jArr (jGet c "sample") do
      let s := jArr smpl
      let i := jNat s[0]!
      check s!"{name}.stj[{i}]" (sameFloat st[i - 1]! (hexF64 s[1]!) && sameFloat stb[i - 1]! (hexF64 s[2]!) &&
        sameFloat st32[i - 1]! (hexF64 s[3]!))
        s!"got ({st[i - 1]!}, {stb[i - 1]!}, {st32[i - 1]!}), expected ({hexF64 s[1]!}, {hexF64 s[2]!}, {hexF64 s[3]!})"
    match jGet c "stj" with
    | .arr full =>
      let bad := (List.range full.size).filter fun i => !sameFloat st[i]! (hexF64 full[i]!)
      check s!"{name}.stj (all {full.size})" bad.isEmpty s!"{bad.length} differ, first at {bad.head?.getD 0}"
    | _ => pure ()

end Tests.Wilkinson.Stieltjes
