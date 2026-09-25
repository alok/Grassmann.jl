import JuliaBase

/-!
Compare Julia's own elementary functions in `JuliaBase` (`JuliaBase.F64.sin`, …) with a sweep written by `oracle/geophysics/mathsamples.jl`:

    lake env lean --run oracle/geophysics/MathSweep.lean /tmp/geo_math.txt

Prints the mismatch count per function (all zero is required).
-/

open JuliaBase

/-- Count mismatches per function name. -/
def main (args : List String) : IO Unit := do
  let path := args.headD "geo_math.txt"
  let s ← IO.FS.readFile path
  let mut names : Array String := #[]
  let mut bad : Array Nat := #[]
  let mut tot : Array Nat := #[]
  for line in s.splitOn "\n" do
    let ws := (line.splitOn " ").toArray
    if ws.size < 3 then continue
    let v (i : Nat) : Float := Float.ofBits ((ws[i]!).toNat!.toUInt64)
    let x := v 1
    let checks : List (String × Float × Float) :=
      match ws[0]! with
      | "exp" => [("exp", F64.exp x, v 2)]
      | "pow" => [("pow", F64.pow x (v 2), v 3)]
      | "trig" => [("sin", F64.sin x, v 2), ("cos", F64.cos x, v 3), ("tan", F64.tan x, v 4)]
      | "atan" => [("atan", F64.atan x, v 2)]
      | "arc" => [("asin", F64.asin x, v 2), ("atanh", F64.atanh x, v 3),
                  ("log1p", F64.log1p x, v 4)]
      | _ => []
    for (nm, got, want) in checks do
      let k := (names.findIdx? (· == nm)).getD names.size
      if k == names.size then
        names := names.push nm; bad := bad.push 0; tot := tot.push 0
      tot := tot.modify k (· + 1)
      if got.toBits != want.toBits && !(got.isNaN && want.isNaN) then
        if bad[k]! < 5 then
          IO.println s!"{nm} x = {x} (bits {x.toBits}): got {got.toBits}, want {want.toBits}"
        bad := bad.modify k (· + 1)
  for i in [0:names.size] do
    IO.println s!"{names[i]!}: {bad[i]!} / {tot[i]!} mismatches"
