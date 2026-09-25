import Geophysics.JuliaMath

/-!
Compare `Geophysics.JMath` with a sweep written by `oracle/geophysics/mathsamples.jl`:

    lake env lean --run oracle/geophysics/MathSweep.lean /tmp/geo_math.txt

Prints the mismatch count per function (all zero is required).
-/

open Geophysics

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
      | "exp" => [("exp", JMath.exp x, v 2)]
      | "pow" => [("pow", JMath.pow x (v 2), v 3)]
      | "trig" => [("sin", JMath.sin x, v 2), ("cos", JMath.cos x, v 3), ("tan", JMath.tan x, v 4)]
      | "atan" => [("atan", JMath.atan x, v 2)]
      | "arc" => [("asin", JMath.asin x, v 2), ("atanh", JMath.atanh x, v 3),
                  ("log1p", JMath.log1p x, v 4)]
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
