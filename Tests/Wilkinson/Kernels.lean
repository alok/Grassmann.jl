import Tests.Wilkinson.Util

/-!
Julia's float kernels and MPFR's `BigFloat` against Julia
(`oracle/golden/wilkinson/kernels.json`), bit for bit: the compensated
`x^n` (`pow_body`), `literal_pow`, `Float32` powers, the SIMD-blocked
`sum(::Vector{Float64})`, Julia's own `exp`/`log` (`Float64` and `Float32`), and
256-bit `+ - * /`, `^n`, conversions and `BigFloat(p//q)`. `BigFloat` `log` is
within an ulp at 256 bits.
-/

open Lean Wilkinson Tests.Golden

namespace Tests.Wilkinson.Kernels

/-- The vector the generator sums: integers scaled by powers of two (exact in both). -/
def sumVec (n seed : Nat) : FloatArray :=
  (List.range n).foldl (fun acc k =>
    let i := k + 1
    let h : Int := ((i * 0x9E3779B1 + seed) % 2 ^ 32 : Nat)
    let e : Int := ((i * seed + 7) % 61 : Nat)
    acc.push (Float.scaleB (Float.ofInt (h - 2 ^ 31)) (e - 91))) (FloatArray.emptyWithCapacity n)

/-- The suite. -/
def suite : TestM Unit := do
  let j ← loadJson "oracle/golden/wilkinson/kernels.json"
  for c in jArr (jGet j "pow") do
    let x := hexF64 (jGet c "x")
    let n := jInt (jGet c "n")
    let r := powInt x n
    check s!"{x}^{n}" (sameFloat r (hexF64 (jGet c "r"))) s!"got {r}, expected {hexF64 (jGet c "r")}"
    let rf := JNum.powF64 x (Float.ofInt n)
    check s!"{x}^{n}.0" (sameFloat rf (hexF64 (jGet c "rf"))) s!"got {rf}, expected {hexF64 (jGet c "rf")}"
  for c in jArr (jGet j "literal_pow") do
    let x := hexF64 (jGet c "x")
    let k := jInt (jGet c "k")
    check s!"literal_pow({x}, {k})" (sameFloat (literalPow x k) (hexF64 (jGet c "r")))
  for c in jArr (jGet j "pow32") do
    let x := hexF32 (jGet c "x")
    let n := jInt (jGet c "n")
    check s!"{x}f0^{n}" (sameF32 (powInt32 x n) (hexF32 (jGet c "r")))
      s!"got {powInt32 x n}, expected {hexF32 (jGet c "r")}"
  for c in jArr (jGet j "sum") do
    let n := jNat (jGet c "n")
    let s := juliaSum (sumVec n (jNat (jGet c "seed")))
    check s!"sum(length {n})" (sameFloat s (hexF64 (jGet c "r"))) s!"got {s}, expected {hexF64 (jGet c "r")}"
  for c in jArr (jGet j "big") do
    let (a, b, cc) := (hexF64 (jGet c "a"), hexF64 (jGet c "b"), hexF64 (jGet c "c"))
    let (A, B, C) := (BigFloat.ofFloat 256 a, BigFloat.ofFloat 256 b, BigFloat.ofFloat 256 cc)
    let n := jInt (jGet c "n")
    let name := s!"big({a}, {b})"
    checkEq s!"{name}.add" (reprStr (A + B)) (reprStr (jBig (jGet c "add")))
    checkEq s!"{name}.sub" (reprStr (A - B)) (reprStr (jBig (jGet c "sub")))
    checkEq s!"{name}.mul" (reprStr (A * B)) (reprStr (jBig (jGet c "mul")))
    checkEq s!"{name}.div" (reprStr (A / B)) (reprStr (jBig (jGet c "div")))
    let F := (A * B + C) / A
    checkEq s!"{name}.(ab+c)/a" (reprStr F) (reprStr (jBig (jGet c "fma")))
    checkEq s!"{name}.pow({n})" (reprStr (A.powInt n)) (reprStr (jBig (jGet c "pow")))
    let L := BigFloat.log A.abs
    check s!"{name}.log" (match bigUlps L (jBig (jGet c "log")) with | some u => decide (u ≤ 1) | none => false)
      s!"got {reprStr L}"
    check s!"{name}.Float64" (sameFloat F.toFloat (hexF64 (jGet c "tofloat")))
    check s!"{name}.Float32" (sameF32 F.toFloat32 (hexF32 (jGet c "tofloat32")))
  for c in jArr (jGet j "bigrat") do
    let q : Rat := ((jStr (jGet c "p")).toInt?.getD 0 : Rat) / ((jStr (jGet c "q")).toInt?.getD 1 : Rat)
    checkEq s!"BigFloat({q})" (reprStr (BigFloat.ofRat 256 q)) (reprStr (jBig (jGet c "r")))
  checkEq "eps(BigFloat)" (reprStr (BigFloat.round 256 false 1 (-255))) (reprStr (jBig (jGet j "bigeps")))
  -- Julia's table-driven exp/log, bit for bit
  for (key, f) in [("exp", JuliaMath.exp), ("log", JuliaMath.log)] do
    let cs := jArr (jGet j key)
    let bad := cs.toList.filter fun c => let a := jArr c; !sameFloat (f (hexF64 a[0]!)) (hexF64 a[1]!)
    check s!"{key}(::Float64) ({cs.size} values)" bad.isEmpty
      s!"{bad.length} differ, first {(bad.head?.map fun c => hexF64 (jArr c)[0]!).getD 0}"
  for (key, f) in [("exp32", JuliaMath.exp32), ("log32", JuliaMath.log32)] do
    let cs := jArr (jGet j key)
    let bad := cs.toList.filter fun c => let a := jArr c; !sameF32 (f (hexF32 a[0]!)) (hexF32 a[1]!)
    check s!"{key}(::Float32) ({cs.size} values)" bad.isEmpty
      s!"{bad.length} differ, first {(bad.head?.map fun c => hexF32 (jArr c)[0]!).getD 0}"

end Tests.Wilkinson.Kernels
