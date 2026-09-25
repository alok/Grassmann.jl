import Tests.JuliaBase.Util

/-!
Julia numeric semantics against the oracle (`Tests/JuliaBase/num.json`): `hypot`, `rem`,
`mod`, `fld`, `cld`, `div`, `max`, `min`, `cbrt`, `round`, `sign`, `trunc`,
`nextfloat`/`prevfloat` (all compared bit for bit), `isapprox` with default, `atol`, `rtol`
and `nans` keywords, `ComplexF64` division/inverse/product/abs, and integer
`div`/`rem`/`fld`/`mod`/`cld`.
-/

open JuliaBase

namespace Tests.JuliaBase.Num

/-- Binary `Float64` operations by oracle name. -/
def binop : String → Option (Float → Float → Float)
  | "hypot" => some F64.hypot
  | "rem" => some F64.rem
  | "mod" => some F64.mod
  | "fld" => some F64.fld
  | "cld" => some F64.cld
  | "div" => some F64.div
  | "max" => some F64.max
  | "min" => some F64.min
  | _ => none

/-- Unary `Float64` operations by oracle name. -/
def unop : String → Option (Float → Float)
  | "cbrt" => some F64.cbrt
  | "round" => some F64.round
  | "sign" => some F64.sign
  | "trunc" => some F64.trunc
  | "nextfloat" => some F64.nextfloat
  | "prevfloat" => some F64.prevfloat
  | _ => none

/-- Check a binary-op row `[name, x, y, result]`. -/
def checkBin (t : Tally) : List String → Tally
  | [name, hx, hy, hr] =>
    match binop name, floatOfHex hx, floatOfHex hy, floatOfHex hr with
    | some f, some x, some y, some r =>
      let got := f x y
      t.check (sameFloat got r) fun _ =>
        s!"{name}({F64.showString x}, {F64.showString y}): got {F64.showString got} (0x{hexOfFloat got}), want {F64.showString r} (0x{hr})"
    | _, _, _, _ => t.check false fun _ => s!"bad binop row {name} {hx} {hy} {hr}"
  | r => t.check false fun _ => s!"malformed binop row {r}"

/-- Check a unary-op row `[name, x, result]`. -/
def checkUn (t : Tally) : List String → Tally
  | [name, hx, hr] =>
    match unop name, floatOfHex hx, floatOfHex hr with
    | some f, some x, some r =>
      let got := f x
      t.check (sameFloat got r) fun _ =>
        s!"{name}({F64.showString x}): got {F64.showString got}, want {F64.showString r}"
    | _, _, _ => t.check false fun _ => s!"bad unop row {name} {hx} {hr}"
  | r => t.check false fun _ => s!"malformed unop row {r}"

/-- Check an `isapprox` row `[kind, x, y, atol, rtol, result]`. -/
def checkApprox (t : Tally) : List String → Tally
  | [kind, hx, hy, ha, hr, want] =>
    match floatOfHex hx, floatOfHex hy with
    | some x, some y =>
      let got :=
        match kind with
        | "atol" => F64.isapprox x y (atol := (floatOfHex ha).getD 0)
        | "rtol" => F64.isapprox x y (rtol := (floatOfHex hr).getD 0)
        | "nans" => F64.isapprox x y (nans := true)
        | _ => F64.isapprox x y
      t.check (toString got == want) fun _ =>
        s!"isapprox[{kind}]({F64.showString x}, {F64.showString y}): got {got}, want {want}"
    | _, _ => t.check false fun _ => s!"bad isapprox row {hx} {hy}"
  | r => t.check false fun _ => s!"malformed isapprox row {r}"

/-- Check a complex row `[op, a, b, c, d, re, im]` for `z = a+bi`, `w = c+di`. -/
def checkComplex (t : Tally) : List String → Tally
  | [op, ha, hb, hc, hd, hre, him] =>
    match floatOfHex ha, floatOfHex hb, floatOfHex hc, floatOfHex hd, floatOfHex hre, floatOfHex him with
    | some a, some b, some c, some d, some re, some im =>
      let z : Complex Float := ⟨a, b⟩
      let w : Complex Float := ⟨c, d⟩
      let got : Complex Float :=
        match op with
        | "div" => ComplexF64.div z w
        | "inv" => ComplexF64.inv z
        | "mul" => z * w
        | _ => ⟨ComplexF64.abs z, Complex.abs2 z⟩
      t.check (sameFloat got.re re && sameFloat got.im im) fun _ =>
        s!"complex {op} ({a}, {b}) ({c}, {d}): got ({got.re}, {got.im}), want ({re}, {im})"
    | _, _, _, _, _, _ => t.check false fun _ => s!"bad complex row"
  | r => t.check false fun _ => s!"malformed complex row {r}"

/-- Check an integer row `[x, y, div, rem, fld, mod, cld]`. -/
def checkInt (t : Tally) : List Int → Tally
  | [x, y, d, r, f, m, c] =>
    let got := [JInt.div x y, JInt.rem x y, JInt.fld x y, JInt.mod x y, JInt.cld x y]
    t.check (got == [d, r, f, m, c]) fun _ => s!"int ops {x} {y}: got {got}, want {[d, r, f, m, c]}"
  | r => t.check false fun _ => s!"malformed int row {r}"

/-- The committed golden `num.json`. -/
def golden : IO (Nat × Nat) := do
  let j ← loadGolden "num.json"
  let mut t : Tally := {}
  for row in jArr j "binop" do t := checkBin t (jRow row)
  for row in jArr j "unop" do t := checkUn t (jRow row)
  for row in jArr j "isapprox" do t := checkApprox t (jRow row)
  for row in jArr j "complex" do t := checkComplex t (jRow row)
  for row in jArr j "int" do t := checkInt t (jInts row)
  t.report "num golden"

/-- The TSV fuzz file `PREFIX_num.tsv` (rows tagged `bin`, `un`, `approx`, `cplx`). -/
def fuzz (path : System.FilePath) : IO (Nat × Nat) := do
  let mut t : Tally := {}
  for row in ← readTsv path do
    match row with
    | "bin" :: r => t := checkBin t r
    | "un" :: r => t := checkUn t r
    | "approx" :: r => t := checkApprox t r
    | "cplx" :: r => t := checkComplex t r
    | r => t := t.check false fun _ => s!"malformed fuzz row {r}"
  t.report "num fuzz"

/-! Compile-time checks of the Julia semantics that differ from Lean's defaults. -/

#guard F64.max (-0.0) 0.0 == 0.0 && !F64.signbit (F64.max (-0.0) 0.0)
#guard F64.signbit (F64.min 0.0 (-0.0))
#guard (F64.max F64.nan 1.0).isNaN && (F64.min 1.0 F64.nan).isNaN
#guard F64.isapprox 1.0 (1.0 + 1e-9) && !F64.isapprox 1.0 (1.0 + 1e-7)
#guard !F64.isapprox 1e-300 0.0 && F64.isapprox 1e-10 0 (atol := 1e-8)
#guard F64.mod (-1.0) 3.0 == 2.0 && F64.rem (-1.0) 3.0 == -1.0
#guard F64.signbit (F64.round (-0.4)) && F64.round 2.5 == 2.0 && F64.round 3.5 == 4.0
#guard JInt.fld (-7) 2 == -4 && JInt.div (-7) 2 == -3 && JInt.mod 7 (-2) == -1 && JInt.cld 7 2 == 4
#guard F64.hypot 3.0 4.0 == 5.0 && F64.hypot F64.nan F64.inf == F64.inf
#guard F64.cbrt 27.0 == 3.0 && F64.cbrt (-8.0) == -2.0

end Tests.JuliaBase.Num
