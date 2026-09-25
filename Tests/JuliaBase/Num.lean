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
#guard F64.isless (-0.0) 0.0 && !F64.isless 0.0 (-0.0) && F64.isless F64.inf F64.nan
#guard F64.ulpDist 1.0 (F64.nextfloat 1.0) == 1 && F64.ulpDist (-0.0) 0.0 == 1
#guard F64.ulpDist F64.nan F64.nan == 0 && F64.ulpDist (F64.prevfloat 0.0) 5e-324 == 3
#guard F64.ofRat ((1 : Rat) / 3) == 1.0 / 3.0 && F64.ofRat (-7) == -7.0
#guard F64.exponent 1.0 == 0 && F64.exponent (-12.0) == 3 && F64.exponent 5e-324 == -1074
#guard F64.ldexp 1.0 (-1074) == 5e-324 && F64.ldexp 3.0 4 == 48.0
#guard F64.expm1 0.0 == 0.0 && F64.expm1 (-F64.inf) == -1.0 && F64.log1p (-1.0) == -F64.inf
/-- Julia 1.13 `ComplexF32` goldens `(z, w, z / w, inv(w))` as `Float32` bits:
`(re z, im z, re w, im w, re q, im q, re i, im i)`. -/
def complexF32Goldens : List (UInt32 × UInt32 × UInt32 × UInt32 × UInt32 × UInt32 × UInt32 × UInt32) := [
  (0x3f800000, 0x40000000, 0x40400000, 0x40800000, 0x3ee147ae, 0x3da3d70a, 0x3df5c28f, 0xbe23d70a),
  (0x0da24260, 0x40400000, 0x612d78ec, 0xbbe56042, 0x80000177, 0x1e8dabc6, 0x1dbce508, 0x0000007d),
  (0x3dcccccd, 0xbe99999a, 0x7f800000, 0x3f800000, 0x00000000, 0x00000000, 0x00000000, 0x80000000),
  (0x7fc00000, 0x3f800000, 0x7f800000, 0x00000000, 0x7fc00000, 0x7fc00000, 0x00000000, 0x80000000),
  (0x80000000, 0x40a00000, 0x3f800000, 0x80000000, 0x80000000, 0x40a00000, 0x3f800000, 0x00000000),
  (0xbedfa36c, 0x3ffe28e1, 0xbfd23cb0, 0x3f90aedb, 0x3f3ebb43, 0xbf323951, 0xbed389dc, 0xbe919424),
  (0xbf3cf070, 0xbdcb8166, 0xbedb9fb6, 0x3f6d16b0, 0x3e5cbd8c, 0x3f327330, 0xbed2d462, 0xbf639855),
  (0xbee55fdf, 0x3e98f08c, 0x3f47a64c, 0xbe8fc5c9, 0xbf216efd, 0x3e1fb545, 0x3f914a92, 0x3ed14174),
  (0x40167f2a, 0xbfc01f33, 0xbfbedbf3, 0xbf55c7a0, 0xbf4577a1, 0x3fb82467, 0xbf02b1c0, 0x3e9263c0),
  (0xbf9d5290, 0x3ff83277, 0x3f0f81c7, 0xbef1c4cf, 0xc03f291c, 0x3f71683d, 0x3f859076, 0x3f6104ab)]

/-- Bitwise `Float32` equality with all NaNs equal. -/
def sameF32 (x : Float32) (b : UInt32) : Bool :=
  (x.isNaN && (Float32.ofBits b).isNaN) || x.toBits == b

#guard complexF32Goldens.all fun (a, b, c, d, qr, qi, ir, ii) =>
  let z : Complex Float32 := ⟨Float32.ofBits a, Float32.ofBits b⟩
  let w : Complex Float32 := ⟨Float32.ofBits c, Float32.ofBits d⟩
  let q := z / w
  let i := w⁻¹
  sameF32 q.re qr && sameF32 q.im qi && sameF32 i.re ir && sameF32 i.im ii

#guard JInt.isodd (-3) && !JInt.isodd 4
#guard powBySquaring (· * ·) 1 (3 : Nat) 13 == 1594323 && powBySquaring (· * ·) 1 (2 : Nat) 0 == 1

end Tests.JuliaBase.Num
