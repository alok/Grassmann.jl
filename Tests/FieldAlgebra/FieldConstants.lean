import FieldConstants
import Tests.FieldAlgebra.Harness

/-!
# FieldConstants golden tests

Against `oracle/golden/unitsystems/floats.json` (`oracle/unitsystems/floats.jl`):
Julia float printing, parsing, the `Base.Math` exp/log/pow ports (bit-exact),
`round(digits/sigdigits)`, `power_by_squaring`, and the `Constant` operator table.
-/

namespace Tests.FieldAlgebra.FieldConstantsTests

open Lean Tests.Units FieldConstants FieldConstants.Julia

/-- Decode a `[kind, value]` pair of the operator table into a `JNum`. -/
def jnumOf (j : Json) : JNum :=
  match str (idx j 0) with
  | "Int64" => .int (Int64.ofInt ((str (idx j 1)).toInt?.getD 0))
  | _ => .float (hexFloat (idx j 1))

/-- Kind-and-bits identity of two `JNum`s. -/
def jnumSame : JNum → JNum → Bool
  | .int a, .int b => a == b
  | .float a, .float b => sameBits a b
  | _, _ => false

/-- Run all FieldConstants checks. -/
def run : IO Suite := do
  let j ← loadJson "unitsystems/floats.json"
  let mut s : Suite := { name := "FieldConstants" }
  -- printing
  for r in arr (fld j "show") do
    let x := hexFloat (idx r 0)
    let want := str (idx r 1)
    let got := JuliaBase.F64.showString x
    s := s.check (got == want) fun _ => s!"show {hexOf x}: got {got}, want {want}"
    -- shortest repr must round-trip through the parser
    if x.isFinite then
      let back := parseFloat want
      s := s.check (sameBits back x) fun _ => s!"parse(repr) {want}"
  -- parsing arbitrary decimal strings
  for r in arr (fld j "parse") do
    let txt := str (idx r 0)
    let want := str (idx r 1)
    match parseFloat? txt with
    | none => s := s.check (want == "ERR") fun _ => s!"parse {txt}: got ERR, want {want}"
    | some v =>
      s := s.check (want != "ERR" && sameBits v (hexFloat (idx r 1))) fun _ =>
        s!"parse {txt}: got {hexOf v}, want {want}"
  -- Float^Int
  for r in arr (fld j "powi") do
    let x := hexFloat (idx r 0)
    let n := int (idx r 1)
    let want := hexFloat (idx r 2)
    let got := powInt x n
    s := s.check (sameBits got want) fun _ => s!"{JuliaBase.F64.showString x}^{n}: got {JuliaBase.F64.showString got}, want {JuliaBase.F64.showString want}"
  -- Float^Float
  for r in arr (fld j "powf") do
    let x := hexFloat (idx r 0)
    let y := hexFloat (idx r 1)
    let want := hexFloat (idx r 2)
    let got := pow x y
    s := s.check (sameBits got want) fun _ =>
      s!"{JuliaBase.F64.showString x}^{JuliaBase.F64.showString y}: got {JuliaBase.F64.showString got}, want {JuliaBase.F64.showString want}"
  -- exp/log family
  let funs := fld j "funs"
  for (nm, f) in [("exp", Julia.exp), ("exp2", Julia.exp2), ("exp10", Julia.exp10),
                  ("log", Julia.log), ("log2", Julia.log2), ("log10", Julia.log10)] do
    for r in arr (fld funs nm) do
      let x := hexFloat (idx r 0)
      let want := hexFloat (idx r 1)
      let got := f x
      s := s.check (sameBits got want) fun _ =>
        s!"{nm}({JuliaBase.F64.showString x}): got {JuliaBase.F64.showString got}, want {JuliaBase.F64.showString want}"
  -- rounding
  for r in arr (fld j "round") do
    let x := hexFloat (idx r 0)
    let d := int (idx r 1)
    let n := int (idx r 3)
    let wd := hexFloat (idx r 2)
    let ws := hexFloat (idx r 4)
    let wh := int (idx r 5)
    s := s.check (sameBits (roundDigits x d) wd) fun _ =>
      s!"round({JuliaBase.F64.showString x}, digits={d}): got {JuliaBase.F64.showString (roundDigits x d)}, want {JuliaBase.F64.showString wd}"
    s := s.check (sameBits (roundSigdigits x n) ws) fun _ =>
      s!"round({JuliaBase.F64.showString x}, sigdigits={n}): got {JuliaBase.F64.showString (roundSigdigits x n)}, want {JuliaBase.F64.showString ws}"
    s := s.check (hidigit x == wh) fun _ => s!"hidigit({JuliaBase.F64.showString x}) = {hidigit x}, want {wh}"
  -- power_by_squaring on irrational bases
  for r in arr (fld j "pbs") do
    let nm := str (idx r 0)
    let p := (int (idx r 1)).toNat
    let want := hexFloat (idx r 2)
    let got := match nm with
      | "φ" => powerBySquaring 1.618033988749895 p
      | "γ" => powerBySquaring 0.5772156649015329 p
      | _ => Julia.exp (Float.ofNat p)
    s := s.check (sameBits got want) fun _ => s!"{nm}^{p}: got {JuliaBase.F64.showString got}, want {JuliaBase.F64.showString want}"
  -- Constant operator table
  for r in arr (fld j "constant_ops") do
    let op := str (idx r 0)
    let a := jnumOf (idx r 1)
    if op == "show" then
      s := s.check (a.toString == str (idx r 2)) fun _ => s!"show {a}: want {str (idx r 2)}"
    else
      let (got, want) := match op with
        | "*" => (a * jnumOf (idx r 2), jnumOf (idx r 3))
        | "/" => (a / jnumOf (idx r 2), jnumOf (idx r 3))
        | "+" => (a + jnumOf (idx r 2), jnumOf (idx r 3))
        | "-" => (a - jnumOf (idx r 2), jnumOf (idx r 3))
        | "inv" => (a⁻¹, jnumOf (idx r 2))
        | "sqrt" => (a.sqrt, jnumOf (idx r 2))
        | "log10" => (a.log10, jnumOf (idx r 2))
        | "logdb" => (logdb a, jnumOf (idx r 2))
        | "expdb" => (expdb a, jnumOf (idx r 2))
        | o => (a.lpow ((o.drop 1).toString.toInt?.getD 0), jnumOf (idx r 2))
      s := s.check (jnumSame got want) fun _ => s!"Constant {op} on {a}: got {got} ({got.kind}), want {want} ({want.kind})"
  s := s.check (sameBits (hexFloat (fld j "unit_rtol")) 8.161992717227193e-15) fun _ => "eps()^0.9"
  s := s.check (sameBits (Julia.exp10 0.1) (hexFloat (fld j "exp10_0.1"))) fun _ => "exp10(0.1)"
  s := s.check (sameBits (Julia.pow (2.220446049250313e-16) 0.9) 8.161992717227193e-15) fun _ => "eps^0.9 via pow"
  return s

end Tests.FieldAlgebra.FieldConstantsTests
