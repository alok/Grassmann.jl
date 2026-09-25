import Tests.JuliaBase.Util

/-!
Julia's own trigonometric, hyperbolic and `ComplexF64` functions against the oracle
(`Tests/JuliaBase/trig.json`, written by `gen_golden.jl trig`), all bit for bit:

* `t64`/`t32`: `sin`, `cos`, `tan`, `asin`, `acos`, `atan`, `sinh`, `cosh`, `tanh`, `asinh`,
  `acosh`, `atanh`, `sinpi`, `cospi` for `Float64` (`F64.sin`, …) and `Float32` (`F32.sin`, …);
* `sincos64`/`sincos32`, `sincospi64`: the two-result forms;
* `atan2_64`/`atan2_32`: `atan(y, x)` (`F64.atan2`, `F32.atan2`);
* `c64`: `exp`, `expm1`, `log`, `log1p`, `sqrt` and the trigonometric and hyperbolic functions
  and their inverses on `ComplexF64` (`ComplexF64.sin`, …), `cis` and `z^p` (`ComplexF64.pow`).

Julia throws a `DomainError` where these functions return `NaN` (`asin(2.0)`, `sin(Inf)`); the
generator skips such inputs.
-/

open JuliaBase

namespace Tests.JuliaBase.Trig

/-- A `Float32` from hex (`0` if malformed). -/
def f32 (s : String) : Float32 := (float32OfHex s).getD 0

/-- A `Float` from hex (`0` if malformed). -/
def f64 (s : String) : Float := (floatOfHex s).getD 0

/-- Bitwise `Float32` equality with all NaNs equal. -/
def sameF32 (x y : Float32) : Bool := (x.isNaN && y.isNaN) || x.toBits == y.toBits

/-- Julia's unary `Float64` functions by name. -/
def unary64 : String → Option (Float → Float)
  | "sin" => some F64.sin | "cos" => some F64.cos | "tan" => some F64.tan
  | "asin" => some F64.asin | "acos" => some F64.acos | "atan" => some F64.atan
  | "sinh" => some F64.sinh | "cosh" => some F64.cosh | "tanh" => some F64.tanh
  | "asinh" => some F64.asinh | "acosh" => some F64.acosh | "atanh" => some F64.atanh
  | "sinpi" => some F64.sinpi | "cospi" => some F64.cospi
  | _ => none

/-- Julia's unary `Float32` functions by name. -/
def unary32 : String → Option (Float32 → Float32)
  | "sin" => some F32.sin | "cos" => some F32.cos | "tan" => some F32.tan
  | "asin" => some F32.asin | "acos" => some F32.acos | "atan" => some F32.atan
  | "sinh" => some F32.sinh | "cosh" => some F32.cosh | "tanh" => some F32.tanh
  | "asinh" => some F32.asinh | "acosh" => some F32.acosh | "atanh" => some F32.atanh
  | "sinpi" => some F32.sinpi | "cospi" => some F32.cospi
  | _ => none

/-- Julia's unary `ComplexF64` functions by name. -/
def unaryC : String → Option (Complex Float → Complex Float)
  | "exp" => some ComplexF64.exp | "expm1" => some ComplexF64.expm1
  | "log" => some ComplexF64.log | "log1p" => some ComplexF64.log1p
  | "sqrt" => some ComplexF64.sqrt
  | "sin" => some ComplexF64.sin | "cos" => some ComplexF64.cos | "tan" => some ComplexF64.tan
  | "sinh" => some ComplexF64.sinh | "cosh" => some ComplexF64.cosh | "tanh" => some ComplexF64.tanh
  | "asin" => some ComplexF64.asin | "acos" => some ComplexF64.acos | "atan" => some ComplexF64.atan
  | "asinh" => some ComplexF64.asinh | "acosh" => some ComplexF64.acosh
  | "atanh" => some ComplexF64.atanh
  | _ => none

/-- Julia's `show` of a `Float64`, for failure messages. -/
def s64 (x : Float) : String := F64.showString x

/-- A complex value for failure messages. -/
def sC (z : Complex Float) : String := s!"{s64 z.re} + {s64 z.im}im"

/-- Bitwise equality of complex values (NaNs equal). -/
def sameC (z w : Complex Float) : Bool := sameFloat z.re w.re && sameFloat z.im w.im

/-- Check one `trig.json` row (an unknown row kind is a failure). -/
def checkRow (t : Tally) : List String → Tally
  | ["t64", name, hx, hr] =>
    match unary64 name with
    | some f =>
      let got := f (f64 hx)
      t.check (sameFloat got (f64 hr)) fun _ =>
        s!"{name}({s64 (f64 hx)}): got {s64 got}, want {s64 (f64 hr)}"
    | none => t.check false fun _ => s!"unknown Float64 function {name}"
  | ["t32", name, hx, hr] =>
    match unary32 name with
    | some f =>
      let got := f (f32 hx)
      t.check (sameF32 got (f32 hr)) fun _ =>
        s!"{name}({F32.showString (f32 hx)}): got {F32.showString got}, want {F32.showString (f32 hr)}"
    | none => t.check false fun _ => s!"unknown Float32 function {name}"
  | ["sincos64", hx, hs, hc] =>
    let (s, c) := F64.sincos (f64 hx)
    t.check (sameFloat s (f64 hs) && sameFloat c (f64 hc)) fun _ =>
      s!"sincos({s64 (f64 hx)}): got ({s64 s}, {s64 c}), want ({s64 (f64 hs)}, {s64 (f64 hc)})"
  | ["sincos32", hx, hs, hc] =>
    let (s, c) := F32.sincos (f32 hx)
    t.check (sameF32 s (f32 hs) && sameF32 c (f32 hc)) fun _ =>
      s!"sincos({F32.showString (f32 hx)}): got ({F32.showString s}, {F32.showString c})"
  | ["sincospi64", hx, hs, hc] =>
    let (s, c) := F64.sincospi (f64 hx)
    t.check (sameFloat s (f64 hs) && sameFloat c (f64 hc)) fun _ =>
      s!"sincospi({s64 (f64 hx)}): got ({s64 s}, {s64 c}), want ({s64 (f64 hs)}, {s64 (f64 hc)})"
  | ["atan2_64", hy, hx, hr] =>
    let got := F64.atan2 (f64 hy) (f64 hx)
    t.check (sameFloat got (f64 hr)) fun _ =>
      s!"atan({s64 (f64 hy)}, {s64 (f64 hx)}): got {s64 got}, want {s64 (f64 hr)}"
  | ["atan2_32", hy, hx, hr] =>
    let got := F32.atan2 (f32 hy) (f32 hx)
    t.check (sameF32 got (f32 hr)) fun _ =>
      s!"atan({F32.showString (f32 hy)}, {F32.showString (f32 hx)}): got {F32.showString got}, want {F32.showString (f32 hr)}"
  | ["c64", name, hre, him, rre, rim] =>
    match unaryC name with
    | some f =>
      let z : Complex Float := ⟨f64 hre, f64 him⟩
      let want : Complex Float := ⟨f64 rre, f64 rim⟩
      let got := f z
      t.check (sameC got want) fun _ => s!"{name}({sC z}): got {sC got}, want {sC want}"
    | none => t.check false fun _ => s!"unknown ComplexF64 function {name}"
  | ["cis", hx, rre, rim] =>
    let got := ComplexF64.cis (f64 hx)
    let want : Complex Float := ⟨f64 rre, f64 rim⟩
    t.check (sameC got want) fun _ => s!"cis({s64 (f64 hx)}): got {sC got}, want {sC want}"
  | ["cpow", are, aim, bre, bim, rre, rim] =>
    let z : Complex Float := ⟨f64 are, f64 aim⟩
    let p : Complex Float := ⟨f64 bre, f64 bim⟩
    let want : Complex Float := ⟨f64 rre, f64 rim⟩
    let got := ComplexF64.pow z p
    t.check (sameC got want) fun _ => s!"({sC z})^({sC p}): got {sC got}, want {sC want}"
  | r => t.check false fun _ => s!"unknown trig row {r.take 2}"

/-- The committed golden `trig.json`. -/
def golden : IO (Nat × Nat) := do
  let j ← loadGolden "trig.json"
  let mut t : Tally := {}
  for row in jArr j "cases" do t := checkRow t (jRow row)
  t.report "trig golden"

/-- The TSV fuzz file `PREFIX_trig.tsv`. -/
def fuzz (path : System.FilePath) : IO (Nat × Nat) := do
  let mut t : Tally := {}
  for row in ← readTsv path do t := checkRow t row
  t.report "trig fuzz"

end Tests.JuliaBase.Trig
