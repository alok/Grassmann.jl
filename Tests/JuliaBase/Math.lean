import Tests.JuliaBase.Util
import Tests.Util.Random

/-!
Julia's own numerics against the oracle (`Tests/JuliaBase/math.json`, written by
`gen_golden.jl math`), all bit for bit, and property checks of the exact IEEE toolkit:

* `u64`/`u32`: Julia's own `exp`, `exp2`, `exp10`, `expm1`, `log`, `log2`, `log10`,
  `log1p` for `Float64` (`F64.exp`, …) and `Float32` (`F32.exp`, …);
* `powf64`/`powi64`/`powf32`/`powi32`, `lit64`/`lit32`, `pbs64`: `x^y`, `x^n`,
  `literal_pow` and `power_by_squaring` (the fixed Julia defect
  `float32-pow-large-odd-sign` is checked against the sign-corrected value);
* `rdig`/`rsig`/`hidigit`: `round(x; digits)`, `round(x; sigdigits)`, `Base.hidigit`;
* `eps64`/`eps32`, `exponent64`/`exponent32`, `rat64`/`rat32`: `F64.epsOf`, `F32.epsOf`,
  `IEEEFloat.exponent`, and the correctly rounded `IEEEFloat.ofFraction`/`ofRat` of big
  rationals.
-/

open JuliaBase

namespace Tests.JuliaBase.Math

/-- A `Float32` from hex (`0` if malformed). -/
def f32 (s : String) : Float32 := (float32OfHex s).getD 0

/-- A `Float` from hex (`0` if malformed). -/
def f64 (s : String) : Float := (floatOfHex s).getD 0

/-- Bitwise `Float32` equality with all NaNs equal. -/
def sameF32 (x y : Float32) : Bool := (x.isNaN && y.isNaN) || x.toBits == y.toBits

/-- An integer field. -/
def int (s : String) : Int := s.toInt?.getD 0

/-- Julia's unary `Float64` kernels by name. -/
def unary64 : String → Option (Float → Float)
  | "exp" => some F64.exp
  | "exp2" => some F64.exp2
  | "exp10" => some F64.exp10
  | "expm1" => some F64.expm1
  | "log" => some F64.log
  | "log2" => some F64.log2
  | "log10" => some F64.log10
  | "log1p" => some F64.log1p
  | _ => none

/-- Julia's unary `Float32` kernels by name. -/
def unary32 : String → Option (Float32 → Float32)
  | "exp" => some F32.exp
  | "exp2" => some F32.exp2
  | "exp10" => some F32.exp10
  | "expm1" => some F32.expm1
  | "log" => some F32.log
  | "log2" => some F32.log2
  | "log10" => some F32.log10
  | "log1p" => some F32.log1p
  | _ => none

/-- Rows hitting the documented Julia defect `float32-pow-large-odd-sign`: `x^n` for
`x::Float32 < 0` and an odd `n` (after Julia's `clamp(n, Int32)`) outside
`power_by_squaring`'s range, where Julia drops the sign (`F32.powInt` applies it). -/
def f32PowSignDefect (x : Float32) (n : Int) : Bool :=
  let n := max (-2147483648) (min 2147483647 n)
  x < 0 && n % 2 != 0 && !(-4096 ≤ n && n ≤ 24576)

/-- Check one `math.json` row (rows of kinds this module does not know are skipped). -/
def checkRow (t : Tally) : List String → Tally
  | ["u64", name, hx, hr] =>
    match unary64 name with
    | some f =>
      let got := f (f64 hx)
      t.check (sameFloat got (f64 hr)) fun _ =>
        s!"{name}({F64.showString (f64 hx)}): got {F64.showString got}, want {F64.showString (f64 hr)}"
    | none => t.check false fun _ => s!"unknown Float64 function {name}"
  | ["u32", name, hx, hr] =>
    match unary32 name with
    | some f =>
      let got := f (f32 hx)
      t.check (sameF32 got (f32 hr)) fun _ =>
        s!"{name}({F32.showString (f32 hx)}): got {F32.showString got}, want {F32.showString (f32 hr)}"
    | none => t.check false fun _ => s!"unknown Float32 function {name}"
  | ["powf64", hx, hy, hr] =>
    let got := F64.pow (f64 hx) (f64 hy)
    t.check (sameFloat got (f64 hr)) fun _ =>
      s!"{F64.showString (f64 hx)}^{F64.showString (f64 hy)}: got {F64.showString got}, want {F64.showString (f64 hr)}"
  | ["powi64", hx, n, hr] =>
    let got := F64.powInt (f64 hx) (int n)
    t.check (sameFloat got (f64 hr)) fun _ =>
      s!"{F64.showString (f64 hx)}^{n}: got {F64.showString got}, want {F64.showString (f64 hr)}"
  | ["powf32", hx, hy, hr] =>
    let got := F32.pow (f32 hx) (f32 hy)
    t.check (sameF32 got (f32 hr)) fun _ =>
      s!"{F32.showString (f32 hx)}^{F32.showString (f32 hy)}: got {F32.showString got}, want {F32.showString (f32 hr)}"
  | ["powi32", hx, n, hr] =>
    let x := f32 hx
    if f32PowSignDefect x (int n) then
      -- the fixed defect: the same magnitude with the sign of an odd power
      t.check (sameF32 (F32.powInt x (int n)) (-(f32 hr))) fun _ => s!"{F32.showString x}^{n} (sign fixed)"
    else
      let got := F32.powInt x (int n)
      t.check (sameF32 got (f32 hr)) fun _ =>
        s!"{F32.showString x}^{n}: got {F32.showString got}, want {F32.showString (f32 hr)}"
  | ["lit64", hx, k, hr] =>
    let got := F64.literalPow (f64 hx) (int k)
    t.check (sameFloat got (f64 hr)) fun _ =>
      s!"literal_pow({F64.showString (f64 hx)}, {k}): got {F64.showString got}, want {F64.showString (f64 hr)}"
  | ["lit32", hx, k, hr] =>
    let got := F32.literalPow (f32 hx) (int k)
    t.check (sameF32 got (f32 hr)) fun _ =>
      s!"literal_pow({F32.showString (f32 hx)}, {k}): got {F32.showString got}, want {F32.showString (f32 hr)}"
  | ["pbs64", hx, p, hr] =>
    let got := F64.powerBySquaring (f64 hx) (int p).toNat
    t.check (sameFloat got (f64 hr)) fun _ =>
      s!"power_by_squaring({F64.showString (f64 hx)}, {p}): got {F64.showString got}, want {F64.showString (f64 hr)}"
  | ["rdig", hx, d, hr] =>
    let got := F64.roundDigits (f64 hx) (int d)
    t.check (sameFloat got (f64 hr)) fun _ =>
      s!"round({F64.showString (f64 hx)}, digits = {d}): got {F64.showString got}, want {F64.showString (f64 hr)}"
  | ["rsig", hx, n, hr] =>
    let got := F64.roundSigdigits (f64 hx) (int n)
    t.check (sameFloat got (f64 hr)) fun _ =>
      s!"round({F64.showString (f64 hx)}, sigdigits = {n}): got {F64.showString got}, want {F64.showString (f64 hr)}"
  | ["hidigit", hx, h] =>
    t.check (F64.hidigit (f64 hx) == int h) fun _ =>
      s!"hidigit({F64.showString (f64 hx)}): got {F64.hidigit (f64 hx)}, want {h}"
  | ["eps64", hx, hr] =>
    let got := F64.epsOf (f64 hx)
    t.check (sameFloat got (f64 hr)) fun _ => s!"eps({F64.showString (f64 hx)}): got {F64.showString got}"
  | ["eps32", hx, hr] =>
    let got := F32.epsOf (f32 hx)
    t.check (sameF32 got (f32 hr)) fun _ => s!"eps({F32.showString (f32 hx)}): got {F32.showString got}"
  | ["exponent64", hx, e] =>
    let x := f64 hx
    t.check (IEEEFloat.exponent x == int e && F64.exponent x == int e) fun _ =>
      s!"exponent({F64.showString x}): got {IEEEFloat.exponent x}, want {e}"
  | ["exponent32", hx, e] =>
    let x := f32 hx
    t.check (IEEEFloat.exponent x == int e) fun _ =>
      s!"exponent({F32.showString x}): got {IEEEFloat.exponent x}, want {e}"
  | ["rat64", p, q, hr] =>
    let got := IEEEFloat.ofFraction Float (int p) (int q).toNat
    let viaRat := IEEEFloat.ofRat Float ((int p : Rat) / (int q : Rat))
    t.check (sameFloat got (f64 hr) && sameFloat viaRat (f64 hr)) fun _ =>
      s!"Float64({p}/{q}): got {F64.showString got}, want {F64.showString (f64 hr)}"
  | ["rat32", p, q, hr] =>
    let got := IEEEFloat.ofFraction Float32 (int p) (int q).toNat
    t.check (sameF32 got (f32 hr)) fun _ =>
      s!"Float32({p}/{q}): got {F32.showString got}, want {F32.showString (f32 hr)}"
  | _ => t

/-- A random finite `Float` from random bits. -/
def randFinite (g : Tests.Rng) : Float × Tests.Rng :=
  let (u, g) := g.next
  let x := Float.ofBits u
  (if x.isFinite then x else Float.ofBits (u &&& 0x3FFFFFFFFFFFFFFF), g)

/-- Property checks of the exact IEEE toolkit against the bit-level `F64`/`F32` functions. -/
def props : Tally := Id.run do
  let mut t : Tally := {}
  let mut g := Tests.Rng.ofSeed 0x1EEE754
  for _ in [0:5000] do
    let (x, g') := randFinite g
    g := g'
    t := t.check ((IEEEFloat.toRat? x).map (fun q => sameFloat (IEEEFloat.ofRat Float q) x || (x == 0 && q == 0))
      |>.getD false) fun _ => s!"ofRat ∘ toRat at {F64.showString x}"
    t := t.check (sameFloat (IEEEFloat.nextFloat x) (F64.nextfloat x) &&
      sameFloat (IEEEFloat.prevFloat x) (F64.prevfloat x) && IEEEFloat.signBit x == F64.signbit x) fun _ =>
      s!"nextFloat/prevFloat/signBit at {F64.showString x}"
    let (u, g') := g.next
    g := g'
    let y := Float32.ofBits u.toUInt32
    t := t.check (IEEEFloat.toRat? y |>.map (fun q => sameF32 (IEEEFloat.ofRat Float32 q) y || (y == 0 && q == 0))
      |>.getD (!IEEEFloat.isFinite y)) fun _ => s!"Float32 ofRat ∘ toRat at {F32.showString y}"
    t := t.check (sameF32 (IEEEFloat.nextFloat y) (F32.nextfloat y) &&
      sameF32 (IEEEFloat.prevFloat y) (F32.prevfloat y)) fun _ => s!"Float32 neighbours at {F32.showString y}"
    let (a, g1) := g.int (-1000000) 1000000
    let (b, g2) := g1.nat 1000000
    g := g2
    t := t.check (sameFloat (IEEEFloat.ofFraction Float a (b + 1)) (Float.ofInt a / Float.ofNat (b + 1)))
      fun _ => s!"ofFraction {a}/{b + 1}"
  -- the generic constants agree with the bit-level ones, and with Julia's printed values
  t := t.check ([IEEEFloat.eps Float, IEEEFloat.floatmax Float, IEEEFloat.floatmin Float,
      IEEEFloat.maxintfloat Float, IEEEFloat.inf Float, IEEEFloat.nan Float].zip [F64.eps, F64.floatmax,
      F64.floatmin, F64.maxintfloat, F64.inf, F64.nan] |>.all fun (a, b) => sameFloat a b)
    fun _ => "generic Float64 constants"
  t := t.check ([IEEEFloat.eps Float32, IEEEFloat.floatmax Float32, IEEEFloat.floatmin Float32,
      IEEEFloat.maxintfloat Float32, IEEEFloat.inf Float32, IEEEFloat.nan Float32].zip [F32.eps, F32.floatmax,
      F32.floatmin, F32.maxintfloat, F32.inf, F32.nan] |>.all fun (a, b) => sameF32 a b)
    fun _ => "generic Float32 constants"
  t := t.check (([F32.eps, F32.floatmax, F32.floatmin, F32.maxintfloat, F32.prevfloat F32.inf].map
      F32.showString) == ["1.1920929f-7", "3.4028235f38", "1.1754944f-38", "1.6777216f7", "3.4028235f38"])
    fun _ => "Julia's Float32 constants"
  return t

/-- The committed golden `math.json`, plus the property checks. -/
def golden : IO (Nat × Nat) := do
  let j ← loadGolden "math.json"
  let mut t : Tally := props
  for row in jArr j "cases" do t := checkRow t (jRow row)
  t.report "math golden"

/-- The TSV fuzz file `PREFIX_math.tsv`. -/
def fuzz (path : System.FilePath) : IO (Nat × Nat) := do
  let mut t : Tally := {}
  for row in ← readTsv path do t := checkRow t row
  t.report "math fuzz"

end Tests.JuliaBase.Math
