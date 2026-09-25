import FieldConstants.Julia.Math

/-!
# `JNum`: the payload of a Julia `FieldConstants.Constant{N}`

In Julia, `Constant{N}` stores its value `N` *in the type* (an `Int64` or a
`Float64`) so the compiler folds whole unit-system computations at compile
time (`FieldConstants.jl/src/FieldConstants.jl:21-89`). In Lean a value-level
number with the same promotion rules is enough: named constants are closed
terms, which the compiler hoists and evaluates once, and nothing about the
payload is needed at the type level.

`JNum` reproduces Julia's numeric tower on these payloads exactly:

* `Int64 ∘ Int64` stays `Int64` for `+ - *` and non-negative literal powers, and
  **wraps on overflow** (`Constant(2)^70 == 0`);
* `/`, `inv`, `sqrt`, `cbrt`, `log`, `exp` always produce `Float64`;
* mixed `Int64`/`Float64` arithmetic promotes to `Float64`;
* literal powers `x^n` lower to `Base.literal_pow`: `n < 0` means `inv(x)^(-n)`
  (`base/intfuncs.jl:477-488`), with Julia's compensated `pow_body`.

The Int/Float distinction is observable: it decides whether a result prints as
`1` or `1.0`, and `UnitSystems.unit` snaps near-one factors to the *integer* 1.
-/

namespace FieldConstants

open Julia

/-- A Julia real scalar: `Int64` or `Float64` (the payload of `Constant{N}`). -/
inductive JNum where
  /-- a Julia `Int64` -/
  | int (n : Int64)
  /-- a Julia `Float64` -/
  | float (x : Float)
  deriving Inhabited

namespace JNum

/-- The value as a `Float64` (Julia `float(x)`). -/
@[inline] def toFloat : JNum → Float
  | int n => Float.ofInt n.toInt
  | float x => x

/-- Is this an `Int64` payload? -/
@[inline] def isInt : JNum → Bool
  | int _ => true
  | float _ => false

/-- Julia `==`: numeric equality across `Int64`/`Float64`. -/
def beq : JNum → JNum → Bool
  | int a, int b => a == b
  | a, b => a.toFloat == b.toFloat

instance : BEq JNum := ⟨beq⟩

/-- Julia `===` on the payload: same kind and bit-identical value. This is the
identity that dispatch on `UnitSystem{…}` type parameters uses. -/
def ident : JNum → JNum → Bool
  | int a, int b => a == b
  | float a, float b => a.toBits == b.toBits
  | _, _ => false

instance (n : Nat) : OfNat JNum n := ⟨int (Int64.ofNat n)⟩

/-- Coerce a float literal. -/
instance : OfScientific JNum := ⟨fun m s e => float (OfScientific.ofScientific m s e)⟩

@[inline] private def lift2 (fi : Int64 → Int64 → Int64) (ff : Float → Float → Float) :
    JNum → JNum → JNum
  | int a, int b => int (fi a b)
  | a, b => float (ff a.toFloat b.toFloat)

/-- Julia `+` with promotion. -/
def add : JNum → JNum → JNum := lift2 (· + ·) (· + ·)
/-- Julia `-` with promotion. -/
def sub : JNum → JNum → JNum := lift2 (· - ·) (· - ·)
/-- Julia `*` with promotion (`Int64` wraps). -/
def mul : JNum → JNum → JNum := lift2 (· * ·) (· * ·)
/-- Julia `/`: always `Float64`. -/
def div (a b : JNum) : JNum := float (a.toFloat / b.toFloat)
/-- Julia `inv`: always `Float64`. -/
def inv (a : JNum) : JNum := float (1.0 / a.toFloat)
/-- Julia unary `-`. -/
def neg : JNum → JNum
  | int a => int (-a)
  | float x => float (-x)

instance : Add JNum := ⟨add⟩
instance : Sub JNum := ⟨sub⟩
instance : Mul JNum := ⟨mul⟩
instance : Div JNum := ⟨div⟩
instance : Neg JNum := ⟨neg⟩
instance : Inv JNum := ⟨inv⟩

/-- Julia `power_by_squaring` for `Int64` (wrapping), `p ≥ 0`. -/
def ipow (x : Int64) (p : Nat) : Int64 := go x 1 p 64
where
  go (b acc : Int64) (p : Nat) : Nat → Int64
    | 0 => acc
    | f + 1 => if p == 0 then acc else
        go (b * b) (if p % 2 == 1 then acc * b else acc) (p / 2) f

/-- Julia `^(x, n::Integer)` on a payload with non-negative `n`
(`Int64` stays `Int64`, `Float64` uses `pow_body`). A negative `n` on an
`Int64` (a `DomainError` in Julia) is computed in `Float64`. -/
def npow : JNum → Int → JNum
  | int a, n => if n ≥ 0 then int (ipow a n.toNat) else float (powInt (Float.ofInt a.toInt) n)
  | float x, n => float (powInt x n)

/-- `Constant{N}^n` for a *literal* integer `n`: Julia lowers `x^n` to
`literal_pow`, which for a `Constant` computes `inv(x)^(-n)` when `n < 0`. -/
def lpow (x : JNum) (n : Int) : JNum :=
  if n < 0 then npow (inv x) (-n) else npow x n

instance : HPow JNum Int JNum := ⟨lpow⟩
instance : HPow JNum Nat JNum := ⟨fun x n => lpow x n⟩

/-- Julia `x^y` with a `Float64` exponent. -/
def fpow (x : JNum) (y : Float) : JNum := float (pow x.toFloat y)

/-- Julia `sqrt`. -/
def sqrt (x : JNum) : JNum := float x.toFloat.sqrt
/-- Julia `cbrt` (Julia's own, via `JuliaBase.F64.cbrt`). -/
def cbrt (x : JNum) : JNum := float (JuliaBase.F64.cbrt x.toFloat)
/-- Julia `log`. -/
def log (x : JNum) : JNum := float (Julia.log x.toFloat)
/-- Julia `log10`. -/
def log10 (x : JNum) : JNum := float (Julia.log10 x.toFloat)
/-- Julia `log2`. -/
def log2 (x : JNum) : JNum := float (Julia.log2 x.toFloat)
/-- Julia `exp`. -/
def exp (x : JNum) : JNum := float (Julia.exp x.toFloat)
/-- Julia `exp10`. -/
def exp10 (x : JNum) : JNum := float (Julia.exp10 x.toFloat)
/-- Julia `abs`. -/
def abs : JNum → JNum
  | int a => int (if a < 0 then -a else a)
  | float x => float x.abs

/-- Julia `isone`. -/
def isOne : JNum → Bool
  | int a => a == 1
  | float x => x == 1.0

/-- Julia `iszero`. -/
def isZero : JNum → Bool
  | int a => a == 0
  | float x => x == 0.0

/-- Julia `isapprox(y, x; rtol = eps()^0.9)` as used by `UnitSystems.unit`
(`UnitSystems.jl:276`): `x == y`, or both finite with
`|x - y| ≤ rtol·max(|x|, |y|)`. -/
def isApproxUnit (y x : JNum) : Bool :=
  let a := y.toFloat
  let b := x.toFloat
  a == b || (a.isFinite && b.isFinite && (a - b).abs ≤ 8.161992717227193e-15 * max a.abs b.abs)

/-- Julia `UnitSystems.unit(x, y=1) = isapprox(y, x, rtol=eps()^0.9) ? y : x`:
snap a conversion factor that is within `8.2e-15` of `y` to exactly `y`. -/
def snap (x : JNum) (y : JNum := 1) : JNum := if isApproxUnit y x then y else x

/-- Julia `<` across kinds. -/
def lt : JNum → JNum → Bool
  | int a, int b => a < b
  | a, b => a.toFloat < b.toFloat

/-- Julia `show`/`print`: `Int64` in decimal, `Float64` in shortest repr. -/
protected def toString : JNum → String
  | int a => toString a.toInt
  | float x => JuliaBase.F64.showString x

instance : ToString JNum := ⟨JNum.toString⟩
instance : Repr JNum := ⟨fun x _ => JNum.toString x⟩

/-- Julia kind name of the payload (`"Int64"` or `"Float64"`). -/
def kind : JNum → String
  | int _ => "Int64"
  | float _ => "Float64"

end JNum

/-- `FieldConstants.Constant{N}`: in Lean a constant is just its payload. -/
abbrev Constant := JNum

/-- Julia `FieldConstants.logdb(x) = 10log10(x)` (decibels). -/
def logdb (x : JNum) : JNum := JNum.mul 10 (JNum.log10 x)

/-- Julia `FieldConstants.expdb(x) = exp10(0.1)^x`. For an `Int64` exponent this
is `^(Float64, Integer)`; note `expdb(20) = 100.00000000000011`. -/
def expdb : JNum → JNum
  | .int n => .float (Julia.powInt 1.2589254117941673 n.toInt)
  | .float x => .float (Julia.pow 1.2589254117941673 x)

/-- Julia `FieldConstants.dB = logdb`. -/
abbrev dB := logdb

end FieldConstants
