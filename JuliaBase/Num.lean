import JuliaBase.FloatLit

/-
Julia `Base` numeric semantics for `Float` (Julia `Float64`), `Float32` and `Int`.

Everything here reproduces what Julia 1.13 computes, bit for bit, on the oracle
machine (Apple Silicon, where `Core.Intrinsics.have_fma(Float64)` is `true` and
`muladd` lowers to a fused multiply-add). Lean core already gives us correctly
rounded `+ - * / sqrt fma`, so the ports below only have to replay Julia's
operation order. Julia's own transcendental kernels (`exp`, `log`, `expm1`, `log1p`, `^`)
are in `JuliaBase.Math`.

Citations are to Julia's `share/julia/base/`.
-/

universe u

namespace JuliaBase

/-! ## `Float` (Julia `Float64`) -/

namespace F64

/-- Bit mask of the sign bit of a `Float64`. -/
def signMask : UInt64 := 0x8000000000000000

/-- Bit mask of the 52 explicit significand bits of a `Float64`. -/
def fracMask : UInt64 := 0x000FFFFFFFFFFFFF

/-- Julia `signbit(x::Float64)`: the IEEE sign bit (true for `-0.0` and negative NaNs). -/
@[inline] def signbit (x : Float) : Bool := x.toBits &&& signMask != 0

/-- Julia `copysign(x, y)` (floatfuncs.jl:5): magnitude of `x`, sign bit of `y`. -/
@[inline] def copysign (x y : Float) : Float :=
  Float.ofBits ((x.toBits &&& ~~~signMask) ||| (y.toBits &&& signMask))

/-- Julia `flipsign(x, y)` (number.jl:249): `signbit(y) ? -x : x`. -/
@[inline] def flipsign (x y : Float) : Float :=
  if signbit y then -x else x

/-- Julia `eps(Float64)` = `2^-52`. -/
def eps : Float := Float.ofBits 0x3CB0000000000000

/-- Julia `floatmin(Float64)` = `2^-1022`, the smallest positive normal number. -/
def floatmin : Float := Float.ofBits 0x0010000000000000

/-- Julia `floatmax(Float64)` = `1.7976931348623157e308`. -/
def floatmax : Float := Float.ofBits 0x7FEFFFFFFFFFFFFF

/-- Julia `maxintfloat(Float64)` = `2^53`. -/
def maxintfloat : Float := Float.ofBits 0x4340000000000000

/-- Julia `NaN`. -/
def nan : Float := Float.ofBits 0x7FF8000000000000

/-- Julia `Inf`. -/
def inf : Float := Float.ofBits 0x7FF0000000000000

/-- Julia `iszero(x)`: `x == 0` (true for both signed zeros). -/
@[inline] def iszero (x : Float) : Bool := x == 0

/-- Julia `isnan(x)`: `x != x`, inline (Lean's `Float.isNaN` is an out-of-line runtime call). -/
@[inline] def isnan (x : Float) : Bool := x != x

/-- Julia `isinf(x)`: `|x| == Inf`, inline (Lean's `Float.isInf` is an out-of-line call). -/
@[inline] def isinf (x : Float) : Bool := x.abs == inf

/-- Julia `isfinite(x)`: `|x| < Inf` (false for `NaN`), inline (unlike `Float.isFinite`). -/
@[inline] def isfinite (x : Float) : Bool := x.abs < inf

/-- Julia `nextfloat(x::Float64)` (float.jl): the next representable value toward `+Inf`.
`NaN` and `Inf` map to themselves; `-0.0` and `0.0` both go to `5.0e-324`. -/
def nextfloat (x : Float) : Float :=
  if x.isNaN || x == inf then x
  else
    let b := x.toBits
    if x == 0 then Float.ofBits 1
    else if signbit x then Float.ofBits (b - 1) else Float.ofBits (b + 1)

/-- Julia `prevfloat(x::Float64)`: the next representable value toward `-Inf`. -/
def prevfloat (x : Float) : Float :=
  if x.isNaN || x == -inf then x
  else
    let b := x.toBits
    if x == 0 then Float.ofBits (signMask ||| 1)
    else if signbit x then Float.ofBits (b + 1) else Float.ofBits (b - 1)

/-- `2^52`: every `Float64` of at least this magnitude is an integer. -/
def two52 : Float := Float.ofBits 0x4330000000000000

/-- Julia `round(x)` = `round(x, RoundNearest)` = LLVM `rint` (float.jl:466): round half to
even, keeping the sign of zero (`round(-0.4) == -0.0`). Inline and free of bit casts (it sits
on the argument reduction of `sin`/`cos`). -/
@[inline] def round (x : Float) : Float :=
  let a := x.abs
  if !(a < two52) then x  -- NaN, Inf, or already an integer (|x| ≥ 2^52)
  else
    -- adding and subtracting 2^52 rounds to an integer in the current (nearest-even) mode;
    -- the sign of `x` is `copysign`'s, and `round(±0) = ±0`
    let r := (a + two52) - two52
    if x < f64! 0.0 then -r else if x > f64! 0.0 then r else x

/-- Julia `trunc(x)` (round toward zero). -/
def trunc (x : Float) : Float :=
  if x.isNaN || x.isInf then x
  else copysign (if x < 0 then (-x).floor else x.floor) x

/-- Julia `isinteger(x::Float64)`: finite with no fractional part. -/
@[inline] def isinteger (x : Float) : Bool := x.isFinite && x.floor == x

/-- Exact integer value of a finite float with no fractional part; the fractional part of a
non-integer argument is truncated toward zero. Non-finite inputs give `0`. This is the
exact conversion Julia performs in `trunc(Int, x)` / `Int(x)` when no `InexactError` fires. -/
def toIntTrunc (x : Float) : Int :=
  if !x.isFinite then 0
  else
    let b := x.toBits
    let e := ((b >>> 52) &&& 0x7FF).toNat
    let m : Nat := if e == 0 then (b &&& fracMask).toNat else ((b &&& fracMask) ||| 0x0010000000000000).toNat
    let ee : Int := (if e == 0 then 1 else (e : Int)) - 1075
    let mag : Nat := if ee ≥ 0 then m <<< ee.toNat else m >>> (-ee).toNat
    if signbit x then -(mag : Int) else (mag : Int)

/-- Julia `round(Int, x)`: round half to even, then convert exactly. -/
@[inline] def roundInt (x : Float) : Int := toIntTrunc (round x)

/-- Julia `Float64(i::Integer)`: correctly rounded conversion. -/
@[inline] def ofInt (i : Int) : Float := Float.ofInt i

/-- `(m * 2^d) mod y` computed in 11-bit chunks so nothing leaves `UInt64`
(`r < y < 2^53`, so `r <<< 11 < 2^64`). `fuel ≥ d` guarantees completion. -/
def remShift (y : UInt64) : Nat → UInt64 → Nat → UInt64
  | 0, r, _ => r
  | fuel + 1, r, d =>
    if d == 0 then r
    else if d ≤ 11 then (r <<< d.toUInt64) % y
    else remShift y fuel ((r <<< 11) % y) (d - 11)

/-- Julia `rem_internal(x, y)` (float.jl:530): the exact IEEE remainder `fmod(x, y)` for
finite, positive, nonzero `x` and `y`. The result is exactly representable, so any exact
algorithm agrees bit-for-bit with Julia's; this one stays inside `UInt64`. -/
def remInternal (x y : Float) : Float :=
  let xb := x.toBits
  let yb := y.toBits
  if xb < yb then x
  else if xb == yb then 0
  else
    let ex := (xb >>> 52).toNat
    let ey := (yb >>> 52).toNat
    let mx := if ex == 0 then xb &&& fracMask else (xb &&& fracMask) ||| 0x0010000000000000
    let my := if ey == 0 then yb &&& fracMask else (yb &&& fracMask) ||| 0x0010000000000000
    let ex' := if ex == 0 then 1 else ex
    let ey' := if ey == 0 then 1 else ey
    -- |x| = mx·2^(ex'-1075), |y| = my·2^(ey'-1075), and xb > yb gives ex' ≥ ey'
    let d := ex' - ey'
    let r := remShift my (d + 1) (mx % my) d
    if r == 0 then 0 else r.toFloat.scaleB ((ey' : Int) - 1075)

/-- Julia `rem(x::Float64, y::Float64)` (float.jl:596): truncated remainder, sign of `x`,
exact. `rem(x, 0) = NaN`, `rem(±Inf, y) = NaN`, `rem(x, ±Inf) = x` for finite `x`. -/
def rem (x y : Float) : Float :=
  if x.isFinite && !iszero x && y.isFinite && !iszero y then
    copysign (remInternal x.abs y.abs) x
  else if x.isInf || y.isNaN || iszero y then nan
  else x

/-- Julia `mod(x::Float64, y::Float64)` (float.jl:606): floored remainder with the sign of `y`. -/
def mod (x y : Float) : Float :=
  if y.isInf && x.isFinite then x
  else
    let r := rem x y
    if r == 0 then copysign r y
    else if (r > 0) != (y > 0) then r + y
    else r

/-- Julia `div(x, y)` for floats (div.jl:383 with `RoundToZero`):
`round((x - rem(x, y)) / y)`. -/
@[inline] def div (x y : Float) : Float := round ((x - rem x y) / y)

/-- Julia `fld(x, y)` for floats (div.jl:336, 383, 115): `round((x - mod(x, y)) / y)`. -/
@[inline] def fld (x y : Float) : Float := round ((x - mod x y) / y)

/-- Julia `cld(x, y)` for floats (div.jl:337, 383, 116): `round((x - mod(x, -y)) / y)`. -/
@[inline] def cld (x y : Float) : Float := round ((x - mod x (-y)) / y)

/-- Julia `max(x::Float64, y::Float64)` (math.jl:856, `max_float`): NaN-propagating and
`-0.0 < 0.0`. Lean's `max` is `if x ≤ y then y else x`, which differs on both counts. -/
@[inline] def max (x y : Float) : Float :=
  if x.isNaN then x
  else if y.isNaN then y
  else if x == y then (if signbit x then y else x)
  else if x < y then y else x

/-- Julia `min(x::Float64, y::Float64)` (math.jl:852, `min_float`): NaN-propagating and
`-0.0 < 0.0`. -/
@[inline] def min (x y : Float) : Float :=
  if x.isNaN then x
  else if y.isNaN then y
  else if x == y then (if signbit x then x else y)
  else if x < y then x else y

/-- Julia `minmax(x, y) = (min(x, y), max(x, y))` (math.jl:850). -/
@[inline] def minmax (x y : Float) : Float × Float := (min x y, max x y)

/-- The IEEE bits of a float mapped monotonically onto `Int` (Julia's `fpiseq`/`isless`
integer trick): negative floats map below positive ones, `-0.0 ↦ -1` and `0.0 ↦ 0` are
adjacent, and consecutive floats map to consecutive integers. -/
def orderedBits (x : Float) : Int :=
  let b := x.toBits
  if signbit x then -((b &&& ~~~signMask).toNat : Int) - 1 else (b.toNat : Int)

/-- Julia `isless(a::Float64, b::Float64)` (float.jl): the total order used by `sort`,
with `-0.0 < 0.0` and every NaN after `Inf`. -/
def isless (a b : Float) : Bool :=
  if a.isNaN || b.isNaN then !a.isNaN
  else orderedBits a < orderedBits b

/-- Julia `isequal(a::Float64, b::Float64)`: like `==` but all NaNs are equal and
`-0.0 ≠ 0.0`. This is also the comparator of the oracle's bit-exact suites (bitwise
equality up to the NaN payload). -/
@[inline] def isequal (a b : Float) : Bool :=
  (a.isNaN && b.isNaN) || a.toBits == b.toBits

/-- Distance in units in the last place, `|orderedBits x - orderedBits y|` (not a Julia
function; the comparator of the oracle suites for `libm`-backed results). NaNs are at
distance 0 from each other and `2^64` from everything else. -/
def ulpDist (x y : Float) : Nat :=
  if x.isNaN && y.isNaN then 0
  else if x.isNaN || y.isNaN then 2 ^ 64
  else (orderedBits x - orderedBits y).natAbs

/-- Julia `sign(x::Float64)` (number.jl:206): `-1.0`, `1.0`, or `x` itself for `±0.0` and NaN. -/
@[inline] def sign (x : Float) : Float :=
  if x < 0 then -1 else if x > 0 then 1 else x

/-- Julia `rtoldefault(Float64)` = `sqrt(eps(Float64))` = `2^-26` (floatfuncs.jl:264). -/
def rtoldefault : Float := Float.ofBits 0x3E50000000000000

/-- Julia `isapprox(x::Float64, y::Float64; atol=0, rtol=atol>0 ? 0 : √eps, nans=false)`
(floatfuncs.jl:222):
`x == y || (isfinite(x) && isfinite(y) && |x-y| ≤ max(atol, rtol*max(|x|,|y|))) || (nans && isnan(x) && isnan(y))`.
With the default tolerances, `isapprox(x, 0)` holds only for `x == 0`. -/
def isapprox (x y : Float) (atol : Float := 0) (rtol : Float := if atol > 0 then 0 else rtoldefault)
    (nans : Bool := false) : Bool :=
  x == y ||
    (x.isFinite && y.isFinite && (x - y).abs ≤ max atol (rtol * max x.abs y.abs)) ||
    (nans && x.isNaN && y.isNaN)

/-- `sqrt(eps(Float64)/2)`, the "widely varying operands" threshold in `_hypot`. -/
def hypotWide : Float := (eps / 2).sqrt

/-- `eps(Float64)*sqrt(floatmin(Float64))`, the rescaling constant in `_hypot` (= `2^-563`). -/
def hypotScale : Float := eps * floatmin.sqrt

/-- `sqrt(floatmax(Float64)/2)`, the overflow threshold in `_hypot`. -/
def hypotBig : Float := (floatmax / 2).sqrt

/-- `sqrt(floatmin(Float64))` = `2^-511`, the underflow threshold in `_hypot`. -/
def hypotSmall : Float := floatmin.sqrt

/-- The rescaled core of `_hypot` (math.jl:785-800): `sqrt(muladd(ax, ax, ay*ay))` plus one
FMA-based correction step, times `scale`. -/
@[inline] def hypotCore (ax ay scale : Float) : Float :=
  let h := (Float.fma ax ax (ay * ay)).sqrt
  let hsquared := h * h
  let axsquared := ax * ax
  let h := h - (Float.fma (-ay) ay (hsquared - axsquared) + Float.fma h h (-hsquared)
    - Float.fma ax ax (-axsquared)) / (2 * h)
  h * scale

/-- `_hypot` after ordering, `ax ≥ ay` (math.jl:766-785). -/
@[inline] def hypotOrdered (ax ay : Float) : Float :=
  if ay ≤ ax * hypotWide then ax
  else if ax > hypotBig then hypotCore (ax * hypotScale) (ay * hypotScale) (1 / hypotScale)
  else if ay < hypotSmall then hypotCore (ax / hypotScale) (ay / hypotScale) hypotScale
  else hypotCore ax ay 1

/-- Julia `hypot(x::Float64, y::Float64)` (math.jl:748-801), the FMA branch taken on
machines with native FMA (the oracle's). `muladd` is fused there too. Correctly rounded;
`Inf` wins over NaN. -/
def hypot (x y : Float) : Float :=
  let ax := x.abs
  let ay := y.abs
  if ax.isInf || ay.isInf then inf
  else if ay > ax then hypotOrdered ay ax
  else hypotOrdered ax ay

/-- Julia `highword(x::Float64)`: the upper 32 bits of the representation. -/
@[inline] def highword (x : Float) : UInt32 := (x.toBits >>> 32).toUInt32

/-- Julia `fromhighword(Float64, u)`: a float whose upper 32 bits are `u` (lower bits zero). -/
@[inline] def fromhighword (u : UInt32) : Float := Float.ofBits (u.toUInt64 <<< 32)

/-- Julia `_approx_cbrt(x::Float64)` (special/cbrt.jl): a 5-bit first guess from integer
division of the exponent bits. Assumes `x` finite and nonzero. -/
def approxCbrt (x : Float) : Float :=
  let adj0 : Float := 2046 / 3 - 0.03306235651
  let k : Float := 1048576  -- exp2(20), k = significand_bits - 32
  let u := highword x &&& 0x7fffffff
  if u ≥ highword floatmin then
    let v := u / 3 + (adj0 * k).floor.toUInt32
    copysign (fromhighword v) x
  else
    let x' := x * maxintfloat
    let adj := adj0 - 53 / 3
    let u := highword x' &&& 0x7fffffff
    let v := u / 3 + (adj * k).floor.toUInt32
    copysign (fromhighword v) x'

/-- Julia `_improve_cbrt(x::Float64, t)` (special/cbrt.jl): one polynomial step, rounding
`t` to 23 bits, then one Newton step. `@horner`/`muladd` are fused (FMA). -/
def improveCbrt (x t : Float) : Float :=
  let r := (t * t) * (t / x)
  let p1 := Float.fma r (Float.fma r 1.621429720105354466140 (-1.88497979543377169875)) 1.87595182427177009643
  let p2 := Float.fma r 0.145996192886612446982 (-0.758397934778766047437)
  let t := t * (p1 + ((r * r) * r) * p2)
  let u := t.toBits
  let t := Float.ofBits ((u + 0x80000000) &&& 0xffffffffc0000000)
  let s := t * t
  let r := x / s
  let w := t + t
  let r := (r - t) / (w + r)
  Float.fma t r t

/-- Julia `cbrt(x::Float64)` (special/cbrt.jl): the real cube root, Julia's own algorithm
(not the platform libm, which Lean's `Float.cbrt` calls). -/
def cbrt (x : Float) : Float :=
  if !x.isFinite || iszero x then x
  else improveCbrt x (approxCbrt x)

/-- Julia `Float64(x::Rational)` (rational.jl:162): `Float64(num) / Float64(den)`, one
correctly rounded division of the converted parts. Correctly rounded whenever numerator
and denominator are below `2^53`; larger ones are rounded twice, as in Julia. -/
@[inline] def ofRat (r : Rat) : Float := Float.ofInt r.num / Float.ofNat r.den

/-- Julia `exponent(x::Float64)` (math.jl:951): the unbiased binary exponent `⌊log₂|x|⌋`
of a finite nonzero `x`, subnormals included. (Julia throws a `DomainError` for `0`, NaN
and `Inf`; the value here is then unspecified.) -/
@[inline] def exponent (x : Float) : Int := x.frExp.2 - 1

/-- Julia `ldexp(x::Float64, k)` (math.jl:873) = `x · 2ᵏ`, correctly rounded
(`scalbn`). -/
@[inline] def ldexp (x : Float) (k : Int) : Float := x.scaleB k

/-! ### Constants

Julia's own `exp`, `log`, `expm1`, `log1p` and `^` kernels are in `JuliaBase.Math`. -/

/-- Julia `Float64(π)`. -/
def pi : Float := Float.ofBits 0x400921FB54442D18

/-- Julia `log(2.0)`. -/
def ln2 : Float := Float.ofBits 0x3FE62E42FEFA39EF

/-- Julia `log(10.0)`. -/
def ln10 : Float := Float.ofBits 0x40026BB1BBB55516

/-- Julia `log2(ℯ)`. -/
def log2e : Float := Float.ofBits 0x3FF71547652B82FE

/-- Julia `log10(ℯ)`. -/
def log10e : Float := Float.ofBits 0x3FDBCB7B1526E50E

end F64

/-- Julia `max` on `Float64`; alias of `F64.max` (port-notes §8.4 name). -/
abbrev juliaMax := F64.max

/-- Julia `min` on `Float64`; alias of `F64.min` (port-notes §8.4 name). -/
abbrev juliaMin := F64.min

/-! ## `Float32` -/

namespace F32

/-- Julia `signbit(x::Float32)`. -/
@[inline] def signbit (x : Float32) : Bool := x.toBits &&& 0x80000000 != 0

/-- Julia `copysign(x::Float32, y::Float32)`. -/
@[inline] def copysign (x y : Float32) : Float32 :=
  Float32.ofBits ((x.toBits &&& 0x7FFFFFFF) ||| (y.toBits &&& 0x80000000))

/-- Julia `eps(Float32)` = `2^-23`. -/
def eps : Float32 := Float32.ofBits 0x34000000

/-- Julia `floatmin(Float32)` = `2^-126`, the smallest positive normal number. -/
def floatmin : Float32 := Float32.ofBits 0x00800000

/-- Julia `floatmax(Float32)` = `3.4028235f38`. -/
def floatmax : Float32 := Float32.ofBits 0x7F7FFFFF

/-- Julia `maxintfloat(Float32)` = `2^24`. -/
def maxintfloat : Float32 := Float32.ofBits 0x4B800000

/-- Julia `NaN32`. -/
def nan : Float32 := Float32.ofBits 0x7FC00000

/-- Julia `Inf32`. -/
def inf : Float32 := Float32.ofBits 0x7F800000

/-- Julia `isnan(x::Float32)`: `x != x`, inline. -/
@[inline] def isnan (x : Float32) : Bool := x != x

/-- Julia `isinf(x::Float32)`: `|x| == Inf32`, inline. -/
@[inline] def isinf (x : Float32) : Bool := x.abs == inf

/-- Julia `isfinite(x::Float32)`: `|x| < Inf32`, inline. -/
@[inline] def isfinite (x : Float32) : Bool := x.abs < inf

/-- Julia `nextfloat(x::Float32)`: the next representable value toward `+Inf` (`NaN` and
`Inf32` map to themselves, both zeros go to `1.0f-45`). -/
def nextfloat (x : Float32) : Float32 :=
  if x.isNaN || x == inf then x
  else
    let b := x.toBits
    if x == 0 then Float32.ofBits 1
    else if signbit x then Float32.ofBits (b - 1) else Float32.ofBits (b + 1)

/-- Julia `prevfloat(x::Float32)`: the next representable value toward `-Inf`. -/
def prevfloat (x : Float32) : Float32 :=
  if x.isNaN || x == -inf then x
  else
    let b := x.toBits
    if x == 0 then Float32.ofBits 0x80000001
    else if signbit x then Float32.ofBits (b + 1) else Float32.ofBits (b - 1)

/-- Julia `max(x::Float32, y::Float32)`: NaN-propagating, `-0f0 < 0f0`. -/
@[inline] def max (x y : Float32) : Float32 :=
  if x.isNaN then x
  else if y.isNaN then y
  else if x == y then (if signbit x then y else x)
  else if x < y then y else x

/-- Julia `min(x::Float32, y::Float32)`: NaN-propagating, `-0f0 < 0f0`. -/
@[inline] def min (x y : Float32) : Float32 :=
  if x.isNaN then x
  else if y.isNaN then y
  else if x == y then (if signbit x then x else y)
  else if x < y then x else y

/-- Julia `sign(x::Float32)`: `-1f0`, `1f0`, or `x` itself for `±0f0` and NaN. -/
@[inline] def sign (x : Float32) : Float32 :=
  if x < 0 then -1 else if x > 0 then 1 else x

/-- Julia `rtoldefault(Float32)` = `sqrt(eps(Float32))` = `2^-11.5`, rounded. -/
def rtoldefault : Float32 := (Float32.ofBits 0x34000000).sqrt

/-- Julia `isapprox(x::Float32, y::Float32; atol, rtol, nans)` (floatfuncs.jl:222). -/
def isapprox (x y : Float32) (atol : Float32 := 0)
    (rtol : Float32 := if atol > 0 then 0 else rtoldefault) (nans : Bool := false) : Bool :=
  x == y ||
    (x.isFinite && y.isFinite && (x - y).abs ≤ max atol (rtol * max x.abs y.abs)) ||
    (nans && x.isNaN && y.isNaN)

/-- Julia `hypot(x::Float32, y::Float32)` (math.jl:803): widen to `Float64`,
`sqrt(muladd(x, x, y*y))` (fused), round back. -/
def hypot (x y : Float32) : Float32 :=
  if x.isInf || y.isInf then Float32.ofBits 0x7F800000
  else
    let x' := x.toFloat
    let y' := y.toFloat
    (Float.fma x' x' (y' * y')).sqrt.toFloat32

/-- Julia `_approx_cbrt(x::Float32)` (special/cbrt.jl:61): the bit-level first guess
`u ÷ 3 + ⌊adj·2^23⌋` with `adj = 127·2/3 - 0.03306235651` (`709958130`), rescaling subnormals
by `maxintfloat(Float32) = 2^24` (`adj - 8`: `642849266`). Assumes `x` finite and nonzero. -/
def approxCbrt (x : Float32) : Float32 :=
  let u := x.toBits &&& 0x7FFFFFFF
  if u ≥ 0x00800000 then copysign (Float32.ofBits (u / 3 + 709958130)) x
  else
    let x' := x * Float32.ofBits 0x4B800000
    let u := x'.toBits &&& 0x7FFFFFFF
    copysign (Float32.ofBits (u / 3 + 642849266)) x'

/-- Julia `_improve_cbrt(x::Float32, t)` (special/cbrt.jl:79): two Newton steps
`t ← t·(t³ + 2x)/(2t³ + x)` in `Float64`, rounded once. -/
def improveCbrt (x t : Float32) : Float32 :=
  let xx := x.toFloat
  let tt := t.toFloat
  let tt3 := tt * tt * tt
  let tt := tt * ((2 * xx + tt3) / (xx + 2 * tt3))
  let tt3 := tt * tt * tt
  let tt := tt * ((2 * xx + tt3) / (xx + 2 * tt3))
  tt.toFloat32

/-- Julia `cbrt(x::Float32)` (special/cbrt.jl:142), Julia's own algorithm (not the platform
libm that `Float32.cbrt` calls). -/
def cbrt (x : Float32) : Float32 :=
  if !x.isFinite || x == 0 then x else improveCbrt x (approxCbrt x)

end F32

/-! ## `Int` (Julia `Int64`, without overflow)

Lean's `Int` is arbitrary precision, so the Julia wrap-around at `typemin`/`typemax`
does not happen; the division functions are otherwise exact ports. Division by zero,
a `DivideError` in Julia, returns `0` here. -/

namespace JInt

/-- Julia `div(x, y)` on integers: quotient truncated toward zero. -/
@[inline] def div (x y : Int) : Int := x.tdiv y

/-- Julia `rem(x, y)` on integers: remainder with the sign of `x`. -/
@[inline] def rem (x y : Int) : Int := x.tmod y

/-- Julia `fld(x, y)` on integers: quotient rounded toward `-∞`. -/
@[inline] def fld (x y : Int) : Int := x.fdiv y

/-- Julia `mod(x, y)` on integers (int.jl:325): `x - fld(x, y) * y`, sign of `y`. -/
@[inline] def mod (x y : Int) : Int := x.fmod y

/-- Julia `cld(x, y)` on integers (div.jl:377): quotient rounded toward `+∞`. -/
def cld (x y : Int) : Int :=
  let d := x.tdiv y
  d + (if ((x > 0) == (y > 0)) && d * y != x then 1 else 0)

/-- Julia `sign(x::Integer)`. -/
@[inline] def sign (x : Int) : Int := if x < 0 then -1 else if x > 0 then 1 else 0

/-- Julia `signbit(x::Integer) = x < 0`. -/
@[inline] def signbit (x : Int) : Bool := x < 0

/-- Julia `copysign(x::Signed, y::Signed)`: `|x|` with the sign of `y`. -/
@[inline] def copysign (x y : Int) : Int := if y < 0 then -(x.natAbs : Int) else x.natAbs

/-- Julia `flipsign(x, y)`: `y < 0 ? -x : x`. -/
@[inline] def flipsign (x y : Int) : Int := if y < 0 then -x else x

/-- Julia `isodd(x::Integer)` (int.jl:155): `rem(x, 2) != 0`. -/
@[inline] def isodd (x : Int) : Bool := x % 2 != 0

/-- Julia `isapprox(x::Integer, y::Integer; atol=0, rtol=0)` (floatfuncs.jl:231) with the
default `norm = abs`: exact equality when `atol < 1` and `rtol == 0`, otherwise
`|x - y| ≤ max(atol, rtol*max(|x|, |y|))` in `Float64`. -/
def isapprox (x y : Int) (atol : Float := 0) (rtol : Float := 0) : Bool :=
  if atol < 1 && rtol == 0 then x == y
  else
    Float.ofInt (x - y).natAbs ≤
      F64.max atol (rtol * F64.max (Float.ofInt x.natAbs) (Float.ofInt y.natAbs))

end JInt

/-! ## `power_by_squaring` -/

/-- Julia `Base.power_by_squaring(x, p)` (intfuncs.jl:394) for `p ≥ 0`: the exact
multiplication order Julia uses for `x^p` with an integer exponent, generic in the
multiplication `mul` (`p = 2` is `x*x`; otherwise square away the trailing zero bits of
`p`, then multiply in the remaining set bits from low to high). -/
def powBySquaring {β : Type u} (mul : β → β → β) (one x : β) (p : Nat) : β :=
  if p == 0 then one
  else if p == 1 then x
  else if p == 2 then mul x x
  else
    let t := trailingZeros p + 1
    let p := p >>> t
    let x := square x (t - 1)
    loop x x p (p + 1)
where
  /-- Number of trailing zero bits of a positive `n` (`0` for `n = 0`). -/
  trailingZeros (n : Nat) : Nat := tz n 64
  /-- Fuelled trailing-zero count. -/
  tz : Nat → Nat → Nat
    | _, 0 => 0
    | m, fuel + 1 => if m % 2 == 1 || m == 0 then 0 else tz (m / 2) fuel + 1
  /-- `x^(2^k)` by repeated squaring. -/
  square (x : β) : Nat → β
    | 0 => x
    | k + 1 => square (mul x x) k
  /-- The main loop of `power_by_squaring` (the fuel bounds the bit count). -/
  loop (x y : β) (p : Nat) : Nat → β
    | 0 => y
    | fuel + 1 =>
      if p == 0 then y
      else
        let t := trailingZeros p + 1
        let p := p >>> t
        let x := square x t
        loop x (mul y x) p fuel

end JuliaBase
