/-
Julia `Base` float semantics that `StaticVectors` needs locally.

`JuliaBase` owns the canonical versions of these (it is written in
parallel); this module keeps `StaticVectors` self-contained with the few
helpers its reductions and norms depend on. Every function states the Julia
definition it reproduces, and all of them are bit-exact with Julia 1.13 on
Apple Silicon (where `muladd` contracts to a hardware FMA), except where a
docstring says otherwise.
-/

namespace StaticVectors.Julia

/-! ## Constants -/

/-- `eps(Float64) = 2^-52`. -/
def epsF : Float := 2.220446049250313e-16
/-- `floatmin(Float64) = 2^-1022`. -/
def floatminF : Float := 2.2250738585072014e-308
/-- `floatmax(Float64)`. -/
def floatmaxF : Float := 1.7976931348623157e308
/-- `Base.rtoldefault(Float64) = sqrt(eps(Float64))`. -/
def rtolF : Float := 1.4901161193847656e-8
/-- `Base.rtoldefault(Float32) = sqrt(eps(Float32))`. -/
def rtolF32 : Float32 := 0.00034526698

/-! ## Sign bits and IEEE helpers -/

/-- Julia `signbit(x)`: the IEEE sign bit (true for `-0.0` and negative NaNs). -/
@[inline] def signbit (x : Float) : Bool := x.toBits >>> 63 == 1

/-- Julia `signbit` for `Float32`. -/
@[inline] def signbit32 (x : Float32) : Bool := x.toBits >>> 31 == 1

/-- Julia `copysign(x, y)`: `|x|` with the sign of `y`. -/
@[inline] def copysign (x y : Float) : Float :=
  Float.ofBits ((x.toBits &&& 0x7FFFFFFFFFFFFFFF) ||| (y.toBits &&& 0x8000000000000000))

/-- Julia `flipsign(x, y)`: `x` negated when `signbit(y)`. -/
@[inline] def flipsign (x y : Float) : Float :=
  Float.ofBits (x.toBits ^^^ (y.toBits &&& 0x8000000000000000))

/-- Julia `isfinite`. -/
@[inline] def isfinite (x : Float) : Bool := x.isFinite

/-! ## `max` / `min` (Julia `Base.max(::Float64, ::Float64)`, the LLVM
`maximum`/`minimum` intrinsics: NaN-propagating, `-0.0 < 0.0`) -/

/-- Julia `max` on `Float64` (`base/math.jl:856`): propagates NaN, and orders
`-0.0` below `0.0`. Lean's `max` on `Float` does neither. -/
@[inline] def max (a b : Float) : Float :=
  if a.isNaN then a
  else if b.isNaN then b
  else if a < b then b
  else if b < a then a
  else if signbit a then b else a

/-- Julia `min` on `Float64` (`base/math.jl:852`): propagates NaN, and orders
`-0.0` below `0.0`. -/
@[inline] def min (a b : Float) : Float :=
  if a.isNaN then a
  else if b.isNaN then b
  else if a < b then a
  else if b < a then b
  else if signbit a then a else b

/-- Julia `max` on `Float32`. -/
@[inline] def max32 (a b : Float32) : Float32 :=
  if a.isNaN then a
  else if b.isNaN then b
  else if a < b then b
  else if b < a then a
  else if signbit32 a then b else a

/-- Julia `min` on `Float32`. -/
@[inline] def min32 (a b : Float32) : Float32 :=
  if a.isNaN then a
  else if b.isNaN then b
  else if a < b then a
  else if b < a then b
  else if signbit32 a then a else b

/-! ## `isapprox` (Julia `base/floatfuncs.jl:222`) -/

/-- Julia `isapprox(x::Float64, y::Float64; atol, rtol, nans)`:
`x == y || (isfinite(x) && isfinite(y) && |x-y| ≤ max(atol, rtol·max(|x|,|y|))) || (nans && isnan x && isnan y)`.
The default `rtol` is `rtoldefault(Float64) = √eps` when `atol == 0`, else `0`
(Julia `rtoldefault(x, y, atol)`). -/
@[inline] def isapprox (x y : Float) (atol : Float := 0) (rtol : Float := if atol > 0 then 0 else rtolF)
    (nans : Bool := false) : Bool :=
  x == y ||
    (x.isFinite && y.isFinite && (x - y).abs ≤ max atol (rtol * max x.abs y.abs)) ||
    (nans && x.isNaN && y.isNaN)

/-! ## `hypot` (Julia `base/math.jl:748`) -/

/-- Julia `hypot(x::Float64, y::Float64)` (`Base.Math._hypot`), the branch
taken on hardware with FMA (Apple Silicon, x86-64 with FMA3): scale, take
`sqrt(muladd(ax,ax,ay*ay))` (contracted to an FMA), then apply one exact
correction step. The result is correctly rounded. -/
def hypot (x y : Float) : Float := Id.run do
  let mut ax := x.abs
  let mut ay := y.abs
  if ax.isInf || ay.isInf then return Float.inf
  if ay > ax then
    let t := ax
    ax := ay
    ay := t
  let axu := ax
  if ay ≤ ax * Float.sqrt (epsF / 2) then return axu
  let mut scale := epsF * Float.sqrt floatminF
  if ax > Float.sqrt (floatmaxF / 2) then
    ax := ax * scale
    ay := ay * scale
    scale := 1 / scale
  else if ay < Float.sqrt floatminF then
    ax := ax / scale
    ay := ay / scale
  else
    scale := 1
  let mut h := Float.sqrt (Float.fma ax ax (ay * ay))
  let hsquared := h * h
  let axsquared := ax * ax
  h := h - (Float.fma (-ay) ay (hsquared - axsquared) + Float.fma h h (-hsquared)
      - Float.fma ax ax (-axsquared)) / (2 * h)
  return h * scale

/-! ## `Rational` → `Float64` -/

/-- `Float64(r::Rational)`. Correctly rounded whenever numerator and
denominator are below `2^53` (one IEEE division of exact operands); larger
values are rounded twice. -/
@[inline] def ratToFloat (r : Rat) : Float := Float.ofInt r.num / Float.ofNat r.den

/-! ## Units in the last place (for tests) -/

/-- Map a float to a monotone integer line (Julia's ordered-integer trick):
negative floats map below positive ones, `-0.0` and `0.0` are adjacent. -/
def orderedBits (x : Float) : Int :=
  let b := x.toBits
  if b >>> 63 == 1 then -((b &&& 0x7FFFFFFFFFFFFFFF).toNat : Int) - 1 else (b.toNat : Int)

/-- Distance in units of the last place between two floats. NaNs are at
distance 0 from each other and far from everything else. -/
def ulpDist (x y : Float) : Nat :=
  if x.isNaN && y.isNaN then 0
  else if x.isNaN || y.isNaN then 1 <<< 64
  else ((orderedBits x - orderedBits y).natAbs)

/-- Bitwise equality treating all NaNs as equal and distinguishing `±0`
(the comparator of the oracle's exact suites). -/
def sameBits (x y : Float) : Bool := (x.isNaN && y.isNaN) || x.toBits == y.toBits

end StaticVectors.Julia
