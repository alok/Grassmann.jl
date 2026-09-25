import JuliaBase.Math

/-!
# Julia's own hyperbolic functions, bit for bit

Julia's `sinh`, `cosh`, `tanh`, `asinh`, `acosh` and `atanh` (`base/special/hyperbolic.jl`) are
FDLIBM-style ports built on its own `exp`, `expm1`, `log` and `log1p` (`JuliaBase.Math`) plus
minimax polynomials; this module replays them operation by operation for `Float64` (`F64.sinh`,
…) and `Float32` (`F32.sinh`, …). As everywhere in `JuliaBase`, `muladd`/`evalpoly` are fused
multiply-adds (the oracle machine is Apple aarch64) and `two_mul`/`exthorner` are Julia's
error-free transformations. Arguments outside a function's domain (Julia throws a
`DomainError`: `acosh(0.5)`, `atanh(2.0)`) return `NaN`.
-/

namespace JuliaBase

namespace Math

/-- Julia `exthorner(x, (p₁, p₂, p₃))` (math.jl:215-229): Horner's scheme with a compensated low
part, `(hi, lo)`. -/
@[inline] def exthorner3 (x p1 p2 p3 : Float) : Float × Float :=
  let step (c hi lo : Float) : Float × Float :=
    let (prod, err) := twoMul hi x
    let hi' := c + prod
    (hi', Float.fma lo x ((prod - (hi' - c)) + err))
  let (hi, lo) := step p2 p3 f64! 0.0
  step p1 hi lo

/-- Julia `sinh_kernel(x::Float64)` (hyperbolic.jl:34-42): `sinh x` for `|x| ≤ 2.1` in
double-double arithmetic. -/
@[inline] def sinhKernel (x : Float) : Float :=
  let (x2, x2lo) := twoMul x x
  let hiOrder := Float.fma x2 (Float.fma x2 (Float.fma x2 (Float.fma x2 (Float.fma x2 (Float.fma x2
    f64! 2.9696954760355812e-15 f64! 7.634842144412119e-13) f64! 1.6059550718903307e-10)
    f64! 2.5052096530035283e-8) f64! 2.7557319381151335e-6) f64! 1.9841269840165435e-4)
    f64! 8.333333333336817e-3
  let (hi, lo) := exthorner3 x2 (f64! 1.0) (f64! 0.16666666666666635) hiOrder
  Float.fma x hi (Float.fma x lo (x * x2lo * f64! 0.16666666666666635))

/-- Julia `sinh_kernel(x::Float32)` (hyperbolic.jl:44-50), in `Float64`. -/
@[inline] def sinhKernel32 (x : Float32) : Float32 :=
  let x := x.toFloat
  let res := Float.fma (x * x) (Float.fma (x * x) (Float.fma (x * x) (Float.fma (x * x) (Float.fma (x * x)
    (Float.fma (x * x) f64! 1.6260094552031644e-10 f64! 2.5143389765825282e-8) f64! 2.7555538207080807e-6)
    f64! 0.00019841001151414065) f64! 0.008333336726447933) f64! 0.1666666779967941) f64! 1.0
  (res * x).toFloat32

/-- Julia `cosh_kernel(x2::Float64)` (hyperbolic.jl:92-97). -/
@[inline] def coshKernel (x2 : Float) : Float :=
  Float.fma x2 (Float.fma x2 (Float.fma x2 (Float.fma x2 (Float.fma x2 (Float.fma x2 (Float.fma x2
    f64! 1.1663435515945578e-11 f64! 2.0873617441235094e-9) f64! 2.7557345825742837e-7)
    f64! 2.4801587176784207e-5) f64! 1.3888888889206764e-3) f64! 0.04166666666666269)
    f64! 0.5000000000000002) f64! 1.0

/-- Julia `cosh_kernel(x2::Float32)` (hyperbolic.jl:88-90). -/
@[inline] def coshKernel32 (x2 : Float32) : Float32 :=
  Float32.fma x2 (Float32.fma x2 (Float32.fma x2 (Float32.fma x2 f32! 2.549933e-5 f32! 0.0013882756)
    f32! 0.041666888) f32! 0.49999997) f32! 1.0

/-- Julia `tanh_kernel(x::Float64)` (hyperbolic.jl:131-137), a polynomial in `x = t²`. -/
@[inline] def tanhKernel (x : Float) : Float :=
  Float.fma x (Float.fma x (Float.fma x (Float.fma x (Float.fma x (Float.fma x (Float.fma x (Float.fma x
    (Float.fma x (Float.fma x f64! 5.5752458452673005e-5 (-f64! 0.00021647574085351332))
    f64! 0.0005825521659411748) (-f64! 0.0014542587440487815)) f64! 0.003591910693118715)
    (-f64! 0.008863215974794633)) f64! 0.02186948742242217) (-f64! 0.05396825393066753))
    f64! 0.13333333333267555) (-f64! 0.33333333333332904)) f64! 1.0

/-- Julia `tanh_kernel(x::Float32)` (hyperbolic.jl:138-141). -/
@[inline] def tanhKernel32 (x : Float32) : Float32 :=
  Float32.fma x (Float32.fma x (Float32.fma x (Float32.fma x (Float32.fma x (-f32! 0.0050525228)
    f32! 0.019975215) (-f32! 0.05350336)) f32! 0.13328037) (-f32! 0.3333312)) f32! 1.0

end Math

open Math

/-! ## `Float64` -/

namespace F64

/-- Julia `sinh(x::Float64)` (hyperbolic.jl:59-81). -/
def sinh (x : Float) : Float :=
  let absx := x.abs
  if absx ≤ f64! 2.1 then sinhKernel x
  else if absx ≥ f64! 709.7822265633563 then
    let e := exp (f64! 0.5 * absx)
    copysign (f64! 0.5 * e * e) x
  else
    let e := exp absx
    copysign (f64! 0.5 * (e - f64! 1.0 / e)) x

/-- Julia `cosh(x::Float64)` (hyperbolic.jl:99-119). -/
def cosh (x : Float) : Float :=
  let absx := x.abs
  if absx ≤ f64! 1.0 then coshKernel (x * x)
  else if absx ≥ f64! 709.7822265633563 then
    let e := exp (f64! 0.5 * absx)
    f64! 0.5 * e * e
  else
    let e := exp absx
    f64! 0.5 * (e + f64! 1.0 / e)

/-- Julia `tanh(x::Float64)` (hyperbolic.jl:142-159). -/
def tanh (x : Float) : Float :=
  let abs2x := (f64! 2.0 * x).abs
  if abs2x ≥ f64! 44.0 then copysign (f64! 1.0) x
  else if abs2x ≤ f64! 1.0 then x * tanhKernel (x * x)
  else
    let k := exp abs2x
    copysign (f64! 1.0 - f64! 2.0 / (k + f64! 1.0)) x

/-- Julia `asinh(x::Float64)` (hyperbolic.jl:165-196). -/
def asinh (x : Float) : Float :=
  if !x.isFinite then x
  else
    let absx := x.abs
    if absx < f64! 2.0 then
      if absx < f64! 3.725290298461914e-9 then x  -- `2^-28`
      else
        let t := x * x
        copysign (log1p (absx + t / (f64! 1.0 + (f64! 1.0 + t).sqrt))) x
    else if absx < f64! 268435456.0 then  -- `2^28`
      copysign (log (f64! 2.0 * absx + f64! 1.0 / ((x * x + f64! 1.0).sqrt + absx))) x
    else copysign (log absx + f64! 6.93147180559945286227e-01) x

/-- Julia `acosh(x::Float64)` (hyperbolic.jl:200-229); `NaN` for `x < 1`. -/
def acosh (x : Float) : Float :=
  if x.isNaN then x
  else if x < f64! 1.0 then nan
  else if x == f64! 1.0 then f64! 0.0
  else if x < f64! 2.0 then
    let t := x - f64! 1.0
    log1p (t + (f64! 2.0 * t + t * t).sqrt)
  else if x < f64! 268435456.0 then
    let t := x * x
    log (f64! 2.0 * x - f64! 1.0 / (x + (t - f64! 1.0).sqrt))
  else log x + f64! 6.93147180559945286227e-01

/-- Julia `atanh(x::Float64)` (hyperbolic.jl:233-266); `NaN` for `|x| > 1`. -/
def atanh (x : Float) : Float :=
  if x.isNaN then x
  else
    let absx := x.abs
    if absx > f64! 1.0 then nan
    else
      let t := if absx < f64! 0.5 then log1p (f64! 2.0 * absx / (f64! 1.0 - absx))
        else log ((f64! 1.0 + absx) / (f64! 1.0 - absx))
      f64! 0.5 * copysign t x

end F64

/-! ## `Float32` -/

namespace F32

/-- Julia `sinh(x::Float32)` (hyperbolic.jl:59-81): the kernel in `Float64`, `exp` in `Float32`. -/
def sinh (x : Float32) : Float32 :=
  let absx := x.abs
  if absx ≤ f32! 3.0 then sinhKernel32 x
  else if absx ≥ f32! 88.72283 then
    let e := exp (f32! 0.5 * absx)
    copysign (f32! 0.5 * e * e) x
  else
    let e := exp absx
    copysign (f32! 0.5 * (e - f32! 1.0 / e)) x

/-- Julia `cosh(x::Float32)` (hyperbolic.jl:99-119). -/
def cosh (x : Float32) : Float32 :=
  let absx := x.abs
  if absx ≤ f32! 1.0 then coshKernel32 (x * x)
  else if absx ≥ f32! 88.72283 then
    let e := exp (f32! 0.5 * absx)
    f32! 0.5 * e * e
  else
    let e := exp absx
    f32! 0.5 * (e + f32! 1.0 / e)

/-- Julia `tanh(x::Float32)` (hyperbolic.jl:142-159). -/
def tanh (x : Float32) : Float32 :=
  let abs2x := (f32! 2.0 * x).abs
  if abs2x ≥ f32! 18.0 then copysign (f32! 1.0) x
  else if abs2x ≤ f32! 1.3862944 then x * tanhKernel32 (x * x)
  else
    let k := exp abs2x
    copysign (f32! 1.0 - f32! 2.0 / (k + f32! 1.0)) x

/-- Julia `asinh(x::Float32)` (hyperbolic.jl:165-196). -/
def asinh (x : Float32) : Float32 :=
  if !x.isFinite then x
  else
    let absx := x.abs
    if absx < f32! 2.0 then
      if absx < Float32.ofBits 0x31800000 then x  -- `2f0^-28`
      else
        let t := x * x
        copysign (log1p (absx + t / (f32! 1.0 + (f32! 1.0 + t).sqrt))) x
    else if absx < Float32.ofBits 0x4d800000 then  -- `2f0^28`
      copysign (log (f32! 2.0 * absx + f32! 1.0 / ((x * x + f32! 1.0).sqrt + absx))) x
    else copysign (log absx + f32! 6.9314718246e-01) x

/-- Julia `acosh(x::Float32)` (hyperbolic.jl:200-229); `NaN` for `x < 1`. -/
def acosh (x : Float32) : Float32 :=
  if x.isNaN then x
  else if x < f32! 1.0 then nan
  else if x == f32! 1.0 then f32! 0.0
  else if x < f32! 2.0 then
    let t := x - f32! 1.0
    log1p (t + (f32! 2.0 * t + t * t).sqrt)
  else if x < Float32.ofBits 0x4d800000 then
    let t := x * x
    log (f32! 2.0 * x - f32! 1.0 / (x + (t - f32! 1.0).sqrt))
  else log x + f32! 6.9314718246e-01

/-- Julia `atanh(x::Float32)` (hyperbolic.jl:233-266); `NaN` for `|x| > 1`. -/
def atanh (x : Float32) : Float32 :=
  if x.isNaN then x
  else
    let absx := x.abs
    if absx > f32! 1.0 then nan
    else
      let t := if absx < f32! 0.5 then log1p (f32! 2.0 * absx / (f32! 1.0 - absx))
        else log ((f32! 1.0 + absx) / (f32! 1.0 - absx))
      f32! 0.5 * copysign t x

end F32

end JuliaBase
