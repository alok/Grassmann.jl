import JuliaBase.Math

/-!
# Julia's own trigonometric functions, bit for bit

Julia does not call the platform `libm` for `sin`, `cos`, `tan`, `sincos`, `asin`, `acos`,
`atan`, `atan(y, x)`, `sinpi`, `cospi` or `sincospi`: it ships ports of openlibm's (FDLIBM's)
kernels (`base/special/trig.jl`) with its own argument reduction (`base/special/rem_pio2.jl`,
Cody–Waite for moderate arguments and Payne–Hanek beyond `2^20·π/2`). The macOS `libm` (Lean's
`Float.sin`, …) disagrees with them in the last bit on a few percent of arguments (`tan` 39 %,
`asin` 9 %, `atan` 7 %, `cos` 5 %, `sin` 4 % on 10⁵ samples), so this module replays Julia's
kernels operation by operation, for `Float64` (`F64.sin`, …) and `Float32` (`F32.sin`, …).

**`muladd` is fused, with measured exceptions.** As in `JuliaBase.Math`, every `muladd` (and
`@horner`/`evalpoly`, built from it) is a hardware FMA on the oracle machine (Apple aarch64,
Julia 1.13), except where LLVM keeps the product unfused. Two sites here: the outermost
`muladd` of `sin_kernel`'s first polynomial, and `cospi_kernel`'s `muladd(c, x², -a_x²)`, whose
product `c·x²` is the same value as `a_x² = c*x²` and is common-subexpression-eliminated with it,
so that term is `a_x² - a_x²` (read off Julia's native code). The model was validated on sweeps
of several million oracle samples per function (`Tests/JuliaBase/gen_golden.jl trig`), bit for
bit, including Payne–Hanek arguments up to `floatmax`.

**Performance.** `Float.toBits`/`ofBits`, `isNaN`, `isInf` and `isFinite` are out-of-line runtime
calls in compiled Lean, so the hot paths test `x != x` and compare `|x|` with `Inf`, and take a
sign from a comparison wherever the operand cannot be `±0` (a signed zero needs the bits). No
function returns a tuple of `Float`s on a hot path (tuples box their fields): `sincos` has a
continuation-passing form `sincosK` for callers such as `ComplexF64.exp`. Payne–Hanek runs its
128-bit arithmetic on `UInt64` limbs. `docs/PERF.md` has the numbers.

Arguments outside a function's domain (Julia throws a `DomainError`: `sin(Inf)`,
`asin(2.0)`, …) return `NaN`.

Julia sources (1.13): `base/special/trig.jl`, `base/special/rem_pio2.jl`.
-/

namespace JuliaBase

namespace Math

/-! ## Argument reduction (`rem_pio2.jl`) -/

/-- The result of Julia's `rem_pio2_kernel(x)`: the quadrant `n` and the remainder
`r = hi + lo` (a `DoubleFloat64`) with `n·π/2 = x - r`. -/
structure RemPio2 where
  /-- the quadrant `k` (positive for `x > 0`, negative for `x ≤ 0`) -/
  n : Int64
  /-- leading part of the remainder -/
  hi : Float
  /-- trailing part of the remainder -/
  lo : Float

/-- Zero the low 32 bits (Julia `reinterpret(Float64, (reinterpret(UInt64, x) >> 32) << 32)`). -/
@[inline] def truncLow (x : Float) : Float := Float.ofBits ((x.toBits >>> 32) <<< 32)

/-- Julia `poshighword(x::Float64)`: the upper 32 bits without the sign. -/
@[inline] def poshighword (x : Float) : UInt32 := ((x.toBits >>> 32) &&& 0x7FFFFFFF).toUInt32

/-- Julia `cody_waite_2c_pio2(x, fn, n)` (rem_pio2.jl:40-47): `x - fn·π/2` with two constants. -/
@[inline] def codyWaite2c (x fn : Float) (n : Int64) : RemPio2 :=
  let z := Float.fma (-fn) f64! 1.57079632673412561417e+00 x
  let y1 := Float.fma (-fn) f64! 6.07710050650619224932e-11 z
  let y2 := Float.fma (-fn) f64! 6.07710050650619224932e-11 (z - y1)
  ⟨n, y1, y2⟩

/-- Julia `cody_waite_ext_pio2(x, xhp)` (rem_pio2.jl:49-87): up to three Cody–Waite steps. -/
@[inline] def codyWaiteExt (x : Float) (xhp : UInt32) : RemPio2 :=
  let fn := F64.round (x * f64! 0.6366197723675814)
  let r := Float.fma (-fn) f64! 1.57079632673412561417e+00 x
  let w := fn * f64! 6.07710050650619224932e-11
  let j := xhp >>> 20
  let y1 := r - w
  -- `i = j - ((highword(y1) >> 20) & 0x7ff)` wraps as `UInt32`, like Julia's
  let i := j - ((F64.highword y1 >>> 20) &&& 0x7ff)
  if i > 16 then
    let t := r
    let w := fn * f64! 6.07710050630396597660e-11
    let r := t - w
    let w := Float.fma fn f64! 2.02226624879595063154e-21 (-((t - r) - w))
    let y1 := r - w
    let i := j - ((F64.highword y1 >>> 20) &&& 0x7ff)
    if i > 49 then
      let t := r
      let w := fn * f64! 2.02226624871116645580e-21
      let r := t - w
      let w := Float.fma fn f64! 8.47842766036889956997e-32 (-((t - r) - w))
      let y1 := r - w
      ⟨fn.toInt64, y1, (r - y1) - w⟩
    else ⟨fn.toInt64, y1, (r - y1) - w⟩
  else ⟨fn.toInt64, y1, (r - y1) - w⟩

/-- Julia `INV_2PI` (rem_pio2.jl:26-38): the bits of `1/(2π)` in 64-bit words. -/
def inv2pi : Array UInt64 := #[
  0x28be60db9391054a, 0x7f09d5f47d4d3770, 0x36d8a5664f10e410, 0x7f9458eaf7aef158,
  0x6dc91b8e909374b8, 0x01924bba82746487, 0x3f877ac72c4a69cf, 0xba208d7d4baed121,
  0x3a671c09ad17df90, 0x4e64758e60d4ce7d, 0x272117e2ef7e4a0e, 0xc7fe25fff7816603,
  0xfbcbc462d6829b47, 0xdb4d9fb3c9f2c26d, 0xd3d18fd9a797fa8b, 0x5d49eeb1faf97c5e,
  0xcf41ce7de294a4ba, 0x9afed7ec47e35742, 0x1580cc11bf1edaea]

/-! ### 128-bit integers as `UInt64` limbs `(hi, lo)`, for Payne–Hanek -/

/-- Julia `top_set_bit(x)` = `⌊log₂ x⌋ + 1` (`0` for `0`) of a `UInt64`, by binary search. -/
@[inline] def topSetBit64 (x : UInt64) : UInt64 :=
  let b32 := x >>> 32 != 0
  let x := if b32 then x >>> 32 else x
  let b16 := x >>> 16 != 0
  let x := if b16 then x >>> 16 else x
  let b8 := x >>> 8 != 0
  let x := if b8 then x >>> 8 else x
  let b4 := x >>> 4 != 0
  let x := if b4 then x >>> 4 else x
  let b2 := x >>> 2 != 0
  let x := if b2 then x >>> 2 else x
  (if b32 then 32 else 0) + (if b16 then 16 else 0) + (if b8 then 8 else 0) + (if b4 then 4 else 0) +
    (if b2 then 2 else 0) + (if x >>> 1 != 0 then 1 else 0) + (if x == 0 then 0 else 1)

/-- Julia `top_set_bit` of the 128-bit `(hi, lo)`. -/
@[inline] def topSetBit128 (hi lo : UInt64) : UInt64 :=
  if hi != 0 then 64 + topSetBit64 hi else topSetBit64 lo

/-- The full product `a·b` of two `UInt64`s as `(hi, lo)` (Julia `widemul`). -/
@[inline] def mul64 (a b : UInt64) : UInt64 × UInt64 :=
  let a0 := a &&& (0xFFFFFFFF : UInt64)
  let a1 := a >>> 32
  let b0 := b &&& (0xFFFFFFFF : UInt64)
  let b1 := b >>> 32
  let p00 := a0 * b0
  let p01 := a0 * b1
  let p10 := a1 * b0
  let mask : UInt64 := 0xFFFFFFFF
  let mid := (p00 >>> 32) + (p01 &&& mask) + (p10 &&& mask)
  (a1 * b1 + (p01 >>> 32) + (p10 >>> 32) + (mid >>> 32), (p00 &&& mask) ||| (mid <<< 32))

/-- The low limb of the 128-bit `(hi, lo) >> s` for `0 ≤ s < 128`. -/
@[inline] def shr128lo (hi lo s : UInt64) : UInt64 :=
  if s == 0 then lo
  else if s < 64 then (lo >>> s) ||| (hi <<< (64 - s))
  else hi >>> (s - 64)

/-- The 128-bit `(0, x) << s` for `0 ≤ s < 128`. -/
@[inline] def shl128 (x s : UInt64) : UInt64 × UInt64 :=
  if s == 0 then (0, x)
  else if s < 64 then (x >>> (64 - s), x <<< s)
  else (x <<< (s - 64), 0)

/-- Julia `fromfraction(f::Int128)` (rem_pio2.jl:96-122): `(z1, z2)` with `z1 + z2 = f/2^128`,
for the magnitude `|f| = (xh, xl)` and the sign `neg`. -/
@[inline] def fromFraction (neg : Bool) (xh xl : UInt64) : Float × Float :=
  if xh == 0 && xl == 0 then (f64! 0.0, f64! 0.0)
  else
    let s : UInt64 := if neg then 0x8000000000000000 else 0
    let n1 := topSetBit128 xh xl  -- in [1, 128]
    -- `m1 = ((x >> (n1-26)) % UInt64) << 27` (a left shift when `n1 < 26`)
    let top := if n1 ≥ 26 then shr128lo xh xl (n1 - 26) else xl <<< (26 - n1)
    let m1 := top <<< 27
    let z1 := Float.ofBits (s ||| (((n1 + 893) <<< 52) + m1))  -- `d1 = (n1-128+1021) << 52`
    -- `x2 = x - (UInt128(m1) << (n1-53))` (a right shift when `n1 < 53`)
    let (ph, pl) := if n1 ≥ 53 then shl128 m1 (n1 - 53) else (0, m1 >>> (53 - n1))
    let x2l := xl - pl
    let x2h := xh - ph - (if xl < pl then 1 else 0)
    if x2h == 0 && x2l == 0 then (z1, f64! 0.0)
    else
      let n2 := topSetBit128 x2h x2l
      let m2 := if n2 ≥ 53 then shr128lo x2h x2l (n2 - 53) else x2l <<< (53 - n2)
      (z1, Float.ofBits (s ||| (((n2 + 893) <<< 52) + m2)))

/-- Word `i` of the bits of `1/(2π)` (`0` for a negative index), an inline read. -/
@[inline] def inv2piWord (i : Int64) : UInt64 :=
  if i < i64! 0 then 0 else inv2pi[i.toNatClampNeg]?.getD 0

/-- Julia `paynehanek(x::Float64)` (rem_pio2.jl:124-196): reduction of a huge argument
(`|x| ≥ 2^20·π/2`) modulo `π/2` against the bits of `1/(2π)`, in 128-bit integer arithmetic. -/
def paynehanek (x : Float) : RemPio2 :=
  let u := x.toBits
  let bigX := (u &&& 0x000FFFFFFFFFFFFF) ||| 0x0010000000000000
  let k : Int64 := ((u &&& 0x7FF0000000000000) >>> 52).toInt64 - i64! 1075
  let idx : Int64 := k >>> i64! 6  -- arithmetic shift, as Julia's `>>`
  let shift : UInt64 := (k - (idx <<< i64! 6)).toUInt64
  let (a1, a2, a3) : UInt64 × UInt64 × UInt64 :=
    if shift == 0 then (inv2piWord idx, inv2piWord (idx + i64! 1), inv2piWord (idx + i64! 2))
    else
      ((inv2piWord idx <<< shift) ||| (inv2piWord (idx + i64! 1) >>> (64 - shift)),
       (inv2piWord (idx + i64! 1) <<< shift) ||| (inv2piWord (idx + i64! 2) >>> (64 - shift)),
       (inv2piWord (idx + i64! 2) <<< shift) ||| (inv2piWord (idx + i64! 3) >>> (64 - shift)))
  -- `w = UInt128(X*a1) << 64 + widemul(X, a2) + widemul(X, a3) >> 64` (mod 2^128)
  let (w2h, w2l) := mul64 bigX a2
  let (w3h, _) := mul64 bigX a3
  let wl := w2l + w3h
  let wh := bigX * a1 + w2h + (if wl < w2l then 1 else 0)
  -- `flipsign(w, x)`: two's-complement negation for negative `x`
  let (wh, wl) := if x < f64! 0.0 then (~~~wh + (if wl == 0 then 1 else 0), ~~~wl + 1) else (wh, wl)
  -- `q = (((w >> 125) % Int + 1) >> 1)`, `f = (w << 2) % Int128`
  let q : Int64 := (((wh >>> 61) + 1) >>> 1).toInt64
  let fh := (wh <<< 2) ||| (wl >>> 62)
  let fl := wl <<< 2
  let neg := fh >>> 63 != 0
  let (mh, ml) := if neg then (~~~fh + (if fl == 0 then 1 else 0), ~~~fl + 1) else (fh, fl)
  let (zhi, zlo) := fromFraction neg mh ml
  let yhi := (zhi + zlo) * f64! 1.5707963267948966
  let ylo := (((zhi * f64! 1.5707963407039642 - yhi) + zhi * (f64! -1.3909067614167116e-8)) +
    zlo * f64! 1.5707963407039642) + zlo * (f64! -1.3909067614167116e-8)
  ⟨q, yhi, ylo⟩

/-- Julia `rem_pio2_kernel(x::Float64)` (rem_pio2.jl:198-266), accurate to about `1e-22`. -/
@[inline] def remPio2 (x : Float) : RemPio2 :=
  let xhp := poshighword x
  if xhp ≤ 0x400f6a7a then
    if (xhp &&& 0xfffff) == 0x921fb then codyWaiteExt x xhp
    else if xhp ≤ 0x4002d97c then
      if x > f64! 0.0 then codyWaite2c x (f64! 1.0) (i64! 1) else codyWaite2c x (f64! -1.0) (i64! -1)
    else if x > f64! 0.0 then codyWaite2c x (f64! 2.0) (i64! 2) else codyWaite2c x (f64! -2.0) (i64! -2)
  else if xhp ≤ 0x401c463b then
    if xhp ≤ 0x4015fdbc then
      if xhp == 0x4012d97c then codyWaiteExt x xhp
      else if x > f64! 0.0 then codyWaite2c x (f64! 3.0) (i64! 3) else codyWaite2c x (f64! -3.0) (i64! -3)
    else if xhp == 0x401921fb then codyWaiteExt x xhp
    else if x > f64! 0.0 then codyWaite2c x (f64! 4.0) (i64! 4) else codyWaite2c x (f64! -4.0) (i64! -4)
  else if xhp < 0x413921fb then codyWaiteExt x xhp
  else paynehanek x

/-- Julia `rem_pio2_kernel(x::Float32)` (rem_pio2.jl:280-293): the reduction in `Float64`, one
Cody–Waite step with an `fma` below `2^28·π/2`, Payne–Hanek beyond. The remainder is the
`Float64` `hi` (a `DoubleFloat32`); `lo` is `0`. -/
@[inline] def remPio2F32 (x : Float32) : RemPio2 :=
  let xd := x.toFloat
  if x.abs < Float32.ofBits 0x4dc90fdb then  -- `Float32(pi*0x1p27)`
    let fn := F64.round (xd * f64! 0.6366197723675814)
    let r := Float.fma fn (f64! -1.5707963267948966) xd
    ⟨fn.toInt64, Float.fma fn (f64! -6.123233995736766e-17) r, f64! 0.0⟩
  else
    let r := paynehanek xd
    ⟨r.n, r.hi, f64! 0.0⟩

/-! ## `Float64` kernels on `[-π/4, π/4]` (trig.jl:54-151, 238-338) -/

/-- `DS1`, the first sine coefficient. -/ def ds1 : Float := f64! -1.66666666666666324348e-01
/-- `DS2`. -/ def ds2 : Float := f64! 8.33333333332248946124e-03
/-- `DS3`. -/ def ds3 : Float := f64! -1.98412698298579493134e-04
/-- `DS4`. -/ def ds4 : Float := f64! 2.75573137070700676789e-06
/-- `DS5`. -/ def ds5 : Float := f64! -2.50507602534068634195e-08
/-- `DS6`. -/ def ds6 : Float := f64! 1.58969099521155010221e-10
/-- `DC1`, the first cosine coefficient. -/ def dc1 : Float := f64! 4.16666666666666019037e-02
/-- `DC2`. -/ def dc2 : Float := f64! -1.38888888888741095749e-03
/-- `DC3`. -/ def dc3 : Float := f64! 2.48015872894767294178e-05
/-- `DC4`. -/ def dc4 : Float := f64! -2.75573143513906633035e-07
/-- `DC5`. -/ def dc5 : Float := f64! 2.08757232129817482790e-09
/-- `DC6`. -/ def dc6 : Float := f64! -1.13596475577881948265e-11

/-- The polynomial `r` of `sin_kernel`: `@horner(y², DS2, DS3, DS4) + y²·y⁴·@horner(y², DS5,
DS6)`, whose outermost `muladd` compiles unfused in Julia's system image. -/
@[inline] def sinPoly (y2 : Float) : Float :=
  (y2 * Float.fma y2 ds4 ds3 + ds2) + y2 * (y2 * y2) * Float.fma y2 ds6 ds5

/-- Julia `sin_kernel(y::Float64)` (trig.jl:76-82). -/
@[inline] def sinKernel (y : Float) : Float :=
  let y2 := y * y
  let r := sinPoly y2
  y + y2 * y * (ds1 + y2 * r)

/-- Julia `sin_kernel(y::DoubleFloat64)` (trig.jl:69-75). -/
@[inline] def sinKernelDD (hi lo : Float) : Float :=
  let y2 := hi * hi
  let r := sinPoly y2
  let y3 := y2 * hi
  hi - ((y2 * (f64! 0.5 * lo - y3 * r) - lo) - y3 * ds1)

/-- The polynomial `r` of `cos_kernel`. -/
@[inline] def cosPoly (y2 : Float) : Float :=
  let y4 := y2 * y2
  y2 * Float.fma y2 (Float.fma y2 dc3 dc2) dc1 + y4 * y4 * Float.fma y2 (Float.fma y2 dc6 dc5) dc4

/-- Julia `cos_kernel(y::Float64)` (trig.jl:144-151). -/
@[inline] def cosKernel (y : Float) : Float :=
  let y2 := y * y
  let r := cosPoly y2
  let halfY2 := f64! 0.5 * y2
  let w := f64! 1.0 - halfY2
  w + (((f64! 1.0 - w) - halfY2) + y2 * r)

/-- Julia `cos_kernel(y::DoubleFloat64)` (trig.jl:136-143). -/
@[inline] def cosKernelDD (hi lo : Float) : Float :=
  let y2 := hi * hi
  let r := cosPoly y2
  let halfY2 := f64! 0.5 * y2
  let w := f64! 1.0 - halfY2
  w + (((f64! 1.0 - w) - halfY2) + (y2 * r - hi * lo))

/-- The shared polynomial part of `tan_kernel`: `r` after its two updates, from the reduced
`yhi + ylo` (`trig.jl:285-310`). -/
@[inline] def tanR (yhi ylo : Float) : Float :=
  let y2 := yhi * yhi
  let y4 := y2 * y2
  let r := Float.fma y4 (Float.fma y4 (Float.fma y4 (Float.fma y4 (Float.fma y4
      (f64! -1.85586374855275456654e-05) f64! 7.81794442939557092300e-05) f64! 5.88041240820264096874e-04)
      f64! 3.59207910759131235356e-03) f64! 2.18694882948595424599e-02) f64! 1.33333333333201242699e-01
  let v := y2 * Float.fma y4 (Float.fma y4 (Float.fma y4 (Float.fma y4 (Float.fma y4
      f64! 2.59073051863633712884e-05 f64! 7.14072491382608190305e-05) f64! 2.46463134818469906812e-04)
      f64! 1.45620945432529025516e-03) f64! 8.86323982359930005737e-03) f64! 5.39682539762260521377e-02
  let y3 := y2 * yhi
  let r := ylo + y2 * (y3 * (r + v) + ylo)
  r + f64! 3.33333333333334091986e-01 * y3

/-- Julia `tan_kernel(y::DoubleFloat64, k)` (trig.jl:239-338): `tan(y)` for `k = 1`, `-1/tan(y)`
for `k = -1`. -/
def tanKernel (hi lo k : Float) : Float :=
  if hi.abs ≥ f64! 0.6744 then
    -- reduce to `π/4 - |y|` (then `ylo = 0`); `|hi| ≥ 0.6744`, so its sign is a comparison
    let neg := hi < f64! 0.0
    let yhi := (f64! 0.7853981633974483 - (if neg then -hi else hi)) +
      (f64! 3.06161699786838301793e-17 - (if neg then -lo else lo))
    let r := tanR yhi (f64! 0.0)
    let px := yhi + r
    (if neg then f64! -1.0 else f64! 1.0) * (k - f64! 2.0 * (yhi - (px * px / (k + px) - r)))
  else
    let r := tanR hi lo
    let px := hi + r
    if k == f64! 1.0 then px
    else
      let px0 := truncLow px
      let v := r - (px0 - hi)
      let a := f64! -1.0 / px
      let t := truncLow a
      let s := f64! 1.0 + t * px0
      t + a * (s + t * v)

/-! ## `Float32` kernels (trig.jl:85-94, 154-162, 340-355): evaluated in `Float64` -/

/-- Julia `sin_kernel(y::DoubleFloat32)`. -/
@[inline] def sinKernel32 (y : Float) : Float32 :=
  let z := y * y
  let w := z * z
  let r := Float.fma z f64! 2.718311493989822e-6 (f64! -0.00019839334836096632)
  let s := z * y
  ((y + s * Float.fma z f64! 0.008333329385889463 (f64! -0.16666666641626524)) + s * w * r).toFloat32

/-- Julia `cos_kernel(y::DoubleFloat32)`. -/
@[inline] def cosKernel32 (y : Float) : Float32 :=
  let y2 := y * y
  let y4 := y2 * y2
  let r := Float.fma y2 f64! 2.439044879627741e-5 (f64! -0.001388676377460993)
  (((f64! 1.0 + y2 * (f64! -0.499999997251031)) + y4 * f64! 0.04166662332373906) + (y4 * y2) * r).toFloat32

/-- Julia `tan_kernel(y::DoubleFloat32, k)`: `tan(y)` for `k = 1`, `-1/tan(y)` otherwise. -/
@[inline] def tanKernel32 (y : Float) (k1 : Bool) : Float32 :=
  let y2 := y * y
  let r := Float.fma y2 f64! 0.00946564784943673166728 f64! 0.00297435743359967304927
  let t := Float.fma y2 f64! 0.0245283181166547278873 f64! 0.0533812378445670393523
  let y4 := y2 * y2
  let y3 := y2 * y
  let u := Float.fma y2 f64! 0.133392002712976742718 f64! 0.333331395030791399758
  let py := (y + y3 * u) + (y3 * y4) * (t + y4 * r)
  if k1 then py.toFloat32 else (f64! -1.0 / py).toFloat32

/-! ## Inverse functions: `Float64` (trig.jl:363-659) -/

/-- Julia `arc_p(t)/arc_q(t)` for `Float64` (trig.jl:368-393). -/
@[inline] def arcTRt (t : Float) : Float :=
  let p := t * Float.fma t (Float.fma t (Float.fma t (Float.fma t (Float.fma t
      f64! 3.47933107596021167570e-05 f64! 7.91534994289814532176e-04) (f64! -4.00555345006794114027e-02))
      f64! 2.01212532134862925881e-01) (f64! -3.25565818622400915405e-01)) f64! 1.66666666666666657415e-01
  let q := Float.fma t (Float.fma t (Float.fma t (Float.fma t f64! 7.70381505559019352791e-02
      (f64! -6.88283971605453293030e-01)) f64! 2.02094576023350569471e+00) (f64! -2.40339491173441421878e+00))
      f64! 1.0
  p / q

/-- `p + q` of Julia's `atan_pq(x)` for `Float64` (trig.jl:482-502): the odd and even halves of
the arctangent polynomial. -/
@[inline] def atanPQ (x : Float) : Float :=
  let x2 := x * x
  let x4 := x2 * x2
  let p := x2 * Float.fma x4 (Float.fma x4 (Float.fma x4 (Float.fma x4 (Float.fma x4
      f64! 1.62858201153657823623e-02 f64! 4.97687799461593236017e-02) f64! 6.66107313738753120669e-02)
      f64! 9.09088713343650656196e-02) f64! 1.42857142725034663711e-01) f64! 3.33333333333329318027e-01
  let q := x4 * Float.fma x4 (Float.fma x4 (Float.fma x4 (Float.fma x4 (f64! -3.65315727442169155270e-02)
      (f64! -5.83357013379057348645e-02)) (f64! -7.69187620504482999495e-02))
      (f64! -1.11111104054623557880e-01)) (f64! -1.99999999998764832476e-01)
  p + q

/-- The tail of Julia's `atan(x::Float64)` after the argument reduction:
`copysign(hi - ((x·(p + q) - lo) - x), sign(x₀))`, the sign given as `neg` (`x₀ ≠ 0`). -/
@[inline] def atanTail (hi lo x : Float) (neg : Bool) : Float :=
  let z := (hi - ((x * atanPQ x - lo) - x)).abs
  if neg then -z else z

/-! ## Inverse functions: `Float32` -/

/-- Julia `arc_p(t)/arc_q(t)` for `Float32`. -/
@[inline] def arcTRt32 (t : Float32) : Float32 :=
  let p := t * Float32.fma t (Float32.fma t (f32! -8.6563630030e-03) (f32! -4.2743422091e-02))
    f32! 1.6666586697e-01
  let q := Float32.fma t (f32! -7.0662963390e-01) f32! 1.0
  p / q

/-- `p + q` of Julia's `atan_pq(x)` for `Float32`. -/
@[inline] def atanPQ32 (x : Float32) : Float32 :=
  let x2 := x * x
  let x4 := x2 * x2
  let p := x2 * Float32.fma x4 (Float32.fma x4 f32! 6.1687607318e-02 f32! 1.4253635705e-01)
    f32! 3.3333328366e-01
  let q := x4 * Float32.fma x4 (f32! -1.0648017377e-01) (f32! -1.9999158382e-01)
  p + q

/-- The tail of Julia's `atan(x::Float32)` after the argument reduction (`x₀ ≠ 0`). -/
@[inline] def atanTail32 (hi lo x : Float32) (neg : Bool) : Float32 :=
  let z := (hi - ((x * atanPQ32 x - lo) - x)).abs
  if neg then -z else z

/-! ## `sinpi`/`cospi` kernels (trig.jl:728-785) -/

/-- Julia `sinpi_kernel_wide(x::Float64)`: `sin(πx)` for `πx ∈ [0, π/4]`. -/
@[inline] def sinpiKernel (x : Float) : Float :=
  let x2 := x * x
  let x4 := x2 * x2
  let r := Float.fma x2 (Float.fma x2 (Float.fma x2 (Float.fma x2 (Float.fma x2
      (f64! -2.1717412523382308e-5) f64! 4.662827319453555e-4) (f64! -7.370429884921779e-3))
      f64! 0.08214588658006512) (f64! -0.5992645293202981)) f64! 2.5501640398773415
  Float.fma f64! 3.141592653589793 x (x * Float.fma (f64! -5.16771278004997) x2
    (Float.fma x4 r f64! 1.2245907532225998e-16))

/-- Julia `cospi_kernel_wide(x::Float64)`: `cos(πx)` for `πx ∈ [0, π/4]`. The product of
`muladd(4.934802200544679, x², -a_x²)` is CSE'd with `a_x²`, so that term is `a_x² - a_x²`. -/
@[inline] def cospiKernel (x : Float) : Float :=
  let x2 := x * x
  let r := x2 * Float.fma x2 (Float.fma x2 (Float.fma x2 (Float.fma x2 (Float.fma x2
      (f64! -1.0368935675474665e-4) f64! 1.9294917136379183e-3) (f64! -0.025806887811869204))
      f64! 0.23533063027900392) (f64! -1.3352627688537357)) f64! 4.058712126416765
  let ax := f64! 4.934802200544679 * x2
  let axlo := Float.fma x2 f64! 3.109686485461973e-16 (ax - ax)
  let w := f64! 1.0 - ax
  w + Float.fma x2 r (((f64! 1.0 - w) - ax) - axlo)

/-- Julia `sinpi_kernel_wide(x::Float32)`, in `Float64`. -/
@[inline] def sinpiKernel32 (x : Float32) : Float32 :=
  let x := x.toFloat
  let x2 := x * x
  (x * Float.fma x2 (Float.fma x2 (Float.fma x2 (Float.fma x2 f64! 0.08100185277841528
    (f64! -0.5992021090314925)) f64! 2.5501626483206374) (f64! -5.167712769188119))
    f64! 3.1415926535762266).toFloat32

/-- Julia `cospi_kernel_wide(x::Float32)`, in `Float64`. -/
@[inline] def cospiKernel32 (x : Float32) : Float32 :=
  let x := x.toFloat
  let x2 := x * x
  (Float.fma x2 (Float.fma x2 (Float.fma x2 (Float.fma x2 (Float.fma x2 (f64! -0.02550710082498761)
    f64! 0.23531426791507182) (f64! -1.3352624040152927)) f64! 4.058712123568637)
    (f64! -4.934802200541122)) f64! 1.0).toFloat32

end Math

open Math

/-! ## `Float64` entry points -/

namespace F64

/-- Julia `sin(x::Float64)` (trig.jl:29-52); `NaN` for infinite `x` (Julia throws). -/
def sin (x : Float) : Float :=
  let absx := x.abs
  if absx < f64! 0.7853981633974483 then
    if absx < f64! 1.4901161193847656e-8 then x else sinKernel x
  else if x != x then x
  else if absx == inf then nan
  else
    let r := remPio2 x
    match r.n.toUInt64 &&& 3 with
    | 0 => sinKernelDD r.hi r.lo
    | 1 => cosKernelDD r.hi r.lo
    | 2 => -sinKernelDD r.hi r.lo
    | _ => -cosKernelDD r.hi r.lo

/-- Julia `cos(x::Float64)` (trig.jl:98-122); `NaN` for infinite `x`. -/
def cos (x : Float) : Float :=
  let absx := x.abs
  if absx < f64! 0.7853981633974483 then
    if absx < f64! 1.0536712127723509e-8 then f64! 1.0 else cosKernel x
  else if x != x then x
  else if absx == inf then nan
  else
    let r := remPio2 x
    match r.n.toUInt64 &&& 3 with
    | 0 => cosKernelDD r.hi r.lo
    | 1 => -sinKernelDD r.hi r.lo
    | 2 => -cosKernelDD r.hi r.lo
    | _ => sinKernelDD r.hi r.lo

/-- Julia `sincos(x::Float64)` (trig.jl:177-203) in continuation-passing form: `k (sin x) (cos x)`
from one reduction, with no tuple (`(NaN, NaN)` for infinite `x`). -/
@[inline] def sincosK {α : Type} (x : Float) (k : Float → Float → α) : α :=
  let absx := x.abs
  if absx < f64! 0.7853981633974483 then
    if x == f64! 0.0 then k x (f64! 1.0) else k (sinKernel x) (cosKernel x)
  else if x != x then k x x
  else if absx == inf then k nan nan
  else
    let r := remPio2 x
    let si := sinKernelDD r.hi r.lo
    let co := cosKernelDD r.hi r.lo
    match r.n.toUInt64 &&& 3 with
    | 0 => k si co
    | 1 => k co (-si)
    | 2 => k (-si) (-co)
    | _ => k (-co) si

/-- Julia `sincos(x::Float64)` (trig.jl:177-203): `(sin x, cos x)` from one reduction.
`(NaN, NaN)` for infinite `x`. -/
def sincos (x : Float) : Float × Float := sincosK x fun s c => (s, c)

/-- Julia `tan(x::Float64)` (trig.jl:218-236); `NaN` for infinite `x`. -/
def tan (x : Float) : Float :=
  let absx := x.abs
  if absx < f64! 0.7853981633974483 then
    if absx < f64! 7.450580596923828e-9 then x else tanKernel x (f64! 0.0) (f64! 1.0)
  else if x != x then x
  else if absx == inf then nan
  else
    let r := remPio2 x
    tanKernel r.hi r.lo (if r.n.toUInt64 &&& 1 == 0 then f64! 1.0 else f64! -1.0)

/-- Julia `asin(x::Float64)` (trig.jl:396-454); `NaN` for `|x| > 1`. -/
def asin (x : Float) : Float :=
  let absx := x.abs
  if absx ≥ f64! 1.0 then
    if absx == f64! 1.0 then (if x < f64! 0.0 then f64! -1.5707963267948966 else f64! 1.5707963267948966)
    else nan
  else if absx < f64! 0.5 then
    if absx < f64! 1.4901161193847656e-8 then x else Float.fma x (arcTRt (x * x)) x
  else
    -- `asin_kernel(t, x)`; `flipsign(·, x)` for `|x| ≥ 1/2` is a comparison
    let t := (f64! 1.0 - absx) / f64! 2.0
    let pio2lo := f64! 6.12323399573676603587e-17
    let s := t.sqrt
    let tRt := arcTRt t
    let v :=
      if absx ≥ f64! 0.975 then f64! 1.5707963267948966 - (f64! 2.0 * (s + s * tRt) - pio2lo)
      else
        let s0 := truncLow s
        let c := (t - s0 * s0) / (s + s0)
        let p := f64! 2.0 * s * tRt - (pio2lo - f64! 2.0 * c)
        let q := f64! 0.7853981633974483 - f64! 2.0 * s0
        f64! 0.7853981633974483 - (p - q)
    if x < f64! 0.0 then -v else v

/-- Julia `acos(x::Float64)` (trig.jl:673-726); `NaN` for `|x| > 1`. -/
def acos (x : Float) : Float :=
  let absx := x.abs
  if absx ≥ f64! 1.0 then
    if absx == f64! 1.0 then (if x > f64! 0.0 then f64! 0.0 else pi) else nan
  else if absx < f64! 0.5 then
    if absx < f64! 6.938893903907228e-18 then f64! 1.5707963267948966  -- `2.0^-57`
    else f64! 1.57079632679489655800e+00 - (x - (f64! 6.12323399573676603587e-17 - x * arcTRt (x * x)))
  else
    let z := (f64! 1.0 - absx) * f64! 0.5
    let zRz := arcTRt z
    let s := z.sqrt
    if x < f64! 0.0 then
      f64! 3.14159265358979311600e+00 - f64! 2.0 * (s + (zRz * s - f64! 6.12323399573676603587e-17))
    else
      let df := truncLow s
      let c := (z - df * df) / (s + df)
      f64! 2.0 * (df + (zRz * s + c))

/-- Julia `atan(x::Float64)` (trig.jl:504-558). -/
def atan (x : Float) : Float :=
  let absx := x.abs
  let neg := x < f64! 0.0
  if absx ≥ f64! 7.378697629483821e19 then  -- `2.0^66`
    if neg then f64! -1.5707963267948966 else f64! 1.5707963267948966
  else if absx < f64! 0.4375 then
    if absx < f64! 7.450580596923828e-9 then x  -- `2.0^-27`
    else x - x * atanPQ x
  else if absx < f64! 1.1875 then
    if absx < f64! 0.6875 then
      atanTail f64! 4.63647609000806093515e-01 f64! 2.26987774529616870924e-17
        ((f64! 2.0 * absx - f64! 1.0) / (f64! 2.0 + absx)) neg
    else
      atanTail f64! 7.85398163397448278999e-01 f64! 3.06161699786838301793e-17
        ((absx - f64! 1.0) / (absx + f64! 1.0)) neg
  else if absx < f64! 2.4375 then
    atanTail f64! 9.82793723247329054082e-01 f64! 1.39033110312309984516e-17
      ((absx - f64! 1.5) / (f64! 1.0 + f64! 1.5 * absx)) neg
  else
    -- also `NaN`, whose (unobservable) sign `copysign` would take
    atanTail f64! 1.57079632679489655800e+00 f64! 6.12323399573676603587e-17 (f64! -1.0 / absx) neg

/-- Julia `atan(y::Float64, x::Float64)` (trig.jl:568-659), the two-argument arctangent (the
angle of `x + iy`). -/
def atan2 (y x : Float) : Float :=
  if x != x then x
  else if y != y then y
  else if x == f64! 1.0 then atan y
  else
    -- `m = 2*signbit(x) + signbit(y)`; outside `y == ±0` both signs are comparisons
    -- (`y ≠ 0`; `x = ±0` only matters through `y`)
    let piLo := f64! 1.2246467991473531772E-16
    if y == f64! 0.0 then
      if !signbit x then y else if !signbit y then pi else -pi
    else
      let sx := x < f64! 0.0
      let sy := y < f64! 0.0
      if x == f64! 0.0 then (if sy then f64! -1.5707963267948966 else f64! 1.5707963267948966)
      else if x.abs == inf then
        if y.abs == inf then
          let v := if sx then f64! 2.356194490192345 else f64! 0.7853981633974483
          if sy then -v else v
        else
          let v := if sx then pi else f64! 0.0
          if sy then -v else v
      else if y.abs == inf then (if sy then f64! -1.5707963267948966 else f64! 1.5707963267948966)
      else
        -- `k = reinterpret(Int32, ypw - xpw) >> 20`: the exponent difference of `y/x`
        let k : Int32 := (poshighword y - poshighword x).toInt32 >>> i32! 20
        if k > i32! 60 then
          -- `|y/x| > 2^60`: `m &= 1`
          let z := f64! 1.5707963267948966 + f64! 0.5 * piLo
          if sy then -z else z
        else
          let z := if x < f64! 0.0 && k < i32! -60 then f64! 0.0 else atan (y / x).abs
          if !sx then (if sy then -z else z)
          else if !sy then pi - (z - piLo)
          else (z - piLo) - pi

/-- Julia `sinpi(x::Float64)` (trig.jl:796-819): `sin(πx)`, exact at integers; `NaN` for
infinite `x`. -/
def sinpi (x0 : Float) : Float :=
  let x := x0.abs
  if !(x < inf) then (if x != x then x else nan)
  else if x ≥ maxintfloat then (if x0 < f64! 0.0 then f64! -0.0 else f64! 0.0)
  else
    let n := round (f64! 2.0 * x)
    let rx := Float.fma (f64! -0.5) n x
    let res := match n.toInt64.toUInt64 &&& 3 with
      | 0 => sinpiKernel rx
      | 1 => cospiKernel rx
      | 2 => f64! 0.0 - sinpiKernel rx
      | _ => f64! 0.0 - cospiKernel rx
    -- `ifelse(signbit(x₀), -res, res)`: for `x₀ = ±0` that is `x₀` itself
    if x0 < f64! 0.0 then -res else if x0 == f64! 0.0 then x0 else res

/-- Julia `cospi(x::Float64)` (trig.jl:829-851): `cos(πx)`; `NaN` for infinite `x`. -/
def cospi (x0 : Float) : Float :=
  let x := x0.abs
  if !(x < inf) then (if x != x then x else nan)
  else if x ≥ maxintfloat then f64! 1.0
  else
    let n := round (f64! 2.0 * x)
    let rx := Float.fma (f64! -0.5) n x
    match n.toInt64.toUInt64 &&& 3 with
    | 0 => cospiKernel rx
    | 1 => f64! 0.0 - sinpiKernel rx
    | 2 => f64! 0.0 - cospiKernel rx
    | _ => sinpiKernel rx

/-- Julia `sincospi(x::Float64)` (trig.jl:865-890): `(sinpi x, cospi x)`. -/
def sincospi (x0 : Float) : Float × Float :=
  let x := x0.abs
  if !(x < inf) then (if x != x then (x, x) else (nan, nan))
  else if x ≥ maxintfloat then (if x0 < f64! 0.0 then f64! -0.0 else f64! 0.0, f64! 1.0)
  else
    let n := round (f64! 2.0 * x)
    let rx := Float.fma (f64! -0.5) n x
    let si := sinpiKernel rx
    let co := cospiKernel rx
    let sgn (s : Float) : Float := if x0 < f64! 0.0 then -s else if x0 == f64! 0.0 then x0 else s
    match n.toInt64.toUInt64 &&& 3 with
    | 0 => (sgn si, co)
    | 1 => (sgn co, f64! 0.0 - si)
    | 2 => (sgn (f64! 0.0 - si), f64! 0.0 - co)
    | _ => (sgn (f64! 0.0 - co), si)

end F64

/-! ## `Float32` entry points -/

namespace F32

/-- Julia `flipsign(x::Float32, y::Float32)`: `x` with its sign flipped when `y`'s sign bit
is set. -/
@[inline] def flipsign (x y : Float32) : Float32 := if signbit y then -x else x

/-- Julia `sin(x::Float32)` (trig.jl:29-52): the kernels run in `Float64`. -/
def sin (x : Float32) : Float32 :=
  let absx := x.abs
  if absx < Float32.ofBits 0x3f490fdb then  -- `Float32(π)/4`
    if absx < Float32.ofBits 0x39b504f3 then x else sinKernel32 x.toFloat  -- `sqrt(eps(Float32))`
  else if x != x then x
  else if absx == inf then nan
  else
    let r := remPio2F32 x
    match r.n.toUInt64 &&& 3 with
    | 0 => sinKernel32 r.hi
    | 1 => cosKernel32 r.hi
    | 2 => -sinKernel32 r.hi
    | _ => -cosKernel32 r.hi

/-- Julia `cos(x::Float32)` (trig.jl:98-122). -/
def cos (x : Float32) : Float32 :=
  let absx := x.abs
  if absx < Float32.ofBits 0x3f490fdb then
    if absx < Float32.ofBits 0x39800000 then f32! 1.0 else cosKernel32 x.toFloat  -- `2^-12`
  else if x != x then x
  else if absx == inf then nan
  else
    let r := remPio2F32 x
    match r.n.toUInt64 &&& 3 with
    | 0 => cosKernel32 r.hi
    | 1 => -sinKernel32 r.hi
    | 2 => -cosKernel32 r.hi
    | _ => sinKernel32 r.hi

/-- Julia `sincos(x::Float32)` (trig.jl:177-203). -/
def sincos (x : Float32) : Float32 × Float32 :=
  let absx := x.abs
  if absx < Float32.ofBits 0x3f490fdb then
    if x == f32! 0.0 then (x, f32! 1.0) else (sinKernel32 x.toFloat, cosKernel32 x.toFloat)
  else if x != x then (x, x)
  else if absx == inf then (nan, nan)
  else
    let r := remPio2F32 x
    let si := sinKernel32 r.hi
    let co := cosKernel32 r.hi
    match r.n.toUInt64 &&& 3 with
    | 0 => (si, co)
    | 1 => (co, -si)
    | 2 => (-si, -co)
    | _ => (-co, si)

/-- Julia `tan(x::Float32)` (trig.jl:218-236). -/
def tan (x : Float32) : Float32 :=
  let absx := x.abs
  if absx < Float32.ofBits 0x3f490fdb then
    if absx < Float32.ofBits 0x393504f3 then x else tanKernel32 x.toFloat true  -- `sqrt(eps)/2`
  else if x != x then x
  else if absx == inf then nan
  else
    let r := remPio2F32 x
    tanKernel32 r.hi (r.n.toUInt64 &&& 1 == 0)

/-- Julia `asin(x::Float32)` (trig.jl:423-454); `NaN` for `|x| > 1`. -/
def asin (x : Float32) : Float32 :=
  let absx := x.abs
  if absx ≥ f32! 1.0 then
    if absx == f32! 1.0 then (if x < f32! 0.0 then -Float32.ofBits 0x3fc90fdb else Float32.ofBits 0x3fc90fdb)
    else nan  -- `Float32(π)/2`
  else if absx < f32! 0.5 then
    if absx < f32! 0.000244140625 then x else Float32.fma x (arcTRt32 (x * x)) x  -- `2f0^-12`
  else
    -- `asin_kernel(t::Float32, x)`: `Float32(π/2 - 2(s + s·tRt))` in `Float64`
    let t := (f32! 1.0 - absx) / f32! 2.0
    let s := t.toFloat.sqrt
    let tRt := (arcTRt32 t).toFloat
    let v := (f64! 1.5707963267948966 - f64! 2.0 * (s + s * tRt)).toFloat32
    if x < f32! 0.0 then -v else v

/-- Julia `acos(x::Float32)` (trig.jl:673-726); `NaN` for `|x| > 1`. -/
def acos (x : Float32) : Float32 :=
  let absx := x.abs
  if absx ≥ f32! 1.0 then
    if absx == f32! 1.0 then (if x > f32! 0.0 then f32! 0.0 else Float32.ofBits 0x40490fdb) else nan
  else if absx < f32! 0.5 then
    if absx < Float32.ofBits 0x32800000 then Float32.ofBits 0x3fc90fdb  -- `2f0^-26` → `Float32(π)/2`
    else f32! 1.5707962513 - (x - (f32! 7.5497894159e-08 - x * arcTRt32 (x * x)))
  else
    let z := (f32! 1.0 - absx) * f32! 0.5
    let zRz := arcTRt32 z
    let s := z.sqrt
    if x < f32! 0.0 then
      f32! 3.1415925026 - f32! 2.0 * (s + (zRz * s - f32! 7.5497894159e-08))
    else
      let df := Float32.ofBits (s.toBits &&& 0xfffff000)
      let c := (z - df * df) / (s + df)
      f32! 2.0 * (df + (zRz * s + c))

/-- Julia `atan(x::Float32)` (trig.jl:504-558). -/
def atan (x : Float32) : Float32 :=
  let absx := x.abs
  let neg := x < f32! 0.0
  if absx ≥ f32! 67108864.0 then  -- `2f0^26`
    if neg then -Float32.ofBits 0x3fc90fdb else Float32.ofBits 0x3fc90fdb
  else if absx < f32! 0.4375 then
    if absx < f32! 0.000244140625 then x  -- `2f0^-12`
    else x - x * atanPQ32 x
  else if absx < f32! 1.1875 then
    if absx < f32! 0.6875 then
      atanTail32 f32! 4.6364760399e-01 f32! 5.0121582440e-09
        ((f32! 2.0 * absx - f32! 1.0) / (f32! 2.0 + absx)) neg
    else atanTail32 f32! 7.8539812565e-01 f32! 3.7748947079e-08 ((absx - f32! 1.0) / (absx + f32! 1.0)) neg
  else if absx < f32! 2.4375 then
    atanTail32 f32! 9.8279368877e-01 f32! 3.4473217170e-08
      ((absx - f32! 1.5) / (f32! 1.0 + f32! 1.5 * absx)) neg
  else atanTail32 f32! 1.5707962513e+00 f32! 7.5497894159e-08 (f32! -1.0 / absx) neg

/-- Julia `atan(y::Float32, x::Float32)` (trig.jl:568-659). -/
def atan2 (y x : Float32) : Float32 :=
  let pi32 := Float32.ofBits 0x40490fdb
  let halfPi32 := Float32.ofBits 0x3fc90fdb
  if x != x then x
  else if y != y then y
  else if x == f32! 1.0 then atan y
  else
    let piLo := f32! -8.7422776573e-08
    if y == f32! 0.0 then
      if !signbit x then y else if !signbit y then pi32 else -pi32
    else
      -- `y ≠ 0`, and `x = ±0` only matters through `y`: the signs are comparisons
      let sx := x < f32! 0.0
      let sy := y < f32! 0.0
      if x == f32! 0.0 then (if sy then -halfPi32 else halfPi32)
      else if x.abs == inf then
        if y.abs == inf then
          let v := if sx then Float32.ofBits 0x4016cbe4 else Float32.ofBits 0x3f490fdb
          if sy then -v else v
        else
          let v := if sx then pi32 else f32! 0.0
          if sy then -v else v
      else if y.abs == inf then (if sy then -halfPi32 else halfPi32)
      else
        let pw (v : Float32) : UInt32 := v.toBits &&& 0x7fffffff
        let k : Int32 := (pw y - pw x).toInt32 >>> i32! 23
        if k > i32! 26 then
          let z := halfPi32 + f32! 0.5 * piLo
          if sy then -z else z
        else
          let z := if x < f32! 0.0 && k < i32! -26 then f32! 0.0 else atan (y / x).abs
          if !sx then (if sy then -z else z)
          else if !sy then pi32 - (z - piLo)
          else (z - piLo) - pi32

/-- Julia `sinpi(x::Float32)` (trig.jl:796-819). -/
def sinpi (x0 : Float32) : Float32 :=
  let x := x0.abs
  if !(x < inf) then (if x != x then x else nan)
  else if x ≥ maxintfloat then (if x0 < f32! 0.0 then f32! -0.0 else f32! 0.0)
  else
    let n := Math.round32 (f32! 2.0 * x)
    let rx := Float32.fma (f32! -0.5) n x
    let res := match n.toFloat.toInt64.toUInt64 &&& 3 with
      | 0 => sinpiKernel32 rx
      | 1 => cospiKernel32 rx
      | 2 => f32! 0.0 - sinpiKernel32 rx
      | _ => f32! 0.0 - cospiKernel32 rx
    if x0 < f32! 0.0 then -res else if x0 == f32! 0.0 then x0 else res

/-- Julia `cospi(x::Float32)` (trig.jl:829-851). -/
def cospi (x0 : Float32) : Float32 :=
  let x := x0.abs
  if !(x < inf) then (if x != x then x else nan)
  else if x ≥ maxintfloat then f32! 1.0
  else
    let n := Math.round32 (f32! 2.0 * x)
    let rx := Float32.fma (f32! -0.5) n x
    match n.toFloat.toInt64.toUInt64 &&& 3 with
    | 0 => cospiKernel32 rx
    | 1 => f32! 0.0 - sinpiKernel32 rx
    | 2 => f32! 0.0 - cospiKernel32 rx
    | _ => sinpiKernel32 rx

end F32

end JuliaBase
