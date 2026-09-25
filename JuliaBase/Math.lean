import JuliaBase.Num
import JuliaBase.MathTables

/-!
# Julia's own elementary functions, bit for bit

Julia does not call the C `libm` for `exp`, `exp2`, `exp10`, `expm1`, `log`, `log2`, `log10`,
`log1p` or `^`: it ships pure-Julia table-driven kernels (Tang's methods and ports of ARM's
optimized routines), and they differ from the platform `libm` (Lean's `Float.exp`, …) in the
last bit on a sizeable fraction of inputs. Printed digits, rounding-error scores and snapped
unit factors all depend on those bits, so this module replays Julia's kernels operation by
operation, for `Float64` (`F64.exp`, …) and `Float32` (`F32.exp`, …), together with Julia's
integer powers (`pow_body`, `power_by_squaring`, `literal_pow`).

**`muladd` is fused.** On the oracle machine (Apple aarch64, Julia 1.13) LLVM contracts every
`muladd` whose product has no other use into one `fmadd`, so the kernels use `Float.fma`
wherever Julia writes `muladd` or `evalpoly`/`@horner` (which expand to `muladd`). The one
exception is the last `muladd(x, y, err)` of `pow_body(::Float64, ::Integer)`, whose product
`x*y` is shared with the `ifelse` fallback and is therefore left unfused. Plain `*`/`+`
(`mf*0.693… + hi`) are never contracted. Measured against Julia 1.13 on 300 000 random
inputs across every function here (`Tests/JuliaBase/Math.lean` with `JULIABASE_FUZZ`): all
bit for bit, whereas unfusing every `muladd` (the earlier FieldConstants port) misses 5 of
28 814 `exp`/`exp2`/`exp10` results and 1 of 9 851 `pow_body` results, and the platform
`libm` misses 61 of about 9 600 `exp` and 24 of 9 479 `log` results.

Julia throws a `DomainError` for `log` of a negative number and for a negative base with a
non-integer exponent; these return `NaN`. Julia sources (1.13): `base/special/exp.jl`,
`base/special/log.jl`, `base/special/pow.jl`, `base/math.jl` (`two_mul`, `exthorner`),
`base/intfuncs.jl` (`power_by_squaring`, `literal_pow`).
-/

namespace JuliaBase

namespace Math

/-! ## Shared helpers -/

/-- Julia `Base.Math.two_mul(x, y)` on FMA hardware: `x*y` and its exact rounding error
`fma(x, y, -x*y)` (math.jl:54). -/
@[inline] def twoMul (x y : Float) : Float × Float :=
  let xy := x * y
  (xy, Float.fma x y (-xy))

/-- `Float32` `two_mul` (math.jl:62). -/
@[inline] def twoMul32 (x y : Float32) : Float32 × Float32 :=
  let xy := x * y
  (xy, Float32.fma x y (-xy))

/-- Two's-complement bits of an integer, modulo `2^64` (Julia's wrapping `Int64` shifts). -/
@[inline] def u64OfInt (i : Int) : UInt64 := (i.emod (2 ^ 64)).toNat.toUInt64

/-- Reinterpret a `UInt64` as a signed 64-bit integer. -/
@[inline] def i64OfU64 (u : UInt64) : Int :=
  if u < 0x8000000000000000 then u.toNat else (u.toNat : Int) - 2 ^ 64

/-- Julia `unsafe_trunc(Int64, x)` for the finite values the kernels pass (toward zero). -/
@[inline] def truncInt (x : Float) : Int := x.toInt64.toInt

/-- The bases of Julia's `exp_impl` and `_log`: `Val(2)`, `Val(:ℯ)`, `Val(10)`. -/
inductive Radix where
  /-- base 2 (`exp2`, `log2`) -/
  | two
  /-- base ℯ (`exp`, `log`) -/
  | e
  /-- base 10 (`exp10`, `log10`) -/
  | ten
  deriving DecidableEq, Repr, Inhabited

namespace Radix

/-! ### `Float64` exponential constants (exp.jl:9-60) -/

/-- `LogBo256INV(base, Float64)` = `256/log_b(2)`. -/
def inv256 : Radix → Float
  | two => 256.0 | e => 369.3299304675746 | ten => 850.4135922911647
/-- `LogBo256U(base, Float64)`: high part of `-log_b(2)/256`. -/
def lnU : Radix → Float
  | two => -0.00390625 | e => -0.002707606173999011 | ten => -0.0011758984204561784
/-- `LogBo256L(base, Float64)`: low part of `-log_b(2)/256`. -/
def lnL : Radix → Float
  | two => 0.0 | e => -6.327543041662719e-14 | ten => -1.0624811566412999e-13
/-- `MAX_EXP(base, Float64)`. -/
def maxExp : Radix → Float
  | two => 1024.0 | e => 709.7827128933841 | ten => 308.25471555991675
/-- `MIN_EXP(base, Float64)`. -/
def minExp : Radix → Float
  | two => -1075.0 | e => -745.1332191019412 | ten => -323.60724533877976
/-- `SUBNORM_EXP(base, Float64)` = `|log_b(floatmin)|`. -/
def subnormExp : Radix → Float
  | two => 1022.0 | e => 708.3964185322641 | ten => 307.6526555685887

/-- Julia `expm1b_kernel(base, x::Float64)` (exp.jl:83-94): `b^x - 1` on
`|x| ≤ log_b(2)/512`, `x * evalpoly(x, …)` with fused `muladd`s. -/
@[inline] def kernel : Radix → Float → Float
  | two, x => x * Float.fma x (Float.fma x (Float.fma x 0.009618129548366803 0.05550411502333161)
      0.24022650695910058) 0.6931471805599393
  | e, x => x * Float.fma x (Float.fma x (Float.fma x 0.04166666857598777 0.1666666857598779)
      0.4999999999999997) 0.9999999999999912
  | ten, x => x * Float.fma x (Float.fma x (Float.fma x 1.1712552025835192 2.034678825384765)
      2.6509490552391974) 2.3025850929940255

/-! ### `Float32` exponential constants -/

/-- `LogBINV(base, Float32)` = `1/log_b(2)`. -/
def inv32 : Radix → Float32
  | two => 1.0 | e => 1.442695 | ten => 3.321928
/-- `LogBU(base, Float32)`: high part of `-log_b(2)`. -/
def lnU32 : Radix → Float32
  | two => -1.0 | e => -0.69314575 | ten => -0.3010254
/-- `LogBL(base, Float32)`: low part of `-log_b(2)`. -/
def lnL32 : Radix → Float32
  | two => 0.0 | e => -1.4286068e-6 | ten => -4.605039e-6
/-- `MAX_EXP(base, Float32)`. -/
def maxExp32 : Radix → Float32
  | two => 128.0 | e => 88.72284 | ten => 38.53184
/-- `MIN_EXP(base, Float32)`. -/
def minExp32 : Radix → Float32
  | two => -150.0 | e => -103.97208 | ten => -45.1545
/-- `SUBNORM_EXP(base, Float32)`. -/
def subnormExp32 : Radix → Float32
  | two => 126.00001 | e => 87.33655 | ten => 37.92978

/-- Julia `expb_kernel(base, x::Float32)` (exp.jl:96-110): `b^x` on `|x| ≤ log_b(2)/2`, a
degree-7 `evalpoly` with fused `muladd`s. -/
@[inline] def kernel32 (b : Radix) (x : Float32) : Float32 :=
  let (c0, c1, c2, c3, c4, c5, c6, c7) : Float32 × Float32 × Float32 × Float32 × Float32 ×
      Float32 × Float32 × Float32 :=
    match b with
    | two => (1.0, 0.6931472, 0.2402265, 0.05550411, 0.009618025, 0.0013333423, 0.00015469732,
        1.5316464e-5)
    | e => (1.0, 1.0, 0.5, 0.16666667, 0.041666217, 0.008333249, 0.001394858, 0.00019924171)
    | ten => (1.0, 2.3025851, 2.650949, 2.0346787, 1.1712426, 0.53937745, 0.20788547, 0.06837386)
  Float32.fma x (Float32.fma x (Float32.fma x (Float32.fma x (Float32.fma x (Float32.fma x
    (Float32.fma x c7 c6) c5) c4) c3) c2) c1) c0

/-! ### Logarithm constants (log.jl:147-156) -/

/-- `logbU(Float64, base)`: high part of `1/log(b)`. -/
def logbU : Radix → Float
  | two => 1.4426950408889634 | e => 1.0 | ten => 0.4342944819032518
/-- `logbL(Float64, base)`: low part of `1/log(b)`. -/
def logbL : Radix → Float
  | two => 2.0355273740931033e-17 | e => 0.0 | ten => 1.098319650216765e-17
/-- `logb(Float32, base)`: `1/log(b)` as the `Float64` multiplier of the `Float32` kernels. -/
def logb32 : Radix → Float
  | two => 1.4426950408889634 | e => 1.0 | ten => 0.4342944819032518

end Radix

/-! ## `exp` (exp.jl) -/

/-- `MAGIC_ROUND_CONST(Float64) = 1.5·2^52`. -/
def magic : Float := 6.755399441055744e15

/-- Julia `table_unpack(N)`: `2^(j/256) ≈ jU + jL` for `j = N mod 256`, the table storing 52
high bits of the value and 8 extra bits of the correction. -/
@[inline] def tableUnpack (n : Int) : Float × Float :=
  let j : UInt64 := jTable[(n.emod 256).toNat]!
  (Float.ofBits ((0x3FF0000000000000 : UInt64) ||| (j &&& 0x000FFFFFFFFFFFFF)),
   Float.ofBits ((0x3C00000000000000 : UInt64) ||| (j >>> 8)))

/-- The argument reduction shared by the `exp_impl` methods: `N` (the low 32 bits of the
rounded `x·256/log_b(2)`, signed) and `r = x - N·log_b(2)/256` in two steps. -/
@[inline] def expReduce (x : Float) (b : Radix) : Int × Float :=
  let nf := Float.fma x b.inv256 magic
  let low := nf.toBits.toUInt32.toNat
  let n : Int := if low ≥ 2 ^ 31 then (low : Int) - 2 ^ 32 else low
  let nf := nf - magic
  let r := Float.fma nf b.lnU x
  let r := Float.fma nf b.lnL r
  (n, r)

/-- Scale by `2^k` through the exponent bits (`reinterpret(T, (Int64(k) << 52) + bits)`). -/
@[inline] def scale2k (k : Int) (small : Float) : Float :=
  Float.ofBits ((u64OfInt k <<< 52) + small.toBits)

/-- Julia `exp_impl(x::Float64, base)` (exp.jl:207-231). -/
def expImpl (x : Float) (b : Radix) : Float :=
  let (n, r) := expReduce x b
  let k := Int.fdiv n 256
  let (jU, jL) := tableUnpack n
  let small := Float.fma jU (b.kernel r) jL + jU
  if !(x.abs ≤ b.subnormExp) then
    if x.isNaN then x
    else if x ≥ b.maxExp then F64.inf
    else if x ≤ b.minExp then 0.0
    else if k ≤ -53 then
      Float.ofBits ((u64OfInt (k + 53) <<< 52) + small.toBits) * 1.1102230246251565e-16
    else scale2k k small
  else scale2k k small

/-- Julia `exp_impl(x::Float64, xlo::Float64, base)` (exp.jl:233-259): `b^(x + xlo)`, the
last step of `^(::Float64, ::Float64)`. -/
def expImpl2 (x xlo : Float) (b : Radix) : Float :=
  let (n, r) := expReduce x b
  let k := Int.fdiv n 256
  let (jU, jL) := tableUnpack n
  let kern := b.kernel r
  let verySmall := Float.fma kern (jU * xlo) jL
  -- `canonicalize2(1.0, kern)`
  let hi := 1.0 + kern
  let lo := (1.0 - hi) + kern
  let small := Float.fma jU hi (Float.fma jU (lo + xlo) verySmall)
  if !(x.abs ≤ b.subnormExp) then
    if x.isNaN then x
    else if x ≥ b.maxExp then F64.inf
    else if x ≤ b.minExp then 0.0
    else if k ≤ -53 then
      Float.ofBits ((u64OfInt (k + 53) <<< 52) + small.toBits) * 1.1102230246251565e-16
    else if k == 1024 then (small * 2.0) * 8.98846567431158e307
    else scale2k k small
  else scale2k k small

/-- Julia `round(x::Float32)` (to nearest, ties to even; exact through `Float64`). -/
@[inline] def round32 (x : Float32) : Float32 := (F64.round x.toFloat).toFloat32

/-- Julia `exp_impl(x::Float32, base)` (exp.jl:276-295). -/
def expImpl32 (x : Float32) (b : Radix) : Float32 :=
  let nf := round32 (x * b.inv32)
  let n : Int := truncInt nf.toFloat
  let r := Float32.fma nf b.lnU32 x
  let r := Float32.fma nf b.lnL32 r
  let small := b.kernel32 r
  if x > b.maxExp32 then Float32.ofBits 0x7F800000
  else if x < b.minExp32 then 0.0
  else
    let (power, small) := if x ≤ -b.subnormExp32 then (n + 127 + 24, small * 5.9604645e-8)
      else (n + 127, small)
    let (power, small) := if n == 128 then (power - 1, small * 2.0) else (power, small)
    small * Float32.ofBits ((power * 8388608).emod 4294967296).toNat.toUInt32

/-! ## `expm1` (exp.jl:412-472) -/

/-- Julia `exthorner(x, (1, ½, p))` (math.jl:215): Horner's scheme for `1 + x/2 + x²p` with
a compensated low part, `(hi, lo)`. -/
@[inline] def exthorner (x p : Float) : Float × Float :=
  let step (c hi lo : Float) : Float × Float :=
    let (prod, err) := twoMul hi x
    let hi' := c + prod
    (hi', Float.fma lo x ((prod - (hi' - c)) + err))
  let (hi, lo) := step 0.5 p 0.0
  step 1.0 hi lo

/-- `Float32` `exthorner`. -/
@[inline] def exthorner32 (x p : Float32) : Float32 × Float32 :=
  let step (c hi lo : Float32) : Float32 × Float32 :=
    let (prod, err) := twoMul32 hi x
    let hi' := c + prod
    (hi', Float32.fma lo x ((prod - (hi' - c)) + err))
  let (hi, lo) := step 0.5 p 0.0
  step 1.0 hi lo

/-- Julia `expm1_small(x::Float64)` for `log(3/4) ≤ x ≤ log(5/4)`. -/
def expm1Small (x : Float) : Float :=
  let p := Float.fma x (Float.fma x (Float.fma x (Float.fma x (Float.fma x (Float.fma x (Float.fma x
    (Float.fma x 2.4360682937111612e-8 2.758218402815439e-7) 2.7558212415361945e-6)
    2.480157691845342e-5) 0.00019841269447671544) 0.001388888889068783) 0.008333333333401227)
    0.04166666666666556) 0.16666666666666632
  let (hi, lo) := exthorner x p
  Float.fma x hi (x * lo)

/-- Julia `expm1_small(x::Float32)`. -/
def expm1Small32 (x : Float32) : Float32 :=
  let p := Float32.fma x (Float32.fma x (Float32.fma x (Float32.fma x 0.0001933096 0.0013908712)
    0.008333682) 0.041666627) 0.16666666
  let (hi, lo) := exthorner32 x p
  Float32.fma x hi (x * lo)

/-- Julia `expm1(x::Float64)` (exp.jl:432-455). -/
def expm1 (x : Float) : Float :=
  if -0.2876820724517809 ≤ x && x ≤ 0.22314355131420976 then expm1Small x
  else if x.isNaN then x
  else if x > 709.7827128933845 then F64.inf
  else if x < -37.42994775023705 then -1.0
  else
    let (n, r) := expReduce x .e
    let k := Int.fdiv n 256
    let (jU, jL) := tableUnpack n
    let p := Radix.e.kernel r
    let twopk := Float.ofBits (u64OfInt ((1023 + k) * 2 ^ 52))
    let twopnk := Float.ofBits (u64OfInt ((1023 - k) * 2 ^ 52))
    if k ≥ 106 then Float.ofBits (u64OfInt ((1022 + k) * 2 ^ 52)) * (jU + Float.fma jU p jL) * 2
    else if k ≥ 53 then twopk * (jU + Float.fma jU p (jL - twopnk))
    else if k ≤ -2 then twopk * (jU + Float.fma jU p jL) - 1
    else twopk * ((jU - twopnk) + Float.fma jU p jL)

/-- Julia `expm1(x::Float32)` (exp.jl:457-472): the reduction in `Float64`. -/
def expm1F32 (x : Float32) : Float32 :=
  if x > 88.72284 then Float32.ofBits 0x7F800000
  else if x < -17.32868 then -1.0
  else if -0.2876821 ≤ x && x ≤ 0.22314355 then expm1Small32 x
  else if x.isNaN then x
  else
    let x := x.toFloat
    let nf := F64.round (x * 1.4426950408889634)
    let n := truncInt nf
    let r := Float.fma nf (-0.6931471805599453) x
    let hi := Float.fma r (Float.fma r (Float.fma r (Float.fma r (Float.fma r (Float.fma r
      0.0002004037059220124 0.0013966479175977883) 0.008332997481506921) 0.041666183019487026)
      0.16666667546642386) 0.5) 1.0
    let smallPart := r * hi
    let twopk := Float.ofBits (u64OfInt ((n + 1023) * 2 ^ 52))
    (Float.fma twopk smallPart (twopk - 1.0)).toFloat32

/-! ## `log` (log.jl) -/

/-- Julia `log_proc1(y, mf, F, f, base)` for `Float64` (log.jl:158-187): the table-driven
case, `jp = 128F - 127` indexing `t_log_Float64`. -/
@[inline] def logProc1 (y mf bigF f : Float) (b : Radix) : Float :=
  let jp := (128.0 * bigF).toUInt64.toNat - 127
  let (hb, lb) := logTable64[jp - 1]!
  let lHi := mf * 0.6931471805601177 + Float.ofBits hb
  let lLo := mf * (-1.7239444525614835e-13) + Float.ofBits lb
  let u := (2.0 * f) / (y + bigF)
  let v := u * u
  let q := u * v * Float.fma v 0.012500053168098584 0.08333333333303913
  Float.fma b.logbU lHi (Float.fma b.logbU (u + (q + lLo)) (b.logbL * lHi))

/-- Julia `log_proc2(f, base)` for `Float64` (log.jl:190-213): the case `x ≈ 1`. -/
@[inline] def logProc2 (f : Float) (b : Radix) : Float :=
  let g := 1.0 / (2.0 + f)
  let u := 2.0 * f * g
  let v := u * u
  let q := u * v * Float.fma v (Float.fma v (Float.fma v 0.0004348877777076146 0.0022321399879194482)
      0.012500000003771751) 0.08333333333333179
  Float.fma b.logbU u (Float.fma b.logbL u (b.logbU * Float.fma (Float.fma (-u) f (2.0 * (f - u))) g q))

/-- Julia `_log(x::Float64, base, func)` (log.jl:264-297). -/
def logImpl (x : Float) (b : Radix) : Float :=
  if x > 0.0 then
    if x == F64.inf then x
    else if 0.9394130628134757 < x && x < 1.0644944589178595 then logProc2 (x - 1.0) b
    else
      let xu := x.toBits
      let m := ((xu >>> 52) &&& 0x7FF).toNat
      let (xu, m) : UInt64 × Int :=
        if m == 0 then
          let xu' := (x * 1.8014398509481984e16).toBits
          (xu', (((xu' >>> 52) &&& 0x7FF).toNat : Int) - 54)
        else (xu, m)
      let y := Float.ofBits ((xu &&& 0x000FFFFFFFFFFFFF) ||| 0x3FF0000000000000)
      let mf := Float.ofInt (m - 1023)
      let bigF := (y + 3.5184372088832e13) - 3.5184372088832e13
      logProc1 y mf bigF (y - bigF) b
  else if x == 0.0 then -F64.inf
  else F64.nan

/-- Julia `log_proc1` for `Float32` (log.jl:216-236): the table sum in `Float64`, rounded once. -/
@[inline] def logProc1F32 (y mf bigF f : Float32) (b : Radix) : Float32 :=
  let jp := (128.0 * bigF).toUInt32.toNat - 127
  let l := mf.toFloat * 0.6931471805599453 + Float.ofBits logTable32[jp - 1]!
  let u := (2.0 * f) / (y + bigF)
  let v := u * u
  let q := u * v * 0.08333351
  (b.logb32 * (l + (u + q).toFloat)).toFloat32

/-- Julia `log_proc2` for `Float32` (log.jl:239-255): `u` in `Float64`. -/
@[inline] def logProc2F32 (f : Float32) (b : Radix) : Float32 :=
  let u64 := (2.0 * f).toFloat / (2.0 + f.toFloat)
  let u := u64.toFloat32
  let v := u * u
  let q := u * v * Float32.fma v 0.012512346 0.08333332
  (b.logb32 * (u64 + q.toFloat)).toFloat32

/-- Julia `_log(x::Float32, base, func)` (log.jl:299-332). -/
def logImpl32 (x : Float32) (b : Radix) : Float32 :=
  if x > 0.0 then
    if x.isInf then x
    else if 0.939413 < x && x < 1.0644945 then logProc2F32 (x - 1.0) b
    else
      let xu := x.toBits
      let m := ((xu >>> 23) &&& 0xFF).toNat
      let (xu, m) : UInt32 × Int :=
        if m == 0 then
          let xu' := (x * 3.3554432e7).toBits
          (xu', (((xu' >>> 23) &&& 0xFF).toNat : Int) - 25)
        else (xu, m)
      let y := Float32.ofBits ((xu &&& 0x007FFFFF) ||| 0x3F800000)
      let mf := Float32.ofInt (m - 127)
      let bigF := (y + 65536.0) - 65536.0
      logProc1F32 y mf bigF (y - bigF) b
  else if x == 0.0 then Float32.ofBits 0xFF800000
  else Float32.ofBits 0x7FC00000

/-- Julia `log1p(x::Float64)` (log.jl:335-366). -/
def log1p (x : Float) : Float :=
  if x > -1.0 then
    if x == F64.inf then x
    else if -1.1102230246251565e-16 < x && x < 1.1102230246251565e-16 then x
    else if -0.06058693718652422 < x && x < 0.06449445891785943 then logProc2 x .e
    else
      let z := 1.0 + x
      let zu := z.toBits
      let s := Float.ofBits (0x7FE0000000000000 - (zu &&& 0xFFF0000000000000))
      let m : Int := (((zu >>> 52) &&& 0x7FF).toNat : Int) - 1023
      let c := if m > 0 then 1.0 - (z - x) else x - (z - 1.0)
      let y := Float.ofBits ((zu &&& 0x000FFFFFFFFFFFFF) ||| 0x3FF0000000000000)
      let bigF := (y + 3.5184372088832e13) - 3.5184372088832e13
      logProc1 y (Float.ofInt m) bigF ((y - bigF) + c * s) .e
  else if x == -1.0 then -F64.inf
  else F64.nan

/-- Julia `log1p(x::Float32)` (log.jl:368-398). -/
def log1pF32 (x : Float32) : Float32 :=
  if x > -1.0 then
    if x.isInf then x
    else if -5.9604645e-8 < x && x < 5.9604645e-8 then x
    else if -0.06058694 < x && x < 0.06449446 then logProc2F32 x .e
    else
      let z := 1.0 + x
      let zu := z.toBits
      let s := Float32.ofBits (0x7F000000 - (zu &&& 0xFF800000))
      let m : Int := (((zu >>> 23) &&& 0xFF).toNat : Int) - 127
      let c := if m > 0 then 1.0 - (z - x) else x - (z - 1.0)
      let y := Float32.ofBits ((zu &&& 0x007FFFFF) ||| 0x3F800000)
      let bigF := (y + 65536.0) - 65536.0
      logProc1F32 y (Float32.ofInt m) bigF ((y - bigF) + s * c) .e
  else if x == -1.0 then Float32.ofBits 0xFF800000
  else Float32.ofBits 0x7FC00000

/-- Julia `_log_ext(xu)` (log.jl:559-587, after ARM's `pow.c`): `log(x)` as an unevaluated
sum `hi + lo` with about 68 bits, for `^(::Float64, ::Float64)`. -/
def logExt (xu : UInt64) : Float × Float :=
  let tmpU := xu - 0x3fe6955500000000
  let tmp := i64OfU64 tmpU
  let z := Float.ofBits (xu - (tmpU &&& 0xfff0000000000000))
  let k := Float.ofInt (Int.fdiv tmp (2 ^ 52))
  let idx := ((Int.fdiv tmp (2 ^ 45)).emod 128).toNat
  let t := logTableT[idx]!
  let logctail := Float.ofBits logTableTail[idx]!
  let invc := Float.ofBits (((t &&& 0xff) ||| 0x1ff00) <<< 45)
  let logc := Float.ofBits (t &&& (~~~ (0xff : UInt64)))
  let r := Float.fma z invc (-1.0)
  let t1 := Float.fma k 0.6931471805598903 logc
  let t2 := t1 + r
  let lo1 := Float.fma k 5.497923018708371e-14 logctail
  let lo2 := t1 - t2 + r
  let ar := -0.5 * r
  let (ar2, lo3) := twoMul r ar
  let hi := t2 + ar2
  let lo4 := t2 - hi + ar2
  let p := Float.fma r (Float.fma r (Float.fma r (Float.fma r (Float.fma r 0.25001038159188854
      (-0.28572740711487526)) 0.33333333317438696) (-0.3999999997661988)) 0.5000000000000007)
      (-0.6666666666666679)
  let lo := lo1 + lo2 + lo3 + Float.fma (r * ar2) p lo4
  (hi, lo)

/-! ## Powers (pow.jl, intfuncs.jl) -/

/-- Julia `use_power_by_squaring(n)` = `-2^12 ≤ n ≤ 3·2^13` (pow.jl:1). -/
@[inline] def usePowerBySquaring (n : Int) : Bool := -4096 ≤ n && n ≤ 24576

/-- The squaring loop of `pow_body(x::Float64, n::Integer)`, fuelled by the exponent: the
error `muladd`s are fused, the final `muladd(x, y, err)` is not (its product is shared). -/
def powLoop (x xnlo y ynlo : Float) (n : Nat) : Nat → Float
  | 0 => x * y
  | fuel + 1 =>
    if n > 1 then
      let (y, ynlo) :=
        if n % 2 == 1 then
          let err := Float.fma y xnlo (x * ynlo)
          let (y', ynlo') := twoMul x y
          (y', ynlo' + err)
        else (y, ynlo)
      let err := x * 2.0 * xnlo
      let (x', xnlo') := twoMul x x
      powLoop x' (xnlo' + err) y ynlo (n / 2) fuel
    else
      let err := Float.fma y xnlo (x * ynlo)
      if x.isFinite && err.isFinite then x * y + err else x * y

/-- Julia `pow_body(x::Float64, n::Integer)` (pow.jl:120-146): compensated power by squaring,
the `x^n` of Julia for `-2^12 ≤ n ≤ 3·2^13` (more accurate than repeated multiplication). -/
def powBody (x : Float) (n : Int) : Float :=
  if n == 3 then x * x * x
  else if n < 0 then
    let rx := 1.0 / x
    if n == -2 then rx * rx
    else
      let xnlo := if x.isFinite then -(Float.fma x rx (-1.0)) * rx else -0.0
      powLoop rx xnlo 1.0 0.0 n.natAbs (n.natAbs + 1)
  else powLoop x (-0.0) 1.0 0.0 n.toNat (n.toNat + 1)

/-- Julia `pow_body(x::Float64, y::Float64)` for positive `x` (pow.jl:91-104):
`exp(y·log(x))` through the 68-bit `_log_ext` and the two-part `exp_impl`. -/
def powBodyFloat (x y : Float) : Float :=
  let xu : UInt64 := x.toBits
  let xu : UInt64 :=
    if xu < 0x0010000000000000 then
      ((x * 4.503599627370496e15).toBits &&& (0x7FFFFFFFFFFFFFFF : UInt64)) - ((52 : UInt64) <<< 52)
    else xu
  let (logxhi, logxlo) := logExt xu
  let (xyhi, xylo) := twoMul logxhi y
  let xylo := Float.fma logxlo y xylo
  let hi := xyhi + xylo
  expImpl2 hi (xylo - (hi - xyhi)) .e

/-- Julia `Base.power_by_squaring(x::Float64, p)` for `p ≥ 0` (intfuncs.jl:394), the
multiplication order Julia uses (e.g. for `Irrational^Integer`). -/
@[inline] def powerBySquaring (x : Float) (p : Nat) : Float := JuliaBase.powBySquaring (· * ·) 1.0 x p

/-- `Float32` `power_by_squaring` in `Float64` (what `pow_body(::Float32, ::Int32)` runs). -/
@[inline] def powBody32 (x : Float32) (n : Int) : Float32 :=
  if n == -2 then let i := 1.0 / x; i * i
  else if n == 3 then x * x * x
  else if n < 0 then (powerBySquaring (1.0 / x.toFloat) n.natAbs).toFloat32
  else (powerBySquaring x.toFloat n.toNat).toFloat32

end Math

open Math

/-! ## `Float64` entry points -/

namespace F64

/-- Julia `exp(x::Float64)` (exp.jl, Tang's method with a 256-entry table). -/
def exp (x : Float) : Float := expImpl x .e

/-- Julia `exp2(x::Float64)`. -/
def exp2 (x : Float) : Float := expImpl x .two

/-- Julia `exp10(x::Float64)`. -/
def exp10 (x : Float) : Float := expImpl x .ten

/-- Julia `expm1(x::Float64)` = `eˣ - 1`, accurate near `0` (exp.jl:432). -/
def expm1 (x : Float) : Float := Math.expm1 x

/-- Julia `log(x::Float64)` (log.jl, Tang's table-driven method). Negative arguments (a
`DomainError` in Julia) give `NaN`. -/
def log (x : Float) : Float := logImpl x .e

/-- Julia `log2(x::Float64)`. -/
def log2 (x : Float) : Float := logImpl x .two

/-- Julia `log10(x::Float64)`. -/
def log10 (x : Float) : Float := logImpl x .ten

/-- Julia `log1p(x::Float64)` = `log(1 + x)`, accurate near `0` (log.jl:335); `NaN` for
`x < -1` (Julia throws). -/
def log1p (x : Float) : Float := Math.log1p x

/-- Julia `pow_body(x::Float64, n::Integer)`: the compensated power by squaring. -/
@[inline] def powBody (x : Float) (n : Int) : Float := Math.powBody x n

/-- Julia `^(x::Float64, n::Integer)` (pow.jl:58-75): compensated squaring for
`-2^12 ≤ n ≤ 3·2^13`, otherwise `exp(n·log|x|)` with the sign of an odd power. -/
def powInt (x : Float) (n : Int) : Float :=
  if n == 0 then 1.0
  else if usePowerBySquaring n then Math.powBody x n
  else
    let neg := x < 0 && n % 2 != 0
    let ax := x.abs
    let y := Float.ofInt n
    if Float.ofInt (F64.toIntTrunc y) == y && F64.toIntTrunc y == n then
      copysign (powBodyFloat ax y) (if neg then -1.0 else 1.0)
    else
      -- `n` is not a `Float64`: split off `n % 1024` (Julia's `rem`, sign of `n`)
      let n2 := n.tmod 1024
      powBodyFloat ax (Float.ofInt (n - n2)) * copysign (Math.powBody ax n2) (if neg then -1.0 else 1.0)

/-- Julia `^(x::Float64, y::Float64)` (pow.jl:7-30). A negative base with a non-integer
exponent (Julia `DomainError`) gives `NaN`. -/
def pow (x y : Float) : Float :=
  if x.toBits == (1.0 : Float).toBits then 1.0
  else
    let y := if !(y.abs < 6.917529027641082e18) then
        (if y.isNaN then y else if y > 0 then 6.917529027641082e18 else -6.917529027641082e18)
      else y
    if y.isNaN then y
    else
      let yint : Int := truncInt y
      let yisint := y == Float.ofInt yint
      if yisint && yint == 0 then 1.0
      else if yisint && usePowerBySquaring yint then Math.powBody x yint
      else if x == 0.0 then (if y > 0 then 0.0 else inf)
      else if x < 0 && !yisint then nan
      else
        let s : Float := if x < 0 && yint % 2 != 0 then -1.0 else 1.0
        if !x.isFinite then
          -- `copysign(x, s) * (y > 0 || isnan(x))`, with Julia's `Float * false = ±0.0`
          let c := copysign x s
          if y > 0 || x.isNaN then c else copysign 0.0 c
        else copysign (powBodyFloat x.abs y) s

/-- Julia `Base.power_by_squaring(x::Float64, p)` for `p ≥ 0` (intfuncs.jl:394). -/
@[inline] def powerBySquaring (x : Float) (p : Nat) : Float := Math.powerBySquaring x p

/-- Julia `literal_pow(^, x, Val(k))` for `x::Float64` (intfuncs.jl:465-474): the lowering of
`x^k` with a literal `k`, `x*x` for `2`, `x*x*x` for `3`, `inv(x)` for `-1`, otherwise `x^k`. -/
def literalPow (x : Float) (k : Int) : Float :=
  match k with
  | 0 => 1.0
  | 1 => x
  | 2 => x * x
  | 3 => x * x * x
  | -1 => 1.0 / x
  | _ => powInt x k

/-- Julia `Base.Math.two_mul(x, y)`: `hi + lo = x·y` exactly (barring overflow). -/
@[inline] def twoMul (x y : Float) : Float × Float := Math.twoMul x y

end F64

/-! ## `Float32` entry points -/

namespace F32

/-- Julia `exp(x::Float32)` (exp.jl:276). -/
def exp (x : Float32) : Float32 := expImpl32 x .e

/-- Julia `exp2(x::Float32)`. -/
def exp2 (x : Float32) : Float32 := expImpl32 x .two

/-- Julia `exp10(x::Float32)`. -/
def exp10 (x : Float32) : Float32 := expImpl32 x .ten

/-- Julia `expm1(x::Float32)` (exp.jl:457). -/
def expm1 (x : Float32) : Float32 := expm1F32 x

/-- Julia `log(x::Float32)` (log.jl:299); `NaN` for negative arguments. -/
def log (x : Float32) : Float32 := logImpl32 x .e

/-- Julia `log2(x::Float32)`. -/
def log2 (x : Float32) : Float32 := logImpl32 x .two

/-- Julia `log10(x::Float32)`. -/
def log10 (x : Float32) : Float32 := logImpl32 x .ten

/-- Julia `log1p(x::Float32)` (log.jl:368). -/
def log1p (x : Float32) : Float32 := log1pF32 x

/-- Julia `pow_body(x::Float32, y) = Float32(exp2(log2(abs(Float64(x))) * y))` (pow.jl:106). -/
@[inline] def powBodyFloat (x : Float32) (y : Float) : Float32 :=
  (F64.exp2 (F64.log2 x.toFloat.abs * y)).toFloat32

/-- Julia `^(x::Float32, n::Integer)` (pow.jl:79-89): `power_by_squaring` in `Float64` for
`-2^12 ≤ n ≤ 3·2^13` (`-2` and `3` special-cased in `Float32`), otherwise
`exp2(n·log2|x|)`. **Defect fixed:** for large odd `n` and negative `x` Julia computes the
sign `s` and drops it (`(-1f0)^100001 == 1f0`); here the sign is applied
(`oracle/defects.toml` `float32-pow-large-odd-sign`). -/
def powInt (x : Float32) (n : Int) : Float32 :=
  let n := if n < -2147483648 then -2147483648 else if n > 2147483647 then 2147483647 else n
  if n == 0 then 1.0
  else if usePowerBySquaring n then powBody32 x n
  else
    let r := powBodyFloat x.abs (Float.ofInt n)
    if x < 0 && n % 2 != 0 then -r else r

/-- Julia `^(x::Float32, y::Float32)` (pow.jl:34-55). A negative base with a non-integer
exponent (Julia `DomainError`) gives `NaN`. -/
def pow (x y : Float32) : Float32 :=
  if x == 1.0 then 1.0
  else
    let maxExp : Float32 := 1744830464.0  -- `0x1.Ap30`
    let y := if !(y.abs < maxExp) then (if y.isNaN then y else if y > 0 then maxExp else -maxExp) else y
    if y.isNaN then y
    else
      let yint : Int := truncInt y.toFloat
      let yisint := y.toFloat == Float.ofInt yint
      if yisint && yint == 0 then 1.0
      else if yisint && usePowerBySquaring yint then powBody32 x yint
      else if x < 0 && !yisint then Float32.ofBits 0x7FC00000
      else
        let neg := x < 0 && yint % 2 != 0
        let c := if neg then -x.abs else x.abs  -- `copysign(x, s)`
        if !x.isFinite then (if y > 0 || x.isNaN then c else copysign 0.0 c)
        else
          let r := powBodyFloat x.abs y.toFloat
          if neg then -r else r

/-- Julia `literal_pow(^, x, Val(k))` for `x::Float32`. -/
def literalPow (x : Float32) (k : Int) : Float32 :=
  match k with
  | 0 => 1.0
  | 1 => x
  | 2 => x * x
  | 3 => x * x * x
  | -1 => 1.0 / x
  | _ => powInt x k

end F32

end JuliaBase
