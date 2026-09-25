import JuliaBase.Num
import JuliaBase.FloatLit
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

**Performance.** Every constant is an `f64!`/`f32!` literal (`JuliaBase.FloatLit`): plain
decimal literals of 17 digits are parsed through bignums at run time whenever the code generator
fails to hoist them, which made `F64.log` cost about 3 µs. Integer plumbing is `Int64`/`UInt64`
(never `Int`/`Nat` powers of two), and the tables are unboxed `FloatArray`s. What remains is the
out-of-line `Float.toBits`/`ofBits` runtime calls; `docs/PERF.md` has the numbers (2.5-3.5×
Julia's own kernels, 3-5× the platform `libm`).

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

/-- Julia `reinterpret(Float64, (k << 52) + bits)`: add `k` to the biased exponent of `x`
through the bit pattern (wrapping `Int64` arithmetic, as in Julia). -/
@[inline] def addExponentBits (k : Int64) (x : Float) : Float :=
  Float.ofBits ((k.toUInt64 <<< 52) + x.toBits)

/-- `2^k` from its bits, `reinterpret(Float64, (1023 + k) << 52)`. -/
@[inline] def twoPow (k : Int64) : Float := Float.ofBits ((1023 + k).toUInt64 <<< 52)

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
@[inline] def inv256 : Radix → Float
  | two => f64! 256.0 | e => f64! 369.3299304675746 | ten => f64! 850.4135922911647
/-- `LogBo256U(base, Float64)`: high part of `-log_b(2)/256`. -/
@[inline] def lnU : Radix → Float
  | two => f64! -0.00390625 | e => f64! -0.002707606173999011 | ten => f64! -0.0011758984204561784
/-- `LogBo256L(base, Float64)`: low part of `-log_b(2)/256`. -/
@[inline] def lnL : Radix → Float
  | two => f64! 0.0 | e => f64! -6.327543041662719e-14 | ten => f64! -1.0624811566412999e-13
/-- `MAX_EXP(base, Float64)`. -/
@[inline] def maxExp : Radix → Float
  | two => f64! 1024.0 | e => f64! 709.7827128933841 | ten => f64! 308.25471555991675
/-- `MIN_EXP(base, Float64)`. -/
@[inline] def minExp : Radix → Float
  | two => f64! -1075.0 | e => f64! -745.1332191019412 | ten => f64! -323.60724533877976
/-- `SUBNORM_EXP(base, Float64)` = `|log_b(floatmin)|`. -/
@[inline] def subnormExp : Radix → Float
  | two => f64! 1022.0 | e => f64! 708.3964185322641 | ten => f64! 307.6526555685887

/-- Julia `expm1b_kernel(base, x::Float64)` (exp.jl:83-94): `b^x - 1` on
`|x| ≤ log_b(2)/512`, `x * evalpoly(x, …)` with fused `muladd`s. -/
@[inline] def kernel : Radix → Float → Float
  | two, x => x * Float.fma x (Float.fma x (Float.fma x f64! 0.009618129548366803 f64! 0.05550411502333161)
      f64! 0.24022650695910058) f64! 0.6931471805599393
  | e, x => x * Float.fma x (Float.fma x (Float.fma x f64! 0.04166666857598777 f64! 0.1666666857598779)
      f64! 0.4999999999999997) f64! 0.9999999999999912
  | ten, x => x * Float.fma x (Float.fma x (Float.fma x f64! 1.1712552025835192 f64! 2.034678825384765)
      f64! 2.6509490552391974) f64! 2.3025850929940255

/-! ### `Float32` exponential constants -/

/-- `LogBINV(base, Float32)` = `1/log_b(2)`. -/
@[inline] def inv32 : Radix → Float32
  | two => f32! 1.0 | e => f32! 1.442695 | ten => f32! 3.321928
/-- `LogBU(base, Float32)`: high part of `-log_b(2)`. -/
@[inline] def lnU32 : Radix → Float32
  | two => f32! -1.0 | e => f32! -0.69314575 | ten => f32! -0.3010254
/-- `LogBL(base, Float32)`: low part of `-log_b(2)`. -/
@[inline] def lnL32 : Radix → Float32
  | two => f32! 0.0 | e => f32! -1.4286068e-6 | ten => f32! -4.605039e-6
/-- `MAX_EXP(base, Float32)`. -/
@[inline] def maxExp32 : Radix → Float32
  | two => f32! 128.0 | e => f32! 88.72284 | ten => f32! 38.53184
/-- `MIN_EXP(base, Float32)`. -/
@[inline] def minExp32 : Radix → Float32
  | two => f32! -150.0 | e => f32! -103.97208 | ten => f32! -45.1545
/-- `SUBNORM_EXP(base, Float32)`. -/
@[inline] def subnormExp32 : Radix → Float32
  | two => f32! 126.00001 | e => f32! 87.33655 | ten => f32! 37.92978

/-- Julia `expb_kernel(base, x::Float32)` (exp.jl:96-110): `b^x` on `|x| ≤ log_b(2)/2`, a
degree-7 `evalpoly` with fused `muladd`s. -/
@[inline] def kernel32 (b : Radix) (x : Float32) : Float32 :=
  let (c0, c1, c2, c3, c4, c5, c6, c7) : Float32 × Float32 × Float32 × Float32 × Float32 ×
      Float32 × Float32 × Float32 :=
    match b with
    | two => (f32! 1.0, f32! 0.6931472, f32! 0.2402265, f32! 0.05550411, f32! 0.009618025, f32! 0.0013333423, f32! 0.00015469732,
        f32! 1.5316464e-5)
    | e => (f32! 1.0, f32! 1.0, f32! 0.5, f32! 0.16666667, f32! 0.041666217, f32! 0.008333249, f32! 0.001394858, f32! 0.00019924171)
    | ten => (f32! 1.0, f32! 2.3025851, f32! 2.650949, f32! 2.0346787, f32! 1.1712426, f32! 0.53937745, f32! 0.20788547, f32! 0.06837386)
  Float32.fma x (Float32.fma x (Float32.fma x (Float32.fma x (Float32.fma x (Float32.fma x
    (Float32.fma x c7 c6) c5) c4) c3) c2) c1) c0

/-! ### Logarithm constants (log.jl:147-156) -/

/-- `logbU(Float64, base)`: high part of `1/log(b)`. -/
@[inline] def logbU : Radix → Float
  | two => f64! 1.4426950408889634 | e => f64! 1.0 | ten => f64! 0.4342944819032518
/-- `logbL(Float64, base)`: low part of `1/log(b)`. -/
@[inline] def logbL : Radix → Float
  | two => f64! 2.0355273740931033e-17 | e => f64! 0.0 | ten => f64! 1.098319650216765e-17
/-- `logb(Float32, base)`: `1/log(b)` as the `Float64` multiplier of the `Float32` kernels. -/
@[inline] def logb32 : Radix → Float
  | two => f64! 1.4426950408889634 | e => f64! 1.0 | ten => f64! 0.4342944819032518

end Radix

/-! ## Unpacked tables

The kernels read the tables as unboxed `FloatArray`s, decoded once when the module is
initialized: a `Float.ofBits` is an out-of-line runtime call in compiled Lean, too costly to
repeat per lookup. -/

/-- Decode a table of bit patterns into a packed `FloatArray`. -/
def floatsOfBits (f : UInt64 → UInt64) (t : Array UInt64) : FloatArray :=
  t.foldl (fun a b => a.push (Float.ofBits (f b))) (FloatArray.emptyWithCapacity t.size)

/-- `jU` of `table_unpack`: `2^(j/256)` rounded down to 52 bits. -/
def jTableU : FloatArray :=
  floatsOfBits (fun j => (0x3FF0000000000000 : UInt64) ||| (j &&& 0x000FFFFFFFFFFFFF)) jTable

/-- `jL` of `table_unpack`: the 8 extra bits of the correction. -/
def jTableL : FloatArray := floatsOfBits (fun j => (0x3C00000000000000 : UInt64) ||| (j >>> 8)) jTable

/-- `t_log_Float64` high parts. -/
def logTable64Hi : FloatArray := floatsOfBits id (logTable64.map (·.1))

/-- `t_log_Float64` low parts. -/
def logTable64Lo : FloatArray := floatsOfBits id (logTable64.map (·.2))

/-- `t_log_Float32` as `Float64` values. -/
def logTable32F : FloatArray := floatsOfBits id logTable32

/-- `logctail` of `t_log_table_compact`. -/
def logTableTailF : FloatArray := floatsOfBits id logTableTail

/-! ## `exp` (exp.jl) -/

/-- `MAGIC_ROUND_CONST(Float64) = 1.5·2^52`. -/
def magic : Float := f64! 6.755399441055744e15

/-- Julia `table_unpack(N)`: `2^(j/256) ≈ jU + jL` for `j = N mod 256`, the table storing 52
high bits of the value and 8 extra bits of the correction. -/
@[inline] def tableUnpack (n : Int64) : Float × Float :=
  let j := (n.toUInt64 &&& 255).toNat
  (jTableU.get! j, jTableL.get! j)

/-- The argument reduction shared by the `exp_impl` methods: `N` (the low 32 bits of the
rounded `x·256/log_b(2)`, signed) and `r = x - N·log_b(2)/256` in two steps. -/
@[inline] def expReduce (x : Float) (b : Radix) : Int64 × Float :=
  let nf := Float.fma x b.inv256 magic
  let n : Int64 := nf.toBits.toUInt32.toInt32.toInt64
  let nf := nf - magic
  let r := Float.fma nf b.lnU x
  let r := Float.fma nf b.lnL r
  (n, r)

/-- Scale by `2^k` through the exponent bits (`reinterpret(T, (Int64(k) << 52) + bits)`). -/
@[inline] def scale2k (k : Int64) (small : Float) : Float := addExponentBits k small

/-- Julia `exp_impl(x::Float64, base)` (exp.jl:207-231). -/
@[inline] def expImpl (x : Float) (b : Radix) : Float :=
  let (n, r) := expReduce x b
  let k := n >>> 8
  let (jU, jL) := tableUnpack n
  let small := Float.fma jU (b.kernel r) jL + jU
  if !(x.abs ≤ b.subnormExp) then
    if F64.isnan x then x
    else if x ≥ b.maxExp then F64.inf
    else if x ≤ b.minExp then f64! 0.0
    else if k ≤ -53 then
      addExponentBits (k + 53) small * f64! 1.1102230246251565e-16
    else scale2k k small
  else scale2k k small

/-- Julia `exp_impl(x::Float64, xlo::Float64, base)` (exp.jl:233-259): `b^(x + xlo)`, the
last step of `^(::Float64, ::Float64)`. -/
@[inline] def expImpl2 (x xlo : Float) (b : Radix) : Float :=
  let (n, r) := expReduce x b
  let k := n >>> 8
  let (jU, jL) := tableUnpack n
  let kern := b.kernel r
  let verySmall := Float.fma kern (jU * xlo) jL
  -- `canonicalize2(1.0, kern)`
  let hi := f64! 1.0 + kern
  let lo := (f64! 1.0 - hi) + kern
  let small := Float.fma jU hi (Float.fma jU (lo + xlo) verySmall)
  if !(x.abs ≤ b.subnormExp) then
    if F64.isnan x then x
    else if x ≥ b.maxExp then F64.inf
    else if x ≤ b.minExp then f64! 0.0
    else if k ≤ -53 then
      addExponentBits (k + 53) small * f64! 1.1102230246251565e-16
    else if k == 1024 then (small * f64! 2.0) * f64! 8.98846567431158e307
    else scale2k k small
  else scale2k k small

/-- Julia `round(x::Float32)` (to nearest, ties to even; exact through `Float64`). -/
@[inline] def round32 (x : Float32) : Float32 := (F64.round x.toFloat).toFloat32

/-- Julia `exp_impl(x::Float32, base)` (exp.jl:276-295). -/
@[inline] def expImpl32 (x : Float32) (b : Radix) : Float32 :=
  let nf := round32 (x * b.inv32)
  let n : Int64 := nf.toFloat.toInt64
  let r := Float32.fma nf b.lnU32 x
  let r := Float32.fma nf b.lnL32 r
  let small := b.kernel32 r
  if x > b.maxExp32 then Float32.ofBits 0x7F800000
  else if x < b.minExp32 then f32! 0.0
  else
    let (power, small) := if x ≤ -b.subnormExp32 then (n + 127 + 24, small * f32! 5.9604645e-8)
      else (n + 127, small)
    let (power, small) := if n == 128 then (power - 1, small * f32! 2.0) else (power, small)
    small * Float32.ofBits (power.toInt32.toUInt32 <<< 23)

/-! ## `expm1` (exp.jl:412-472) -/

/-- Julia `exthorner(x, (1, ½, p))` (math.jl:215): Horner's scheme for `1 + x/2 + x²p` with
a compensated low part, `(hi, lo)`. -/
@[inline] def exthorner (x p : Float) : Float × Float :=
  let step (c hi lo : Float) : Float × Float :=
    let (prod, err) := twoMul hi x
    let hi' := c + prod
    (hi', Float.fma lo x ((prod - (hi' - c)) + err))
  let (hi, lo) := step f64! 0.5 p f64! 0.0
  step f64! 1.0 hi lo

/-- `Float32` `exthorner`. -/
@[inline] def exthorner32 (x p : Float32) : Float32 × Float32 :=
  let step (c hi lo : Float32) : Float32 × Float32 :=
    let (prod, err) := twoMul32 hi x
    let hi' := c + prod
    (hi', Float32.fma lo x ((prod - (hi' - c)) + err))
  let (hi, lo) := step f32! 0.5 p f32! 0.0
  step f32! 1.0 hi lo

/-- Julia `expm1_small(x::Float64)` for `log(3/4) ≤ x ≤ log(5/4)`. -/
def expm1Small (x : Float) : Float :=
  let p := Float.fma x (Float.fma x (Float.fma x (Float.fma x (Float.fma x (Float.fma x (Float.fma x
    (Float.fma x f64! 2.4360682937111612e-8 f64! 2.758218402815439e-7) f64! 2.7558212415361945e-6)
    f64! 2.480157691845342e-5) f64! 0.00019841269447671544) f64! 0.001388888889068783) f64! 0.008333333333401227)
    f64! 0.04166666666666556) f64! 0.16666666666666632
  let (hi, lo) := exthorner x p
  Float.fma x hi (x * lo)

/-- Julia `expm1_small(x::Float32)`. -/
def expm1Small32 (x : Float32) : Float32 :=
  let p := Float32.fma x (Float32.fma x (Float32.fma x (Float32.fma x f32! 0.0001933096 f32! 0.0013908712)
    f32! 0.008333682) f32! 0.041666627) f32! 0.16666666
  let (hi, lo) := exthorner32 x p
  Float32.fma x hi (x * lo)

/-- Julia `expm1(x::Float64)` (exp.jl:432-455). -/
def expm1 (x : Float) : Float :=
  if f64! -0.2876820724517809 ≤ x && x ≤ f64! 0.22314355131420976 then expm1Small x
  else if F64.isnan x then x
  else if x > f64! 709.7827128933845 then F64.inf
  else if x < f64! -37.42994775023705 then f64! -1.0
  else
    let (n, r) := expReduce x .e
    let k := n >>> 8
    let (jU, jL) := tableUnpack n
    let p := Radix.e.kernel r
    let twopk := twoPow k
    let twopnk := twoPow (-k)
    if k ≥ 106 then twoPow (k - 1) * (jU + Float.fma jU p jL) * f64! 2.0
    else if k ≥ 53 then twopk * (jU + Float.fma jU p (jL - twopnk))
    else if k ≤ -2 then twopk * (jU + Float.fma jU p jL) - f64! 1.0
    else twopk * ((jU - twopnk) + Float.fma jU p jL)

/-- Julia `expm1(x::Float32)` (exp.jl:457-472): the reduction in `Float64`. -/
def expm1F32 (x : Float32) : Float32 :=
  if x > f32! 88.72284 then Float32.ofBits 0x7F800000
  else if x < f32! -17.32868 then f32! -1.0
  else if f32! -0.2876821 ≤ x && x ≤ f32! 0.22314355 then expm1Small32 x
  else if F32.isnan x then x
  else
    let x := x.toFloat
    let nf := F64.round (x * f64! 1.4426950408889634)
    let n := nf.toInt64
    let r := Float.fma nf (f64! -0.6931471805599453) x
    let hi := Float.fma r (Float.fma r (Float.fma r (Float.fma r (Float.fma r (Float.fma r
      f64! 0.0002004037059220124 f64! 0.0013966479175977883) f64! 0.008332997481506921) f64! 0.041666183019487026)
      f64! 0.16666667546642386) f64! 0.5) f64! 1.0
    let smallPart := r * hi
    let twopk := twoPow n
    (Float.fma twopk smallPart (twopk - f64! 1.0)).toFloat32

/-! ## `log` (log.jl) -/

/-- Julia `log_proc1(y, mf, F, f, base)` for `Float64` (log.jl:158-187): the table-driven
case, `jp = 128F - 127` indexing `t_log_Float64`. -/
@[inline] def logProc1 (y mf bigF f : Float) (b : Radix) : Float :=
  -- `jp = trunc(128F) - 127`, 1-based into `t_log_Float64`
  let jp := ((f64! 128.0 * bigF).toUInt64 - 128).toNat
  let lHi := mf * f64! 0.6931471805601177 + logTable64Hi.get! jp
  let lLo := mf * (f64! -1.7239444525614835e-13) + logTable64Lo.get! jp
  let u := (f64! 2.0 * f) / (y + bigF)
  let v := u * u
  let q := u * v * Float.fma v f64! 0.012500053168098584 f64! 0.08333333333303913
  Float.fma b.logbU lHi (Float.fma b.logbU (u + (q + lLo)) (b.logbL * lHi))

/-- Julia `log_proc2(f, base)` for `Float64` (log.jl:190-213): the case `x ≈ 1`. -/
@[inline] def logProc2 (f : Float) (b : Radix) : Float :=
  let g := f64! 1.0 / (f64! 2.0 + f)
  let u := f64! 2.0 * f * g
  let v := u * u
  let q := u * v * Float.fma v (Float.fma v (Float.fma v f64! 0.0004348877777076146 f64! 0.0022321399879194482)
      f64! 0.012500000003771751) f64! 0.08333333333333179
  Float.fma b.logbU u (Float.fma b.logbL u (b.logbU * Float.fma (Float.fma (-u) f (f64! 2.0 * (f - u))) g q))

/-- Julia `_log(x::Float64, base, func)` (log.jl:264-297). -/
@[inline] def logImpl (x : Float) (b : Radix) : Float :=
  if x > f64! 0.0 then
    if x == F64.inf then x
    else if f64! 0.9394130628134757 < x && x < f64! 1.0644944589178595 then logProc2 (x - f64! 1.0) b
    else
      let xu := x.toBits
      let m := ((xu >>> 52) &&& 0x7FF).toInt64
      let (xu, m) : UInt64 × Int64 :=
        if m == 0 then
          let xu' := (x * f64! 1.8014398509481984e16).toBits
          (xu', ((xu' >>> 52) &&& 0x7FF).toInt64 - 54)
        else (xu, m)
      let y := Float.ofBits ((xu &&& 0x000FFFFFFFFFFFFF) ||| 0x3FF0000000000000)
      let mf := (m - 1023).toFloat
      let bigF := (y + f64! 3.5184372088832e13) - f64! 3.5184372088832e13
      logProc1 y mf bigF (y - bigF) b
  else if x == f64! 0.0 then -F64.inf
  else F64.nan

/-- Julia `log_proc1` for `Float32` (log.jl:216-236): the table sum in `Float64`, rounded once. -/
@[inline] def logProc1F32 (y mf bigF f : Float32) (b : Radix) : Float32 :=
  let l := mf.toFloat * f64! 0.6931471805599453 + logTable32F.get! ((f32! 128.0 * bigF).toUInt32 - 128).toNat
  let u := (f32! 2.0 * f) / (y + bigF)
  let v := u * u
  let q := u * v * f32! 0.08333351
  (b.logb32 * (l + (u + q).toFloat)).toFloat32

/-- Julia `log_proc2` for `Float32` (log.jl:239-255): `u` in `Float64`. -/
@[inline] def logProc2F32 (f : Float32) (b : Radix) : Float32 :=
  let u64 := (f32! 2.0 * f).toFloat / (f64! 2.0 + f.toFloat)
  let u := u64.toFloat32
  let v := u * u
  let q := u * v * Float32.fma v f32! 0.012512346 f32! 0.08333332
  (b.logb32 * (u64 + q.toFloat)).toFloat32

/-- Julia `_log(x::Float32, base, func)` (log.jl:299-332). -/
@[inline] def logImpl32 (x : Float32) (b : Radix) : Float32 :=
  if x > f32! 0.0 then
    if F32.isinf x then x
    else if f32! 0.939413 < x && x < f32! 1.0644945 then logProc2F32 (x - f32! 1.0) b
    else
      let xu := x.toBits
      let m := ((xu >>> 23) &&& 0xFF).toUInt64.toInt64
      let (xu, m) : UInt32 × Int64 :=
        if m == 0 then
          let xu' := (x * f32! 3.3554432e7).toBits
          (xu', ((xu' >>> 23) &&& 0xFF).toUInt64.toInt64 - 25)
        else (xu, m)
      let y := Float32.ofBits ((xu &&& 0x007FFFFF) ||| 0x3F800000)
      let mf := (m - 127).toFloat32
      let bigF := (y + f32! 65536.0) - f32! 65536.0
      logProc1F32 y mf bigF (y - bigF) b
  else if x == f32! 0.0 then Float32.ofBits 0xFF800000
  else Float32.ofBits 0x7FC00000

/-- Julia `log1p(x::Float64)` (log.jl:335-366). -/
def log1p (x : Float) : Float :=
  if x > f64! -1.0 then
    if x == F64.inf then x
    else if f64! -1.1102230246251565e-16 < x && x < f64! 1.1102230246251565e-16 then x
    else if f64! -0.06058693718652422 < x && x < f64! 0.06449445891785943 then logProc2 x .e
    else
      let z := f64! 1.0 + x
      let zu := z.toBits
      let s := Float.ofBits (0x7FE0000000000000 - (zu &&& 0xFFF0000000000000))
      let m : Int64 := ((zu >>> 52) &&& 0x7FF).toInt64 - 1023
      let c := if m > 0 then f64! 1.0 - (z - x) else x - (z - f64! 1.0)
      let y := Float.ofBits ((zu &&& 0x000FFFFFFFFFFFFF) ||| 0x3FF0000000000000)
      let bigF := (y + f64! 3.5184372088832e13) - f64! 3.5184372088832e13
      logProc1 y m.toFloat bigF ((y - bigF) + c * s) .e
  else if x == f64! -1.0 then -F64.inf
  else F64.nan

/-- Julia `log1p(x::Float32)` (log.jl:368-398). -/
def log1pF32 (x : Float32) : Float32 :=
  if x > f32! -1.0 then
    if F32.isinf x then x
    else if f32! -5.9604645e-8 < x && x < f32! 5.9604645e-8 then x
    else if f32! -0.06058694 < x && x < f32! 0.06449446 then logProc2F32 x .e
    else
      let z := f32! 1.0 + x
      let zu := z.toBits
      let s := Float32.ofBits (0x7F000000 - (zu &&& 0xFF800000))
      let m : Int64 := ((zu >>> 23) &&& 0xFF).toUInt64.toInt64 - 127
      let c := if m > 0 then f32! 1.0 - (z - x) else x - (z - f32! 1.0)
      let y := Float32.ofBits ((zu &&& 0x007FFFFF) ||| 0x3F800000)
      let bigF := (y + f32! 65536.0) - f32! 65536.0
      logProc1F32 y m.toFloat32 bigF ((y - bigF) + s * c) .e
  else if x == f32! -1.0 then Float32.ofBits 0xFF800000
  else Float32.ofBits 0x7FC00000

/-- Julia `_log_ext(xu)` (log.jl:559-587, after ARM's `pow.c`): `log(x)` as an unevaluated
sum `hi + lo` with about 68 bits, for `^(::Float64, ::Float64)`. -/
@[inline] def logExt (xu : UInt64) : Float × Float :=
  let tmpU := xu - 0x3fe6955500000000
  let tmp : Int64 := tmpU.toInt64
  let z := Float.ofBits (xu - (tmpU &&& 0xfff0000000000000))
  let k := (tmp >>> 52).toFloat
  let idx := ((tmp >>> 45).toUInt64 &&& 127).toNat
  let t := logTableT[idx]!
  let logctail := logTableTailF.get! idx
  let invc := Float.ofBits (((t &&& 0xff) ||| 0x1ff00) <<< 45)
  let logc := Float.ofBits (t &&& (~~~ (0xff : UInt64)))
  let r := Float.fma z invc (f64! -1.0)
  let t1 := Float.fma k f64! 0.6931471805598903 logc
  let t2 := t1 + r
  let lo1 := Float.fma k f64! 5.497923018708371e-14 logctail
  let lo2 := t1 - t2 + r
  let ar := f64! -0.5 * r
  let (ar2, lo3) := twoMul r ar
  let hi := t2 + ar2
  let lo4 := t2 - hi + ar2
  let p := Float.fma r (Float.fma r (Float.fma r (Float.fma r (Float.fma r f64! 0.25001038159188854
      (f64! -0.28572740711487526)) f64! 0.33333333317438696) (f64! -0.3999999997661988)) f64! 0.5000000000000007)
      (f64! -0.6666666666666679)
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
      let err := x * f64! 2.0 * xnlo
      let (x', xnlo') := twoMul x x
      powLoop x' (xnlo' + err) y ynlo (n / 2) fuel
    else
      let err := Float.fma y xnlo (x * ynlo)
      if F64.isfinite x && F64.isfinite err then x * y + err else x * y

/-- Julia `pow_body(x::Float64, n::Integer)` (pow.jl:120-146): compensated power by squaring,
the `x^n` of Julia for `-2^12 ≤ n ≤ 3·2^13` (more accurate than repeated multiplication). -/
def powBody (x : Float) (n : Int) : Float :=
  if n == 3 then x * x * x
  else if n < 0 then
    let rx := f64! 1.0 / x
    if n == -2 then rx * rx
    else
      let xnlo := if F64.isfinite x then -(Float.fma x rx (f64! -1.0)) * rx else f64! -0.0
      powLoop rx xnlo f64! 1.0 f64! 0.0 n.natAbs (n.natAbs + 1)
  else powLoop x (f64! -0.0) f64! 1.0 f64! 0.0 n.toNat (n.toNat + 1)

/-- Julia `pow_body(x::Float64, y::Float64)` for positive `x` (pow.jl:91-104):
`exp(y·log(x))` through the 68-bit `_log_ext` and the two-part `exp_impl`. -/
def powBodyFloat (x y : Float) : Float :=
  let xu : UInt64 := x.toBits
  let xu : UInt64 :=
    if xu < 0x0010000000000000 then
      ((x * f64! 4.503599627370496e15).toBits &&& (0x7FFFFFFFFFFFFFFF : UInt64)) - ((52 : UInt64) <<< 52)
    else xu
  let (logxhi, logxlo) := logExt xu
  let (xyhi, xylo) := twoMul logxhi y
  let xylo := Float.fma logxlo y xylo
  let hi := xyhi + xylo
  expImpl2 hi (xylo - (hi - xyhi)) .e

/-- Julia `Base.power_by_squaring(x::Float64, p)` for `p ≥ 0` (intfuncs.jl:394), the
multiplication order Julia uses (e.g. for `Irrational^Integer`). -/
@[inline] def powerBySquaring (x : Float) (p : Nat) : Float := JuliaBase.powBySquaring (· * ·) f64! 1.0 x p

/-- `Float32` `power_by_squaring` in `Float64` (what `pow_body(::Float32, ::Int32)` runs). -/
@[inline] def powBody32 (x : Float32) (n : Int) : Float32 :=
  if n == -2 then let i := f32! 1.0 / x; i * i
  else if n == 3 then x * x * x
  else if n < 0 then (powerBySquaring (f64! 1.0 / x.toFloat) n.natAbs).toFloat32
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
  if n == 0 then f64! 1.0
  else if usePowerBySquaring n then Math.powBody x n
  else
    let neg := x < 0 && n % 2 != 0
    let ax := x.abs
    let y := Float.ofInt n
    if Float.ofInt (F64.toIntTrunc y) == y && F64.toIntTrunc y == n then
      copysign (powBodyFloat ax y) (if neg then f64! -1.0 else f64! 1.0)
    else
      -- `n` is not a `Float64`: split off `n % 1024` (Julia's `rem`, sign of `n`)
      let n2 := n.tmod 1024
      powBodyFloat ax (Float.ofInt (n - n2)) * copysign (Math.powBody ax n2) (if neg then f64! -1.0 else f64! 1.0)

/-- Julia `^(x::Float64, y::Float64)` (pow.jl:7-30). A negative base with a non-integer
exponent (Julia `DomainError`) gives `NaN`. -/
def pow (x y : Float) : Float :=
  if x.toBits == (f64! 1.0 : Float).toBits then f64! 1.0
  else
    let y := if !(y.abs < f64! 6.917529027641082e18) then
        (if F64.isnan y then y else if y > 0 then f64! 6.917529027641082e18 else f64! -6.917529027641082e18)
      else y
    if F64.isnan y then y
    else
      let yint64 := y.toInt64
      let yisint := y == yint64.toFloat
      let yint := yint64.toInt
      if yisint && yint == 0 then f64! 1.0
      else if yisint && usePowerBySquaring yint then Math.powBody x yint
      else if x == f64! 0.0 then (if y > 0 then f64! 0.0 else inf)
      else if x < 0 && !yisint then nan
      else
        let s : Float := if x < 0 && yint % 2 != 0 then f64! -1.0 else f64! 1.0
        if !F64.isfinite x then
          -- `copysign(x, s) * (y > 0 || isnan(x))`, with Julia's `Float * false = ±0.0`
          let c := copysign x s
          if y > 0 || F64.isnan x then c else copysign f64! 0.0 c
        else copysign (powBodyFloat x.abs y) s

/-- Julia `Base.power_by_squaring(x::Float64, p)` for `p ≥ 0` (intfuncs.jl:394). -/
@[inline] def powerBySquaring (x : Float) (p : Nat) : Float := Math.powerBySquaring x p

/-- Julia `literal_pow(^, x, Val(k))` for `x::Float64` (intfuncs.jl:465-474): the lowering of
`x^k` with a literal `k`, `x*x` for `2`, `x*x*x` for `3`, `inv(x)` for `-1`, otherwise `x^k`. -/
def literalPow (x : Float) (k : Int) : Float :=
  match k with
  | 0 => f64! 1.0
  | 1 => x
  | 2 => x * x
  | 3 => x * x * x
  | -1 => f64! 1.0 / x
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
  if n == 0 then f32! 1.0
  else if usePowerBySquaring n then powBody32 x n
  else
    let r := powBodyFloat x.abs (Float.ofInt n)
    if x < 0 && n % 2 != 0 then -r else r

/-- Julia `^(x::Float32, y::Float32)` (pow.jl:34-55). A negative base with a non-integer
exponent (Julia `DomainError`) gives `NaN`. -/
def pow (x y : Float32) : Float32 :=
  if x == f32! 1.0 then f32! 1.0
  else
    let maxExp : Float32 := f32! 1744830464.0  -- `0x1.Ap30`
    let y := if !(y.abs < maxExp) then (if F32.isnan y then y else if y > 0 then maxExp else -maxExp) else y
    if F32.isnan y then y
    else
      let yint64 := y.toFloat.toInt64
      let yisint := y.toFloat == yint64.toFloat
      let yint := yint64.toInt
      if yisint && yint == 0 then f32! 1.0
      else if yisint && usePowerBySquaring yint then powBody32 x yint
      else if x < 0 && !yisint then Float32.ofBits 0x7FC00000
      else
        let neg := x < 0 && yint % 2 != 0
        let c := if neg then -x.abs else x.abs  -- `copysign(x, s)`
        if !F32.isfinite x then (if y > 0 || F32.isnan x then c else copysign f32! 0.0 c)
        else
          let r := powBodyFloat x.abs y.toFloat
          if neg then -r else r

/-- Julia `literal_pow(^, x, Val(k))` for `x::Float32`. -/
def literalPow (x : Float32) (k : Int) : Float32 :=
  match k with
  | 0 => f32! 1.0
  | 1 => x
  | 2 => x * x
  | 3 => x * x * x
  | -1 => f32! 1.0 / x
  | _ => powInt x k

end F32

end JuliaBase
