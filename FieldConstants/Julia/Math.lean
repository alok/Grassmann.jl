import FieldConstants.Julia.Float
import FieldConstants.Julia.Tables

/-!
# Julia's own `Float64` elementary functions, bit for bit

Julia does not call libm for `exp`, `exp2`, `exp10`, `log`, `log2`, `log10`
or `^`; it ships table-driven implementations (ported from ARM's optimized
routines and Tang's algorithms). The chakravala packages print the results of
these functions (for example the product of `𝘩^(1/2)·𝘤^(-1/2)…` in
Similitude), so a 1-ulp libm difference would change printed digits.
This module ports them with identical operation order; `muladd` is a fused
multiply-add because Julia's `muladd` contracts on aarch64/x86-64 with FMA.

Julia sources (1.13): `base/special/exp.jl` (`exp_impl`, lines 207-260),
`base/special/log.jl` (`_log`, `log_proc1/2`, `_log_ext`, lines 143-300, 559-585),
`base/special/pow.jl` (`^`, `pow_body`, lines 1-142),
`base/intfuncs.jl` (`power_by_squaring`, `literal_pow`, lines 394-488).
-/

namespace FieldConstants.Julia

/-- Julia `muladd(x, y, z)`. Julia emits it as a `contract`-flagged multiply and
add, which LLVM leaves unfused in these kernels (verified against the oracle:
fusing changes `pow_body` results by one ulp), so it is `x*y + z` here. `fma`
and `two_mul` remain genuinely fused. -/
@[inline] def muladd (x y z : Float) : Float := x * y + z

/-- Julia `Base.Math.two_mul`: `x*y` and its exact rounding error. -/
@[inline] def twoMul (x y : Float) : Float × Float :=
  let xy := x * y
  (xy, Float.fma x y (-xy))

/-- Two's-complement bits of an integer, modulo `2^64`. -/
@[inline] def u64OfInt (i : Int) : UInt64 := (i.emod (2 ^ 64)).toNat.toUInt64

/-- Reinterpret a `UInt64` as a signed 64-bit integer. -/
@[inline] def i64OfU64 (u : UInt64) : Int :=
  if u < 0x8000000000000000 then u.toNat else (u.toNat : Int) - 2 ^ 64

/-- The three bases of Julia's `exp_impl`. -/
inductive ExpBase where
  | two | e | ten
  deriving DecidableEq, Repr

namespace ExpBase
/-- `LogBo256INV`: `256/log_b(2)`. -/
def inv256 : ExpBase → Float
  | two => 256.0 | e => 369.3299304675746 | ten => 850.4135922911647
/-- `LogBo256U`: high part of `-log_b(2)/256`. -/
def lnU : ExpBase → Float
  | two => -0.00390625 | e => -0.002707606173999011 | ten => -0.0011758984204561784
/-- `LogBo256L`: low part of `-log_b(2)/256`. -/
def lnL : ExpBase → Float
  | two => 0.0 | e => -6.327543041662719e-14 | ten => -1.0624811566412999e-13
/-- `MAX_EXP`. -/
def maxExp : ExpBase → Float
  | two => 1024.0 | e => 709.7827128933841 | ten => 308.25471555991675
/-- `MIN_EXP`. -/
def minExp : ExpBase → Float
  | two => -1075.0 | e => -745.1332191019412 | ten => -323.60724533877976
/-- `SUBNORM_EXP`. -/
def subnormExp : ExpBase → Float
  | two => 1022.0 | e => 708.3964185322641 | ten => 307.6526555685887
/-- `expm1b_kernel`: minimax `b^x - 1` on `|x| ≤ log_b(2)/512`. -/
def kernel : ExpBase → Float → Float
  | two, x => x * muladd x (muladd x (muladd x 0.009618129548366803 0.05550411502333161)
      0.24022650695910058) 0.6931471805599393
  | e, x => x * muladd x (muladd x (muladd x 0.04166666857598777 0.1666666857598779)
      0.4999999999999997) 0.9999999999999912
  | ten, x => x * muladd x (muladd x (muladd x 1.1712552025835192 2.034678825384765)
      2.6509490552391974) 2.3025850929940255
end ExpBase

/-- `MAGIC_ROUND_CONST(Float64) = 1.5·2^52`. -/
private def magic : Float := 6.755399441055744e15

/-- Julia `table_unpack`: `2^(j/256)` as a high/low pair. -/
@[inline] private def tableUnpack (n : Int) : Float × Float :=
  let j : UInt64 := jTable[(n.emod 256).toNat]!
  (Float.ofBits ((0x3FF0000000000000 : UInt64) ||| (j &&& 0x000FFFFFFFFFFFFF)),
   Float.ofBits ((0x3C00000000000000 : UInt64) ||| (j >>> 8)))

/-- Argument reduction shared by both `exp_impl` methods: `(N as Int32, r)`. -/
@[inline] private def expReduce (x : Float) (b : ExpBase) : Int × Float :=
  let nf := muladd x b.inv256 magic
  -- `reinterpret(UInt64, N_float) % Int32`: the low 32 bits, signed
  let low := nf.toBits.toUInt32.toNat
  let n : Int := if low ≥ 2 ^ 31 then (low : Int) - 2 ^ 32 else low
  let nf := nf - magic
  let r := muladd nf b.lnU x
  let r := muladd nf b.lnL r
  (n, r)

/-- Scale `small` by `2^k` exactly as Julia does (bit-level exponent add). -/
@[inline] private def scale2k (k : Int) (small : Float) : Float :=
  Float.ofBits ((u64OfInt k <<< 52) + small.toBits)

/-- Julia `exp_impl(x, base)` for `Float64`. -/
def expImpl (x : Float) (b : ExpBase) : Float :=
  let (n, r) := expReduce x b
  let k := Int.fdiv n 256
  let (jU, jL) := tableUnpack n
  let small := muladd jU (b.kernel r) jL + jU
  if !(x.abs ≤ b.subnormExp) then
    if x.isNaN then x
    else if x ≥ b.maxExp then inf
    else if x ≤ b.minExp then 0.0
    else if k ≤ -53 then
      Float.ofBits ((u64OfInt (k + 53) <<< 52) + small.toBits) * 1.1102230246251565e-16
    else scale2k k small
  else scale2k k small

/-- Julia `exp_impl(x, xlo, base)`: `b^(x + xlo)`, used by `pow`. -/
def expImpl2 (x xlo : Float) (b : ExpBase) : Float :=
  let (n, r) := expReduce x b
  let k := Int.fdiv n 256
  let (jU, jL) := tableUnpack n
  let kern := b.kernel r
  let verySmall := muladd kern (jU * xlo) jL
  let hi := 1.0 + kern
  let lo := (1.0 - hi) + kern
  let small := Float.fma jU hi (muladd jU (lo + xlo) verySmall)
  if !(x.abs ≤ b.subnormExp) then
    if x.isNaN then x
    else if x ≥ b.maxExp then inf
    else if x ≤ b.minExp then 0.0
    else if k ≤ -53 then
      Float.ofBits ((u64OfInt (k + 53) <<< 52) + small.toBits) * 1.1102230246251565e-16
    else if k == 1024 then (small * 2.0) * 8.98846567431158e307
    else scale2k k small
  else scale2k k small

/-- Julia `exp(::Float64)`. -/
def exp (x : Float) : Float := expImpl x .e
/-- Julia `exp2(::Float64)`. -/
def exp2 (x : Float) : Float := expImpl x .two
/-- Julia `exp10(::Float64)`. -/
def exp10 (x : Float) : Float := expImpl x .ten

/-! ### Logarithms (`base/special/log.jl`) -/

/-- The bases of Julia's `_log`. -/
inductive LogBase where
  | two | e | ten
  deriving DecidableEq, Repr

private def LogBase.hi : LogBase → Float
  | .two => 1.4426950408889634 | .e => 1.0 | .ten => 0.4342944819032518
private def LogBase.lo : LogBase → Float
  | .two => 2.0355273740931033e-17 | .e => 0.0 | .ten => 1.098319650216765e-17

private def logProc1 (y mf bigF f : Float) (b : LogBase) : Float :=
  let jp := (128.0 * bigF).toUInt64.toNat - 127
  let (hb, lb) := logTable64[jp - 1]!
  let hi := Float.ofBits hb
  let lo := Float.ofBits lb
  let lHi := mf * 0.6931471805601177 + hi
  let lLo := mf * (-1.7239444525614835e-13) + lo
  let u := (2.0 * f) / (y + bigF)
  let v := u * u
  let q := u * v * muladd v 0.012500053168098584 0.08333333333303913
  Float.fma b.hi lHi (Float.fma b.hi (u + (q + lLo)) (b.lo * lHi))

private def logProc2 (f : Float) (b : LogBase) : Float :=
  let g := 1.0 / (2.0 + f)
  let u := 2.0 * f * g
  let v := u * u
  let q := u * v * muladd v (muladd v (muladd v 0.0004348877777076146 0.0022321399879194482)
      0.012500000003771751) 0.08333333333333179
  Float.fma b.hi u (Float.fma b.lo u (b.hi * Float.fma (Float.fma (-u) f (2.0 * (f - u))) g q))

/-- Julia `_log(x::Float64, base)`. Negative arguments (a `DomainError` in
Julia) return `NaN`. -/
def logImpl (x : Float) (b : LogBase) : Float :=
  if x > 0.0 then
    if x.isInf then x
    else if 0.9394130628134757 < x && x < 1.0644944589178595 then logProc2 (x - 1.0) b
    else
      let xu := x.toBits
      let m := ((xu >>> 52) &&& 0x7FF).toNat
      let (xu, m) : UInt64 × Int :=
        if m == 0 then
          let x' := x * 1.8014398509481984e16
          let xu' := x'.toBits
          (xu', (((xu' >>> 52) &&& 0x7FF).toNat : Int) - 54)
        else (xu, m)
      let m := m - 1023
      let y := Float.ofBits ((xu &&& 0x000FFFFFFFFFFFFF) ||| 0x3FF0000000000000)
      let mf := Float.ofInt m
      let bigF := (y + 3.5184372088832e13) - 3.5184372088832e13
      let f := y - bigF
      logProc1 y mf bigF f b
  else if x == 0.0 then -inf
  else nan

/-- Julia `log(::Float64)`. -/
def log (x : Float) : Float := logImpl x .e
/-- Julia `log2(::Float64)`. -/
def log2 (x : Float) : Float := logImpl x .two
/-- Julia `log10(::Float64)`. -/
def log10 (x : Float) : Float := logImpl x .ten

/-- Julia `_log_ext`: `log(x)` as an unevaluated sum `hi + lo` with ~68 bits. -/
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
  let t1 := muladd k 0.6931471805598903 logc
  let t2 := t1 + r
  let lo1 := muladd k 5.497923018708371e-14 logctail
  let lo2 := t1 - t2 + r
  let ar := -0.5 * r
  let (ar2, lo3) := twoMul r ar
  let hi := t2 + ar2
  let lo4 := t2 - hi + ar2
  let p := muladd r (muladd r (muladd r (muladd r (muladd r 0.25001038159188854
      (-0.28572740711487526)) 0.33333333317438696) (-0.3999999997661988)) 0.5000000000000007)
      (-0.6666666666666679)
  let lo := lo1 + lo2 + lo3 + muladd (r * ar2) p lo4
  (hi, lo)

/-! ### Powers -/

/-- Julia `use_power_by_squaring(n)`. -/
@[inline] def usePowerBySquaring (n : Int) : Bool := -4096 ≤ n && n ≤ 24576

/-- Compensated power-by-squaring loop of `pow_body(x::Float64, n::Integer)`. -/
private def powLoop (x xnlo y ynlo : Float) : Nat → Nat → Float
  | 0, _ => x * y
  | fuel + 1, n =>
    if n > 1 then
      let (y, ynlo) :=
        if n % 2 == 1 then
          let err := muladd y xnlo (x * ynlo)
          let (y', ynlo') := twoMul x y
          (y', ynlo' + err)
        else (y, ynlo)
      let err := x * 2.0 * xnlo
      let (x', xnlo') := twoMul x x
      powLoop x' (xnlo' + err) y ynlo fuel (n / 2)
    else
      let err := muladd y xnlo (x * ynlo)
      if x.isFinite && err.isFinite then muladd x y err else x * y

/-- Julia `pow_body(x::Float64, n::Integer)` (compensated power by squaring). -/
def powBodyInt (x : Float) (n : Int) : Float :=
  if n == 3 then x * x * x
  else if n < 0 then
    let rx := 1.0 / x
    if n == -2 then rx * rx
    else
      let xnlo := if x.isFinite then -(Float.fma x rx (-1.0)) * rx else -0.0
      powLoop rx xnlo 1.0 0.0 70 (-n).toNat
  else powLoop x (-0.0) 1.0 0.0 70 n.toNat

/-- Julia `pow_body(x::Float64, y::Float64)` for positive finite `x`. -/
def powBodyFloat (x y : Float) : Float :=
  let xu := x.toBits
  let xu :=
    if xu < 0x0010000000000000 then
      let xu := (x * 4.503599627370496e15).toBits &&& 0x7FFFFFFFFFFFFFFF
      xu - ((52 : UInt64) <<< 52)
    else xu
  let (logxhi, logxlo) := logExt xu
  let (xyhi, xylo) := twoMul logxhi y
  let xylo := muladd logxlo y xylo
  let hi := xyhi + xylo
  expImpl2 hi (xylo - (hi - xyhi)) .e

/-- Julia `^(x::Float64, n::Integer)`. -/
def powInt (x : Float) (n : Int) : Float :=
  if n == 0 then 1.0
  else if usePowerBySquaring n then powBodyInt x n
  else
    let s := if x < 0 && n % 2 != 0 then -1.0 else 1.0
    let y := Float.ofInt n
    let r := powBodyFloat x.abs y
    if s < 0 then -r else r

/-- `copysign(x, s)` with `s = ±1`. -/
@[inline] private def withSign (x : Float) (neg : Bool) : Float :=
  let b := x.toBits &&& 0x7FFFFFFFFFFFFFFF
  Float.ofBits (if neg then b ||| 0x8000000000000000 else b)

/-- Julia `^(x::Float64, y::Float64)`. A negative base with a non-integer
exponent (Julia `DomainError`) returns `NaN`. -/
def pow (x y : Float) : Float :=
  if x.toBits == (1.0 : Float).toBits then 1.0
  else
    let y := if !(y.abs < 6.917529027641082e18) then
        (if y.isNaN then y else if y > 0 then 6.917529027641082e18 else -6.917529027641082e18)
      else y
    if y.isNaN then y
    else
      let yint : Int := (if y < 0 then -((-y).floor) else y.floor).toInt64.toInt
      let yisint := y == Float.ofInt yint
      if yisint && yint == 0 then 1.0
      else if yisint && usePowerBySquaring yint then powBodyInt x yint
      else if x == 0.0 then (if y > 0 then 0.0 else inf)
      else if x < 0 && !yisint then nan
      else
        let neg := x < 0 && yint % 2 != 0
        if !x.isFinite then
          (if y > 0 || x.isNaN then withSign x neg else 0.0)
        else withSign (powBodyFloat x.abs y) neg

/-- Julia `power_by_squaring(x, p)` for a float base and `p ≥ 1` (the generic
loop used for `Irrational^Integer`, e.g. `φ^3`). -/
def powerBySquaring (x : Float) (p : Nat) : Float :=
  let xsq := x * x
  if p == 0 then 1.0
  else if p == 1 then x
  else if p == 2 then xsq
  else
    let tz := trailingZeros p
    let t := tz + 1
    let p := p >>> t
    let x := if t - 1 > 0 then xsq else x
    let x := sqr x (t - 2)
    outer x x p 64
where
  /-- number of trailing zero bits -/
  trailingZeros (p : Nat) : Nat := go p 0 64
  go (p acc : Nat) : Nat → Nat
    | 0 => acc
    | f + 1 => if p % 2 == 0 && p != 0 then go (p / 2) (acc + 1) f else acc
  /-- square `k` times -/
  sqr (x : Float) : Nat → Float
    | 0 => x
    | k + 1 => sqr (x * x) k
  outer (x y : Float) (p : Nat) : Nat → Float
    | 0 => y
    | f + 1 =>
      if p > 0 then
        let t := trailingZeros p + 1
        let p := p >>> t
        let x := sqr x t
        outer x (y * x) p f
      else y

/-- Julia `round(x, digits = d)` for `Float64` (`base/floatfuncs.jl`,
`_round_digits`): scale by `10^d`, round half to even, unscale; falls back to `x`
when the scaled value is not finite. -/
def roundDigits (x : Float) (d : Int) : Float :=
  if d ≥ 0 then
    let inv := powInt 10.0 d
    let y := roundEven (x * inv) / inv
    if y.isFinite then y else x
  else
    let step := powInt 10.0 (-d)
    let y := roundEven (x / step) * step
    if y.isFinite then y else x
where
  /-- IEEE round-half-to-even (`round(x, RoundNearest)`). -/
  roundEven (x : Float) : Float :=
    if !x.isFinite then x
    else
      let f := x.floor
      let diff := x - f
      let r := if diff < 0.5 then f
        else if diff > 0.5 then f + 1.0
        else if (f / 2.0).floor * 2.0 == f then f else f + 1.0
      -- `rint` keeps the sign of zero: `round(-0.4) == -0.0`
      if r == 0.0 && x < 0.0 then -0.0 else r

/-- Julia `Base.hidigit(x::AbstractFloat, 10) = 1 + floor(Int, log10(abs(x)))`
(`base/floatfuncs.jl:129`), using Julia's own `log10`; `0` for `x = 0`. -/
def hidigit (x : Float) : Int :=
  if x == 0.0 || !x.isFinite then 0
  else 1 + (log10 x.abs).floor.toInt64.toInt

/-- Julia `round(x, sigdigits = n)` (`_round_sigdigits`): round to `n - hidigit(x)`
decimal digits. -/
def roundSigdigits (x : Float) (n : Int) : Float :=
  if x == 0.0 || !x.isFinite then x else roundDigits x (n - hidigit x)

end FieldConstants.Julia
