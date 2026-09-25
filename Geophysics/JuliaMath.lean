import FieldConstants
import Geophysics.Lit

/-!
# Julia's own `Float64` elementary functions used by Geophysics

Julia does not call the platform libm for `sin`, `cos`, `tan`, `atan`, `asin`,
`atanh`, `log1p`, `exp` or `^`: it ships its own implementations
(`base/special/trig.jl`, `rem_pio2.jl`, `hyperbolic.jl`, `log.jl`, `exp.jl`,
`pow.jl`). The macOS libm disagrees with them in the last bit for a few percent of
arguments (measured on 10⁵ samples: `tan` 39 %, `asin` 9 %, `atan` 7 %, `cos`
5 %, `sin` 4 %), and every Geophysics quantity is downstream of a few such calls
(the Somigliana gravity of a weather column uses `tan`, `atan`, `sin`, `cos`).
This module ports those functions with Julia's operation order so the port agrees
with the oracle bit for bit.

**`muladd` fuses, mostly.** Julia lowers `muladd` (and `@horner`/`evalpoly`,
which are built from it) to a `contract`-flagged multiply and add, which LLVM
contracts into one FMA on aarch64. Every `muladd` below is therefore a
`Float.fma` (`ma`), and a plain `a*b + c` in Julia source stays unfused. Two
sites compile unfused in Julia's system image and are unfused here: the final
`muladd(x, y, err)` of `pow_body(x, n::Integer)` (its product is shared with the
other branch of an `ifelse`) and the outermost `muladd` of `sin_kernel`'s first
polynomial. The model was fitted and validated on 1.4·10⁶ oracle samples
(`oracle/geophysics/mathsamples.jl`, `MathSweep.lean`): every other combination
mismatches Julia somewhere (all-unfused `exp` on 1 input in 5000, all-fused
`pow` on 22 % of integer exponents), this one nowhere.

`FieldConstants.Julia` already ports `exp`/`log`/`^` with unfused `muladd`;
those agree with Julia except for rare last-bit cases, which is why Geophysics
uses the functions here. Arguments outside a function's domain (Julia throws a
`DomainError`) return `NaN`.
-/

namespace Geophysics.JMath

/-- Julia `muladd` as compiled on aarch64: a fused multiply-add. -/
@[inline] def ma (x y z : Float) : Float := Float.fma x y z

/-- IEEE bits of `NaN` used for domain errors. -/
def nan : Float := Float.ofBits 0x7FF8000000000000

/-- `+Inf`. -/
def inf : Float := Float.ofBits 0x7FF0000000000000

/-- `Float64(π)`. -/
def pi : Float := (f64% 3.141592653589793)

/-- Julia `copysign(x, y)`. -/
@[inline] def copysign (x y : Float) : Float :=
  Float.ofBits ((x.toBits &&& 0x7FFFFFFFFFFFFFFF) ||| (y.toBits &&& 0x8000000000000000))

/-- Julia `flipsign(x, y)`: `x` with its sign flipped when `y` is negative. -/
@[inline] def flipsign (x y : Float) : Float :=
  Float.ofBits (x.toBits ^^^ (y.toBits &&& 0x8000000000000000))

/-- Julia `signbit`. -/
@[inline] def signbit (x : Float) : Bool := x.toBits &&& 0x8000000000000000 != 0

/-- Zero the low 32 bits (Julia's `reinterpret(Float64, (reinterpret(UInt64, x) >> 32) << 32)`). -/
@[inline] def truncLow (x : Float) : Float := Float.ofBits ((x.toBits >>> 32) <<< 32)

/-- Julia `highword(x)`: the upper 32 bits. -/
@[inline] def highword (x : Float) : UInt32 := (x.toBits >>> 32).toUInt32

/-- Julia `poshighword(x)`: the upper 32 bits without the sign. -/
@[inline] def poshighword (x : Float) : UInt32 := ((x.toBits >>> 32) &&& 0x7FFFFFFF).toUInt32

/-- Julia `round(x)` for `Float64` (ties to even). -/
@[inline] def roundEven (x : Float) : Float := JuliaBase.F64.round x

/-- Julia `unsafe_trunc(Int, x)` for the small integers `rem_pio2` produces. -/
@[inline] def truncInt (x : Float) : Int := JuliaBase.F64.toIntTrunc x

/-! ### `exp` (`base/special/exp.jl`) -/

/-- Julia `expm1b_kernel(Val(:ℯ), x)`: `x * evalpoly(x, …)`. -/
@[inline] def expKernel (x : Float) : Float :=
  x * ma x (ma x (ma x (f64% 0.04166666857598777) (f64% 0.1666666857598779))
    (f64% 0.4999999999999997)) (f64% 0.9999999999999912)

/-- `MAGIC_ROUND_CONST(Float64)`. -/
def magic : Float := (f64% 6.755399441055744e15)

/-- Julia `table_unpack(N)`: `2^(j/256)` as a high/low pair, `j = N & 255`. -/
@[inline] def tableUnpack (n : Int64) : Float × Float :=
  let j : UInt64 := FieldConstants.Julia.jTable[(n.toUInt64 &&& 255).toNat]!
  (Float.ofBits ((0x3FF0000000000000 : UInt64) ||| (j &&& 0x000FFFFFFFFFFFFF)),
   Float.ofBits ((0x3C00000000000000 : UInt64) ||| (j >>> 8)))

/-- Argument reduction of `exp_impl`: `(N::Int32, r)` (`N` widened to `Int64`). -/
@[inline] def expReduce (x : Float) : Int64 × Float :=
  let nf := ma x (f64% 369.3299304675746) magic
  -- `reinterpret(UInt64, N_float) % Int32`: the low 32 bits, signed
  let n : Int64 := nf.toBits.toUInt32.toInt32.toInt64
  let nf := nf - magic
  let r := ma nf (-(f64% 0.002707606173999011)) x
  let r := ma nf (-(f64% 6.327543041662719e-14)) r
  (n, r)

/-- `2^k · small` by adding `k` to the exponent bits (Julia's
`reinterpret(T, Int64(k) << 52 + reinterpret(Int64, small))`, wrapping). -/
@[inline] def scale2k (k : Int64) (small : Float) : Float :=
  Float.ofBits ((k.toUInt64 <<< 52) + small.toBits)

/-- The scaling tail of `exp_impl` shared by both methods. -/
@[inline] def expScale (x small : Float) (k : Int64) (big : Bool) : Float :=
  if !(x.abs ≤ (f64% 708.3964185322641)) then
    if x.isNaN then x
    else if x ≥ (f64% 709.7827128933841) then inf
    else if x ≤ -(f64% 745.1332191019412) then (f64% 0.0)
    else if k ≤ -53 then
      Float.ofBits (((k + 53).toUInt64 <<< 52) + small.toBits) * (f64% 1.1102230246251565e-16)
    else if big && k == 1024 then (small * (f64% 2.0)) * (f64% 8.98846567431158e307)
    else scale2k k small
  else scale2k k small

/-- Julia `exp(x::Float64)` (`exp_impl(x, Val(:ℯ))`, `exp.jl:207-229`). -/
def exp (x : Float) : Float :=
  let (n, r) := expReduce x
  let (jU, jL) := tableUnpack n
  let small := ma jU (expKernel r) jL + jU
  expScale x small (n >>> 8) false

/-- Julia `exp_impl(x, xlo, Val(:ℯ))`: `e^(x + xlo)`, used by `^` (`exp.jl:231-258`). -/
def exp2Part (x xlo : Float) : Float :=
  let (n, r) := expReduce x
  let (jU, jL) := tableUnpack n
  let kern := expKernel r
  let verySmall := ma kern (jU * xlo) jL
  let hi := (f64% 1.0) + kern
  let lo := ((f64% 1.0) - hi) + kern
  let small := Float.fma jU hi (ma jU (lo + xlo) verySmall)
  expScale x small (n >>> 8) true

/-! ### `log`, `log1p` (`base/special/log.jl`) -/

/-- Julia `log_proc1(y, mf, F, f)` for base `e` (`log.jl:155-183`). -/
def logProc1 (y mf bigF f : Float) : Float :=
  let jp := ((f64% 128.0) * bigF).toUInt64.toNat - 127
  let (hb, lb) := FieldConstants.Julia.logTable64[jp - 1]!
  let hi := Float.ofBits hb
  let lo := Float.ofBits lb
  let lHi := mf * (f64% 0.6931471805601177) + hi
  let lLo := mf * (-(f64% 1.7239444525614835e-13)) + lo
  let u := ((f64% 2.0) * f) / (y + bigF)
  let v := u * u
  let q := u * v * ma v (f64% 0.012500053168098584) (f64% 0.08333333333303913)
  Float.fma (f64% 1.0) lHi (Float.fma (f64% 1.0) (u + (q + lLo)) ((f64% 0.0) * lHi))

/-- Julia `log_proc2(f)` for base `e` (`log.jl:186-209`). -/
def logProc2 (f : Float) : Float :=
  let g := (f64% 1.0) / ((f64% 2.0) + f)
  let u := (f64% 2.0) * f * g
  let v := u * u
  let q := u * v * ma v (ma v (ma v (f64% 0.0004348877777076146) (f64% 0.0022321399879194482))
      (f64% 0.012500000003771751)) (f64% 0.08333333333333179)
  Float.fma (f64% 1.0) u
    (Float.fma (f64% 0.0) u ((f64% 1.0) * Float.fma (Float.fma (-u) f ((f64% 2.0) * (f - u))) g q))

/-- Julia `log(x::Float64)` (`_log`, `log.jl:251-282`); `NaN` for `x < 0`. -/
def log (x : Float) : Float :=
  if x > (f64% 0.0) then
    if x.isInf then x
    else if (f64% 0.9394130628134757) < x && x < (f64% 1.0644944589178595) then logProc2 (x - (f64% 1.0))
    else
      let xu := x.toBits
      let m := ((xu >>> 52) &&& 0x7FF).toNat
      let (xu, m) : UInt64 × Int :=
        if m == 0 then
          let x' := x * (f64% 1.8014398509481984e16)
          let xu' := x'.toBits
          (xu', (((xu' >>> 52) &&& 0x7FF).toNat : Int) - 54)
        else (xu, m)
      let m := m - 1023
      let y := Float.ofBits ((xu &&& 0x000FFFFFFFFFFFFF) ||| 0x3FF0000000000000)
      let mf := (Int64.ofInt m).toFloat
      let bigF := (y + (f64% 3.5184372088832e13)) - (f64% 3.5184372088832e13)
      logProc1 y mf bigF (y - bigF)
  else if x == (f64% 0.0) then -inf
  else nan

/-- Julia `log1p(x::Float64)` (`log.jl:335-366`); `NaN` for `x < -1`. -/
def log1p (x : Float) : Float :=
  if x > -(f64% 1.0) then
    if x == inf then x
    else if -(f64% 1.1102230246251565e-16) < x && x < (f64% 1.1102230246251565e-16) then x
    else if -(f64% 0.06058693718652422) < x && x < (f64% 0.06449445891785943) then logProc2 x
    else
      let z := (f64% 1.0) + x
      let zu := z.toBits
      let s := Float.ofBits (0x7FE0000000000000 - (zu &&& 0xFFF0000000000000))
      let m : Int := (((zu >>> 52) &&& 0x7FF).toNat : Int) - 1023
      let c := if m > 0 then (f64% 1.0) - (z - x) else x - (z - (f64% 1.0))
      let y := Float.ofBits ((zu &&& 0x000FFFFFFFFFFFFF) ||| 0x3FF0000000000000)
      let mf := (Int64.ofInt m).toFloat
      let bigF := (y + (f64% 3.5184372088832e13)) - (f64% 3.5184372088832e13)
      let f := (y - bigF) + c * s
      logProc1 y mf bigF f
  else if x == -(f64% 1.0) then -inf
  else nan

/-! ### `^` (`base/special/pow.jl`) -/

/-- Julia `_log_ext(xu)`: `log(x)` as `hi + lo` with about 68 bits (`log.jl:549-587`). -/
@[inline] def logExt (xu : UInt64) : Float × Float :=
  let tmpU := xu - 0x3fe6955500000000
  let tmp := tmpU.toInt64
  let z := Float.ofBits (xu - (tmpU &&& 0xfff0000000000000))
  let k := (tmp >>> 52).toFloat
  let idx := ((tmpU >>> 45) &&& 127).toNat
  let t := FieldConstants.Julia.logTableT[idx]!
  let logctail := Float.ofBits FieldConstants.Julia.logTableTail[idx]!
  let invc := Float.ofBits (((t &&& 0xff) ||| 0x1ff00) <<< 45)
  let logc := Float.ofBits (t &&& (~~~ (0xff : UInt64)))
  let r := Float.fma z invc (-(f64% 1.0))
  let t1 := ma k (f64% 0.6931471805598903) logc
  let t2 := t1 + r
  let lo1 := ma k (f64% 5.497923018708371e-14) logctail
  let lo2 := t1 - t2 + r
  let ar := -(f64% 0.5) * r
  let ar2 := r * ar
  let lo3 := Float.fma r ar (-ar2)
  let hi := t2 + ar2
  let lo4 := t2 - hi + ar2
  let p := ma r (ma r (ma r (ma r (ma r (f64% 0.25001038159188854) (-(f64% 0.28572740711487526)))
      (f64% 0.33333333317438696)) (-(f64% 0.3999999997661988))) (f64% 0.5000000000000007)) (-(f64% 0.6666666666666679))
  let lo := lo1 + lo2 + lo3 + ma (r * ar2) p lo4
  (hi, lo)

/-- Julia `pow_body(x::Float64, y::Float64)` for positive finite `x` (`pow.jl:98-110`). -/
def powBody (x y : Float) : Float :=
  let xu := x.toBits
  let xu :=
    if xu < 0x0010000000000000 then
      let xu := (x * (f64% 4.503599627370496e15)).toBits &&& 0x7FFFFFFFFFFFFFFF
      xu - ((52 : UInt64) <<< 52)
    else xu
  let (logxhi, logxlo) := logExt xu
  let xyhi := logxhi * y
  let xylo := Float.fma logxhi y (-xyhi)
  let xylo := ma logxlo y xylo
  let hi := xyhi + xylo
  exp2Part hi (xylo - (hi - xyhi))

/-- Julia `pow_body(x::Float64, n::Integer)`: compensated power by squaring
(`pow.jl:120-142`). -/
def powBodyInt (x : Float) (n : Int) : Float :=
  if n == 3 then x * x * x
  else if n < 0 then
    let rx := (f64% 1.0) / x
    if n == -2 then rx * rx
    else
      let xnlo := if x.isFinite then -(Float.fma x rx (-(f64% 1.0))) * rx else -(f64% 0.0)
      loop rx xnlo (f64% 1.0) (f64% 0.0) (-n).toNat 70
  else loop x (-(f64% 0.0)) (f64% 1.0) (f64% 0.0) n.toNat 70
where
  /-- The squaring loop; `fuel` bounds the iterations (`n < 2^70`). -/
  loop (x xnlo y ynlo : Float) (n : Nat) : Nat → Float
    | 0 => x * y
    | fuel + 1 =>
      if n > 1 then
        let (y, ynlo) :=
          if n % 2 == 1 then
            let err := ma y xnlo (x * ynlo)
            let y' := x * y
            (y', Float.fma x y (-y') + err)
          else (y, ynlo)
        let err := x * (f64% 2.0) * xnlo
        let x' := x * x
        loop x' (Float.fma x x (-x') + err) y ynlo (n / 2) fuel
      else
        let err := ma y xnlo (x * ynlo)
        -- `ifelse(…, muladd(x, y, err), x*y)`: the product `x*y` is shared by both
        -- branches, so LLVM keeps it and the `muladd` is *not* fused here
        -- (measured: fusing mismatches Julia on 22 % of integer exponents)
        let xy := x * y
        if x.isFinite && err.isFinite then xy + err else xy

/-- Julia `^(x::Float64, y::Float64)` (`pow.jl:7-29`). A negative base with a
non-integer exponent (a `DomainError`) gives `NaN`. -/
def pow (x y : Float) : Float :=
  if x.toBits == ((f64% 1.0) : Float).toBits then (f64% 1.0)
  else
    let y := if !(y.abs < (f64% 6.917529027641082e18)) then
        (if y.isNaN then y else if y > 0 then (f64% 6.917529027641082e18) else -(f64% 6.917529027641082e18))
      else y
    if y.isNaN then y
    else
      -- `yint = unsafe_trunc(Int64, y)` (`|y| < 1.5·2^62` here)
      let yint : Int64 := (if y < 0 then -((-y).floor) else y.floor).toInt64
      let yisint := y == yint.toFloat
      if yisint && yint == 0 then (f64% 1.0)
      else if yisint && -4096 ≤ yint && yint ≤ 24576 then powBodyInt x yint.toInt
      else if 2 * x.toBits == 0 then
        (if y > 0 then (f64% 0.0) else inf)
      else if x < 0 && !yisint then nan
      else
        let neg := x < 0 && yint % 2 != 0
        let s := if neg then -(f64% 1.0) else (f64% 1.0)
        if !x.isFinite then
          -- `copysign(x,s)*(y>0 || isnan(x))`: `Float64 * false` is a signed zero
          (if y > 0 || x.isNaN then copysign x s else copysign (f64% 0.0) (copysign x s))
        else copysign (powBody x.abs y) s

/-! ### `sin`, `cos`, `tan` (`base/special/trig.jl`, `rem_pio2.jl`) -/

/-- A double-double `hi + lo` (Julia `DoubleFloat64`). -/
structure DD where
  /-- leading part -/
  hi : Float
  /-- trailing part -/
  lo : Float

/-- Julia `cody_waite_2c_pio2(x, fn, n)` (`rem_pio2.jl:40-47`). -/
@[inline] def codyWaite2c (x fn : Float) (n : Int) : Int × DD :=
  let z := ma (-fn) (f64% 1.57079632673412561417e+00) x
  let y1 := ma (-fn) (f64% 6.07710050650619224932e-11) z
  let y2 := ma (-fn) (f64% 6.07710050650619224932e-11) (z - y1)
  (n, ⟨y1, y2⟩)

/-- Julia `cody_waite_ext_pio2(x, xhp)` (`rem_pio2.jl:49-87`). -/
@[inline] def codyWaiteExt (x : Float) (xhp : UInt32) : Int × DD :=
  let pio21 := (f64% 1.57079632673412561417e+00)
  let pio21t := (f64% 6.07710050650619224932e-11)
  let pio22 := (f64% 6.07710050630396597660e-11)
  let pio22t := (f64% 2.02226624879595063154e-21)
  let pio23 := (f64% 2.02226624871116645580e-21)
  let pio23t := (f64% 8.47842766036889956997e-32)
  let fn := roundEven (x * (f64% 0.6366197723675814))
  let r := ma (-fn) pio21 x
  let w := fn * pio21t
  let j := xhp >>> 20
  let y1 := r - w
  let i := j - ((highword y1 >>> 20) &&& 0x7ff)
  let (r, w, y1) :=
    if i > 16 then
      let t := r
      let w := fn * pio22
      let r := t - w
      let w := ma fn pio22t (-((t - r) - w))
      let y1 := r - w
      let i := j - ((highword y1 >>> 20) &&& 0x7ff)
      if i > 49 then
        let t := r
        let w := fn * pio23
        let r := t - w
        let w := ma fn pio23t (-((t - r) - w))
        (r, w, r - w)
      else (r, w, y1)
    else (r, w, y1)
  let y2 := (r - y1) - w
  (truncInt fn, ⟨y1, y2⟩)

/-- Julia `INV_2PI`: the bits of `1/(2π)` in 64-bit words (`rem_pio2.jl:26-38`). -/
def inv2pi : Array UInt64 := #[
  0x28be60db9391054a, 0x7f09d5f47d4d3770, 0x36d8a5664f10e410, 0x7f9458eaf7aef158,
  0x6dc91b8e909374b8, 0x01924bba82746487, 0x3f877ac72c4a69cf, 0xba208d7d4baed121,
  0x3a671c09ad17df90, 0x4e64758e60d4ce7d, 0x272117e2ef7e4a0e, 0xc7fe25fff7816603,
  0xfbcbc462d6829b47, 0xdb4d9fb3c9f2c26d, 0xd3d18fd9a797fa8b, 0x5d49eeb1faf97c5e,
  0xcf41ce7de294a4ba, 0x9afed7ec47e35742, 0x1580cc11bf1edaea]

/-- Number of significant bits of a natural number (Julia `top_set_bit`). -/
def topSetBit (x : Nat) : Nat := x.log2 + 1

/-- Julia `x >> s` on an unsigned integer, where a negative `s` shifts left. -/
@[inline] def shr (x : Nat) (s : Int) : Nat :=
  if s ≥ 0 then x >>> s.toNat else x <<< (-s).toNat

/-- Julia `fromfraction(f::Int128)`: `(z1, z2)` with `z1 + z2 == f / 2^128`
(`rem_pio2.jl:96-122`); the magnitude and sign are passed separately. -/
def fromFraction (neg : Bool) (x : Nat) : Float × Float :=
  if x == 0 then ((f64% 0.0), (f64% 0.0))
  else
    let s : UInt64 := if neg then 0x8000000000000000 else 0
    let n1 : Int := topSetBit x
    let m1 : UInt64 := (((shr x (n1 - 26)) % 2 ^ 64).toUInt64 : UInt64) <<< (27 : UInt64)
    let d1 : UInt64 := (FieldConstants.Julia.u64OfInt (n1 - 128 + 1021)) <<< 52
    let z1 := Float.ofBits (s ||| (d1 + m1))
    let x2 := (x - (shr m1.toNat (53 - n1) % 2 ^ 128)) % 2 ^ 128
    if x2 == 0 then (z1, (f64% 0.0))
    else
      let n2 : Int := topSetBit x2
      let m2 : UInt64 := ((shr x2 (n2 - 53)) % 2 ^ 64).toUInt64
      let d2 : UInt64 := (FieldConstants.Julia.u64OfInt (n2 - 128 + 1021)) <<< 52
      (z1, Float.ofBits (s ||| (d2 + m2)))

/-- Julia `paynehanek(x)`: reduction of a huge argument modulo `π/2`
(`rem_pio2.jl:124-196`), with the 128-bit integer arithmetic done in `Nat`. -/
def paynehanek (x : Float) : Int × DD :=
  let u := x.toBits
  let bigX : Nat := ((u &&& 0x000FFFFFFFFFFFFF) ||| 0x0010000000000000).toNat
  let rawExp : Int := ((u &&& 0x7FF0000000000000) >>> 52).toNat
  let k : Int := rawExp - 1023 - 52
  let idx : Int := Int.fdiv k 64
  let shift : Nat := (k - idx * 64).toNat
  let word (i : Int) : Nat := if i < 0 then 0 else (inv2pi[i.toNat]!).toNat
  let m64 : Nat := 2 ^ 64
  let (a1, a2, a3) : Nat × Nat × Nat :=
    if shift == 0 then (word idx, word (idx + 1), word (idx + 2))
    else
      ((((word idx) <<< shift) % m64) ||| (word (idx + 1) >>> (64 - shift)),
       (((word (idx + 1)) <<< shift) % m64) ||| (word (idx + 2) >>> (64 - shift)),
       (((word (idx + 2)) <<< shift) % m64) ||| (word (idx + 3) >>> (64 - shift)))
  let m128 : Nat := 2 ^ 128
  let w1 := (((bigX * a1) % m64) <<< 64) % m128
  let w2 := bigX * a2
  let w3 := (bigX * a3) >>> 64
  let w := (w1 + w2 + w3) % m128
  -- flipsign(w, x): two's complement negation modulo 2^128
  let w := if signbit x then (m128 - w) % m128 else w
  -- signed view of a 128-bit pattern (Julia `% Int128`)
  let signed (v : Nat) : Int := if v ≥ 2 ^ 127 then (v : Int) - m128 else v
  -- `(((w>>125)%Int + 1)>>1)`: a logical shift of the unsigned `w`
  let q : Int := Int.fdiv ((w >>> 125 : Nat) + 1) 2
  let f : Int := signed ((w <<< 2) % m128)
  let (zhi, zlo) := fromFraction (f < 0) f.natAbs
  let pio2 := (f64% 1.5707963267948966)
  let pio2hi := (f64% 1.5707963407039642)
  let pio2lo := -(f64% 1.3909067614167116e-8)
  let yhi := (zhi + zlo) * pio2
  let ylo := (((zhi * pio2hi - yhi) + zhi * pio2lo) + zlo * pio2hi) + zlo * pio2lo
  (q, ⟨yhi, ylo⟩)

/-- Julia `rem_pio2_kernel(x::Float64)`: `(k, r)` with `k·π/2 = x - r`
(`rem_pio2.jl:198-266`). -/
@[inline] def remPio2 (x : Float) : Int × DD :=
  let xhp := poshighword x
  if xhp ≤ 0x400f6a7a then
    if (xhp &&& 0xfffff) == 0x921fb then codyWaiteExt x xhp
    else if xhp ≤ 0x4002d97c then
      if x > (f64% 0.0) then codyWaite2c x (f64% 1.0) 1 else codyWaite2c x (-(f64% 1.0)) (-1)
    else
      if x > (f64% 0.0) then codyWaite2c x (f64% 2.0) 2 else codyWaite2c x (-(f64% 2.0)) (-2)
  else if xhp ≤ 0x401c463b then
    if xhp ≤ 0x4015fdbc then
      if xhp == 0x4012d97c then codyWaiteExt x xhp
      else if x > (f64% 0.0) then codyWaite2c x (f64% 3.0) 3 else codyWaite2c x (-(f64% 3.0)) (-3)
    else
      if xhp == 0x401921fb then codyWaiteExt x xhp
      else if x > (f64% 0.0) then codyWaite2c x (f64% 4.0) 4 else codyWaite2c x (-(f64% 4.0)) (-4)
  else if xhp < 0x413921fb then codyWaiteExt x xhp
  else paynehanek x

/-- `DS1…DS6`: the sine polynomial. -/
def ds1 : Float := -(f64% 1.66666666666666324348e-01)
/-- sine coefficient -/ def ds2 : Float := (f64% 8.33333333332248946124e-03)
/-- sine coefficient -/ def ds3 : Float := -(f64% 1.98412698298579493134e-04)
/-- sine coefficient -/ def ds4 : Float := (f64% 2.75573137070700676789e-06)
/-- sine coefficient -/ def ds5 : Float := -(f64% 2.50507602534068634195e-08)
/-- sine coefficient -/ def ds6 : Float := (f64% 1.58969099521155010221e-10)
/-- cosine coefficient -/ def dc1 : Float := (f64% 4.16666666666666019037e-02)
/-- cosine coefficient -/ def dc2 : Float := -(f64% 1.38888888888741095749e-03)
/-- cosine coefficient -/ def dc3 : Float := (f64% 2.48015872894767294178e-05)
/-- cosine coefficient -/ def dc4 : Float := -(f64% 2.75573143513906633035e-07)
/-- cosine coefficient -/ def dc5 : Float := (f64% 2.08757232129817482790e-09)
/-- cosine coefficient -/ def dc6 : Float := -(f64% 1.13596475577881948265e-11)

/-- Julia `sin_kernel(y::Float64)` on `[-π/4, π/4]` (`trig.jl:76-82`). -/
@[inline] def sinKernel (y : Float) : Float :=
  let y2 := y * y
  let y4 := y2 * y2
  let r := (y2 * ma y2 ds4 ds3 + ds2) + y2 * y4 * ma y2 ds6 ds5
  let y3 := y2 * y
  y + y3 * (ds1 + y2 * r)

/-- Julia `sin_kernel(y::DoubleFloat64)` (`trig.jl:69-75`). -/
@[inline] def sinKernelDD (y : DD) : Float :=
  let y2 := y.hi * y.hi
  let y4 := y2 * y2
  let r := (y2 * ma y2 ds4 ds3 + ds2) + y2 * y4 * ma y2 ds6 ds5
  let y3 := y2 * y.hi
  y.hi - ((y2 * ((f64% 0.5) * y.lo - y3 * r) - y.lo) - y3 * ds1)

/-- Julia `cos_kernel(y::Float64)` (`trig.jl:144-151`). -/
@[inline] def cosKernel (y : Float) : Float :=
  let y2 := y * y
  let y4 := y2 * y2
  let r := y2 * ma y2 (ma y2 dc3 dc2) dc1 + y4 * y4 * ma y2 (ma y2 dc6 dc5) dc4
  let halfY2 := (f64% 0.5) * y2
  let w := (f64% 1.0) - halfY2
  w + ((((f64% 1.0) - w) - halfY2) + (y2 * r))

/-- Julia `cos_kernel(y::DoubleFloat64)` (`trig.jl:136-143`). -/
@[inline] def cosKernelDD (y : DD) : Float :=
  let y2 := y.hi * y.hi
  let y4 := y2 * y2
  let r := y2 * ma y2 (ma y2 dc3 dc2) dc1 + y4 * y4 * ma y2 (ma y2 dc6 dc5) dc4
  let halfY2 := (f64% 0.5) * y2
  let w := (f64% 1.0) - halfY2
  w + ((((f64% 1.0) - w) - halfY2) + (y2 * r - y.hi * y.lo))

/-- Julia `sin(x::Float64)` (`trig.jl:29-52`); `NaN` for infinite `x`. -/
def sin (x : Float) : Float :=
  let absx := x.abs
  if absx < (f64% 0.7853981633974483) then
    if absx < (f64% 1.4901161193847656e-8) then x else sinKernel x
  else if x.isNaN then x
  else if x.isInf then nan
  else
    let (n, y) := remPio2 x
    match (n.emod 4) with
    | 0 => sinKernelDD y
    | 1 => cosKernelDD y
    | 2 => -sinKernelDD y
    | _ => -cosKernelDD y

/-- Julia `cos(x::Float64)` (`trig.jl:98-122`); `NaN` for infinite `x`. -/
def cos (x : Float) : Float :=
  let absx := x.abs
  if absx < (f64% 0.7853981633974483) then
    if absx < (f64% 1.0536712127723509e-8) then (f64% 1.0) else cosKernel x
  else if x.isNaN then x
  else if x.isInf then nan
  else
    let (n, y) := remPio2 x
    match (n.emod 4) with
    | 0 => cosKernelDD y
    | 1 => -sinKernelDD y
    | 2 => -cosKernelDD y
    | _ => sinKernelDD y

/-- Julia `tan_kernel(y::DoubleFloat64, k)` (`trig.jl:239-338`): `tan(y)` when
`k = 1`, `-1/tan(y)` when `k = -1`. -/
def tanKernel (y : DD) (k : Float) : Float :=
  let big := y.hi.abs ≥ (f64% 0.6744)
  let (yhi, ylo) :=
    if big then
      let (yhi, ylo) := if y.hi < (f64% 0.0) then (-y.hi, -y.lo) else (y.hi, y.lo)
      (((f64% 0.7853981633974483) - yhi) + ((f64% 3.06161699786838301793e-17) - ylo), (f64% 0.0))
    else (y.hi, y.lo)
  let y2 := yhi * yhi
  let y4 := y2 * y2
  let r := ma y4 (ma y4 (ma y4 (ma y4 (ma y4 (-(f64% 1.85586374855275456654e-05))
      (f64% 7.81794442939557092300e-05)) (f64% 5.88041240820264096874e-04)) (f64% 3.59207910759131235356e-03))
      (f64% 2.18694882948595424599e-02)) (f64% 1.33333333333201242699e-01)
  let v := y2 * ma y4 (ma y4 (ma y4 (ma y4 (ma y4 (f64% 2.59073051863633712884e-05)
      (f64% 7.14072491382608190305e-05)) (f64% 2.46463134818469906812e-04)) (f64% 1.45620945432529025516e-03))
      (f64% 8.86323982359930005737e-03)) (f64% 5.39682539762260521377e-02)
  let y3 := y2 * yhi
  let r := ylo + y2 * (y3 * (r + v) + ylo)
  let r := r + (f64% 3.33333333333334091986e-01) * y3
  let px := yhi + r
  if big then
    (if signbit y.hi then -(f64% 1.0) else (f64% 1.0)) * (k - (f64% 2.0) * (yhi - (px * px / (k + px) - r)))
  else if k == (f64% 1.0) then px
  else
    let px0 := truncLow px
    let v := r - (px0 - yhi)
    let a := -(f64% 1.0) / px
    let t := truncLow a
    let s := (f64% 1.0) + t * px0
    t + a * (s + t * v)

/-- Julia `tan(x::Float64)` (`trig.jl:218-236`); `NaN` for infinite `x`. -/
def tan (x : Float) : Float :=
  let absx := x.abs
  if absx < (f64% 0.7853981633974483) then
    if absx < (f64% 7.450580596923828e-9) then x else tanKernel ⟨x, (f64% 0.0)⟩ (f64% 1.0)
  else if x.isNaN then x
  else if x.isInf then nan
  else
    let (n, y) := remPio2 x
    if n % 2 == 0 then tanKernel y (f64% 1.0) else tanKernel y (-(f64% 1.0))

/-! ### `atan`, `asin` (`trig.jl`) -/

/-- Julia `atan_pq(x)` (`trig.jl:482-502`). -/
@[inline] def atanPQ (x : Float) : Float × Float :=
  let x2 := x * x
  let x4 := x2 * x2
  let p := x2 * ma x4 (ma x4 (ma x4 (ma x4 (ma x4 (f64% 1.62858201153657823623e-02)
      (f64% 4.97687799461593236017e-02)) (f64% 6.66107313738753120669e-02)) (f64% 9.09088713343650656196e-02))
      (f64% 1.42857142725034663711e-01)) (f64% 3.33333333333329318027e-01)
  let q := x4 * ma x4 (ma x4 (ma x4 (ma x4 (-(f64% 3.65315727442169155270e-02))
      (-(f64% 5.83357013379057348645e-02))) (-(f64% 7.69187620504482999495e-02)))
      (-(f64% 1.11111104054623557880e-01))) (-(f64% 1.99999999998764832476e-01))
  (p, q)

/-- Julia `atan(x::Float64)` (`trig.jl:504-558`). -/
def atan (x : Float) : Float :=
  let absx := x.abs
  if absx ≥ (f64% 7.378697629483821e19) then copysign (f64% 1.5707963267948966) x
  else if absx < (f64% 0.4375) then
    if absx < (f64% 7.450580596923828e-9) then x
    else
      let (p, q) := atanPQ x
      x - x * (p + q)
  else
    let xsign := if x > (f64% 0.0) then (f64% 1.0) else if x < (f64% 0.0) then -(f64% 1.0) else x
    let (hi, lo, x) :=
      if absx < (f64% 1.1875) then
        if absx < (f64% 0.6875) then
          ((f64% 4.63647609000806093515e-01), (f64% 2.26987774529616870924e-17),
            ((f64% 2.0) * absx - (f64% 1.0)) / ((f64% 2.0) + absx))
        else
          ((f64% 7.85398163397448278999e-01), (f64% 3.06161699786838301793e-17),
            (absx - (f64% 1.0)) / (absx + (f64% 1.0)))
      else if absx < (f64% 2.4375) then
        ((f64% 9.82793723247329054082e-01), (f64% 1.39033110312309984516e-17),
          (absx - (f64% 1.5)) / ((f64% 1.0) + (f64% 1.5) * absx))
      else
        ((f64% 1.57079632679489655800e+00), (f64% 6.12323399573676603587e-17), -(f64% 1.0) / absx)
    let (p, q) := atanPQ x
    let z := hi - ((x * (p + q) - lo) - x)
    copysign z xsign

/-- Julia `arc_p(t)/arc_q(t)`, the rational kernel of `asin` (`trig.jl:368-393`). -/
@[inline] def arcTRt (t : Float) : Float :=
  let p := t * ma t (ma t (ma t (ma t (ma t (f64% 3.47933107596021167570e-05)
      (f64% 7.91534994289814532176e-04)) (-(f64% 4.00555345006794114027e-02))) (f64% 2.01212532134862925881e-01))
      (-(f64% 3.25565818622400915405e-01))) (f64% 1.66666666666666657415e-01)
  let q := ma t (ma t (ma t (ma t (f64% 7.70381505559019352791e-02) (-(f64% 6.88283971605453293030e-01)))
      (f64% 2.02094576023350569471e+00)) (-(f64% 2.40339491173441421878e+00))) (f64% 1.0)
  p / q

/-- Julia `asin(x::Float64)` (`trig.jl:396-454`); `NaN` for `|x| > 1`. -/
def asin (x : Float) : Float :=
  let absx := x.abs
  if absx ≥ (f64% 1.0) then
    if absx == (f64% 1.0) then flipsign (f64% 1.5707963267948966) x else nan
  else if absx < (f64% 0.5) then
    if absx < (f64% 1.4901161193847656e-8) then x else ma x (arcTRt (x * x)) x
  else
    let t := ((f64% 1.0) - absx) / (f64% 2.0)
    let pio2lo := (f64% 6.12323399573676603587e-17)
    let s := t.sqrt
    let tRt := arcTRt t
    if absx ≥ (f64% 0.975) then
      flipsign ((f64% 1.5707963267948966) - ((f64% 2.0) * (s + s * tRt) - pio2lo)) x
    else
      let s0 := truncLow s
      let c := (t - s0 * s0) / (s + s0)
      let p := (f64% 2.0) * s * tRt - (pio2lo - (f64% 2.0) * c)
      let q := (f64% 0.7853981633974483) - (f64% 2.0) * s0
      flipsign ((f64% 0.7853981633974483) - (p - q)) x

/-- Julia `atanh(x::Float64)` (`hyperbolic.jl:241-266`); `NaN` for `|x| > 1`. -/
def atanh (x : Float) : Float :=
  if x.isNaN then x
  else
    let absx := x.abs
    if absx > (f64% 1.0) then nan
    else
      let t := if absx < (f64% 0.5) then log1p ((f64% 2.0) * absx / ((f64% 1.0) - absx))
        else log (((f64% 1.0) + absx) / ((f64% 1.0) - absx))
      (f64% 0.5) * copysign t x

end Geophysics.JMath
