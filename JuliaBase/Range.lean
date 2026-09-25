import JuliaBase.Num

/-!
Julia's floating-point ranges, bit for bit.

* `LinRange(start, stop, len)` (Julia `base/range.jl:579-610, 979-985`): element `i` is
  `(1-t)*start + t*stop` with `t = (i-1)/(len-1)`, computed directly (no accumulation).
* `range(start, stop; length)` for `Float64` (`base/twiceprecision.jl:645-747`) is *not* a
  `LinRange`: it is a `StepRangeLen` whose reference point and step are
  `TwicePrecision{Float64}` (double-double) values, chosen by first looking for an exact
  rational description of the endpoints (`rat`). Its elements differ from `LinRange`'s in
  the last bit for many inputs, so the port keeps both.
* `start:step:stop` (`(:)(start, step, stop)`, twiceprecision.jl:390-432) and
  `range(start; step, length)` (twiceprecision.jl:447-466), which share the same
  `floatrange`/`steprangelen_hp` machinery.

All arithmetic is replayed in Julia's order; `mul12` uses a fused multiply-add as Julia
does on FMA hardware (`Math.two_mul`, math.jl:54).
-/

namespace JuliaBase

/-- Julia `TwicePrecision{Float64}` (twiceprecision.jl:199): the unevaluated sum `hi + lo`. -/
structure TwicePrecision where
  /-- most significant part -/
  hi : Float
  /-- least significant part -/
  lo : Float
  deriving Repr, Inhabited

namespace TwicePrecision

/-- Julia `truncbits(x, nb)` (twiceprecision.jl:32): clear the low `nb` bits of the
representation. -/
@[inline] def truncbits (x : Float) (nb : Nat) : Float :=
  if nb ≥ 64 then Float.ofBits 0
  else Float.ofBits (x.toBits &&& ((0xFFFFFFFFFFFFFFFF : UInt64) <<< nb.toUInt64))

/-- Julia `canonicalize2(big, little)` (twiceprecision.jl:45). -/
@[inline] def canonicalize2 (big little : Float) : TwicePrecision :=
  let h := big + little
  ⟨h, (big - h) + little⟩

/-- Julia `add12(x, y)` (twiceprecision.jl:79): exact `x + y` as `hi + lo`. -/
@[inline] def add12 (x y : Float) : TwicePrecision :=
  if y.abs > x.abs then canonicalize2 y x else canonicalize2 x y

/-- Julia `mul12(x, y)` (twiceprecision.jl:111): exact `x * y` via `fma`. -/
@[inline] def mul12 (x y : Float) : TwicePrecision :=
  let h := x * y
  if !h.isFinite then ⟨h, h⟩ else ⟨h, Float.fma x y (-h)⟩

/-- Julia `splitprec(Float64, i)` then `canonicalize2` = `TwicePrecision{Float64}(i::Integer)`
(twiceprecision.jl:22, 214): an integer as an exact double-double. -/
def ofInt (i : Int) : TwicePrecision :=
  let hi := truncbits (Float.ofInt i) 27
  let ihi := F64.toIntTrunc hi
  canonicalize2 hi (Float.ofInt (i - ihi))

/-- Julia `TwicePrecision{Float64}(x::Float64)` = `(x, 0.0)`. -/
@[inline] def ofFloat (x : Float) : TwicePrecision := ⟨x, 0⟩

/-- Julia `/(x::TwicePrecision, y::TwicePrecision)` (twiceprecision.jl:329). -/
def div (x y : TwicePrecision) : TwicePrecision :=
  let hi := x.hi / y.hi
  let u := mul12 hi y.hi
  let lo := ((((x.hi - u.hi) - u.lo) + x.lo) - hi * y.lo) / y.hi
  if hi == 0 || !hi.isFinite then ⟨hi, hi⟩ else canonicalize2 hi lo

/-- Julia `TwicePrecision{Float64}((num, den))` (twiceprecision.jl:224):
`TwicePrecision(num) / Float64(den)`. -/
@[inline] def ofRatio (num den : Int) : TwicePrecision :=
  div (ofInt num) (ofFloat (Float.ofInt den))

/-- Julia `twiceprecision(val::TwicePrecision, nb)` (twiceprecision.jl:246): truncate `hi` to
make `k * hi` exact for small `k`, pushing the remainder into `lo`. -/
@[inline] def twiceprecision (v : TwicePrecision) (nb : Nat) : TwicePrecision :=
  let hi := truncbits v.hi nb
  ⟨hi, (v.hi - hi) + v.lo⟩

/-- Julia `Float64(x::TwicePrecision)` = `hi + lo` (twiceprecision.jl:268). -/
@[inline] def toFloat (x : TwicePrecision) : Float := x.hi + x.lo

/-- Julia `+(x::TwicePrecision, y::TwicePrecision)` (twiceprecision.jl:293). -/
def add (x y : TwicePrecision) : TwicePrecision :=
  let r := x.hi + y.hi
  let s :=
    if x.hi.abs > y.hi.abs then (((x.hi - r) + y.hi) + y.lo) + x.lo
    else (((y.hi - r) + x.hi) + x.lo) + y.lo
  canonicalize2 r s

/-- Julia `-(x::TwicePrecision)`. -/
@[inline] def neg (x : TwicePrecision) : TwicePrecision := ⟨-x.hi, -x.lo⟩

/-- Julia `+(x::TwicePrecision, y::Number)` (twiceprecision.jl:287). -/
def addFloat (x : TwicePrecision) (y : Float) : TwicePrecision :=
  let s := add12 x.hi y
  canonicalize2 s.hi (s.lo + x.lo)

/-- Julia `*(x::TwicePrecision, y::TwicePrecision)` (twiceprecision.jl:317). -/
def mul (x y : TwicePrecision) : TwicePrecision :=
  let z := mul12 x.hi y.hi
  if z.hi == 0 || !z.hi.isFinite then ⟨z.hi, z.hi⟩
  else canonicalize2 z.hi ((x.hi * y.lo + x.lo * y.hi) + z.lo)

/-- Julia `*(x::TwicePrecision, v::Number)` for a float `v` (twiceprecision.jl:303). -/
def mulFloat (x : TwicePrecision) (v : Float) : TwicePrecision :=
  if v == 0 then ⟨x.hi * v, x.lo * v⟩ else mul x (ofFloat v)

/-- Julia `/(x::TwicePrecision, v::Number)` for a float `v` (twiceprecision.jl:325). -/
@[inline] def divFloat (x : TwicePrecision) (v : Float) : TwicePrecision := div x (ofFloat v)

end TwicePrecision

open TwicePrecision

/-- Julia `StepRangeLen{Float64, TwicePrecision{Float64}, TwicePrecision{Float64}, Int}`:
element `i` (1-based) is `ref + (i - offset) * step`, evaluated in double-double. -/
structure StepRangeLen where
  /-- the reference value (the element of smallest magnitude, for accuracy) -/
  ref : TwicePrecision
  /-- the step; `step.hi` has enough trailing zeros that `k * step.hi` is exact -/
  step : TwicePrecision
  /-- number of elements -/
  len : Nat
  /-- the index of `ref` -/
  offset : Int
  deriving Repr, Inhabited

namespace StepRangeLen

/-- Julia `unsafe_getindex(r::StepRangeLen{T,<:TwicePrecision,<:TwicePrecision}, i)`
(twiceprecision.jl:477-483), 1-based and unchecked. -/
def get (r : StepRangeLen) (i : Int) : Float :=
  let u := Float.ofInt (i - r.offset)
  let shiftHi := u * r.step.hi
  let shiftLo := u * r.step.lo
  let x := add12 r.ref.hi shiftHi
  x.hi + (x.lo + (shiftLo + r.ref.lo))

/-- Julia `first(r)`. -/
@[inline] def first (r : StepRangeLen) : Float := r.get 1

/-- Julia `last(r)`. -/
@[inline] def last (r : StepRangeLen) : Float := r.get r.len

/-- Julia `step(r)` = `Float64(r.step)` (twiceprecision.jl:434). -/
@[inline] def stepValue (r : StepRangeLen) : Float := r.step.toFloat

/-- Julia `collect(r)`, packed. -/
def toFloatArray (r : StepRangeLen) : FloatArray :=
  go r.len (FloatArray.emptyWithCapacity r.len) 1
where
  /-- tail-recursive fill -/
  go : Nat → FloatArray → Int → FloatArray
    | 0, acc, _ => acc
    | n + 1, acc, i => go n (acc.push (r.get i)) (i + 1)

/-- Julia `-(r)` / `.-r` for a `TwicePrecision` `StepRangeLen` (range.jl `-(r::StepRangeLen)`):
negate `ref` and `step`. -/
def neg (r : StepRangeLen) : StepRangeLen := { r with ref := r.ref.neg, step := r.step.neg }

/-- Julia `nbitslen(len, offset)` (twiceprecision.jl:257):
`len < 2 ? 0 : top_set_bit(max(offset-1, len-offset) - 1) + 1`, capped at
`cld(precision(Float64), 2) = 27`. -/
def nbitslen (len : Nat) (offset : Int) : Nat :=
  if len < 2 then 0
  else
    let x := (max (offset - 1) ((len : Int) - offset) - 1).toNat
    Nat.min 27 (Nat.log2 x + (if x == 0 then 0 else 1) + 1)

/-- Julia `x * r` (and `r * x`) for a real `x` (twiceprecision.jl:533):
`StepRangeLen(x*ref, twiceprecision(x*step, nbitslen(r)), length(r), offset)`. Note that
the broadcast `x .* r` differs (`bcastMul`). -/
def mulFloat (x : Float) (r : StepRangeLen) : StepRangeLen :=
  { r with ref := r.ref.mulFloat x,
           step := twiceprecision (r.step.mulFloat x) (nbitslen r.len r.offset) }

/-- Julia `r / x` for a real `x` (twiceprecision.jl:536): as `mulFloat`, with the step
re-truncated. The broadcast `r ./ x` differs (`bcastDiv`). -/
def divFloat (r : StepRangeLen) (x : Float) : StepRangeLen :=
  { r with ref := r.ref.divFloat x,
           step := twiceprecision (r.step.divFloat x) (nbitslen r.len r.offset) }

/-- Julia `x .* r` and `r .* x` (broadcast.jl:1174, 1181):
`StepRangeLen(x*r.ref, x*r.step, length(r), r.offset)`, without re-truncating the step. -/
def bcastMul (x : Float) (r : StepRangeLen) : StepRangeLen :=
  { r with ref := r.ref.mulFloat x, step := r.step.mulFloat x }

/-- Julia `r ./ x` (broadcast.jl:1189): `StepRangeLen(r.ref/x, r.step/x, length(r), r.offset)`. -/
def bcastDiv (r : StepRangeLen) (x : Float) : StepRangeLen :=
  { r with ref := r.ref.divFloat x, step := r.step.divFloat x }

/-- Julia `r .+ x` and `x .+ r` (broadcast.jl:1150-1153): shift `ref`, keep `step`. -/
def bcastAdd (r : StepRangeLen) (x : Float) : StepRangeLen :=
  { r with ref := r.ref.addFloat x }

/-- Julia `r .- x` (broadcast.jl:1164): `StepRangeLen(r.ref - x, r.step, …)`. -/
def bcastSub (r : StepRangeLen) (x : Float) : StepRangeLen :=
  { r with ref := r.ref.addFloat (-x) }

/-- Julia `x .- r` (broadcast.jl:1166): `StepRangeLen(x - r.ref, -r.step, …)`. -/
def bcastRSub (x : Float) (r : StepRangeLen) : StepRangeLen :=
  { r with ref := r.ref.neg.addFloat x, step := r.step.neg }

end StepRangeLen

/-- Julia `steprangelen_hp(Float64, ref::(Int,Int), step::(Int,Int), nb, len, offset)`
(twiceprecision.jl:340). -/
def steprangelenRatio (refNum refDen stepNum stepDen : Int) (nb len : Nat) (offset : Int) :
    StepRangeLen :=
  ⟨ofRatio refNum refDen, twiceprecision (ofRatio stepNum stepDen) nb, len, offset⟩

/-- Julia `steprangelen_hp(Float64, ref::Float64 or (hi,lo), step::(hi,lo), nb, len, offset)`
(twiceprecision.jl:361): the pairs are taken as raw `TwicePrecision` fields. -/
def steprangelenPair (ref step : TwicePrecision) (nb len : Nat) (offset : Int) : StepRangeLen :=
  ⟨ref, twiceprecision step nb, len, offset⟩

/-- Julia `maxintfloat(Float32, Int)` = `2^24`, the bound used by `rat` on `Float64`. -/
def ratBound : Int := 16777216

/-- Julia `rat(x)` (twiceprecision.jl:760-776): continued-fraction approximation `a/b`
with `|a|, |b| ≤ 2^24`, stopping as soon as `Float64(a)/Float64(b) == x`. Returns `(a, b)`;
`b = 0` signals failure. -/
def rat (x : Float) : Int × Int :=
  go 100 x 1 0 0 1
where
  /-- the convergent loop; state `(y, a, b, c, d)` as in Julia -/
  go : Nat → Float → Int → Int → Int → Int → Int × Int
    | 0, _, a, b, _, _ => (a, b)
    | fuel + 1, y, a, b, c, d =>
      if !(y.abs ≤ Float.ofInt ratBound) then (a, b)
      else
        let f := F64.toIntTrunc y
        let y := y - Float.ofInt f
        let a' := f * a + c
        let b' := f * b + d
        if !(max a'.natAbs b'.natAbs ≤ ratBound.toNat) then (a, b)
        else if Float.ofInt a' / Float.ofInt b' == x then (a', b')
        else go fuel (1 / y) a' b' a b

/-- Julia `lcm_unchecked(a, b) = a * div(b, gcd(a, b))` (twiceprecision.jl:779). -/
@[inline] def lcmUnchecked (a b : Int) : Int := a * b.tdiv (Int.gcd a b)

/-- Julia `_linspace1(Float64, start, stop, len)` for `len < 2` (twiceprecision.jl:735). -/
def linspace1 (start stop : Float) (len : Nat) : StepRangeLen :=
  ⟨⟨start, 0⟩, ⟨start, -stop⟩, len, 1⟩

/-- Julia `_linspace(Float64, start_n, stop_n, len, den)` (twiceprecision.jl:716): the range
`start_n/den … stop_n/den` with an exactly rational step. -/
def linspaceRatio (startN stopN : Int) (len : Nat) (den : Int) : StepRangeLen :=
  if len < 2 then linspace1 (Float.ofInt startN / Float.ofInt den) (Float.ofInt stopN / Float.ofInt den) len
  else if startN == stopN then steprangelenRatio startN den 0 den 0 len 1
  else
    let tmin := Float.ofInt (-startN) / (Float.ofInt stopN - Float.ofInt startN)
    let imin := F64.roundInt (tmin * Float.ofNat (len - 1) + 1)
    let imin := if imin < 1 then 1 else if imin > len then (len : Int) else imin
    let refNum := ((len : Int) - imin) * startN + (imin - 1) * stopN
    let refDen := ((len : Int) - 1) * den
    steprangelenRatio refNum refDen (stopN - startN) refDen (StepRangeLen.nbitslen len imin) len imin

/-- Julia `clamp(x, lo, hi)` = `x > hi ? hi : (x < lo ? lo : x)`. -/
@[inline] def clampF (x lo hi : Float) : Float := if x > hi then hi else if x < lo then lo else x

/-- Julia `_linspace(start::Float64, stop::Float64, len)` (twiceprecision.jl:668-712): the
general case, for endpoints without a small rational description. Julia throws for
non-finite endpoints; the result is unspecified here. -/
def linspaceFloat (start stop : Float) (len : Nat) : StepRangeLen :=
  let lenF := Float.ofNat len
  let Δ0 := stop - start
  let (Δ, Δfac) := if Δ0.isFinite then (Δ0, (1 : Float)) else (stop / lenF - start / lenF, lenF)
  let tmin := -(start / Δ) / Δfac
  let lenn1 : Int := (len : Int) - 1
  let imin0 := F64.roundInt (tmin * Float.ofInt lenn1 + 1)
  let (imin, ref, step) :=
    if 1 < imin0 && imin0 < len then
      let t := Float.ofInt (imin0 - 1) / Float.ofInt lenn1
      let ref := (1 - t) * start + t * stop
      let step :=
        if imin0 - 1 < (len : Int) - imin0 then (ref - start) / Float.ofInt (imin0 - 1)
        else (stop - ref) / Float.ofInt ((len : Int) - imin0)
      (imin0, ref, step)
    else if imin0 ≤ 1 then ((1 : Int), start, (Δ / Float.ofInt lenn1) * Δfac)
    else ((len : Int), stop, (Δ / Float.ofInt lenn1) * Δfac)
  if len == 2 && !step.isFinite then
    steprangelenPair ⟨start, 0⟩ ⟨-start, stop⟩ 0 len 1
  else
    let m := F64.prevfloat F64.floatmax
    let k := Float.ofInt (max (imin - 1) ((len : Int) - imin))
    let stepHiPre := clampF step (F64.max (-(m + ref) / k) ((-m + ref) / k))
      (F64.min ((m - ref) / k) ((m + ref) / k))
    let nb := StepRangeLen.nbitslen len imin
    let stepHi := truncbits stepHiPre nb
    let x1 := add12 (Float.ofInt (1 - imin) * stepHi) ref
    let x2 := add12 (Float.ofInt ((len : Int) - imin) * stepHi) ref
    let a := (start - x1.hi) - x1.lo
    let b := (stop - x2.hi) - x2.lo
    let stepLo := (b - a) / Float.ofInt ((len : Int) - 1)
    let refLo := a - Float.ofInt (1 - imin) * stepLo
    steprangelenPair ⟨ref, refLo⟩ ⟨stepHi, stepLo⟩ 0 len imin

/-- Julia `range(start, stop; length = len)` / `range(start, stop, len)` for `Float64`
endpoints (`range_start_stop_length`, twiceprecision.jl:645-666). -/
def range (start stop : Float) (len : Nat) : StepRangeLen :=
  if len < 2 then linspace1 start stop len
  else if start == stop then steprangelenPair ⟨start, 0⟩ ⟨0, 0⟩ 0 len 1
  else
    let (_, startD) := rat start
    let (_, stopD) := rat stop
    let fallback : Unit → StepRangeLen := fun _ => linspaceFloat start stop len
    if startD != 0 && stopD != 0 then
      let den := lcmUnchecked startD stopD
      let denF := Float.ofInt den
      if den != 0 && (denF * start).abs ≤ F64.maxintfloat && (denF * stop).abs ≤ F64.maxintfloat then
        let startN := F64.roundInt (denF * start)
        let stopN := F64.roundInt (denF * stop)
        if Float.ofInt startN / denF == start && Float.ofInt stopN / denF == stop then
          linspaceRatio startN stopN len den
        else fallback ()
      else fallback ()
    else fallback ()

/-- Julia `range(start, stop; length)` for integer endpoints (`range_start_stop_length`
with `T <: Integer`, range.jl:616): `_linspace(Float64, start, stop, len, 1)`. -/
def rangeInt (start stop : Int) (len : Nat) : StepRangeLen := linspaceRatio start stop len 1

/-- Julia `floatrange(Float64, start_n, step_n, len, den)` (twiceprecision.jl:376): the range
`start_n/den + (0:len-1) * step_n/den`. -/
def floatrange (startN stepN : Int) (len : Nat) (den : Int) : StepRangeLen :=
  if len < 2 || stepN == 0 then steprangelenRatio startN den stepN den 0 len 1
  else
    let imin := F64.roundInt (Float.ofInt (-startN) / Float.ofInt stepN + 1)
    let imin := if imin < 1 then 1 else if imin > len then (len : Int) else imin
    let refN := startN + (imin - 1) * stepN
    steprangelenRatio refN den stepN den (StepRangeLen.nbitslen len imin) len imin

/-- Julia `isbetween(a, x, b) = a <= x <= b || b <= x <= a` (twiceprecision.jl:790). -/
@[inline] def isbetween (a x b : Float) : Bool := (a ≤ x && x ≤ b) || (b ≤ x && x ≤ a)

/-- Julia `start:step:stop` for `Float64` (`(:)(start, step, stop)`,
twiceprecision.jl:390-432). Julia throws for `step == 0`; this returns an empty range. -/
def colon (start step stop : Float) : StepRangeLen :=
  if step == 0 then linspace1 start stop 0
  else
    let literal : Unit → StepRangeLen := fun _ =>
      let lf := (stop - start) / step
      let len : Int :=
        if lf < 0 then 0
        else if lf == 0 then 1
        else
          let len := F64.roundInt lf + 1
          let stop' := start + Float.ofInt (len - 1) * step
          len - (if start < stop && stop < stop' then 1 else 0)
              - (if start > stop && stop > stop' then 1 else 0)
      steprangelenPair ⟨start, 0⟩ ⟨step, 0⟩ 0 len.toNat 1
    let (stepN, stepD) := rat step
    if stepD != 0 && Float.ofInt stepN / Float.ofInt stepD == step then
      let (startN, startD) := rat start
      let (stopN, stopD) := rat stop
      if startD != 0 && stopD != 0 && Float.ofInt startN / Float.ofInt startD == start &&
          Float.ofInt stopN / Float.ofInt stopD == stop then
        let den := lcmUnchecked startD stepD
        let denF := Float.ofInt den
        if den != 0 && (start * denF).abs ≤ F64.maxintfloat && (step * denF).abs ≤ F64.maxintfloat &&
            den.tmod startD == 0 && den.tmod stepD == 0 then
          let startN := F64.roundInt (start * denF)
          let stepN := F64.roundInt (step * denF)
          let len := max 0 ((den * stopN - stopD * startN + stepN * stopD).tdiv (stepN * stopD))
          if isbetween start (start + Float.ofInt (len - 1) * step) (stop + step / 2) &&
              !isbetween start (start + Float.ofInt len * step) stop then
            floatrange startN stepN len.toNat den
          else literal ()
        else literal ()
      else literal ()
    else literal ()

/-- Julia `range(start; step, length)` for `Float64` (`range_start_step_length`,
twiceprecision.jl:447-466). -/
def rangeStep (a st : Float) (len : Nat) : StepRangeLen :=
  let (startN, startD) := rat a
  let (stepN, stepD) := rat st
  let literal := steprangelenPair ⟨a, 0⟩ ⟨st, 0⟩ 0 len 1
  if startD != 0 && stepD != 0 && Float.ofInt startN / Float.ofInt startD == a &&
      Float.ofInt stepN / Float.ofInt stepD == st then
    let den := lcmUnchecked startD stepD
    let denF := Float.ofInt den
    if (denF * a).abs ≤ F64.maxintfloat && (denF * st).abs ≤ F64.maxintfloat &&
        den.tmod startD == 0 && den.tmod stepD == 0 then
      floatrange (F64.roundInt (denF * a)) (F64.roundInt (denF * st)) len den
    else literal
  else literal

/-! ## `Float32` ranges

For `Float32` endpoints Julia builds a `StepRangeLen{Float32, Float64, Float64}`: the
reference point and step are plain `Float64` (twiceprecision.jl:337-362 ignore `nb`), the
search for them runs in `Float32` arithmetic, and each element is
`Float32(ref + (i - offset) * step)` (range.jl:975). LeanPlot's `contourf` levels
(`range(Float32(lo), nextfloat(Float32(hi)), length = n)`) go through this path. -/

/-- Julia `StepRangeLen{Float32, Float64, Float64, Int}`. -/
structure StepRangeLen32 where
  /-- reference value (`Float64`) -/
  ref : Float
  /-- step (`Float64`) -/
  step : Float
  /-- number of elements -/
  len : Nat
  /-- index of `ref` -/
  offset : Int
  deriving Repr, Inhabited

namespace StepRangeLen32

/-- Julia `unsafe_getindex(r::StepRangeLen{T}, i)` (range.jl:975): `T(ref + u*step)`. -/
@[inline] def get (r : StepRangeLen32) (i : Int) : Float32 :=
  (r.ref + Float.ofInt (i - r.offset) * r.step).toFloat32

/-- Julia `collect(r)`. -/
def toArray (r : StepRangeLen32) : Array Float32 :=
  (Array.range r.len).map fun (i : Nat) => r.get ((i : Int) + 1)

end StepRangeLen32

/-- Julia `truncbits(x::Float32, nb)`. -/
@[inline] def truncbits32 (x : Float32) (nb : Nat) : Float32 :=
  if nb ≥ 32 then Float32.ofBits 0
  else Float32.ofBits (x.toBits &&& ((0xFFFFFFFF : UInt32) <<< nb.toUInt32))

/-- Julia `add12(x::Float32, y::Float32)`. -/
@[inline] def add12F32 (x y : Float32) : Float32 × Float32 :=
  let (x, y) := if y.abs > x.abs then (y, x) else (x, y)
  let h := x + y
  (h, (x - h) + y)

/-- Julia `rat(x::Float32)` (twiceprecision.jl:760): as `rat`, in `Float32` arithmetic, with
bound `maxintfloat(Float16, Int) = 2048`. -/
def rat32 (x : Float32) : Int × Int :=
  go 100 x 1 0 0 1
where
  /-- the convergent loop -/
  go : Nat → Float32 → Int → Int → Int → Int → Int × Int
    | 0, _, a, b, _, _ => (a, b)
    | fuel + 1, y, a, b, c, d =>
      if !(y.abs ≤ 2048) then (a, b)
      else
        let f := F64.toIntTrunc y.toFloat
        let y := y - Float32.ofInt f
        let a' := f * a + c
        let b' := f * b + d
        if !(max a'.natAbs b'.natAbs ≤ 2048) then (a, b)
        else if Float32.ofInt a' / Float32.ofInt b' == x then (a', b')
        else go fuel (1 / y) a' b' a b

/-- Julia `_linspace(Float32, start_n, stop_n, len, den)` (twiceprecision.jl:716) with the
`Float32` `steprangelen_hp` (`ref[1]/ref[2]`, `step[1]/step[2]` in `Float64`). -/
def linspaceRatio32 (startN stopN : Int) (len : Nat) (den : Int) : StepRangeLen32 :=
  let q (n d : Int) : Float := Float.ofInt n / Float.ofInt d
  if len < 2 then ⟨q startN den, q startN den - q stopN den, len, 1⟩
  else if startN == stopN then ⟨q startN den, q 0 den, len, 1⟩
  else
    let tmin := Float.ofInt (-startN) / (Float.ofInt stopN - Float.ofInt startN)
    let imin := F64.roundInt (tmin * Float.ofNat (len - 1) + 1)
    let imin := if imin < 1 then 1 else if imin > len then (len : Int) else imin
    let refNum := ((len : Int) - imin) * startN + (imin - 1) * stopN
    let refDen := ((len : Int) - 1) * den
    ⟨q refNum refDen, q (stopN - startN) refDen, len, imin⟩

/-- Julia `_linspace(start::Float32, stop::Float32, len)` (twiceprecision.jl:668-712) with the
`Float32` `steprangelen_hp` (`asF64((hi, lo)) = Float64(hi) + Float64(lo)`). -/
def linspaceFloat32 (start stop : Float32) (len : Nat) : StepRangeLen32 :=
  let lenF := Float32.ofNat len
  let Δ0 := stop - start
  let (Δ, Δfac) := if Δ0.isFinite then (Δ0, (1 : Float32)) else (stop / lenF - start / lenF, lenF)
  let tmin := -(start / Δ) / Δfac
  let lenn1 : Int := (len : Int) - 1
  let imin0 := F64.roundInt (tmin * Float32.ofInt lenn1 + 1).toFloat
  let (imin, ref, step) :=
    if 1 < imin0 && imin0 < len then
      let t := Float.ofInt (imin0 - 1) / Float.ofInt lenn1
      let ref := ((1 - t) * start.toFloat + t * stop.toFloat).toFloat32
      let step :=
        if imin0 - 1 < (len : Int) - imin0 then (ref - start) / Float32.ofInt (imin0 - 1)
        else (stop - ref) / Float32.ofInt ((len : Int) - imin0)
      (imin0, ref, step)
    else if imin0 ≤ 1 then ((1 : Int), start, (Δ / Float32.ofInt lenn1) * Δfac)
    else ((len : Int), stop, (Δ / Float32.ofInt lenn1) * Δfac)
  if len == 2 && !step.isFinite then
    ⟨start.toFloat, -start.toFloat + stop.toFloat, len, 1⟩
  else
    let m : Float32 := Float32.ofBits 0x7F7FFFFE  -- prevfloat(floatmax(Float32))
    let k := Float32.ofInt (max (imin - 1) ((len : Int) - imin))
    let lo := F32.max (-(m + ref) / k) ((-m + ref) / k)
    let hi := F32.min ((m - ref) / k) ((m + ref) / k)
    let stepHiPre := if step > hi then hi else if step < lo then lo else step
    let nb :=
      if len < 2 then 0
      else
        let x := (max (imin - 1) ((len : Int) - imin) - 1).toNat
        Nat.min 12 (Nat.log2 x + (if x == 0 then 0 else 1) + 1)
    let stepHi := truncbits32 stepHiPre nb
    let (x1h, x1l) := add12F32 (Float32.ofInt (1 - imin) * stepHi) ref
    let (x2h, x2l) := add12F32 (Float32.ofInt ((len : Int) - imin) * stepHi) ref
    let a := (start - x1h) - x1l
    let b := (stop - x2h) - x2l
    let stepLo := (b - a) / Float32.ofInt ((len : Int) - 1)
    let refLo := a - Float32.ofInt (1 - imin) * stepLo
    ⟨ref.toFloat + refLo.toFloat, stepHi.toFloat + stepLo.toFloat, len, imin⟩

/-- Julia `range(start, stop; length)` for `Float32` endpoints (twiceprecision.jl:645). -/
def range32 (start stop : Float32) (len : Nat) : StepRangeLen32 :=
  if len < 2 then ⟨start.toFloat, start.toFloat - stop.toFloat, len, 1⟩
  else if start == stop then ⟨start.toFloat, 0, len, 1⟩
  else
    let (_, startD) := rat32 start
    let (_, stopD) := rat32 stop
    let fallback : Unit → StepRangeLen32 := fun _ => linspaceFloat32 start stop len
    if startD != 0 && stopD != 0 then
      let den := lcmUnchecked startD stopD
      let denF := Float32.ofInt den
      let m : Float32 := 16777216
      if den != 0 && (denF * start).abs ≤ m && (denF * stop).abs ≤ m then
        let startN := F64.roundInt (denF * start).toFloat
        let stopN := F64.roundInt (denF * stop).toFloat
        if (Float.ofInt startN / Float.ofInt den).toFloat32 == start &&
            (Float.ofInt stopN / Float.ofInt den).toFloat32 == stop then
          linspaceRatio32 startN stopN len den
        else fallback ()
      else fallback ()
    else fallback ()

/-- Julia `LinRange{Float32}` element `i`: `lerpi` with `t = j/d` in `Float64`, then
`Float32((1-t)*a + t*b)` (range.jl:981). -/
def linRange32Get (start stop : Float32) (len : Nat) (i : Int) : Float32 :=
  let lendiv := if len == 1 then 1 else Nat.max (len - 1) 1
  let t := Float.ofInt (i - 1) / Float.ofNat lendiv
  ((1 - t) * start.toFloat + t * stop.toFloat).toFloat32

/-- Julia `LinRange{Float64}` (range.jl:579): `len` points from `start` to `stop`. -/
structure LinRange where
  /-- first element -/
  start : Float
  /-- last element -/
  stop : Float
  /-- number of elements -/
  len : Nat
  /-- `max(len - 1, 1)` -/
  lendiv : Nat
  deriving Repr, Inhabited

namespace LinRange

/-- Julia `LinRange(start, stop, len)` (range.jl:585-608). Julia throws when `len == 1` and
`start ≠ stop`; here the range then just has the single element `start`. -/
def mk' (start stop : Float) (len : Nat) : LinRange :=
  if len == 1 then ⟨start, stop, 1, 1⟩ else ⟨start, stop, len, Nat.max (len - 1) 1⟩

/-- Julia `lerpi(j, d, a, b)` (range.jl:981): `t = j/d; (1-t)*a + t*b`. -/
@[inline] def lerpi (j d : Int) (a b : Float) : Float :=
  let t := Float.ofInt j / Float.ofInt d
  (1 - t) * a + t * b

/-- Julia `unsafe_getindex(r::LinRange, i)` (range.jl:979), 1-based and unchecked. -/
@[inline] def get (r : LinRange) (i : Int) : Float := lerpi (i - 1) r.lendiv r.start r.stop

/-- Julia `step(r::LinRange)` = `(stop - start) / lendiv`. -/
@[inline] def stepValue (r : LinRange) : Float := (r.stop - r.start) / Float.ofNat r.lendiv

/-- Julia `collect(r)`, packed. -/
def toFloatArray (r : LinRange) : FloatArray :=
  go r.len (FloatArray.emptyWithCapacity r.len) 1
where
  /-- tail-recursive fill -/
  go : Nat → FloatArray → Int → FloatArray
    | 0, acc, _ => acc
    | n + 1, acc, i => go n (acc.push (r.get i)) (i + 1)

/-- Julia `x .* r` (broadcast.jl:1176): `LinRange(x * start, x * stop, len)`. -/
def bcastMul (x : Float) (r : LinRange) : LinRange :=
  { r with start := x * r.start, stop := x * r.stop }

/-- Julia `r ./ x` (broadcast.jl:1191): `LinRange(start / x, stop / x, len)`. -/
def bcastDiv (r : LinRange) (x : Float) : LinRange :=
  { r with start := r.start / x, stop := r.stop / x }

/-- Julia `r .+ x` (broadcast.jl:1154): `LinRange(start + x, stop + x, len)`. -/
def bcastAdd (r : LinRange) (x : Float) : LinRange :=
  { r with start := r.start + x, stop := r.stop + x }

/-- Julia `.-r` (broadcast.jl:1139): `LinRange(-start, -stop, len)`. -/
def neg (r : LinRange) : LinRange := { r with start := -r.start, stop := -r.stop }

end LinRange

end JuliaBase
