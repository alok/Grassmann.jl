/-!
# Julia `Float16`: exact conversion and printing

A nonnegative IEEE binary16 value by its fields, with the two things the port needs from
Julia's `Float16` (first for Dendriform's `GroveBin.ppos = Float16(100i // (2^Cn(d) - 1))`,
DF/Dendriform.jl:144):

1. **Correct rounding** of an exact rational to IEEE binary16 (11-bit significand,
   subnormals of quantum `2^-24`, round half to even): Julia's `Float16(::Rational{BigInt})`
   computes `BigFloat(num)/BigFloat(den)` and rounds that to `Float16` with MPFR
   (`to_ieee754`), so up to a 256-bit intermediate this is the correctly rounded value.
2. **Ryu shortest digits** (`base/ryu/shortest.jl`, `reduce_shortest`): the shortest
   decimal in the rounding interval (endpoints included iff the significand is even),
   choosing the closest such decimal with ties to even. Implemented here in exact
   arithmetic, which is what Ryu's table-driven code computes.
3. **Julia's layout** (`writeshortest`, `shortest.jl:334`): plain notation iff
   `-4 < pt ≤ 3` for `Float16` (`pt` = decimal exponent of the leading digit + 1), e.g.
   `22.58`, `100.0`, `0.006092`, otherwise `d.ddde±X`, e.g. `6.104e-5`, `1.0e3`.

Every nonnegative finite value up to `65504` prints exactly as Julia's `string(::Float16)`
(checked exhaustively in `Tests/JuliaBase/Math.lean` and `Tests/Dendriform.lean`). Negative
values are not represented (Julia prints them with a leading `-`).
-/

namespace JuliaBase

/-- An IEEE binary16 value by its fields: biased exponent `e ∈ [0, 31]` and mantissa
`m ∈ [0, 1023]` (sign omitted: `ppos ≥ 0`). -/
structure Float16 where
  /-- biased exponent field -/
  e : Nat
  /-- mantissa field (without the implicit bit) -/
  m : Nat
  deriving DecidableEq, Repr, Inhabited

namespace Float16

/-- `2^k` for an integer `k` as an exact fraction `(num, den)`. -/
private def pow2 (k : Int) : Nat × Nat :=
  if k ≥ 0 then (2 ^ k.toNat, 1) else (1, 2 ^ (-k).toNat)

/-- Round `n / d` to the nearest natural number, ties to even. -/
def roundHalfEven (n d : Nat) : Nat :=
  let q := n / d
  let r := n % d
  if 2 * r > d || (2 * r == d && q % 2 == 1) then q + 1 else q

/-- Correctly rounded conversion of a nonnegative rational `num / den` to binary16
(Julia `Float16(::Rational)`, `base/rational.jl:162` via `BigFloat`). -/
def ofRat (num den : Nat) : Float16 := Id.run do
  if num == 0 || den == 0 then return ⟨0, 0⟩
  -- E with 2^E ≤ num/den < 2^(E+1)
  let mut E : Int := (Nat.log2 num : Int) - (Nat.log2 den : Int)
  let ge (k : Int) : Bool := let (a, b) := pow2 k; num * b ≥ den * a
  if !ge E then E := E - 1
  if ge (E + 1) then E := E + 1
  if E < -14 then
    -- subnormal: m = round(num/den · 2^24)
    let m := roundHalfEven (num * 2 ^ 24) den
    return if m ≥ 1024 then ⟨1, 0⟩ else ⟨0, m⟩
  let (a, b) := pow2 (10 - E)
  let mut M := roundHalfEven (num * a) (den * b)
  if M ≥ 2048 then
    M := M / 2
    E := E + 1
  if E > 15 then return ⟨31, 0⟩
  return ⟨(E + 15).toNat, M - 1024⟩

/-- Number of decimal digits of `n` (at least 1). -/
def decimalLength (n : Nat) : Nat := (Nat.toDigits 10 n).length

/-- Ryu `reduce_shortest` in exact arithmetic: `(digits, exponent)` with the value equal
to `digits · 10^exponent`, `digits` the shortest round-tripping decimal. -/
def shortest (x : Float16) : Nat × Int := Id.run do
  let (mf, ef) : Nat × Int :=
    if x.e == 0 then (x.m, 1 - 15 - 10) else (1024 + x.m, (x.e : Int) - 15 - 10)
  -- integers below 2^11: strip trailing zeros (shortest.jl "c) specialized")
  if -10 ≤ ef ∧ ef ≤ 0 ∧ mf % 2 ^ (-ef).toNat == 0 then
    let mut b := mf / 2 ^ (-ef).toNat
    let mut e10 : Int := 0
    for _ in [0:6] do
      if b != 0 && b % 10 == 0 then
        b := b / 10
        e10 := e10 + 1
    return (b, e10)
  let e2 := ef - 2
  let even := mf % 2 == 0
  let v := 4 * mf
  let w := v + 2
  let shift := if x.m == 0 && x.e > 1 then 1 else 0
  let u := v - 2 + shift
  -- exact scaled bounds at exponent e10
  let (s, e10) : Nat × Int := if e2 ≥ 0 then (2 ^ e2.toNat, 0) else (5 ^ (-e2).toNat, e2)
  let mut vm := u * s
  let mut vr := v * s
  let mut vp := w * s
  if !even then vp := vp - 1
  let mut vmTZ := even
  let mut vrTZ := true
  let mut last := 0
  let mut removed := 0
  for _ in [0:64] do
    if vp / 10 > vm / 10 then
      vmTZ := vmTZ && vm % 10 == 0
      vrTZ := vrTZ && last == 0
      last := vr % 10
      vr := vr / 10
      vp := vp / 10
      vm := vm / 10
      removed := removed + 1
  if vmTZ then
    for _ in [0:64] do
      if vm % 10 == 0 && vm != 0 then
        vrTZ := vrTZ && last == 0
        last := vr % 10
        vr := vr / 10
        vp := vp / 10
        vm := vm / 10
        removed := removed + 1
  if vrTZ && last == 5 && vr % 2 == 0 then last := 4
  let up := (vr == vm && (!even || !vmTZ)) || last ≥ 5
  return (vr + (if up then 1 else 0), e10 + removed)

/-- The exact value as a rational. -/
def toRat (x : Float16) : Rat :=
  if x.e == 0 then (x.m : Rat) / (2 ^ 24 : Nat)
  else
    let M : Rat := (1024 + x.m : Nat)
    let k : Int := (x.e : Int) - 25
    if k ≥ 0 then M * ((2 ^ k.toNat : Nat) : Rat) else M / ((2 ^ (-k).toNat : Nat) : Rat)

/-- Julia `string(::Float16)` (`writeshortest` with `hash = true`, `precision = -1`,
`shortest.jl:228-440`) for nonnegative values. -/
protected def toString (x : Float16) : String :=
  if x.e == 31 then (if x.m == 0 then "Inf" else "NaN")
  else if x.e == 0 && x.m == 0 then "0.0"
  else
    let (out, nexp) := shortest x
    let ds := String.ofList (Nat.toDigits 10 out)
    let olength := ds.length
    let pt : Int := nexp + olength
    let zeros (k : Nat) : String := String.ofList (List.replicate k '0')
    -- the integer-tail check `abs(mod(x + 0.05, 10^(pt - olength)) - 0.05) > 0.05`
    let tailBad : Bool :=
      pt ≥ olength &&
        (let p : Rat := ((10 ^ (pt - olength).toNat : Nat) : Rat)
         let y : Rat := x.toRat + 1 / 20
         let r := y - p * ((y / p).floor : Int)
         let dlt := r - 1 / 20
         (if dlt < 0 then -dlt else dlt) > 1 / 20)
    if -4 < pt && pt ≤ 3 && !tailBad then
      if pt ≤ 0 then "0." ++ zeros (-pt).toNat ++ ds
      else if pt ≥ olength then ds ++ zeros nexp.toNat ++ ".0"
      else
        let k := pt.toNat
        String.ofList (ds.toList.take k) ++ "." ++ String.ofList (ds.toList.drop k)
    else
      let head := String.ofList (ds.toList.take 1)
      let tail := String.ofList (ds.toList.drop 1)
      let mant := head ++ "." ++ (if olength == 1 then "0" else tail)
      let e := nexp + olength - 1
      mant ++ "e" ++ (if e < 0 then "-" ++ toString (-e).toNat else toString e.toNat)

instance : ToString Float16 := ⟨Float16.toString⟩

end Float16

-- goldens from port-notes §6.4
#guard toString (Float16.ofRat 700 31) == "22.58"
#guard toString (Float16.ofRat 100 1) == "100.0"
#guard toString (Float16.ofRat 100 (2 ^ 14 - 1)) == "0.006104"
#guard toString (Float16.ofRat 100 (2 ^ 42 - 1)) == "0.0"
#guard toString (Float16.ofRat 1000 1) == "1.0e3"

end JuliaBase
