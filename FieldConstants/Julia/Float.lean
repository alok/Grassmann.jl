/-!
# Julia `Float64` semantics

The chakravala packages print every number through Julia's `show`, so the
port needs Julia's exact float formatting (Ryu shortest round-trip digits plus
the `writeshortest` layout rules) and a correctly rounded decimal parser.

Everything here is exact big-integer arithmetic on the IEEE-754 encoding:
`decode` exposes `x = ±m·2^e`, `ofRat` rounds a rational to nearest-even, and
`shortest` searches the digit lengths `1…17` for the round-trip representative
nearest to `x` (the specification of Ryu, Adams 2018). This is slower than Ryu
but it is only used for display and golden I/O.

Julia sources: `base/ryu/shortest.jl` (`writeshortest`, lines 228-450),
`base/parse.jl` (`parse(Float64, s)`), `base/float.jl` (`nextfloat`/`prevfloat`).
-/

namespace FieldConstants.Julia

/-- Exact decomposition of a finite float: `|x| = mant · 2^exp`. -/
structure Decoded where
  /-- sign bit -/
  neg : Bool
  /-- integer significand (with the hidden bit for normal numbers) -/
  mant : Nat
  /-- binary exponent of the last significand bit -/
  exp : Int
  deriving Repr

/-- Decode a finite `Float` into sign, integer significand and binary exponent. -/
def decode (x : Float) : Decoded :=
  let b := x.toBits
  let neg := (b >>> 63) == 1
  let e := ((b >>> 52) &&& 0x7FF).toNat
  let f := (b &&& 0xFFFFFFFFFFFFF).toNat
  if e == 0 then ⟨neg, f, -1074⟩ else ⟨neg, f + 2 ^ 52, (e : Int) - 1075⟩

/-- `(quotient, remainder, denominator)` of `p / (q · 2^k)`. -/
private def quotAt (p q : Nat) (k : Int) : Nat × Nat × Nat :=
  let (num, den) := if k ≥ 0 then (p, q <<< k.toNat) else (p <<< (-k).toNat, q)
  (num / den, num % den, den)

/-- Positive infinity. -/
def inf : Float := Float.ofBits 0x7FF0000000000000
/-- A quiet NaN (Julia's `NaN`). -/
def nan : Float := Float.ofBits 0x7FF8000000000000

/-- Correctly rounded (nearest, ties to even) conversion of `±p/q` to `Float`,
with gradual underflow and overflow to `±Inf`. `q = 0` gives `±Inf` (or `NaN`
for `0/0`). -/
def ofRat (neg : Bool) (p q : Nat) : Float :=
  let sgn : UInt64 := if neg then 0x8000000000000000 else 0
  if q == 0 then (if p == 0 then nan else Float.ofBits (sgn ||| 0x7FF0000000000000))
  else if p == 0 then Float.ofBits sgn
  else
    let k0 : Int := (p.log2 : Int) - (q.log2 : Int) - 52
    let (m0, _, _) := quotAt p q k0
    let k := if m0 < 2 ^ 52 then k0 - 1 else k0
    let biased := k + 1075
    if biased ≥ 2047 then Float.ofBits (sgn ||| 0x7FF0000000000000)
    else if biased ≤ 0 then
      -- subnormal: fixed exponent 2^-1074
      let (m, r, d) := quotAt p q (-1074)
      let m := if 2 * r > d || (2 * r == d && m % 2 == 1) then m + 1 else m
      Float.ofBits (sgn ||| m.toUInt64)
    else
      let (m, r, d) := quotAt p q k
      let m := if 2 * r > d || (2 * r == d && m % 2 == 1) then m + 1 else m
      let (m, biased) := if m == 2 ^ 53 then (2 ^ 52, biased + 1) else (m, biased)
      if biased ≥ 2047 then Float.ofBits (sgn ||| 0x7FF0000000000000)
      else Float.ofBits (sgn ||| (biased.toNat.toUInt64 <<< 52) ||| (m - 2 ^ 52).toUInt64)

/-- Correctly rounded value of `±d · 10^e`. -/
def ofDecimal (neg : Bool) (d : Nat) (e : Int) : Float :=
  if e ≥ 0 then ofRat neg (d * 10 ^ e.toNat) 1 else ofRat neg d (10 ^ (-e).toNat)

/-- Parse a decimal floating-point literal the way Julia's `parse(Float64, s)`
does: optional sign, digits with an optional point, optional `e`/`E` exponent,
plus `Inf`/`Infinity`/`NaN` (any case). Leading/trailing ASCII spaces are ignored.
Returns `none` on malformed input. -/
def parseFloat? (s : String) : Option Float := Id.run do
  let s := s.trimAscii.toString
  let (neg, body) :=
    if s.startsWith "-" then (true, (s.drop 1).toString)
    else if s.startsWith "+" then (false, (s.drop 1).toString)
    else (false, s)
  let low := body.toLower
  if low == "inf" || low == "infinity" then return some (if neg then -inf else inf)
  if low == "nan" then return some nan
  let cs := body.toList
  let mut mant : Nat := 0
  let mut nd : Nat := 0          -- number of mantissa digits seen
  let mut frac : Nat := 0        -- digits after the point
  let mut seenPoint := false
  let mut rest : List Char := []
  let mut i := 0
  let mut stop := false
  for c in cs do
    if stop then
      rest := rest ++ [c]
    else if c.isDigit then
      mant := mant * 10 + (c.toNat - '0'.toNat)
      nd := nd + 1
      if seenPoint then frac := frac + 1
    else if c == '.' && !seenPoint then
      seenPoint := true
    else
      stop := true
      rest := [c]
    i := i + 1
  if nd == 0 then return none
  let mut e10 : Int := 0
  match rest with
  | [] => pure ()
  | c :: tl =>
    if c != 'e' && c != 'E' then return none
    let (eneg, digs) := match tl with
      | '-' :: t => (true, t)
      | '+' :: t => (false, t)
      | t => (false, t)
    if digs.isEmpty || !digs.all Char.isDigit then return none
    let v := digs.foldl (fun a ch => a * 10 + (ch.toNat - '0'.toNat)) 0
    e10 := if eneg then -(v : Int) else v
  let r := ofDecimal neg mant (e10 - frac)
  -- Julia's `strtod` wrapper reports `ERANGE`: a nonzero literal that rounds to
  -- zero or overflows to infinity does not parse.
  if mant != 0 && (r == 0 || r.isInf) then return none
  return some r

/-- Julia `parse(Float64, s)`, returning `NaN` on malformed input. -/
def parseFloat (s : String) : Float := (parseFloat? s).getD nan

/-- `10^D ≤ p/q`? -/
private def geqPow10 (p q : Nat) (D : Int) : Bool :=
  if D ≥ 0 then p ≥ q * 10 ^ D.toNat else p * 10 ^ (-D).toNat ≥ q

/-- Strip trailing decimal zeros: `(d, e) ↦ (d', e')` with `d·10^e = d'·10^e'`. -/
def stripZeros (d : Nat) (e : Int) (fuel : Nat := 400) : Nat × Int :=
  match fuel with
  | 0 => (d, e)
  | fuel + 1 => if d != 0 && d % 10 == 0 then stripZeros (d / 10) (e + 1) fuel else (d, e)

/-- Search digit lengths `k, k+1, …, 17` for the shortest round-trip decimal. -/
private def shortestAux (x : Float) (neg : Bool) (p q : Nat) (D : Int) : Nat → Nat → Nat × Int
  | 0, _ => (0, 0)
  | fuel + 1, k =>
    let s : Int := D - k + 1
    -- v / 10^s = num / den
    let (num, den) := if s ≥ 0 then (p, q * 10 ^ s.toNat) else (p * 10 ^ (-s).toNat, q)
    let lo := num / den
    let rem := num % den
    let okLo := lo != 0 && ofDecimal neg lo s == x
    let okHi := ofDecimal neg (lo + 1) s == x
    if okLo && okHi then
      -- both round-trip: take the nearer, ties to even digit
      if 2 * rem < den then stripZeros lo s
      else if 2 * rem > den then stripZeros (lo + 1) s
      else if lo % 2 == 0 then stripZeros lo s else stripZeros (lo + 1) s
    else if okLo then stripZeros lo s
    else if okHi then stripZeros (lo + 1) s
    else shortestAux x neg p q D fuel (k + 1)

/-- Shortest round-trip decimal digits of a finite nonzero float (Ryu's output):
`|x| = digits · 10^nexp`, with `digits` free of trailing zeros. -/
def shortest (x : Float) : Nat × Int :=
  let ⟨neg, m, e⟩ := decode x
  let (p, q) := if e ≥ 0 then (m <<< e.toNat, 1) else (m, 1 <<< (-e).toNat)
  -- decimal exponent D with 10^D ≤ v < 10^(D+1), estimated in floating point and fixed exactly
  let est : Int := (Float.floor (Float.log10 x.abs)).toInt64.toInt
  let D :=
    if !geqPow10 p q est then est - 1
    else if geqPow10 p q (est + 1) then est + 1
    else est
  let D := if !geqPow10 p q D then D - 1 else if geqPow10 p q (D + 1) then D + 1 else D
  shortestAux x neg p q D 18 1

/-- Decimal digits of a natural number as a string. -/
private def natDigits (n : Nat) : String := toString n

/-- Julia `show`/`print`/`string` of a `Float64` (`Base.Ryu.writeshortest` with
default options): shortest round-trip digits, plain notation when the decimal
point position `pt` satisfies `-4 < pt ≤ 6`, otherwise `d.ddde±N`. Always shows a
fractional part (`1.0`, `1.0e6`). -/
def showFloat (x : Float) : String :=
  if x.isNaN then "NaN"
  else if x.isInf then (if x < 0 then "-Inf" else "Inf")
  else if x == 0 then (if (decode x).neg then "-0.0" else "0.0")
  else
    let sign := if (decode x).neg then "-" else ""
    let (d, nexp) := shortest x
    let ds := natDigits d
    let olength : Int := ds.length
    let pt : Int := nexp + olength
    if -4 < pt && pt ≤ 6 then
      if pt ≤ 0 then
        sign ++ "0." ++ String.ofList (List.replicate (-pt).toNat '0') ++ ds
      else if pt ≥ olength then
        sign ++ ds ++ String.ofList (List.replicate nexp.toNat '0') ++ ".0"
      else
        sign ++ (ds.take pt.toNat).toString ++ "." ++ (ds.drop pt.toNat).toString
    else
      let e := nexp + olength - 1
      let mant := if ds.length == 1 then ds ++ ".0"
        else (ds.take 1).toString ++ "." ++ (ds.drop 1).toString
      sign ++ mant ++ "e" ++ toString e

/-- The next representable float toward `+∞` (Julia `nextfloat`). -/
def nextFloat (x : Float) : Float :=
  if x.isNaN || (x.isInf && x > 0) then x
  else if x == 0 then Float.ofBits 1
  else
    let b := x.toBits
    if x > 0 then Float.ofBits (b + 1) else Float.ofBits (b - 1)

/-- The next representable float toward `-∞` (Julia `prevfloat`). -/
def prevFloat (x : Float) : Float := -(nextFloat (-x))

/-- `eps(x)`: the gap from `|x|` to the next larger float. -/
def eps (x : Float) : Float := nextFloat x.abs - x.abs

/-- `x == y` or both NaN: bit-level identity used by golden comparisons. -/
def sameFloat (x y : Float) : Bool := x.toBits == y.toBits || (x.isNaN && y.isNaN)

/-- Relative closeness test `|x - y| ≤ rtol·max(|x|,|y|)`, with exact equality
and matching non-finite values accepted. -/
def closeRel (x y : Float) (rtol : Float) : Bool :=
  if x == y then true
  else if x.isNaN && y.isNaN then true
  else if !x.isFinite || !y.isFinite then false
  else (x - y).abs ≤ rtol * max x.abs y.abs

end FieldConstants.Julia
