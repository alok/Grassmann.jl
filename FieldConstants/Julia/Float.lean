import JuliaBase

/-!
# Julia `Float64` parsing and exact conversions

Julia's float *printing* (`show`, Ryu shortest digits), `nextfloat`, `rem`,
`round` and `isapprox` come from `JuliaBase` (`JuliaBase.F64.showString` etc.).
This module adds what `JuliaBase` does not provide yet: the exact IEEE-754
decomposition `decode` (`x = ±m·2^e`), correctly rounded rational and decimal
conversion (`ofRat`, `ofDecimal`) and Julia's `parse(Float64, s)`.

Julia sources: `base/parse.jl` (`parse(Float64, s)`), `base/rational.jl`
(`Float64(::Rational)`), `base/float.jl` (`eps`).
-/

namespace FieldConstants.Julia

-- Julia's `Inf` and `NaN` come from `JuliaBase`.
export JuliaBase.F64 (inf nan)

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

/-- Julia `eps(x)`: the gap from `|x|` to the next larger float. -/
def eps (x : Float) : Float := JuliaBase.F64.nextfloat x.abs - x.abs

end FieldConstants.Julia
