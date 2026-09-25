import JuliaBase.IEEE

/-!
# Julia `parse(Float64, s)` / `parse(Float32, s)`

Julia parses floats with `jl_try_substrtod` (`base/parse.jl`, `src/support/strtod.c`): the C
library's correctly rounding `strtod`/`strtof`, plus a range check. The port scans the
decimal literal and converts it exactly with `IEEEFloat.ofDecimal`, so the result is the
correctly rounded value by construction.
-/

namespace JuliaBase

namespace IEEEFloat

/-- Scan digits with at most one decimal point: `(value, digit count, digits after the
point, rest of the input)`. -/
def scanMantissa : List Char → Nat → Nat → Nat → Bool → Nat × Nat × Nat × List Char
  | [], m, nd, frac, _ => (m, nd, frac, [])
  | c :: cs, m, nd, frac, pt =>
    if c.isDigit then
      scanMantissa cs (m * 10 + (c.toNat - '0'.toNat)) (nd + 1) (if pt then frac + 1 else frac) pt
    else if c == '.' && !pt then scanMantissa cs m nd frac true
    else (m, nd, frac, c :: cs)

/-- Scan an optional exponent suffix `e`/`E`, optional sign, at least one digit, and nothing
after it; `none` on malformed input. -/
def scanExponent : List Char → Option Int
  | [] => some 0
  | c :: tl =>
    if c != 'e' && c != 'E' then none
    else
      let (eneg, digs) := match tl with
        | '-' :: t => (true, t)
        | '+' :: t => (false, t)
        | t => (false, t)
      if digs.isEmpty || !digs.all Char.isDigit then none
      else
        let v := digs.foldl (fun a ch => a * 10 + (ch.toNat - '0'.toNat)) 0
        some (if eneg then -(v : Int) else v)

/-- Julia `tryparse(F, s)` for a decimal float literal (`base/parse.jl`, a correctly rounding
`strtod`/`strtof`): surrounding ASCII whitespace is ignored; then an optional sign, digits
with at most one `.` (at least one digit), and an optional `e`/`E` exponent; or `Inf`,
`Infinity`, `NaN` in any case. A nonzero literal that rounds to zero or overflows to
infinity (`strtod`'s `ERANGE`) does not parse. Not supported: hexadecimal literals
(`0x1p3`), which `strtod` also accepts. -/
def parse? (F : Type) [IEEEFloat F] (s : String) : Option F :=
  let s := s.trimAscii.toString
  let (neg, body) :=
    if s.startsWith "-" then (true, (s.drop 1).toString)
    else if s.startsWith "+" then (false, (s.drop 1).toString)
    else (false, s)
  let low := body.toLower
  if low == "inf" || low == "infinity" then some (assemble F neg (expMax F) 0)
  else if low == "nan" then some (nan F)
  else
    let (mant, nd, frac, rest) := scanMantissa body.toList 0 0 0 false
    if nd == 0 then none
    else
      match scanExponent rest with
      | none => none
      | some e10 =>
        let r := ofDecimal F neg mant (e10 - frac)
        if mant != 0 && (isZero r || isInf r) then none else some r

end IEEEFloat

namespace F64

/-! ## Fast path

Most literals are short: an optional sign, digits, an optional fraction and exponent, nothing
else (Julia's own `show` output, data files). For those the digits fit a `UInt64`, and when the
mantissa is below `2^53` and the decimal exponent within `±22` both it and `10^|e|` are exact
doubles, so one multiplication or division rounds once to the correctly rounded result
(Clinger's fast path, the first case of every `strtod`). Everything else, and every input the
byte scanner does not accept (whitespace, `Inf`, `NaN`, more than 19 digits, long exponents),
goes to the exact `IEEEFloat.parse?`, so the results are identical by construction. -/

/-- The exact powers `10^0 … 10^22` (Julia's `exp10` table of `strtod`'s fast path). -/
def pow10Exact : FloatArray :=
  (List.range 23).foldl (fun a k => a.push (Float.ofNat (10 ^ k))) (FloatArray.emptyWithCapacity 23)

/-- Byte `i` of `s` (`0` past the end). -/
@[inline] def byteAt (s : String) (i : Nat) : UInt8 :=
  if h : i < s.utf8ByteSize then s.getUTF8Byte ⟨i⟩ (by simpa [String.Pos.Raw.lt_iff] using h) else 0

/-- Scan digits from byte `i` into `m` (at most 19 in total, `ok := false` beyond): returns
`(m, digits, next index, ok)`; `pt` counts the digits after a decimal point. -/
def scanDigits (s : String) (i : Nat) (m : UInt64) (nd : Nat) : Nat → UInt64 × Nat × Nat × Bool
  | 0 => (m, nd, i, true)
  | fuel + 1 =>
    let c := byteAt s i
    if c ≥ 48 && c ≤ 57 then
      if nd ≥ 19 then (m, nd, i, false)
      else scanDigits s (i + 1) (m * 10 + (c - 48).toUInt64) (nd + 1) fuel
    else (m, nd, i, true)

/-- Scan the exponent digits from byte `i` (at most 4, `none` beyond or when there are none). -/
def scanExpDigits (s : String) (i : Nat) (v : Nat) (nd : Nat) : Nat → Option (Nat × Nat)
  | 0 => if nd == 0 then none else some (v, i)
  | fuel + 1 =>
    let c := byteAt s i
    if c ≥ 48 && c ≤ 57 then
      if nd ≥ 4 then none else scanExpDigits s (i + 1) (v * 10 + (c - 48).toNat) (nd + 1) fuel
    else if nd == 0 then none else some (v, i)

/-- The fast scanner: `some (neg, mantissa, decimal exponent)` when `s` is exactly
`[+-]digits[.digits][(e|E)[+-]digits]` with at most 19 significant digits in total and at most
4 exponent digits (and at least one mantissa digit); `none` otherwise. -/
def scanSimple (s : String) : Option (Bool × UInt64 × Int) := do
  let n := s.utf8ByteSize
  let c0 := byteAt s 0
  let (neg, i) := if c0 == 45 then (true, 1) else if c0 == 43 then (false, 1) else (false, 0)
  let (m, nd, i, ok) := scanDigits s i 0 0 n
  guard ok
  let (m, nd, frac, i) ← if byteAt s i == 46 then
      let (m', nd', j, ok') := scanDigits s (i + 1) m nd n
      if ok' then some (m', nd', nd' - nd, j) else none
    else some (m, nd, 0, i)
  guard (nd > 0)
  let c := byteAt s i
  let (e10, i) ← if c == 101 || c == 69 then
      let c1 := byteAt s (i + 1)
      let (eneg, j) := if c1 == 45 then (true, i + 2) else if c1 == 43 then (false, i + 2) else (false, i + 1)
      let (v, j) ← scanExpDigits s j 0 0 n
      some ((if eneg then -(v : Int) else v), j)
    else some (0, i)
  guard (i == n)
  return (neg, m, e10 - frac)

/-- Julia `tryparse(Float64, s)`: the correctly rounded value of a decimal literal, or `none`
(see `IEEEFloat.parse?`); simple literals take the fast path above. -/
def parse? (s : String) : Option Float :=
  match scanSimple s with
  | some (neg, m, e) =>
    if m == 0 then some (if neg then -0.0 else 0.0)
    else if m < 9007199254740992 && -22 ≤ e && e ≤ 22 then
      let x := m.toFloat
      let x := if e ≥ 0 then x * pow10Exact.get! e.toNat else x / pow10Exact.get! (-e).toNat
      some (if neg then -x else x)
    else
      let r := IEEEFloat.ofDecimal Float neg m.toNat e
      if IEEEFloat.isZero r || IEEEFloat.isInf r then none else some r
  | none => IEEEFloat.parse? Float s

/-- Julia `parse(Float64, s)`, with `NaN` in place of Julia's `ArgumentError`. -/
def parse (s : String) : Float := (parse? s).getD nan

end F64

namespace F32

/-- Julia `tryparse(Float32, s)` (rounded once, directly to `Float32`, like `strtof`). -/
def parse? (s : String) : Option Float32 := IEEEFloat.parse? Float32 s

end F32

end JuliaBase
