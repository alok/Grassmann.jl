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

/-- The fast scanner's state machine, one byte per step, every quantity an unboxed argument:
`ph` is the phase (`0` integer digits, `1` fraction digits, `2` right after `e`/`E`,
`3` after the exponent sign, `4` exponent digits), `m` the mantissa (at most 19 digits `nd`),
`fr` the fraction digits, `ev`/`ned` the exponent value and digit count (at most 4). -/
def scanLoop (s : String) (neg : Bool) (i : Nat) (ph : UInt8) (m : UInt64) (nd fr : Nat)
    (eneg : Bool) (ev ned : Nat) : Nat → Option (Bool × UInt64 × Int)
  | 0 => none
  | fuel + 1 =>
    if i ≥ s.utf8ByteSize then
      -- end of input: accept unless the exponent has no digits
      if nd == 0 || ph == 2 || ph == 3 then none
      else some (neg, m, (if eneg then -(ev : Int) else ev) - fr)
    else
      let c := byteAt s i
      let digit := c ≥ 48 && c ≤ 57
      if ph ≤ 1 then
        if digit then
          if nd ≥ 19 then none
          else scanLoop s neg (i + 1) ph (m * 10 + (c - 48).toUInt64) (nd + 1)
            (if ph == 1 then fr + 1 else fr) eneg ev ned fuel
        else if c == 46 && ph == 0 then scanLoop s neg (i + 1) 1 m nd fr eneg ev ned fuel
        else if (c == 101 || c == 69) && nd > 0 then scanLoop s neg (i + 1) 2 m nd fr eneg ev ned fuel
        else none
      else if ph == 2 && (c == 45 || c == 43) then
        scanLoop s neg (i + 1) 3 m nd fr (c == 45) ev ned fuel
      else if digit && ned < 4 then
        scanLoop s neg (i + 1) 4 m nd fr eneg (ev * 10 + (c - 48).toNat) (ned + 1) fuel
      else none

/-- The fast scanner: `some (neg, mantissa, decimal exponent)` when `s` is exactly
`[+-]digits[.digits][(e|E)[+-]digits]` with at most 19 significant digits in total and at most
4 exponent digits (and at least one mantissa digit); `none` otherwise. -/
def scanSimple (s : String) : Option (Bool × UInt64 × Int) :=
  let c0 := byteAt s 0
  let (neg, i) := if c0 == 45 then (true, 1) else if c0 == 43 then (false, 1) else (false, 0)
  scanLoop s neg i 0 0 0 0 false 0 0 (s.utf8ByteSize + 1)

/-! ## Eisel–Lemire

Lemire's algorithm ("Number Parsing at a Gigabyte per Second", 2021; Go's `eiselLemire64`):
multiply the normalized 64-bit mantissa by a 128-bit truncation of `10^q` and read the
correctly rounded double off the top bits, unless the product is too close to a rounding
boundary to decide (then the exact path runs). It covers every 19-digit mantissa with
`-348 ≤ q ≤ 347` except those rare ambiguous cases, so 17-digit round-trip literals (Julia's
own `show` output) no longer need big-number arithmetic. -/

/-- The smallest decimal exponent of the table. -/
def elMinExp : Int := -348

/-- `⌊10^q · 2^s⌋` normalized to 128 bits (top bit set) for `q = -348 … 347`, as
`(high word, low word)`: the truncated powers of ten of Eisel–Lemire, computed exactly once. -/
def elTable : Array (UInt64 × UInt64) :=
  (List.range 696).toArray.map fun (i : Nat) =>
    let q : Int := (i : Int) + elMinExp
    let v : Nat := if q ≥ 0 then 10 ^ q.toNat
      else
        let d := 10 ^ (-q).toNat
        2 ^ (Nat.log2 d + 1 + 128) / d
    let len := Nat.log2 v + 1
    let t := if len ≥ 128 then v >>> (len - 128) else v <<< (128 - len)
    ((t >>> 64).toUInt64, (t % 2 ^ 64).toUInt64)

/-- High words of `elTable` (unboxed reads). -/
def elHi : Array UInt64 := elTable.map (·.1)

/-- Low words of `elTable`. -/
def elLo : Array UInt64 := elTable.map (·.2)

/-- The number of leading zero bits of a nonzero `UInt64`. -/
@[inline] def clz64 (x : UInt64) : UInt64 :=
  let (n, x) : UInt64 × UInt64 := if x >>> 32 == 0 then (32, x <<< 32) else (0, x)
  let (n, x) := if x >>> 48 == 0 then (n + 16, x <<< 16) else (n, x)
  let (n, x) := if x >>> 56 == 0 then (n + 8, x <<< 8) else (n, x)
  let (n, x) := if x >>> 60 == 0 then (n + 4, x <<< 4) else (n, x)
  let (n, x) := if x >>> 62 == 0 then (n + 2, x <<< 2) else (n, x)
  if x >>> 63 == 0 then n + 1 else n

/-- The 128-bit product `a·b` as `(high, low)`. -/
@[inline] def mulFull (a b : UInt64) : UInt64 × UInt64 :=
  let mask : UInt64 := 0xFFFFFFFF
  let a0 := a &&& mask
  let a1 := a >>> 32
  let b0 := b &&& mask
  let b1 := b >>> 32
  let p00 := a0 * b0
  let p01 := a0 * b1
  let p10 := a1 * b0
  let mid := (p00 >>> 32) + (p01 &&& mask) + (p10 &&& mask)
  (a1 * b1 + (p01 >>> 32) + (p10 >>> 32) + (mid >>> 32), (p00 &&& mask) ||| (mid <<< 32))

/-- Eisel–Lemire for `m · 10^q` (`m ≠ 0`): the correctly rounded double, or `none` when the
product is too close to a rounding boundary, outside the table, or not a normal number. -/
def eiselLemire (m : UInt64) (q : Int) (neg : Bool) : Option Float :=
  if q < elMinExp || q > 347 then none
  else
    let i := (q - elMinExp).toNat
    let hi := elHi[i]?.getD 0
    let lo := elLo[i]?.getD 0
    let clz := clz64 m
    let man := m <<< clz
    -- `⌊log2(10^q)⌋ = (217706·q) >> 16` (exact for |q| < 1233), plus 64 + bias, minus the shift
    let exp2 : UInt64 := ((217706 * q) >>> 16 + 64 + 1023).toInt64.toUInt64 - clz
    let (xHi, xLo) := mulFull man hi
    -- the truncated table value may make the product too small by less than `man`
    let wide : Option (UInt64 × UInt64) :=
      if xHi &&& 0x1FF == 0x1FF && xLo + man < man then
        let (yHi, yLo) := mulFull man lo
        let mLo := xLo + yHi
        let mHi := if mLo < xLo then xHi + 1 else xHi
        if mHi &&& 0x1FF == 0x1FF && mLo + 1 == 0 && yLo + man < man then none
        else some (mHi, mLo)
      else some (xHi, xLo)
    match wide with
    | none => none
    | some (xHi, xLo) =>
      let msb := xHi >>> 63
      let mant := xHi >>> (msb + 9)
      let exp2 := exp2 - (1 ^^^ msb)
      -- exactly half-way between two doubles: undecided here
      if xLo == 0 && xHi &&& 0x1FF == 0 && mant &&& 3 == 1 then none
      else
        let mant := (mant + (mant &&& 1)) >>> 1
        let (mant, exp2) := if mant >>> 53 > 0 then (mant >>> 1, exp2 + 1) else (mant, exp2)
        -- subnormal or infinite results take the exact path
        if exp2 - 1 ≥ 0x7FF - 1 then none
        else
          let bits := (exp2 <<< 52) ||| (mant &&& 0x000FFFFFFFFFFFFF)
          some (Float.ofBits (if neg then bits ||| 0x8000000000000000 else bits))

/-- Julia `tryparse(Float64, s)`: the correctly rounded value of a decimal literal, or `none`
(see `IEEEFloat.parse?`); simple literals take Clinger's fast path or Eisel–Lemire above. -/
def parse? (s : String) : Option Float :=
  match scanSimple s with
  | some (neg, m, e) =>
    if m == 0 then some (if neg then -0.0 else 0.0)
    else if m < 9007199254740992 && -22 ≤ e && e ≤ 22 then
      let x := m.toFloat
      let x := if e ≥ 0 then x * pow10Exact.get! e.toNat else x / pow10Exact.get! (-e).toNat
      some (if neg then -x else x)
    else match eiselLemire m e neg with
      | some x => some x
      | none =>
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
