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

/-- Julia `tryparse(Float64, s)`: the correctly rounded value of a decimal literal, or `none`
(see `IEEEFloat.parse?`). -/
def parse? (s : String) : Option Float := IEEEFloat.parse? Float s

/-- Julia `parse(Float64, s)`, with `NaN` in place of Julia's `ArgumentError`. -/
def parse (s : String) : Float := (parse? s).getD nan

end F64

namespace F32

/-- Julia `tryparse(Float32, s)` (rounded once, directly to `Float32`, like `strtof`). -/
def parse? (s : String) : Option Float32 := IEEEFloat.parse? Float32 s

end F32

end JuliaBase
