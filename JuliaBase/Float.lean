import JuliaBase.Num
import JuliaBase.Ryu
import JuliaBase.FloatLit

/-
Julia's float printing: `Ryu.writeshortest` (Julia `share/julia/base/ryu/shortest.jl:262-461`)
and the `show`/`print`/`string` entry points (`base/ryu/Ryu.jl:111-129`).

* `show(x::Float64)`: shortest round-trip digits; plain decimal iff `-4 < pt ≤ 6` (with `pt`
  the decimal-point position), else `d.ddde±X` with no `+` and no zero padding; integers keep
  `.0`; specials `NaN`, `Inf`, `-Inf`, `-0.0`.
* `:compact => true`: digits reduced to at most 6 significant ones, and the extra
  `abs(mod(x + 0.05, 10^(pt - olength)) - 0.05) > 0.05` test that sends e.g. `123456.789`
  to `1.23457e5` (sic).
* `Float32`: `show` is typed (`1.5f0`, `1.0f-5`, `NaN32`, `Inf32`), `print` is not (`1.5`,
  `1.0e-5`); compact `show` is untyped but keeps the `f` exponent character.
-/

namespace JuliaBase

/-- The keyword options of Julia `Ryu.writeshortest` (Ryu.jl:22-46). -/
structure ShortestOpts where
  /-- prefix `+` for non-negative values -/
  plus : Bool := false
  /-- prefix a space for non-negative values (overridden by `plus`) -/
  space : Bool := false
  /-- always write the decimal point (`1.0` rather than `1`) -/
  hash : Bool := true
  /-- minimum number of digits (`-1`: shortest) -/
  precision : Int := -1
  /-- the exponent character (`'e'`, or `'f'` for a typed `Float32`) -/
  expchar : Char := 'e'
  /-- write at least two exponent digits with an explicit sign -/
  padexp : Bool := false
  /-- the decimal point character -/
  decchar : Char := '.'
  /-- append Julia's type markers (`f0`, `NaN32`, `Inf32`) for `Float32` -/
  typed : Bool := false
  /-- reduce to at most 6 significant digits (`:compact => true`) -/
  compact : Bool := false
  deriving Repr, Inhabited

namespace Ryu

/-- Append `n` copies of `c`. -/
def pushN (s : String) (c : Char) : Nat → String
  | 0 => s
  | n + 1 => pushN (s.push c) c n

/-- Julia's `x == 0` / NaN / Inf special cases of `writeshortest` (shortest.jl:268-340), and
the sign (`append_sign`, utils.jl:285-297). `neg` is the sign bit, `isF32` selects the
`Float32` type markers. -/
def writeZero (neg isF32 : Bool) (o : ShortestOpts) : String := Id.run do
  let mut s := ""
  if neg then s := s.push '-'
  else if o.plus then s := s.push '+'
  else if o.space then s := s.push ' '
  s := s.push '0'
  if o.hash then s := s.push o.decchar
  if o.precision == -1 then
    if o.hash then s := s.push '0'
    if o.typed && isF32 then s := s ++ "f0"
    return s
  let mut p := o.precision
  while o.hash && p > 1 do
    s := s.push '0'
    p := p - 1
  if o.typed && isF32 then s := s ++ "f0"
  return s

/-- `NaN`/`Inf` with Julia's sign rule (no minus sign on NaN) and type suffix. -/
def writeSpecial (neg nan isF32 : Bool) (o : ShortestOpts) : String :=
  let sgn := if neg && !nan then "-" else if o.plus then "+" else if o.space then " " else ""
  sgn ++ (if nan then "NaN" else "Inf") ++ (if o.typed && isF32 then "32" else "")

/-- Julia `Int(10)^k` in wrapping `Int64` arithmetic, converted to `Float64`
(the `10^(pt - olength)` of shortest.jl:350). -/
def pow10Wrapped (k : Nat) : Float :=
  let v : UInt64 := 10 ^ k
  if v ≥ 0x8000000000000000 then -(Float.ofNat (0 - v).toNat) else Float.ofNat v.toNat

/-- The digit layout of `writeshortest` after the specials (shortest.jl:342-461), given the
Ryu output `digits · 10^nexp`. `x` is the value (as `Float64`) for the compact
exact-integer test, `neg` its sign bit. -/
def layout (x : Float) (neg isF32 : Bool) (d : Decimal) (o : ShortestOpts) : String := Id.run do
  let output := d.digits
  let nexp := d.exp10
  let digits := toString output.toNat
  let olength : Nat := decimalLength output
  let mut s := ""
  if neg then s := s.push '-'
  else if o.plus then s := s.push '+'
  else if o.space then s := s.push ' '
  let pt : Int := nexp + olength
  let maxpt : Int := if o.precision == -1 then 6 else o.precision
  let expForm :=
    !(-4 < pt && pt ≤ maxpt &&
      !(pt ≥ olength &&
        (F64.mod (x + f64! 0.05) (pow10Wrapped (pt - olength).toNat) - f64! 0.05).abs > f64! 0.05))
  let mut precision := o.precision
  if !expForm then
    if pt ≤ 0 then
      s := pushN (s.push '0' |>.push o.decchar) '0' pt.natAbs
      s := s ++ digits
      precision := precision - olength
    else if pt ≥ olength then
      s := pushN (s ++ digits) '0' nexp.toNat
      precision := precision - olength - nexp
      if o.hash then
        s := s.push o.decchar
        if precision < 0 then s := s.push '0'
    else
      let p := pt.toNat
      s := s ++ (digits.take p).toString
      s := s.push o.decchar
      s := s ++ (digits.drop p).toString
      precision := precision - olength
    if o.hash then
      while precision > 0 do
        s := s.push '0'
        precision := precision - 1
    if o.typed && isF32 then s := s ++ "f0"
    return s
  else
    s := s.push (digits.front)
    if olength > 1 || o.hash then
      s := s.push o.decchar
      s := s ++ (digits.drop 1).toString
      precision := precision - olength
    if o.hash then
      if olength == 1 then s := s.push '0'
      while precision > 0 do
        s := s.push '0'
        precision := precision - 1
    s := s.push o.expchar
    let exp2 : Int := nexp + olength - 1
    if exp2 < 0 then s := s.push '-'
    else if o.padexp then s := s.push '+'
    let ea := exp2.natAbs
    if ea < 10 && o.padexp then s := s.push '0'
    return s ++ toString ea

end Ryu

/-- Julia `Ryu.writeshortest(x::Float64, …)` (shortest.jl:262): shortest round-trip decimal
string of `x` with Julia's layout rules. -/
def writeShortest (x : Float) (o : ShortestOpts := {}) : String :=
  let neg := F64.signbit x
  if x == 0 then Ryu.writeZero neg false o
  else if x.isNaN then Ryu.writeSpecial neg true false o
  else if x.isInf then Ryu.writeSpecial neg false false o
  else
    let d := Ryu.reduceShortest64 x (if o.compact then some 999999 else none)
    Ryu.layout x neg false d o

/-- Julia `Ryu.writeshortest(x::Float32, …)` (shortest.jl:262). -/
def writeShortest32 (x : Float32) (o : ShortestOpts := {}) : String :=
  let neg := F32.signbit x
  if x == 0 then Ryu.writeZero neg true o
  else if x.isNaN then Ryu.writeSpecial neg true true o
  else if x.isInf then Ryu.writeSpecial neg false true o
  else
    let d := Ryu.reduceShortest32 x (if o.compact then some 999999 else none)
    Ryu.layout x.toFloat neg true d o

namespace F64

/-- Julia `show(io, x::Float64)` (= `repr`, `string`, `print`) (Ryu.jl:111):
`0.30000000000000004`, `1.0e6`, `1.0e-5`, `100000.0`, `-0.0`, `NaN`, `-Inf`. -/
def showString (x : Float) : String := writeShortest x

/-- Julia `show(IOContext(io, :compact => true), x::Float64)`: at most 6 significant digits,
`0.333333`, `1.23457e6`, `1.23457e5` for `123456.789` (sic). -/
def showCompact (x : Float) : String := writeShortest x { compact := true }

/-- `show` or `showCompact` according to an IO context's `:compact` flag. -/
@[inline] def showIO (compact : Bool) (x : Float) : String :=
  if compact then showCompact x else showString x

end F64

namespace F32

/-- Julia `show(io, x::Float32)` at top level (Ryu.jl:111, `typed = true`, `expchar = 'f'`):
`1.5f0`, `1.0f-5`, `0.33333334f0`, `NaN32`, `-Inf32`. -/
def showString (x : Float32) : String := writeShortest32 x { typed := true, expchar := 'f' }

/-- Julia `show` of a `Float32` inside a `Float32` container (`typeinfo == Float32`, so
untyped) or compact context without compaction: `1.5`, but `1.0f-5`. -/
def showUntyped (x : Float32) : String := writeShortest32 x { expchar := 'f' }

/-- Julia `show(IOContext(io, :compact => true), x::Float32)`: untyped, 6 significant digits,
exponent character still `f` (`0.333333`, `1.0f-5`). -/
def showCompact (x : Float32) : String := writeShortest32 x { expchar := 'f', compact := true }

/-- Julia `print(io, x::Float32)` (Ryu.jl:129, `forceuntyped`, `fromprint`): `1.5`, `1.0e-5`. -/
def printString (x : Float32) : String := writeShortest32 x

/-- Julia `print(IOContext(io, :compact => true), x::Float32)`. -/
def printCompact (x : Float32) : String := writeShortest32 x { compact := true }

end F32

end JuliaBase
