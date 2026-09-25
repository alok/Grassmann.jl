/-
IEEE-754 bit toolkit and Julia's float printing.

Julia's `AbstractAnalysis` and `Wilkinson` both lean on `Base` float
semantics: `eps`, `nextfloat`/`prevfloat`, `≈`, and the shortest round-trip
printing that shows up verbatim in every `show` golden. This module takes
`Float`/`Float32` apart through `toBits`/`ofBits` and reassembles them through
Lean's IEEE model (`Float.Model.UnpackedFloat.round`), so every conversion from
an exact value is correctly rounded by construction.

It lives here (rather than in `JuliaBase`) until that library lands; the API
is deliberately format-generic so it can move without changes.
-/

namespace AbstractAnalysis

open Float.Model (Format)
open Float.Model.UnpackedFloat (Sign)

/-- A binary IEEE-754 format that can be taken apart bit by bit
(Julia's `Base.IEEEFloat`). -/
class IEEEFloat (F : Type) where
  /-- Significand bits including the implicit one (Julia `precision(F)`). -/
  precision : Nat
  /-- Width of the exponent field. -/
  exponentBits : Nat
  /-- The matching format of Lean's float model. -/
  format : Format
  /-- Raw bits (Julia `reinterpret(Unsigned, x)`). -/
  toBitsNat : F → Nat
  /-- Inverse of `toBitsNat` on in-range bit patterns. -/
  ofBitsNat : Nat → F
  /-- Exact widening to `Float` (Julia `Float64(x)`). -/
  toFloat : F → Float

instance : IEEEFloat Float where
  precision := 53
  exponentBits := 11
  format := .binary64
  toBitsNat x := x.toBits.toNat
  ofBitsNat n := Float.ofBits n.toUInt64
  toFloat x := x

instance : IEEEFloat Float32 where
  precision := 24
  exponentBits := 8
  format := .binary32
  toBitsNat x := x.toBits.toNat
  ofBitsNat n := Float32.ofBits n.toUInt32
  toFloat x := x.toFloat

namespace IEEEFloat

variable {F : Type} [IEEEFloat F]

/-- Fraction-field width (`precision - 1`). -/
@[inline] def fracBits (F : Type) [IEEEFloat F] : Nat := precision F - 1

/-- Exponent bias (`1023` for `Float64`). -/
@[inline] def bias (F : Type) [IEEEFloat F] : Nat := 2 ^ (exponentBits F - 1) - 1

/-- All-ones exponent field (`Inf`/`NaN`). -/
@[inline] def expMax (F : Type) [IEEEFloat F] : Nat := 2 ^ exponentBits F - 1

/-- Sign bit (Julia `signbit`). -/
@[inline] def signBit (x : F) : Bool := toBitsNat x >>> (exponentBits F + fracBits F) % 2 == 1

/-- Biased exponent field. -/
@[inline] def expField (x : F) : Nat := (toBitsNat x >>> fracBits F) % 2 ^ exponentBits F

/-- Fraction field. -/
@[inline] def fracField (x : F) : Nat := toBitsNat x % 2 ^ fracBits F

/-- Finite (neither `Inf` nor `NaN`). -/
@[inline] def isFinite (x : F) : Bool := expField x != expMax F

/-- `NaN` test. -/
@[inline] def isNaN (x : F) : Bool := expField x == expMax F && fracField x != 0

/-- `±Inf` test. -/
@[inline] def isInf (x : F) : Bool := expField x == expMax F && fracField x == 0

/-- `±0` test. -/
@[inline] def isZero (x : F) : Bool := expField x == 0 && fracField x == 0

/-- Assemble a value from sign, biased exponent and fraction fields. -/
@[inline] def assemble (F : Type) [IEEEFloat F] (neg : Bool) (e f : Nat) : F :=
  ofBitsNat ((if neg then 2 ^ (exponentBits F + fracBits F) else 0) + e * 2 ^ fracBits F + f)

/-- `|x| = m * 2^e` for finite nonzero `x`, with `m < 2^precision`
(Julia `significand`/`exponent`, but integral). -/
def decode (x : F) : Option (Bool × Nat × Int) :=
  let e := expField x
  let f := fracField x
  if e == expMax F || (e == 0 && f == 0) then none
  else if e == 0 then some (signBit x, f, 1 - (bias F : Int) - fracBits F)
  else some (signBit x, 2 ^ fracBits F + f, (e : Int) - bias F - fracBits F)

/-- The exact rational value of a finite float. -/
def toRat? (x : F) : Option Rat :=
  if isZero x then some 0
  else match decode x with
    | none => none
    | some (s, m, e) =>
      let q : Rat := if e ≥ 0 then ((m * 2 ^ e.toNat : Nat) : Rat) else (m : Rat) / ((2 ^ (-e).toNat : Nat) : Rat)
      some (if s then -q else q)

/-- Pack a canonical unpacked float of this format. -/
@[inline] def ofUnpacked (u : Float.Model.UnpackedFloat) : F :=
  ofBitsNat (Float.Model.UnpackedFloat.pack (format F) u).toNat

/-- `(-1)^neg * m * 2^e`, correctly rounded (nearest, ties to even; overflow to `Inf`). -/
def ofDyadic (F : Type) [IEEEFloat F] (neg : Bool) (m : Nat) (e : Int) : F :=
  if m = 0 then assemble F neg 0 0
  else ofUnpacked (F := F) (Float.Model.UnpackedFloat.round (format F) (if neg then .negative else .positive) m e)

/-- `n / d` correctly rounded (Julia `F(n//d)`). -/
def ofFraction (F : Type) [IEEEFloat F] (n : Int) (d : Nat) : F :=
  if hd : d = 0 then
    (if n = 0 then ofBitsNat (expMax F * 2 ^ fracBits F + 1) else assemble F (n < 0) (expMax F) 0)
  else if hn : n.natAbs = 0 then assemble F false 0 0
  else
    ofUnpacked (F := F) <| Float.Model.UnpackedFloat.div (format F)
      (.finite (if n < 0 then .negative else .positive) n.natAbs 0 (Nat.pos_of_ne_zero hn))
      (.finite .positive d 0 (Nat.pos_of_ne_zero hd))

/-- A rational, correctly rounded. -/
@[inline] def ofRat (F : Type) [IEEEFloat F] (q : Rat) : F := ofFraction F q.num q.den

/-- Julia `eps(F)`: the gap between `1` and the next float. -/
def eps (F : Type) [IEEEFloat F] : F := ofDyadic F false 1 (-(fracBits F : Int))

/-- Julia `floatmax(F)`. -/
def floatmax (F : Type) [IEEEFloat F] : F := assemble F false (expMax F - 1) (2 ^ fracBits F - 1)

/-- Julia `floatmin(F)` (smallest positive normal). -/
def floatmin (F : Type) [IEEEFloat F] : F := assemble F false 1 0

/-- Julia `maxintfloat(F)`: `2^precision`. -/
def maxintfloat (F : Type) [IEEEFloat F] : F := ofDyadic F false 1 (precision F)

/-- Positive infinity. -/
def inf (F : Type) [IEEEFloat F] : F := assemble F false (expMax F) 0

/-- Canonical `NaN`. -/
def nan (F : Type) [IEEEFloat F] : F := assemble F false (expMax F) (2 ^ fracBits F / 2)

/-- Julia `nextfloat(x)`: the least float greater than `x`. -/
def nextFloat (x : F) : F :=
  if isNaN x then x
  else if isInf x then (if signBit x then ofBitsNat (toBitsNat x - 1) else x)
  else if isZero x then assemble F false 0 1
  else if signBit x then ofBitsNat (toBitsNat x - 1)
  else ofBitsNat (toBitsNat x + 1)

/-- Julia `prevfloat(x)`: the greatest float less than `x`. -/
def prevFloat (x : F) : F :=
  if isNaN x then x
  else if isInf x then (if signBit x then x else ofBitsNat (toBitsNat x - 1))
  else if isZero x then assemble F true 0 1
  else if signBit x then ofBitsNat (toBitsNat x + 1)
  else ofBitsNat (toBitsNat x - 1)

/-- Julia `exponent(x)` for finite nonzero `x`: `⌊log2 |x|⌋`. -/
def exponent (x : F) : Int :=
  match decode x with
  | none => 0
  | some (_, m, e) => (Nat.log2 m : Int) + e

/-- Julia `eps(x)`: the spacing of floats at `x` (`NaN` for non-finite `x`). -/
def ulp (x : F) : F :=
  if !isFinite x then nan F
  else if expField x ≤ 1 then assemble F false 0 1
  else ofDyadic F false 1 (exponent x - fracBits F)

/-- Distance in units of the last place between two finite floats of the same
sign class, measured on the bit lattice (`0` iff bitwise equal up to `±0`). -/
def ulpDistance (x y : F) : Nat :=
  let key (z : F) : Int :=
    if signBit z then -((toBitsNat z % 2 ^ (exponentBits F + fracBits F) : Nat) : Int)
    else (toBitsNat z : Int)
  (key x - key y).natAbs

end IEEEFloat

/-! ## Julia's shortest round-trip printing (Ryu `writeshortest`) -/

namespace JuliaFloat

open IEEEFloat

/-- Compare `a * 10^qa` with `b * 2^eb` exactly. -/
def cmpDecBin (a : Nat) (qa : Int) (b : Nat) (eb : Int) : Ordering :=
  let lhs := a * 10 ^ qa.toNat * 2 ^ (-eb).toNat
  let rhs := b * 2 ^ eb.toNat * 10 ^ (-qa).toNat
  compare lhs rhs

/-- `⌊b * 2^eb / 10^q⌋`. -/
def floorDiv (b : Nat) (eb : Int) (q : Int) : Nat :=
  (b * 2 ^ eb.toNat * 10 ^ (-q).toNat) / (2 ^ (-eb).toNat * 10 ^ q.toNat)

/-- Number of decimal digits of a positive natural. -/
def decimalLength (n : Nat) : Nat := (toString n).length

/-- Strip trailing decimal zeros, moving them into the exponent. -/
def stripZeros (d : Nat) (q : Int) : Nat × Int :=
  go d q d
where
  /-- Fuelled by the digit count. -/
  go (d : Nat) (q : Int) : Nat → Nat × Int
    | 0 => (d, q)
    | fuel + 1 => if d != 0 && d % 10 == 0 then go (d / 10) (q + 1) fuel else (d, q)

/-- Shortest decimal `digits * 10^nexp` that rounds back to the finite, nonzero
float `m * 2^e`. Among the shortest candidates the one closest to the exact
value wins, ties to even: exactly Ryu's output. -/
def shortestDigits (precision : Nat) (m : Nat) (e : Int) (lowerGapHalved : Bool) : Nat × Int :=
  let N := 4 * m
  let E2 := e - 2
  let mp := N + 2
  let mm := if lowerGapHalved then N - 1 else N - 2
  let accept := m % 2 == 0
  -- decimal exponent: 10^E ≤ v < 10^(E+1)
  -- rough estimate `⌊log10 v⌋ ≈ 0.301·log2 v`, then corrected exactly
  let E := fixE N E2 (((Nat.log2 N : Int) + E2) * 301 / 1000) 64
  let maxDigits := precision * 30103 / 100000 + 3
  let inside (c : Nat) (q : Int) : Bool :=
    let lo := cmpDecBin c q mm E2
    let hi := cmpDecBin c q mp E2
    (lo == .gt || (accept && lo == .eq)) && (hi == .lt || (accept && hi == .eq))
  let rec search : Nat → Nat → Nat × Int
    | 0, _ => (m, e) -- unreachable: `maxDigits` digits always suffice
    | fuel + 1, n =>
      let q := E - (n : Int) + 1
      let d := floorDiv N E2 q
      let okD := d != 0 && inside d q
      let okU := inside (d + 1) q
      if okD && okU then
        match cmpDecBin (2 * d + 1) q (2 * N) E2 with
        | .gt => stripZeros d q
        | .lt => stripZeros (d + 1) q
        | .eq => stripZeros (if d % 2 == 0 then d else d + 1) q
      else if okD then stripZeros d q
      else if okU then stripZeros (d + 1) q
      else search fuel (n + 1)
  search (maxDigits + 1) 1
where
  /-- Correct a decimal-exponent estimate with exact comparisons. -/
  fixE (N : Nat) (E2 : Int) (E : Int) : Nat → Int
    | 0 => E
    | fuel + 1 =>
      if cmpDecBin 1 (E + 1) N E2 != .gt then fixE N E2 (E + 1) fuel
      else if cmpDecBin 1 E N E2 == .gt then fixE N E2 (E - 1) fuel
      else E

/-- Shortest digits of a finite, nonzero float: `(neg, digits, nexp)`. -/
def shortest {F : Type} [IEEEFloat F] (x : F) : Option (Bool × Nat × Int) :=
  match decode x with
  | none => none
  | some (s, m, e) =>
    let halved := fracField x == 0 && expField x > 1
    let (d, q) := shortestDigits (precision F) m e halved
    some (s, d, q)

/-- Julia `mod(x, y)` for `Float64` (exact `rem`, then one rounded correction). -/
def fmod (x y : Float) : Float :=
  match IEEEFloat.toRat? x, IEEEFloat.toRat? y with
  | some a, some b =>
    if b == 0 then IEEEFloat.nan Float
    else
      let t := (a / b)
      let tq : Int := if t ≥ 0 then t.floor else t.ceil  -- truncation
      let r : Rat := a - tq * b
      let rf := IEEEFloat.ofRat Float r
      if r == 0 then (if y < 0 then -0.0 else 0.0)
      else if (r > 0) != (b > 0) then rf + y else rf
  | _, _ => IEEEFloat.nan Float

/-- Render shortest digits the way Julia's `Ryu.writeshortest` does with
`hash = true, precision = -1`. `typed` appends Julia's `Float32` marker
(`f0`, or `f` as exponent char). `x64` is the value widened to `Float64` (it
feeds Julia's integer-closeness guard). -/
def render (neg : Bool) (digits : Nat) (nexp : Int) (x64 : Float) (typed32 : Bool) : String :=
  let ds := toString digits
  let olength := ds.length
  let pt : Int := nexp + olength
  let sign := if neg then "-" else ""
  let guard :=
    pt ≥ olength &&
      (let k := (pt - olength).toNat
       let r := fmod (x64 + 0.05) (Float.ofNat (10 ^ k))
       (r - 0.05).abs > 0.05)
  if -4 < pt && pt ≤ 6 && !guard then
    let body :=
      if pt ≤ 0 then "0." ++ String.ofList (List.replicate (-pt).toNat '0') ++ ds
      else if pt ≥ olength then ds ++ String.ofList (List.replicate nexp.toNat '0') ++ ".0"
      else
        let k := pt.toNat
        String.ofList (ds.toList.take k) ++ "." ++ String.ofList (ds.toList.drop k)
    sign ++ body ++ (if typed32 then "f0" else "")
  else
    let first := String.ofList (ds.toList.take 1)
    let rest := String.ofList (ds.toList.drop 1)
    let mant := if olength > 1 then first ++ "." ++ rest else first ++ ".0"
    let e2 := nexp + olength - 1
    sign ++ mant ++ (if typed32 then "f" else "e") ++ toString e2

/-- Julia `string(x)` / `print(x)` for an IEEE float (no type suffix). -/
def toJuliaString {F : Type} [IEEEFloat F] (x : F) : String :=
  if isNaN x then "NaN"
  else if isInf x then (if signBit x then "-Inf" else "Inf")
  else if isZero x then (if signBit x then "-0.0" else "0.0")
  else match shortest x with
    | none => "NaN"
    | some (s, d, q) => render s d q (IEEEFloat.toFloat x) false

/-- Julia `repr(x::Float32)` / `show`: typed (`1.0f0`, `1.0f10`, `NaN32`, `Inf32`). -/
def float32Repr (x : Float32) : String :=
  if isNaN x then "NaN32"
  else if isInf x then (if signBit x then "-Inf32" else "Inf32")
  else if isZero x then (if signBit x then "-0.0f0" else "0.0f0")
  else match shortest x with
    | none => "NaN32"
    | some (s, d, q) => render s d q x.toFloat true

end JuliaFloat

/-- Julia's shortest round-trip rendering, e.g. `0.01`, `3.26592e6`, `Inf`. -/
def Float.toJulia (x : Float) : String := JuliaFloat.toJuliaString x

/-- Julia `print` of a `Float32` (untyped shortest digits). -/
def Float32.toJulia (x : Float32) : String := JuliaFloat.toJuliaString x

/-! ## `isapprox` -/

/-- Julia's default relative tolerance `√eps(Float64)`. -/
def rtolDefault : Float := 1.4901161193847656e-8

/-- Julia `isapprox(x, y)` for `Float64` with default tolerances
(`atol = 0`, `rtol = √eps`): `x == y || (finite ∧ |x-y| ≤ rtol·max(|x|,|y|))`. -/
def Float.isApprox (x y : Float) : Bool :=
  x == y || (x.isFinite && y.isFinite && (x - y).abs ≤ rtolDefault * max x.abs y.abs)

end AbstractAnalysis
