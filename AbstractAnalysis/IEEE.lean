/-!
# Exact IEEE-754 toolkit, generic over the format

Julia's float printing, `isapprox` and the `Float64` constants come from
`JuliaBase` (`F64.showString`, `F32.showString`, `F64.isapprox`, `F64.eps`, …).
This module holds what `JuliaBase` does not provide, all generic over
`Float`/`Float32` through the `IEEEFloat` class:

* exact decoding `x = ±m·2^e` (`decode`) and the exact rational value (`toRat?`);
* correctly rounded conversion *from* exact values: `ofDyadic`, `ofFraction`,
  `ofRat` (Julia `Float64(::Rational)`, `Float32(::BigFloat)`), assembled through
  Lean's IEEE model (`Float.Model.UnpackedFloat.round`), so rounding is right by
  construction;
* the `Float32` constants and neighbours (`eps`, `floatmax`, `floatmin`,
  `maxintfloat`, `inf`, `nan`, `nextFloat`, `prevFloat`), which for `Float` agree
  with `JuliaBase.F64` (checked in `Tests/AbstractAnalysis/Props.lean`);
* Julia `exponent`, `eps(x)` (`ulp`) and an ulp distance for tolerant tests.

The API is format-generic so that it can move into `JuliaBase` unchanged.
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

end AbstractAnalysis
