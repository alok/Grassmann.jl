import Wilkinson
import Tests.AbstractAnalysis.Harness

/-!
Shared decoding for the Wilkinson goldens (`oracle/golden/wilkinson/`): hex bit
patterns, expression trees and exact 256-bit `BigFloat`s.
-/

open Lean Wilkinson Tests.Golden

namespace Tests.Wilkinson

/-- Parse a lowercase hexadecimal string. -/
def hexNat (s : String) : Nat :=
  s.foldl (fun acc c => acc * 16 + (if c.isDigit then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10)) 0

/-- A `Float64` from its hex bit pattern. -/
def hexF64 (j : Json) : Float := Float.ofBits (hexNat (jStr j)).toUInt64

/-- A `Float32` from its hex bit pattern. -/
def hexF32 (j : Json) : Float32 := Float32.ofBits (hexNat (jStr j)).toUInt32

/-- The expression tree of a golden `{"str", "tree"}` record. -/
def jExpr (rec : Json) : JExpr :=
  match JExpr.ofJson (jGet rec "tree") with
  | .ok e => e
  | .error m => .sym s!"<bad tree: {m}>"

/-- The expression string of a golden record. -/
def jExprStr (rec : Json) : String := jStr (jGet rec "str")

/-- An exact `BigFloat` record `{neg, m (hex), e}` / `{zero}` / `{inf}` / `{nan}`. -/
def jBig (j : Json) : Big :=
  if jBool (jGet j "nan") then .nan
  else if jBool (jGet j "zero") then .zero (jBool (jGet j "neg"))
  else if jBool (jGet j "inf") then .inf (jBool (jGet j "neg"))
  else .finite (jBool (jGet j "neg")) (hexNat (jStr (jGet j "m"))) (jInt (jGet j "e"))

/-- Bitwise `Float32` equality (`NaN` equals `NaN`). -/
def sameF32 (a b : Float32) : Bool := a.toBits == b.toBits || (a.isNaN && b.isNaN)

/-- Units in the last place between two finite `BigFloat`s of the same sign
(`none` when they are not comparable that way). -/
def bigUlps {p : Nat} (a b : BigFloat p) : Option Nat :=
  match a, b with
  | .finite s m e, .finite s' m' e' =>
    if s != s' then none
    else
      let lo := min e e'
      -- both mantissas at the smaller exponent: the distance in its ulps
      some ((((m <<< (e - lo).toNat : Nat) : Int) - ((m' <<< (e' - lo).toNat : Nat) : Int)).natAbs)
  | _, _ => if a == b then some 0 else none

end Tests.Wilkinson
