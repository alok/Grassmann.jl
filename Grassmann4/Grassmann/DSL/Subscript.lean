/-
  Grassmann/DSL/Subscript.lean - Unicode Subscript Notation for Blades

  Provides elegant notation for basis vectors and blades:
    e₁, e₂, e₃     -- Basis vectors
    e₁₂, e₁₃, e₂₃  -- Bivectors
    e₁₂₃           -- Trivector

  Also provides fallback for indices > 9:
    e[10], e[15,23]

  The subscript characters used are:
    ₀ (U+2080), ₁ (U+2081), ₂ (U+2082), ₃ (U+2083), ₄ (U+2084)
    ₅ (U+2085), ₆ (U+2086), ₇ (U+2087), ₈ (U+2088), ₉ (U+2089)
-/
import Lean
import Grassmann.GATypeclass

open Lean Elab Meta Term Macro

namespace Grassmann.DSL

/-! ## Subscript Parsing Utilities -/

/-- Convert a unicode subscript character to its digit value -/
def subscriptToDigit : Char → Option Nat
  | '₀' => some 0
  | '₁' => some 1
  | '₂' => some 2
  | '₃' => some 3
  | '₄' => some 4
  | '₅' => some 5
  | '₆' => some 6
  | '₇' => some 7
  | '₈' => some 8
  | '₉' => some 9
  | _ => none

/-- Convert a digit (1-9) to its unicode subscript character -/
def digitToSubscript : Nat → Char
  | 0 => '₀'
  | 1 => '₁'
  | 2 => '₂'
  | 3 => '₃'
  | 4 => '₄'
  | 5 => '₅'
  | 6 => '₆'
  | 7 => '₇'
  | 8 => '₈'
  | 9 => '₉'
  | _ => '?'

/-- Parse a string of subscript characters into a list of 1-indexed positions -/
def parseSubscripts (s : String) : List Nat :=
  s.toList.filterMap subscriptToDigit

/-- Convert a list of 1-indexed blade indices to a bitmask -/
def indicesToBitmask (indices : List Nat) : Nat :=
  indices.foldl (fun acc i => acc ||| (1 <<< (i - 1))) 0

/-- Convert a bitmask to a blade name like "e123" -/
def bitmaskToName (mask : Nat) (dim : Nat) : String :=
  if mask == 0 then "scalar"
  else
    let indices := (List.range dim).filter fun i => mask &&& (1 <<< i) != 0
    "e" ++ String.join (indices.map fun i => toString (i + 1))

/-- Convert a bitmask to a subscript blade name like "e₁₂₃" -/
def bitmaskToSubscript (mask : Nat) (dim : Nat) : String :=
  if mask == 0 then "scalar"
  else
    let indices := (List.range dim).filter fun i => mask &&& (1 <<< i) != 0
    "e" ++ (indices.map fun i => digitToSubscript (i + 1)).asString

/-! ## Syntax Declarations -/

-- Define what constitutes subscript digits
declare_syntax_cat subscriptDigits

-- Individual subscript characters
syntax "₀" : subscriptDigits
syntax "₁" : subscriptDigits
syntax "₂" : subscriptDigits
syntax "₃" : subscriptDigits
syntax "₄" : subscriptDigits
syntax "₅" : subscriptDigits
syntax "₆" : subscriptDigits
syntax "₇" : subscriptDigits
syntax "₈" : subscriptDigits
syntax "₉" : subscriptDigits

-- Concatenation of subscript digits
syntax subscriptDigits subscriptDigits : subscriptDigits

/-- Main blade syntax: e followed by subscript digits -/
syntax "e" subscriptDigits : term

/-- Fallback syntax for indices > 9: e[10] or e[1,5,10] -/
syntax "e[" num,* "]" : term

/-! ## Macro Rules -/

/-- Extract subscript string from syntax -/
partial def extractSubscriptString : TSyntax `subscriptDigits → String
  | stx =>
    let s := stx.raw.reprint.getD ""
    s.trim

/-- Parse subscript syntax into list of indices -/
def parseSubscriptSyntax (stx : TSyntax `subscriptDigits) : List Nat :=
  parseSubscripts (extractSubscriptString stx)

/-- Main macro for e₁₂₃ notation -/
macro_rules
  | `(e $subs:subscriptDigits) => do
    let indices := parseSubscriptSyntax subs
    -- Validate: indices must be 1-9 and non-empty
    if indices.isEmpty then
      Macro.throwError "Blade notation requires at least one index"
    for i in indices do
      if i == 0 then
        Macro.throwError "Blade index 0 is not valid (indices are 1-based)"
      if i > 9 then
        Macro.throwError s!"Index {i} exceeds maximum subscript (use e[{i}] for large indices)"
    let bits := indicesToBitmask indices
    -- Generate: GABlade.blade (BitVec.ofNat n bits)
    -- The dimension n will be inferred from context
    `(GABlade.blade (BitVec.ofNat _ $(Lean.quote bits)))

/-- Fallback macro for e[10], e[1,5,10], etc. -/
macro_rules
  | `(e[ $[$ns:num],* ]) => do
    let indices := ns.toList.map (·.getNat)
    if indices.isEmpty then
      Macro.throwError "Blade notation requires at least one index"
    for i in indices do
      if i == 0 then
        Macro.throwError "Blade index 0 is not valid (indices are 1-based)"
    let bits := indicesToBitmask indices
    `(GABlade.blade (BitVec.ofNat _ $(Lean.quote bits)))

/-! ## Standalone Basis Notation (without algebra context) -/

/-- For use outside of Cl() blocks, with explicit type -/
syntax "basis" "(" num ")" : term

macro_rules
  | `(basis($i:num)) => do
    let idx := i.getNat
    if idx == 0 then
      Macro.throwError "Basis index 0 is not valid (indices are 1-based)"
    let bit := 1 <<< (idx - 1)
    `(GABlade.blade (BitVec.ofNat _ $(Lean.quote bit)))

end Grassmann.DSL
