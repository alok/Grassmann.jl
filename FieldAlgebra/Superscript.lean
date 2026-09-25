import FieldConstants

/-!
# Superscript printing (FieldAlgebra's `printexpo` family)

FieldAlgebra prints group elements as monomials with Unicode superscript
exponents: `ML²T⁻²`, `𝘩¹ᐟ²𝘤⁻¹ᐟ²`, `kg⁰⋅³`. This module ports the printing
primitives exactly, including their quirks:

* `makeint` (`FieldAlgebra.jl:102-116`) snaps floats within ~`1e-17` relative of
  an integer to that integer, and the `+1` branch rounds up even for negatives;
* `findpower` (`:118-119`) returns the position of the *first* zero digit;
* `printexpo(io, "10", x::Float)` prints both `/` and `⁻` for negative
  non-integer exponents (`:305-355`).

Julia sources: `FieldAlgebra.jl/src/FieldAlgebra.jl:97-301, 391-429`.
-/

namespace FieldAlgebra

open FieldConstants

/-- Superscript digits `⁰…⁹` (Julia `expos`, `FieldAlgebra.jl:97`). -/
def expos : Array Char := #['⁰', '¹', '²', '³', '⁴', '⁵', '⁶', '⁷', '⁸', '⁹']

/-- Superscript decimal digits of a natural number. -/
def supNat (n : Nat) : String :=
  String.ofList ((toString n).toList.map fun c => expos[c.toNat - '0'.toNat]!)

/-- Julia's `chars` table (`FieldAlgebra.jl:98`): characters of a printed
float mapped to superscripts (`.`↦`⋅`, `-`↦`⁻`, `e`↦`ᵉ`). -/
def supChar (c : Char) : Char :=
  if c.isDigit then expos[c.toNat - '0'.toNat]!
  else match c with
    | '.' => '⋅' | '-' => '⁻' | 'e' => 'ᵉ' | 'v' => 'ᵛ'
    | '₀' => '⁰' | '₁' => '¹' | '₂' => '²' | '₃' => '³' | '₄' => '⁴'
    | '₅' => '⁵' | '₆' => '⁶' | '₇' => '⁷' | '₈' => '⁸' | '₉' => '⁹'
    | c => c

/-- Julia `Float64(n)` for an `Int`: a machine conversion when `n` fits in 64 bits
(`Float.ofInt` goes through `OfScientific` and `Nat.log2`, ~100 ns). -/
@[inline] def intToFloat (n : Int) : Float :=
  match n with
  | .ofNat k => if k < 18446744073709551616 then k.toUInt64.toFloat else Float.ofNat k
  | .negSucc k => if k < 18446744073709551615 then -((k.toUInt64 + 1).toFloat) else Float.ofInt n

/-- A Julia exponent: `Int`, `Rational{Int}` or `Float64` (the element type of
a `Group`'s exponent vector). -/
inductive Expo where
  /-- an `Int` exponent -/
  | int (n : Int)
  /-- a `Rational{Int}` exponent (not necessarily with denominator ≠ 1) -/
  | rat (q : Rat)
  /-- a `Float64` exponent -/
  | float (x : Float)
  deriving Inhabited

namespace Expo

/-- Numeric value as a `Float64`. -/
def toFloat : Expo → Float
  | int n => intToFloat n
  | rat q => JuliaBase.IEEEFloat.ofRat Float q
  | float x => x

/-- Julia `iszero`. -/
def isZero : Expo → Bool
  | int n => n == 0
  | rat q => q == 0
  | float x => x == 0.0

/-- Julia `isone`. -/
def isOne : Expo → Bool
  | int n => n == 1
  | rat q => q == 1
  | float x => x == 1.0

/-- Julia `print` of the exponent value itself. -/
def print : Expo → String
  | int n => toString n
  | rat q => s!"{q.num}//{q.den}"
  | float x => JuliaBase.F64.showString x

end Expo

/-- Julia `makeint(x::AbstractFloat)` (`FieldAlgebra.jl:102-116`): return the
integer `x` is (numerically) indistinguishable from, else `x` itself. -/
def makeint (x : Float) : JNum :=
  if x == 0.0 then .int 0
  else
    let ax := x.abs
    let rem := (JuliaBase.F64.rem x 1.0).abs
    let ne := (f64! 2.220446049250313e-16 * ax).sqrt
    if ne < 1.0 then
      let t := (if x < 0 then -((-x).floor) else x.floor)   -- `x ÷ 1`
      if JuliaBase.F64.log10 ax - JuliaBase.F64.log rem / JuliaBase.F64.log (f64! 1.7) > f64! 20.0 then .int (Int64.ofInt t.toInt64.toInt)
      else if JuliaBase.F64.log10 ax - JuliaBase.F64.log10 (f64! 1.0 - rem) > f64! 17.0 then .int (Int64.ofInt t.toInt64.toInt + 1)
      else .float x
    else .float x

/-- `makeint` lifted to exponents: identity on `Int` and `Rational`. -/
def Expo.makeint : Expo → Expo
  | .float x => match FieldAlgebra.makeint x with
    | .int n => .int n.toInt
    | .float y => .float y
  | e => e

/-- Julia `findpower(x::Int)` (`FieldAlgebra.jl:118-119`): scanning decimal
digits from the most significant, `i+1` for the first zero digit at `10^i`,
`0` when there is none. -/
def findpower (x : Nat) : Nat :=
  let ds := (toString x).toList
  go ds.reverse.length ds
where
  go : Nat → List Char → Nat
    | _, [] => 0
    | k, c :: cs => if c == '0' then k else go (k - 1) cs

/-- Julia `printexpo(io, x::Integer)`: nothing for `1`, else optional `⁻` and
superscript digits. -/
def printExpoInt (x : Int) : String :=
  if x == 1 then "" else (if x < 0 then "⁻" else "") ++ supNat x.natAbs

/-- Julia `printexpo(io, x::Rational)`: `num` in superscript, then `ᐟden` when
`den ≠ 1`. -/
def printExpoRat (x : Rat) : String :=
  if x == 1 then ""
  else (if x.num < 0 then "⁻" else "") ++ supNat x.num.natAbs ++
    (if x.den != 1 then "ᐟ" ++ supNat x.den else "")

/-- Julia `printexpo(io, x::AbstractFloat)`: the characters of `string(|x|)`
through the `chars` table. -/
def printExpoFloat (x : Float) : String :=
  if x == 1.0 then ""
  else (if x < 0 then "⁻" else "") ++ String.ofList ((JuliaBase.F64.showString x.abs).toList.map supChar)

/-- Julia `printexpo(io, x)` for any exponent kind. -/
def printExpo : Expo → String
  | .int n => printExpoInt n
  | .rat q => printExpoRat q
  | .float x => printExpoFloat x

/-- Julia `rationalize(x::Float64)` for the printing path: the simplest
fraction within `eps(x)` (continued fractions; identical to Julia's result for
the half/third/quarter exponents that occur). -/
def rationalize (x : Float) : Rat :=
  match JuliaBase.IEEEFloat.decode x with
  | none => 0
  | some (neg, m, e) =>
    let tol := JuliaBase.F64.epsOf x
    let (p, q) := if e ≥ 0 then (m <<< e.toNat, 1) else (m, 1 <<< (-e).toNat)
    let r := go p q 0 1 1 0 tol x.abs 64
    if neg then -r else r
where
  go (p q h0 k0 h1 k1 : Nat) (tol ax : Float) : Nat → Rat
    | 0 => mkRat h1 k1
    | f + 1 =>
      if q == 0 then mkRat h1 k1 else
      let a := p / q
      let h2 := a * h1 + h0
      let k2 := a * k1 + k0
      let approx := JuliaBase.IEEEFloat.ofFraction Float h2 k2
      if (approx - ax).abs ≤ tol then mkRat h2 k2
      else go q (p % q) h1 k1 h2 k2 tol ax f

/-- Julia `printexpo(io, d, x)` (`FieldAlgebra.jl:304-355`): the base `d`
followed by the superscript exponent, nothing for a zero exponent. Float
exponents go through `makeint` and the base-`10` special cases. -/
partial def printExpoBased (d : String) : Expo → String
  | .int n => if n == 0 then "" else d ++ printExpoInt n
  | .rat q => if q == 0 then "" else d ++ printExpoRat q
  | .float x =>
    if x == 0.0 then ""
    else
      let isTen := d == "10"
      let ix := makeint x
      if x.abs < 1.0 then
        match makeint (1.0 / x) with
        | .int m => printExpoBased d (.rat (Rat.divInt 1 m.toInt))
        | .float _ =>
          if isTen && (JuliaBase.F64.showString x.abs).length > 5 then
            (if x < 0 then "/" else "") ++ (makeint (powFloat10 x.abs)).toString ++
              (if x < 0 then "" else "⋅")
          else d ++ printExpoFloat x
      else if isTen then
        let pre := if x < 0 then "/" else ""
        match makeint x.abs with
        | .int mx => pre ++ printExpoBased d (.int mx.toInt)
        | .float _ =>
          match makeint (powFloat10 x.abs) with
          | .int ten =>
            let pow := findpower ten.toInt.toNat
            if pow != 0 then
              let net := ten.toInt / (10 ^ pow : Nat)
              pre ++ (if net != 1 then toString net ++ (if x < 0 then "/" else "⋅") else "") ++
                d ++ printExpoInt pow
            else if (JuliaBase.F64.showString x.abs).length > 5 then
              pre ++ toString ten.toInt ++ (if x < 0 then "" else "⋅")
            else pre ++ printExpoBased d (.rat (rationalize x))
          | .float t =>
            if (JuliaBase.F64.showString x.abs).length > 5 then
              pre ++ JuliaBase.F64.showString t ++ (if x < 0 then "" else "⋅")
            else pre ++ printExpoBased d (.rat (rationalize x))
      else match ix with
        | .int n => printExpoBased d (.int n.toInt)
        | .float _ => d ++ printExpoFloat x
where
  /-- Julia `10^x` for a `Float64` exponent (`Int^Float64`). -/
  powFloat10 (x : Float) : Float := JuliaBase.F64.pow 10.0 x

/-- The captures of Julia's regex `r"(\d+.\d+)[e](-?\d+)"` on a printed float in
scientific notation: the mantissa *without its sign* (the regex starts matching
at the first digit) and the exponent. -/
def sciParts (sf : String) : Option (String × String) :=
  match sf.splitOn "e" with
  | [m, e] => some ((if m.startsWith "-" then (m.drop 1).toString else m), e)
  | _ => none

/-- Julia `print_special(io, f::Float64)` (`FieldAlgebra.jl:419-429`): scientific
notation rendered as `m×10ⁿ`. Faithful to Julia, the sign of a negative number
in scientific notation is dropped by the regex. -/
def printSpecialFloat (f : Float) : String :=
  let sf := JuliaBase.F64.showString f
  match sciParts sf with
  | some (m, e) => m ++ "×10" ++ printExpoInt (e.toInt?.getD 0)
  | none => sf

/-- Julia `special_print(io, f::Float64)` (`FieldAlgebra.jl:234-243`): LaTeX
scientific notation `m \times 10^{n}`. -/
def specialPrintFloat (f : Float) : String :=
  let sf := JuliaBase.F64.showString f
  match sciParts sf with
  | some (m, e) => m ++ " \\times 10^{" ++ e ++ "}"
  | none => sf

/-! ### LaTeX exponents (`latexpo`, `FieldAlgebra.jl:121-190`) -/

/-- Julia `latexpo(io, x::Integer)`. -/
def latexpoInt (x : Int) : String := if x == 1 then "" else "^{" ++ toString x ++ "}"

/-- Julia `latexpo(io, x::Rational)`. -/
def latexpoRat (x : Rat) : String :=
  if x == 1 then "" else "^{" ++ toString x.num ++ (if x.den != 1 then "/" ++ toString x.den else "") ++ "}"

/-- Julia `latexpo(io, x::AbstractFloat)`. -/
def latexpoFloat (x : Float) : String := if x == 1.0 then "" else "^{" ++ JuliaBase.F64.showString x ++ "}"

/-- Julia `latexpo(io, x)`. -/
def latexpo : Expo → String
  | .int n => latexpoInt n
  | .rat q => latexpoRat q
  | .float x => latexpoFloat x

/-- Julia `latexpo(io, d, x)`: base and LaTeX exponent (Float exponents follow the
same case analysis as `printExpoBased`, with `\cdot `). -/
partial def latexpoBased (d : String) : Expo → String
  | .int n => if n == 0 then "" else d ++ latexpoInt n
  | .rat q => if q == 0 then "" else d ++ latexpoRat q
  | .float x =>
    if x == 0.0 then ""
    else
      let isTen := d == "10"
      if x.abs < 1.0 then
        match makeint (1.0 / x) with
        | .int m => latexpoBased d (.rat (Rat.divInt 1 m.toInt))
        | .float _ =>
          if isTen && (JuliaBase.F64.showString x.abs).length > 5 then
            (if x < 0 then "/" else "") ++ (makeint (JuliaBase.F64.pow 10.0 x.abs)).toString ++
              (if x < 0 then "" else "\\cdot ")
          else d ++ latexpoFloat x
      else if isTen then
        let pre := if x < 0 then "/" else ""
        match makeint x.abs with
        | .int mx => pre ++ latexpoBased d (.int mx.toInt)
        | .float _ => pre ++ latexpoBased d (.rat (rationalize x))
      else match makeint x with
        | .int n => latexpoBased d (.int n.toInt)
        | .float _ => d ++ latexpoFloat x

end FieldAlgebra
