import FieldAlgebra

/-!
# Measurements with linear error propagation

A port of the parts of Measurements.jl (v2, `src/Measurements.jl`, `math.jl`,
`parsing.jl`, `show.jl`) that MeasureSystems uses. A `Measurement` carries its
nominal value, its standard uncertainty and the partial derivatives with
respect to every *independent* measurement it was computed from, so the
uncertainty of a result is propagated linearly **with correlations**:

  `σ_G = sqrt(Σₓ (σₓ · ∂G/∂x)²)` over the independent variables `x`,

hence `x - x = 0 ± 0` and `x/x = 1 ± 0`. Operations are Julia's, in Julia's
order (the derivative list is Julia's immutable linked list, newest first), so
values and uncertainties agree bit for bit.

Julia tags independent measurements from a global counter; here a tag is
supplied by the caller (`Measurement.indep`). MeasureSystems gives each measured
constant a fixed tag, so two products that share a constant are correlated;
Julia creates fresh tags on every evaluation, which makes them independent
(`R∞ - R∞` is `0 ± 3.0e-5` in Julia and `0 ± 0` here).
-/

namespace MeasureSystems

open FieldConstants FieldConstants.Julia

/-- The identity of an independent measurement: `(value, uncertainty, tag)`. -/
abbrev MTag := Float × Float × Nat

/-- Julia `isequal` on tags: bitwise-equal floats (NaNs equal) and equal tags. -/
@[inline] def MTag.same (a b : MTag) : Bool :=
  a.2.2 == b.2.2 && (a.1 == b.1 || (a.1.isNaN && b.1.isNaN)) &&
    (a.2.1 == b.2.1 || (a.2.1.isNaN && b.2.1.isNaN))

/-- Julia `Measurement{Float64}`. -/
structure Measurement where
  /-- nominal value -/
  val : Float
  /-- standard uncertainty -/
  err : Float
  /-- tag of an independent measurement, `0` for derived ones -/
  tag : Nat := 0
  /-- `∂self/∂x` for each independent `x` (newest first, as Julia's `Derivatives`) -/
  der : List (MTag × Float) := []
  deriving Inhabited

namespace Measurement

/-- An exact number (`measurement(x)`, zero uncertainty, no derivatives). -/
@[inline] def ofFloat (x : Float) : Measurement := ⟨x, 0.0, 0, []⟩

/-- Julia `measurement(val, err)` with an explicit tag `id > 0` for the new
independent variable (a zero uncertainty gives an exact number). -/
def indep (val err : Float) (id : Nat) : Measurement :=
  if err == 0.0 then ⟨val, err, 0, []⟩ else ⟨val, err, id, [((val, err, id), 1.0)]⟩

/-- `get(x.der, tag, 0)`. -/
def derivative (x : Measurement) (t : MTag) : Float :=
  match x.der.find? (·.1.same t) with
  | some (_, d) => d
  | none => 0.0

/-- Julia's one-argument `result(val, der, a)` (`math.jl:41-54`). -/
def result1 (val der : Float) (a : Measurement) : Measurement :=
  let newder := a.der.foldl (fun acc (t, d) => if t.2.1 == 0.0 then acc else (t, der * d) :: acc) []
  let σ := if a.err == 0.0 then a.err else (der * a.err).abs
  ⟨val, σ, 0, newder⟩

/-- Julia's many-argument `result(val, ders, args)` (`math.jl:80-118`): the
derivative of the result with respect to each independent variable, and the
uncertainty `sqrt(Σ (σₓ·∂G/∂x)²)` summed in Julia's order. -/
def resultN (val : Float) (ders : List Float) (args : List Measurement) : Measurement := Id.run do
  let mut err := 0.0
  let mut newder : List (MTag × Float) := []
  for y in args do
    for (t, _) in y.der do
      if newder.any (·.1.same t) then continue
      let σx := t.2.1
      if σx == 0.0 then continue
      let mut dG := 0.0
      for (d, x) in ders.zip args do
        let dax := x.derivative t
        if dax != 0.0 then dG := dG + d * dax
      if dG != 0.0 then
        newder := (t, dG) :: newder
        let e := σx * dG
        err := err + e * e
  return ⟨val, err.sqrt, 0, newder⟩

/-- `a + b` -/
def add (a b : Measurement) : Measurement := resultN (a.val + b.val) [1.0, 1.0] [a, b]
/-- `a - b` -/
def sub (a b : Measurement) : Measurement := resultN (a.val - b.val) [1.0, -1.0] [a, b]
/-- `a * b` -/
def mul (a b : Measurement) : Measurement := resultN (a.val * b.val) [b.val, a.val] [a, b]
/-- `a / b` -/
def div (a b : Measurement) : Measurement :=
  let oneovery := 1.0 / b.val
  resultN (a.val / b.val) [oneovery, -a.val * (oneovery * oneovery)] [a, b]
/-- `-a` -/
def neg (a : Measurement) : Measurement := result1 (-a.val) (-1.0) a
/-- `inv(a)` -/
def inv (a : Measurement) : Measurement := let i := 1.0 / a.val; result1 i (-(i * i)) a
/-- `x + a` for a plain number -/
def addReal (x : Float) (a : Measurement) : Measurement := result1 (x + a.val) 1.0 a
/-- `a - x` for a plain number -/
def subReal (a : Measurement) (x : Float) : Measurement := result1 (a.val - x) 1.0 a
/-- `x - a` for a plain number -/
def realSub (x : Float) (a : Measurement) : Measurement := result1 (x - a.val) (-1.0) a
/-- `x * a` for a plain number -/
def scale (x : Float) (a : Measurement) : Measurement := result1 (x * a.val) x a
/-- `a * x` for a plain number -/
def mulReal (a : Measurement) (x : Float) : Measurement := result1 (a.val * x) x a
/-- `a / x` for a plain number -/
def divReal (a : Measurement) (x : Float) : Measurement := result1 (a.val / x) (1.0 / x) a
/-- `x / a` for a plain number -/
def realDiv (x : Float) (a : Measurement) : Measurement :=
  result1 (x / a.val) (-x / (a.val * a.val)) a
/-- `a^n` for an integer (`math.jl:287`). -/
def powInt (a : Measurement) (n : Int) : Measurement :=
  result1 (Julia.powInt a.val n) (Float.ofInt n * Julia.powInt a.val (n - 1)) a
/-- `a^r` for a `Rational` (`math.jl:292`). -/
def powRat (a : Measurement) (r : Rat) : Measurement :=
  let b := FieldAlgebra.Coef.toFloat (.rat r)
  result1 (Julia.pow a.val b) (b * Julia.pow a.val (b - 1.0)) a
/-- `a^y` for a `Float64` (`math.jl:297`). -/
def powFloat (a : Measurement) (y : Float) : Measurement :=
  result1 (Julia.pow a.val y) (y * Julia.pow a.val (y - 1.0)) a
/-- `sqrt(a)` -/
def sqrt (a : Measurement) : Measurement := let v := a.val.sqrt; result1 v (1.0 / (2.0 * v)) a
/-- `cbrt(a)` -/
def cbrt (a : Measurement) : Measurement :=
  let v := JuliaBase.F64.cbrt a.val; result1 v (v / (3.0 * a.val)) a

instance : Add Measurement := ⟨add⟩
instance : Sub Measurement := ⟨sub⟩
instance : Mul Measurement := ⟨mul⟩
instance : Div Measurement := ⟨div⟩
instance : Neg Measurement := ⟨neg⟩

/-! ### Parsing (`parsing.jl`) -/

/-- `[+-]?digits(.digits)?`: returns (text, decimal part including the point). -/
private def numPart (s : String) : Option (String × Option String) :=
  let (sgn, body) := if s.startsWith "-" || s.startsWith "+" then ((s.take 1).toString, (s.drop 1).toString) else ("", s)
  match body.splitOn "." with
  | [i] => if !i.isEmpty && i.all Char.isDigit then some (sgn ++ i, none) else none
  | [i, f] =>
    if !i.isEmpty && i.all Char.isDigit && !f.isEmpty && f.all Char.isDigit then
      some (sgn ++ i ++ "." ++ f, some ("." ++ f))
    else none
  | _ => none

/-- Julia `measurement("v(e)[eN]")` for the parenthesised form (and a bare
number), with the uncertainty on the last digits of the value; tagged `id`. -/
def parse? (str : String) (id : Nat) : Option Measurement := do
  let s := str.trimAscii.toString
  match s.splitOn "(" with
  | [v, rest] =>
    let (errTxt, tail) ← match rest.splitOn ")" with
      | [e, t] => some (e, t)
      | _ => none
    let (valStr, valDec) ← numPart v
    let (errStr, errDec) ← numPart errTxt
    let mut val ← parseFloat? valStr
    let mut err ← parseFloat? errStr
    if valDec.isSome && errDec.isNone then
      err := err / Julia.exp10 (Float.ofNat (valDec.get!.length - 1))
    if !tail.isEmpty then
      let fact ← parseFloat? ("1" ++ tail)
      val := val * fact
      err := err * fact
    return indep val err id
  | [v] => let x ← parseFloat? v; return indep x 0.0 id
  | _ => none

/-! ### Display -/

/-- Julia `show(io, m)` (`show.jl:19-45`, two error digits): `val ± err`. -/
def display (m : Measurement) : String :=
  let val :=
    if m.err == 0.0 || !m.err.isFinite then m.val
    else
      let errDigits := -hidigit m.err + 2
      let digits := if m.val.isFinite then max (-hidigit m.val + 2) errDigits else errDigits
      roundDigits m.val digits
  s!"{JuliaBase.F64.showString val} ± {JuliaBase.F64.showString (roundSigdigits m.err 2)}"

instance : ToString Measurement := ⟨display⟩

/-- MeasureSystems' `round_extra(x)` (`MeasureSystems.jl:76-87`): the neighbour
of `x` with a strictly shorter printed form, if any. -/
def roundExtra (x : Float) : Float :=
  let len (y : Float) := (JuliaBase.F64.showString y).length
  let (l, lp, ln) := (len x, len (JuliaBase.F64.prevfloat x), len (JuliaBase.F64.nextfloat x))
  if ln < l && ln < lp then JuliaBase.F64.nextfloat x
  else if lp < l && lp < ln then JuliaBase.F64.prevfloat x
  else x

/-- The captures of Julia's `r"(\d+.\d+)[e](-?\d+)"` on a printed float:
mantissa digits (without a sign) and the exponent (`FieldAlgebra.sciParts`). -/
private def sciParts (s : String) : String × String := (FieldAlgebra.sciParts s).getD (s, "0")

/-- The two error digits MeasureSystems prints (`ms` is the rounded error's
digits without the point). `sci` selects the scientific branch's quirk. -/
private def errDigitsStr (ms : String) (sci : Bool) : String :=
  let cs := ms.toList
  let n := cs.length
  if cs.headD '0' != '0' then String.ofList (cs.take 2)
  else if cs.getD (n - 2) '0' != '0' then String.ofList (cs.drop (n - 2))
  else if sci then String.ofList [cs.getD (n - 1) '0'] else String.ofList [cs.getD (n - 1) '0', '0']

/-- Length of the first match of `r"0\.0*"` in `s`, if any. -/
private def zeroPointLen? (s : String) : Option Nat :=
  let cs := s.toList
  let rec go : List Char → Option Nat
    | '0' :: '.' :: rest => some (2 + (rest.takeWhile (· == '0')).length)
    | _ :: rest => go rest
    | [] => none
  go cs

/-- Shared rounding of `print_special`/`special_print`: `(digits, val, err)`. -/
private def specialRound (m : Measurement) : Int × Float × Float :=
  let errDigits := -hidigit m.err + 2
  let digits := if m.val.isFinite then max (-hidigit m.val + 2) errDigits else errDigits
  let val := if m.err == 0.0 || !m.err.isFinite then m.val else roundExtra (roundDigits m.val digits)
  let err := roundExtra (roundSigdigits m.err 2)
  (digits, val, err)

/-- MeasureSystems' `print_special(io, M)` (`MeasureSystems.jl:153-189`): the
concise form `1.0973731568160(21) × 10⁷`, including its quirks (the
`r"0\.0*"` term pads values such as `500.0` with an extra zero). -/
def printSpecial (m : Measurement) : String :=
  if m.val.isInf then "Inf" else
  let (digits, val, err) := specialRound m
  let sval := JuliaBase.F64.showString val
  let neg : Int := if m.val < 0 then 1 else 0
  if sval.contains 'e' then
    let serr := JuliaBase.F64.showString err
    let serr := if serr.contains 'e' then (sciParts serr).1 else serr
    let (m1, m2) := sciParts sval
    let ms := serr.replace "." ""
    let zs := digits + 1 + hidigit m.val + neg - m1.length
    let z := String.ofList (List.replicate zs.toNat '0')
    m1 ++ z ++ "(" ++ errDigitsStr ms true ++ ") × 10" ++ FieldAlgebra.printExpoInt (m2.toInt?.getD 0)
  else
    let zs := digits + 1 + hidigit m.val + neg - sval.length +
      (match zeroPointLen? sval with | some k => (k : Int) - 1 | none => 0)
    if zs < 0 && sval.endsWith ".0" then
      sval ++ "(±" ++ FieldAlgebra.printSpecialFloat err ++ ")"
    else
      let ms := (JuliaBase.F64.showString err).replace "." ""
      sval ++ String.ofList (List.replicate zs.toNat '0') ++ "(" ++ errDigitsStr ms false ++ ")"

/-- MeasureSystems' `special_print(io, M)` (`MeasureSystems.jl:117-152`): the
LaTeX form `1.0973731568160(21) \times 10^{7}`. -/
def specialPrint (m : Measurement) : String :=
  if m.val.isInf then "\\infty " else
  let (digits, val, err) := specialRound m
  let sval := JuliaBase.F64.showString val
  let neg : Int := if m.val < 0 then 1 else 0
  if sval.contains 'e' then
    let serr := JuliaBase.F64.showString err
    let serr := if serr.contains 'e' then (sciParts serr).1 else serr
    let (m1, m2) := sciParts sval
    let ms := serr.replace "." ""
    let zs := digits + 1 + hidigit m.val + neg - m1.length
    let z := String.ofList (List.replicate zs.toNat '0')
    m1 ++ z ++ "(" ++ errDigitsStr ms false ++ ") \\times 10^{" ++ m2 ++ "}"
  else
    let zs := digits + 1 + hidigit m.val + neg - sval.length +
      (match zeroPointLen? sval with | some k => (k : Int) - 1 | none => 0)
    if zs < 0 && sval.endsWith ".0" then
      sval ++ " (\\pm " ++ FieldAlgebra.specialPrintFloat err ++ ")"
    else
      let ms := (JuliaBase.F64.showString err).replace "." ""
      sval ++ String.ofList (List.replicate zs.toNat '0') ++ "(" ++ errDigitsStr ms false ++ ")"

end Measurement

end MeasureSystems
