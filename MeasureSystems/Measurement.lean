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

open FieldConstants

/-- The identity of an independent measurement: `(value, uncertainty, tag)` (a
structure with unboxed floats). -/
structure MTag where
  /-- nominal value of the independent measurement -/
  val : Float
  /-- its uncertainty -/
  err : Float
  /-- its tag -/
  tag : Nat
  deriving Inhabited

/-- Julia `isequal` on tags: bitwise-equal floats (NaNs equal) and equal tags. -/
@[inline] def MTag.same (a b : MTag) : Bool :=
  a.tag == b.tag && (a.val == b.val || (JuliaBase.F64.isnan a.val && JuliaBase.F64.isnan b.val)) &&
    (a.err == b.err || (JuliaBase.F64.isnan a.err && JuliaBase.F64.isnan b.err))

/-- Partial derivatives with respect to independent measurements, newest first
(Julia's `Derivatives` linked list); each entry keeps its derivative unboxed. -/
inductive Ders where
  /-- no derivatives -/
  | nil
  /-- `∂/∂t = d`, then the older entries -/
  | cons (t : MTag) (d : Float) (rest : Ders)
  deriving Inhabited

namespace Ders

/-- `get(ders, t, 0)`. -/
def get (t : MTag) : Ders → Float
  | nil => 0.0
  | cons u d r => if u.same t then d else get t r

/-- Does `t` occur? -/
def contains (t : MTag) : Ders → Bool
  | nil => false
  | cons u _ r => u.same t || contains t r

/-- The entries as a list, newest first. -/
def toList : Ders → List (MTag × Float)
  | nil => []
  | cons t d r => (t, d) :: r.toList

end Ders

/-- Julia `Measurement{Float64}`. -/
structure Measurement where
  /-- nominal value -/
  val : Float
  /-- standard uncertainty -/
  err : Float
  /-- tag of an independent measurement, `0` for derived ones -/
  tag : Nat := 0
  /-- `∂self/∂x` for each independent `x` (newest first, as Julia's `Derivatives`) -/
  der : Ders := .nil
  deriving Inhabited

namespace Measurement

/-- An exact number (`measurement(x)`, zero uncertainty, no derivatives). -/
@[inline] def ofFloat (x : Float) : Measurement := ⟨x, 0.0, 0, .nil⟩

/-- Julia `measurement(val, err)` with an explicit tag `id > 0` for the new
independent variable (a zero uncertainty gives an exact number). -/
def indep (val err : Float) (id : Nat) : Measurement :=
  if err == 0.0 then ⟨val, err, 0, .nil⟩ else ⟨val, err, id, .cons ⟨val, err, id⟩ 1.0 .nil⟩

/-- `get(x.der, tag, 0)`. -/
@[inline] def derivative (x : Measurement) (t : MTag) : Float := x.der.get t

/-- The largest tag this measurement depends on (`0` for an exact number). -/
def maxTag (x : Measurement) : Nat := go x.der x.tag
where
  /-- Fold over the derivative list. -/
  go : Ders → Nat → Nat
    | .nil, m => m
    | .cons t _ r, m => go r (max m t.tag)

/-- The same measurement with every independent tag shifted by `off`: a fresh copy
of the independent measurements it depends on (Julia creates new tags each time a
literal `measurement("…")` is evaluated). -/
def shiftTags (x : Measurement) (off : Nat) : Measurement :=
  ⟨x.val, x.err, if x.tag == 0 then 0 else x.tag + off, go x.der⟩
where
  /-- Shift the derivative list. -/
  go : Ders → Ders
    | .nil => .nil
    | .cons t d r => .cons { t with tag := t.tag + off } d (go r)

/-- The derivative list of `result1`: `der·d` for every entry with a nonzero
uncertainty, in reverse order (Julia's fold into a fresh list). -/
def scaleDers (der : Float) : Ders → Ders → Ders
  | .nil, acc => acc
  | .cons t d r, acc => scaleDers der r (if t.err == 0.0 then acc else .cons t (der * d) acc)

/-- Julia's one-argument `result(val, der, a)` (`math.jl:41-54`). -/
def result1 (val der : Float) (a : Measurement) : Measurement :=
  let σ := if a.err == 0.0 then a.err else (der * a.err).abs
  ⟨val, σ, 0, scaleDers der a.der .nil⟩

/-- Julia's many-argument `result(val, ders, args)` (`math.jl:80-118`): the
derivative of the result with respect to each independent variable, and the
uncertainty `sqrt(Σ (σₓ·∂G/∂x)²)` summed in Julia's order. -/
def resultN (val : Float) (ders : List Float) (args : List Measurement) : Measurement :=
  -- `∂G/∂x = Σᵢ ∂G/∂aᵢ · ∂aᵢ/∂x`, skipping zero partials, in argument order
  let dGdx (t : MTag) : Float :=
    (ders.zip args).foldl (fun acc (d, x) => let dax := x.derivative t; if dax != 0.0 then acc + d * dax else acc) 0.0
  let step (acc : Float × Ders) (t : MTag) : Float × Ders :=
    let (err, newder) := acc
    if newder.contains t || t.err == 0.0 then acc
    else
      let dG := dGdx t
      if dG == 0.0 then acc
      else let e := t.err * dG; (err + e * e, .cons t dG newder)
  let (err, newder) := args.foldl (fun acc y => y.der.toList.foldl (fun acc (t, _) => step acc t) acc) (0.0, .nil)
  ⟨val, err.sqrt, 0, newder⟩

/-- The walk of `result2` over `a`'s derivative list and then `rest` (`b`'s):
`err` and `newder` accumulate as in `resultN`. -/
partial def walk2 (val da db : Float) (a b : Measurement) : Ders → Ders → Float → Ders → Measurement
  | .nil, .nil, err, newder => ⟨val, err.sqrt, 0, newder⟩
  | .nil, rest, err, newder => walk2 val da db a b rest .nil err newder
  | .cons t _ r, rest, err, newder =>
    if newder.contains t || t.err == 0.0 then walk2 val da db a b r rest err newder
    else
      let x := a.derivative t
      let acc := if x != 0.0 then 0.0 + da * x else 0.0
      let y := b.derivative t
      let dG := if y != 0.0 then acc + db * y else acc
      if dG == 0.0 then walk2 val da db a b r rest err newder
      else let e := t.err * dG; walk2 val da db a b r rest (err + e * e) (.cons t dG newder)

/-- `resultN val [da, db] [a, b]`, without the argument lists (the same operations
in the same order, so the same bits). -/
@[inline] def result2 (val da db : Float) (a b : Measurement) : Measurement :=
  walk2 val da db a b a.der b.der 0.0 .nil

/-- `a + b` -/
def add (a b : Measurement) : Measurement := result2 (a.val + b.val) 1.0 1.0 a b
/-- `a - b` -/
def sub (a b : Measurement) : Measurement := result2 (a.val - b.val) 1.0 (-1.0) a b
/-- `a * b` -/
def mul (a b : Measurement) : Measurement := result2 (a.val * b.val) b.val a.val a b
/-- `a / b` -/
def div (a b : Measurement) : Measurement :=
  let oneovery := 1.0 / b.val
  result2 (a.val / b.val) oneovery (-a.val * (oneovery * oneovery)) a b
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
  result1 (JuliaBase.F64.powInt a.val n) (Float.ofInt n * JuliaBase.F64.powInt a.val (n - 1)) a
/-- `a^r` for a `Rational` (`math.jl:292`). -/
def powRat (a : Measurement) (r : Rat) : Measurement :=
  let b := FieldAlgebra.Coef.toFloat (.rat r)
  result1 (JuliaBase.F64.pow a.val b) (b * JuliaBase.F64.pow a.val (b - 1.0)) a
/-- `a^y` for a `Float64` (`math.jl:297`). -/
def powFloat (a : Measurement) (y : Float) : Measurement :=
  result1 (JuliaBase.F64.pow a.val y) (y * JuliaBase.F64.pow a.val (y - 1.0)) a
/-- `log(a)` (`math.jl`: `result(log(a.val), inv(a.val), a)`). -/
def log (a : Measurement) : Measurement := result1 (JuliaBase.F64.log a.val) (1.0 / a.val) a
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
    let mut val ← JuliaBase.F64.parse? valStr
    let mut err ← JuliaBase.F64.parse? errStr
    if valDec.isSome && errDec.isNone then
      err := err / JuliaBase.F64.exp10 (Float.ofNat (valDec.get!.length - 1))
    if !tail.isEmpty then
      let fact ← JuliaBase.F64.parse? ("1" ++ tail)
      val := val * fact
      err := err * fact
    return indep val err id
  | [v] => let x ← JuliaBase.F64.parse? v; return indep x 0.0 id
  | _ => none

/-! ### Display -/

/-- Julia `show(io, m)` (`show.jl:19-45`, two error digits): `val ± err`. -/
def display (m : Measurement) : String :=
  let val :=
    if m.err == 0.0 || !m.err.isFinite then m.val
    else
      let errDigits := -JuliaBase.F64.hidigit m.err + 2
      let digits := if m.val.isFinite then max (-JuliaBase.F64.hidigit m.val + 2) errDigits else errDigits
      JuliaBase.F64.roundDigits m.val digits
  s!"{JuliaBase.F64.showString val} ± {JuliaBase.F64.showString (JuliaBase.F64.roundSigdigits m.err 2)}"

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
  let errDigits := -JuliaBase.F64.hidigit m.err + 2
  let digits := if m.val.isFinite then max (-JuliaBase.F64.hidigit m.val + 2) errDigits else errDigits
  let val := if m.err == 0.0 || !m.err.isFinite then m.val else roundExtra (JuliaBase.F64.roundDigits m.val digits)
  let err := roundExtra (JuliaBase.F64.roundSigdigits m.err 2)
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
    let zs := digits + 1 + JuliaBase.F64.hidigit m.val + neg - m1.length
    let z := String.ofList (List.replicate zs.toNat '0')
    m1 ++ z ++ "(" ++ errDigitsStr ms true ++ ") × 10" ++ FieldAlgebra.printExpoInt (m2.toInt?.getD 0)
  else
    let zs := digits + 1 + JuliaBase.F64.hidigit m.val + neg - sval.length +
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
    let zs := digits + 1 + JuliaBase.F64.hidigit m.val + neg - m1.length
    let z := String.ofList (List.replicate zs.toNat '0')
    m1 ++ z ++ "(" ++ errDigitsStr ms false ++ ") \\times 10^{" ++ m2 ++ "}"
  else
    let zs := digits + 1 + JuliaBase.F64.hidigit m.val + neg - sval.length +
      (match zeroPointLen? sval with | some k => (k : Int) - 1 | none => 0)
    if zs < 0 && sval.endsWith ".0" then
      sval ++ " (\\pm " ++ FieldAlgebra.specialPrintFloat err ++ ")"
    else
      let ms := (JuliaBase.F64.showString err).replace "." ""
      sval ++ String.ofList (List.replicate zs.toNat '0') ++ "(" ++ errDigitsStr ms false ++ ")"

end Measurement

end MeasureSystems
