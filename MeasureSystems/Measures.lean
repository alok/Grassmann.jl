import MeasureSystems.Measurement
import Similitude

/-!
# Measured constants

MeasureSystems re-evaluates UnitSystems and Similitude over `Group{:Measures}`
(`MeasureSystems.jl:264-309`), the same free abelian group on the same 44
generators as Similitude's constants, except that 13 generators carry
CODATA/IAU uncertainties (`R∞ α μₑᵤ μₚᵤ ΩΛ H0 au RK KJ Rᵤ2014 mP GME GMJ`).
The group algebra is exact and identical, so every unit-system constant and
conversion ratio has the same exponents as in Similitude; only its *value*
changes: `product` becomes a `Measurement` with propagated uncertainty.

The port therefore reuses Similitude's exact values (`Similitude.Scalar`) and
adds the measured evaluation (`productM`), MeasureSystems' printing
(`print_special`: `𝘩⋅𝘤⁻¹R∞⋅α⁻²2 = 9.1093837016(28) × 10⁻³¹`) and `MValue`, a
quantity value in which sums of constants are measurements.
-/

namespace MeasureSystems

open FieldConstants FieldConstants.Julia FieldAlgebra UnitSystems Similitude

/-- The measured generators (0-based basis indices) with their Julia definitions;
each independent measurement is tagged by its 1-based generator index. -/
def measuredGen : Nat → Option Measurement
  | 7 => Measurement.parse? "10973731.5681601(210)" 8
  | 8 => (Measurement.parse? "137.035999084(21)" 9).map Measurement.inv
  | 9 => (Measurement.parse? "1822.888486209(53)" 10).map Measurement.inv
  | 10 => Measurement.parse? "1.007276466621(53)" 11
  | 11 => Measurement.parse? "0.6889(56)" 12
  | 12 => Measurement.parse? "67.66(42)" 13
  | 15 => Measurement.parse? "149597870700(3)" 16
  | 24 => Measurement.parse? "25812.8074555(59)" 25
  | 25 => (Measurement.parse? "483597.8525(30)" 26).map (·.mulReal 1e9)
  | 26 => Measurement.parse? "8.3144598(48)" 27
  | 30 => Measurement.parse? "0.00000002176434(24)" 31
  | 31 => (Measurement.parse? "3.986004418(8)" 32).map (·.mulReal 1e14)
  | 32 => (Measurement.parse? "1.26686534(9)" 33).map (·.mulReal 1e17)
  | _ => none

/-- The 0-based indices of the measured generators, in basis order. -/
def measuredIdx : List Nat := [7, 8, 9, 10, 11, 12, 15, 24, 25, 26, 30, 31, 32]

/-- The measured generators' values (computed once). -/
def measuredVals : Array Measurement := measuredIdx.toArray.map fun i => (measuredGen i).getD default

/-- A value of MeasureSystems' `product`: a plain `Float64` when no measured
generator occurs, otherwise a `Measurement`. -/
inductive MNum where
  /-- exact (zero uncertainty) -/
  | float (x : Float)
  /-- with uncertainty -/
  | meas (m : Measurement)
  deriving Inhabited

namespace MNum

/-- As a measurement. -/
def toMeas : MNum → Measurement
  | float x => .ofFloat x
  | meas m => m

/-- Nominal value. -/
def val : MNum → Float
  | float x => x
  | meas m => m.val

/-- Uncertainty. -/
def err : MNum → Float
  | float _ => 0.0
  | meas m => m.err

/-- Julia `+` on products (`Float64`, or `Measurement` arithmetic). -/
def add : MNum → MNum → MNum
  | float a, float b => float (a + b)
  | float a, meas b => meas (Measurement.addReal a b)
  | meas a, float b => meas (Measurement.result1 (a.val + b) 1.0 a)
  | meas a, meas b => meas (a + b)

/-- Julia `-` on products. -/
def sub : MNum → MNum → MNum
  | float a, float b => float (a - b)
  | float a, meas b => meas (Measurement.realSub a b)
  | meas a, float b => meas (Measurement.subReal a b)
  | meas a, meas b => meas (a - b)

/-- MeasureSystems' `print_special`. -/
def printSpecial : MNum → String
  | float x => printSpecialFloat x
  | meas m => m.printSpecial

/-- MeasureSystems' `special_print` (LaTeX). -/
def specialPrint : MNum → String
  | float x => specialPrintFloat x
  | meas m => m.specialPrint

end MNum

/-- MeasureSystems' generated `product(g)` for `Group{:Measures}`
(`FieldAlgebra.jl:694-712`): the unmeasured generators in basis order times the
primes and the coefficient, all in `Float64`; then, if any measured generator
has a nonzero exponent, times the left-folded product of all 13 measured powers
in `Measurement` arithmetic. -/
def productM (g : Consts) : MNum :=
  let term (i : Fin 44) : Float := (genValues[i.1]!).pow (g.v.get i)
  let foldl1 : List Float → Float
    | [] => 1.0
    | x :: xs => xs.foldl (· * ·) x
  let nonint := ((List.finRange 44).take 37).filter (!measuredIdx.contains ·.1) |>.map term
  let ints := ((List.finRange 44).drop 37).map term
  let out := foldl1 nonint * (foldl1 ints * g.c.toFloat)
  let es := measuredIdx.filterMap fun i => if h : i < 44 then some (g.v.get ⟨i, h⟩) else none
  if es.all (·.isZero) then .float out
  else
    let pw (m : Measurement) : Expo → Measurement
      | .int n => m.powInt n
      | .rat q => m.powRat q
      | .float y => m.powFloat y
    let terms := (measuredVals.toList.zip es).map fun (m, e) => pw m e.makeint
    match terms with
    | [] => .float out
    | t :: ts => .meas (Measurement.scale out (ts.foldl (· * ·) t))

/-- A coefficient as MeasureSystems prints it (`print_special(makeint(c))`). -/
def printCoef : Coef → String
  | .float x => match makeint x with
    | .int n => toString n.toInt
    | .float y => printSpecialFloat y
  | c => c.showMakeint

/-- MeasureSystems' `showgroup` for `Group{:Measures}` (`MeasureSystems.jl:89-114`):
the monomial, the coefficient and always ` = print_special(product)`. -/
def showMeasures (g : Consts) : String :=
  let iz := g.v.allZero
  let c := g.c
  let pre := if iz && (c.isOne || c.abs.toFloat < 1.0) then "𝟏" else ""
  let coefStr :=
    if c.isOne then pre
    else if c.abs.toFloat < 1.0 then pre ++ "/" ++ printCoef c.inv
    else pre ++ (if iz then "" else "⋅") ++ printCoef c
  Group.printDims g.v constantsNames false ++ coefStr ++ " = " ++ (productM g).printSpecial

/-- A value in MeasureSystems: an exact Similitude value evaluated with
uncertainties, or a measurement produced by a sum of constants. -/
inductive MValue where
  /-- an exact value (a constants group or a plain number) -/
  | exact (s : Scalar)
  /-- a measurement -/
  | meas (m : Measurement)
  deriving Inhabited

namespace MValue

/-- The measured value (`product` for groups). -/
def toMNum : MValue → MNum
  | exact (.grp g) => productM g
  | exact s => .float s.toFloat
  | meas m => .meas m

/-- Nominal value and uncertainty. -/
def toMeas (v : MValue) : Measurement := v.toMNum.toMeas

/-- Julia `print(v)`: groups in MeasureSystems' form, measurements as `val ± err`. -/
def jprint : MValue → String
  | exact (.grp g) => showMeasures g
  | exact s => s.toString
  | meas m => m.display

/-- Arithmetic of MeasureSystems values: exact operations stay exact (the group
algebra is Similitude's); `+`/`-` of groups are evaluated (`MeasureSystems.jl:328-337`);
a measurement times a group is the measurement times the group's product
(Julia keeps it as a group with a measured coefficient). -/
def lift2 (fe : Scalar → Scalar → Scalar) (fm : Measurement → Measurement → Measurement)
    (fr : Scalar → Scalar → Bool) : MValue → MValue → MValue
  | exact a, exact b => if fr a b then .meas (fm (exact a).toMeas (exact b).toMeas) else exact (fe a b)
  | a, b => .meas (fm a.toMeas b.toMeas)

/-- Is either operand a constants group (whose sum MeasureSystems evaluates)? -/
def anyGroup : Scalar → Scalar → Bool
  | .grp _, _ => true
  | _, .grp _ => true
  | _, _ => false

instance : Add MValue := ⟨fun a b => match a, b with
  | exact a', exact b' =>
    if anyGroup a' b' then match (MNum.add (exact a').toMNum (exact b').toMNum) with
      | .float x => exact (.ofFloat x) | .meas m => meas m
    else exact (a' + b')
  | a, b => meas (a.toMeas + b.toMeas)⟩
instance : Sub MValue := ⟨fun a b => match a, b with
  | exact a', exact b' =>
    if anyGroup a' b' then match (MNum.sub (exact a').toMNum (exact b').toMNum) with
      | .float x => exact (.ofFloat x) | .meas m => meas m
    else exact (a' - b')
  | a, b => meas (a.toMeas - b.toMeas)⟩
instance : Mul MValue := ⟨lift2 (· * ·) (· * ·) fun _ _ => false⟩
instance : Div MValue := ⟨lift2 (· / ·) (· / ·) fun _ _ => false⟩
instance : Neg MValue := ⟨fun | exact s => exact (-s) | meas m => meas (-m)⟩
instance : Inv MValue := ⟨fun | exact s => exact s⁻¹ | meas m => meas m.inv⟩

end MValue

instance : QScalar MValue where
  npow v n := match v with
    | .exact s => .exact (QScalar.npow s n)
    | .meas m => .meas (m.powInt n)
  sqrt v := match v with
    | .exact s => .exact s.sqrt
    | .meas m => .meas m.sqrt
  cbrt v := match v with
    | .exact s => .exact s.cbrt
    | .meas m => .meas m.cbrt
  ofRatio s := .exact s
  jprint := MValue.jprint

/-- A Similitude quantity viewed in MeasureSystems (same exact value, measured
evaluation). -/
def measured {U : Sys} {d : Dim} (q : Q U d) : Quantity U d MValue := ⟨.exact q.val⟩

/-- MeasureSystems' `show(io, ::ConvertUnit)`: as Similitude's, with the ratio
printed with uncertainty. -/
def showConvertM (d : Exps 11) (U S : Sys) : String :=
  let cr := constRatios U.consts S.consts
  let d' := convertDim cr d
  let r := ratioOf cr (usqMap.apply d)
  s!"{(MValue.exact r).jprint} [{S.showDim d'}]/[{U.showDim d'}] {U.name} -> {S.name}"

end MeasureSystems
