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

open FieldConstants FieldAlgebra UnitSystems Similitude

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

/-- `productM` of the exponents of `g` with coefficient `c` when `c` is a
`Measurement` (Julia's `Group{:Measures}` with a `Measure` coefficient, whose
`measure(g.c)` enters the integer factor: `nonint * (ints * c)` in
`Measurement` arithmetic, then times the measured generators). -/
def productMWith (g : Consts) (cM : Option Measurement) (salt : Nat := 0) : MNum :=
  let all := g.v.toExpos
  let term (i : Nat) : Float := (genValues[i]!).pow (all[i]!)
  let foldl1 : List Float → Float
    | [] => 1.0
    | x :: xs => xs.foldl (· * ·) x
  let nonint := ((List.range 37).filter (!measuredIdx.contains ·)).map term
  let ints := (List.range' 37 7).map term
  let es := measuredIdx.map fun i => all[i]!
  let pw (m : Measurement) : Expo → Measurement
    | .int n => m.powInt n
    | .rat q => m.powRat q
    | .float y => m.powFloat y
  let measured : Option Measurement :=
    if es.all (·.isZero) then none
    else
      let vals := if salt == 0 then measuredVals else measuredVals.map (·.shiftTags (64 * salt))
      match (vals.toList.zip es).map fun (m, e) => pw m e.makeint with
        | [] => none
        | t :: ts => some (ts.foldl (· * ·) t)
  match cM with
  | none =>
    let out := foldl1 nonint * (foldl1 ints * g.c.toFloat)
    match measured with
    | none => .float out
    | some m => .meas (Measurement.scale out m)
  | some c =>
    let out := Measurement.scale (foldl1 nonint) (Measurement.scale (foldl1 ints) c)
    match measured with
    | none => .meas out
    | some m => .meas (out * m)

/-- MeasureSystems' generated `product(g)` for `Group{:Measures}`
(`FieldAlgebra.jl:694-712`): the unmeasured generators in basis order times the
primes and the coefficient, all in `Float64`; then, if any measured generator
has a nonzero exponent, times the left-folded product of all 13 measured powers
in `Measurement` arithmetic. -/
def productM (g : Consts) : MNum := productMWith g none

/-- A tag salt above every tag `≤ above`: products evaluated with it use fresh
copies of the measured generators. Julia's generated `product` evaluates the
literal `measurement("…")` of every measured generator on each call, so two
products are *independent*; the port reuses one tag per generator (products of
one expression are correlated) and salts the products that meet a measurement
in the same operation (sums, a group with a measured coefficient). -/
def freshSalt (above : Nat) : Nat := if above == 0 then 0 else above / 64 + 1

/-- The largest tag of a product's value. -/
def MNum.maxTag : MNum → Nat
  | .float _ => 0
  | .meas m => m.maxTag

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

/-- MeasureSystems' `showgroup` of a group whose coefficient is a measurement
(`MeasureSystems.jl:89-114` with `measure(xc)` a `Measurement`): `/print_special(inv(c))`
for a coefficient below one, `⋅print_special(c)` otherwise. -/
def showMeasuresM (g : Consts) (c : Measurement) : String :=
  let iz := g.v.allZero
  let one := c.val == 1.0 && c.err == 0.0
  let pre := if iz && (one || c.val.abs < 1.0) then "𝟏" else ""
  let coefStr :=
    if one then pre
    else if c.val.abs < 1.0 then pre ++ "/" ++ c.inv.printSpecial
    else pre ++ (if iz then "" else "⋅") ++ c.printSpecial
  Group.printDims g.v constantsNames false ++ coefStr ++ " = " ++ (productMWith g (some c)).printSpecial

/-- A value in MeasureSystems: an exact Similitude value evaluated with
uncertainties, a measurement produced by a sum of constants, or a constants
group whose coefficient is a measurement (Julia's `Group{:Measures}` with a
`Measure` coefficient: `earthmass/μE☾`, a group times a sum). -/
inductive MValue where
  /-- an exact value (a constants group or a plain number) -/
  | exact (s : Scalar)
  /-- a measurement -/
  | meas (m : Measurement)
  /-- the exponents of `g` (its coefficient is ignored) with the measured coefficient `c` -/
  | grpM (g : Consts) (c : Measurement)
  deriving Inhabited

namespace MValue

/-- The largest tag of a value's own measurements (`0` for exact values). -/
def ownTag : MValue → Nat
  | exact _ => 0
  | meas m => m.maxTag
  | grpM _ c => c.maxTag

/-- The measured value with the products' generators fresh above tag `above`. -/
def evalAbove (v : MValue) (above : Nat) : MNum :=
  match v with
  | exact (.grp g) => productMWith g none (freshSalt above)
  | exact s => .float s.toFloat
  | meas m => .meas m
  | grpM g c => productMWith g (some c) (freshSalt (max above c.maxTag))

/-- The measured value (`product` for groups; a group with a measured coefficient
evaluates its generators fresh, independent of the coefficient). -/
def toMNum (v : MValue) : MNum := v.evalAbove 0

/-- Evaluate two operands independently (Julia's fresh generator tags per product):
first the measurements they carry, then each product above all tags seen. -/
def evalPair (a b : MValue) : MNum × MNum :=
  let t := max a.ownTag b.ownTag
  let ma := a.evalAbove t
  let mb := b.evalAbove (max t ma.maxTag)
  (ma, mb)

/-- Nominal value and uncertainty. -/
def toMeas (v : MValue) : Measurement := v.toMNum.toMeas

/-- Julia `print(v)`: groups in MeasureSystems' form, measurements as `val ± err`. -/
def jprint : MValue → String
  | exact (.grp g) => showMeasures g
  | exact s => s.toString
  | meas m => m.display
  | grpM g c => showMeasuresM g c

/-- Arithmetic of MeasureSystems values: exact operations stay exact (the group
algebra is Similitude's); `+`/`-` of groups are evaluated (`MeasureSystems.jl:328-337`). -/
def lift2 (fe : Scalar → Scalar → Scalar) (fm : Measurement → Measurement → Measurement)
    (fr : Scalar → Scalar → Bool) : MValue → MValue → MValue
  | exact a, exact b =>
    if fr a b then let (x, y) := evalPair (exact a) (exact b); .meas (fm x.toMeas y.toMeas)
    else exact (fe a b)
  | a, b => let (x, y) := evalPair a b; .meas (fm x.toMeas y.toMeas)

/-- A group coefficient as a measurement factor (`Float64(c)`; exact). -/
def coefF (g : Consts) : Float := g.c.toFloat

/-- Julia's products involving measurements and groups (`MeasureSystems.jl:316-339`,
`FieldAlgebra.jl:603-616`): a group times a measurement keeps the group and
multiplies the coefficient (`times(g, m) = Group(g.v, coef(g)*m)`), so the result
prints as `monomial⋅coefficient = value`; plain numbers factorize into the group. -/
def mul : MValue → MValue → MValue
  | exact a, exact b => exact (a * b)
  | exact (.grp g), meas m => grpM g (Measurement.scale (coefF g) m)
  | meas m, exact (.grp g) => grpM g (m.mulReal (coefF g))
  | exact (.grp g), grpM h c => grpM (g * h) (Measurement.scale (coefF g) c)
  | grpM h c, exact (.grp g) => grpM (h * g) (c.mulReal (coefF g))
  | exact x, grpM h c => let f := x.factor; grpM (f * h) (Measurement.scale (coefF f) c)
  | grpM h c, exact x => let f := x.factor; grpM (h * f) (c.mulReal (coefF f))
  | grpM g c, grpM h d => grpM (g * h) (c * d)
  | grpM g c, meas m => grpM g (c * m)
  | meas m, grpM g c => grpM g (m * c)
  | a, b => let (x, y) := evalPair a b; meas (x.toMeas * y.toMeas)

/-- `inv` (`inv(g)` of a group with a measured coefficient inverts both). -/
def inv : MValue → MValue
  | exact s => exact s⁻¹
  | meas m => meas m.inv
  | grpM g c => grpM g⁻¹ c.inv

/-- Julia `/` (`a*inv(b)` whenever a measurement is involved). -/
def div : MValue → MValue → MValue
  | exact a, exact b => exact (a / b)
  | a, b => mul a b.inv

/-- Is either operand a constants group (whose sum MeasureSystems evaluates)? -/
def anyGroup : Scalar → Scalar → Bool
  | .grp _, _ => true
  | _, .grp _ => true
  | _, _ => false

instance : Add MValue := ⟨fun a b => match a, b with
  | exact a', exact b' =>
    if anyGroup a' b' then
      let (x, y) := evalPair (exact a') (exact b')
      match MNum.add x y with
      | .float x => exact (.ofFloat x) | .meas m => meas m
    else exact (a' + b')
  | a, b => let (x, y) := evalPair a b; meas (x.toMeas + y.toMeas)⟩
instance : Sub MValue := ⟨fun a b => match a, b with
  | exact a', exact b' =>
    if anyGroup a' b' then
      let (x, y) := evalPair (exact a') (exact b')
      match MNum.sub x y with
      | .float x => exact (.ofFloat x) | .meas m => meas m
    else exact (a' - b')
  | a, b => let (x, y) := evalPair a b; meas (x.toMeas - y.toMeas)⟩
instance : Mul MValue := ⟨mul⟩
instance : Div MValue := ⟨div⟩
instance : Neg MValue := ⟨fun | exact s => exact (-s) | meas m => meas (-m) | grpM g c => grpM g (-c)⟩
instance : Inv MValue := ⟨inv⟩

end MValue

instance : QScalar MValue where
  npow v n := match v with
    | .exact s => .exact (QScalar.npow s n)
    | .meas m => .meas (m.powInt n)
    | .grpM g c => .grpM (g ^ (n : Int)) (c.powInt n)
  sqrt v := match v with
    | .exact s => .exact s.sqrt
    | .meas m => .meas m.sqrt
    | .grpM g c => .grpM g.sqrt c.sqrt
  cbrt v := match v with
    | .exact s => .exact s.cbrt
    | .meas m => .meas m.cbrt
    | .grpM g c => .grpM g.cbrt c.cbrt
  rpow v r := match v with
    | .exact s => .exact (s.qpow r)
    | .meas m => .meas (m.powRat r)
    | .grpM g c => .grpM (g ^ r) (c.powRat r)
  ofRatio s := .exact s
  jprint := MValue.jprint

/-- A Similitude quantity viewed in MeasureSystems (same exact value, measured
evaluation). -/
def measured {U : Sys} {d : Dim} (q : Q U d) : Quantity U d MValue := ⟨.exact q.val⟩

/-- MeasureSystems' `show(io, ::ConvertUnit)`: as Similitude's, with the ratio
printed with uncertainty. -/
def showConvertM (d : Exps 11) (U S : Sys) : String :=
  let (cr, ones) := pairData U S
  let d' := convertDim ones d
  let r := ratioOf cr (usqMap.apply d)
  s!"{(MValue.exact r).jprint} [{S.showDim d'}]/[{U.showDim d'}] {U.name} -> {S.name}"

end MeasureSystems
