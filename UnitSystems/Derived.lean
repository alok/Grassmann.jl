import UnitSystems.Convert

/-!
# Derived constants and standardized units

The one-argument functions of `UnitSystems.jl` expressing a physical constant
or a standardized unit in a given system: `physics.jl:15-59` (Hubble, month and
year lengths, Loschmidt, Wien, …), `derived.jl:17-251` (193 units from
`steradian` to `roentgen`) and the system prefixes of `UnitSystems.jl:346-373`
(`mega(U) = (Constant(1.0)*kilo(U))^2` is a `Float64`, unlike the module
constant `mega = 1000000`).

A unit is "one of it, converted into `U`": `foot(U) = length(one(U), U, English)`.
Every definition is Julia's, operation by operation.

Julia defects kept as documented (they are the published values):
`inchmercury` uses `inHg = 1/3386.389` (inverted); `bradian`, `apostilb`,
`lambert`, `footlambert`, `bril`, `parsec` and `greatcircle` mix the unit
system's angle into the value; `jovianyear` is only meaningful in IAU systems;
`photonirradiance`-derived units have dimension `L⁻²T`. The exported but
undefined `neper`, `bel`, `decibel` are omitted.
-/

namespace UnitSystems

open FieldConstants UnitAlg

variable {α : Type} [UnitAlg α]

/-- `q(v, U, S)` for a `Constant` value (single division). -/
@[inline] private def cv (q : Conv) (v : α) (U S : UnitSystem α) : α := q.convert v U S

section prefixes
/-- `deka(U) = two(U)*five(U)` -/ def dekaU (U : UnitSystem α) : α := two U * five U
/-- `hecto(U) = deka(U)^2` -/ def hectoU (U : UnitSystem α) : α := dekaU U ^ (2 : Int)
/-- `kilo(U) = deka(U)^3` -/ def kiloU (U : UnitSystem α) : α := dekaU U ^ (3 : Int)
/-- `mega(U) = (Constant(1.0)*kilo(U))^2` -/ def megaU (U : UnitSystem α) : α := (flit 1.0 * kiloU U) ^ (2 : Int)
/-- `giga(U) = (Constant(1.0)*kilo(U))^3` -/ def gigaU (U : UnitSystem α) : α := (flit 1.0 * kiloU U) ^ (3 : Int)
/-- `tera(U)` -/ def teraU (U : UnitSystem α) : α := (flit 1.0 * kiloU U) ^ (4 : Int)
/-- `peta(U)` -/ def petaU (U : UnitSystem α) : α := (flit 1.0 * kiloU U) ^ (5 : Int)
/-- `exa(U)` -/ def exaU (U : UnitSystem α) : α := (flit 1.0 * kiloU U) ^ (6 : Int)
/-- `zetta(U)` -/ def zettaU (U : UnitSystem α) : α := (flit 1.0 * kiloU U) ^ (7 : Int)
/-- `yotta(U)` -/ def yottaU (U : UnitSystem α) : α := (flit 1.0 * kiloU U) ^ (8 : Int)
/-- `deci(U) = inv(deka(U))` -/ def deciU (U : UnitSystem α) : α := UnitAlg.inv (dekaU U)
/-- `centi(U) = inv(hecto(U))` -/ def centiU (U : UnitSystem α) : α := UnitAlg.inv (hectoU U)
/-- `milli(U) = inv(kilo(U))` -/ def milliU (U : UnitSystem α) : α := UnitAlg.inv (kiloU U)
/-- `micro(U) = inv(mega(U))` -/ def microU (U : UnitSystem α) : α := UnitAlg.inv (megaU U)
/-- `nano(U) = inv(giga(U))` -/ def nanoU (U : UnitSystem α) : α := UnitAlg.inv (gigaU U)
/-- `pico(U) = inv(tera(U))` -/ def picoU (U : UnitSystem α) : α := UnitAlg.inv (teraU U)
/-- `femto(U) = inv(peta(U))` -/ def femtoU (U : UnitSystem α) : α := UnitAlg.inv (petaU U)
/-- `atto(U) = inv(exa(U))` -/ def attoU (U : UnitSystem α) : α := UnitAlg.inv (exaU U)
/-- `zepto(U) = inv(zetta(U))` -/ def zeptoU (U : UnitSystem α) : α := UnitAlg.inv (zettaU U)
/-- `yocto(U) = inv(yotta(U))` -/ def yoctoU (U : UnitSystem α) : α := UnitAlg.inv (yottaU U)
/-- `kibi(U) = two(U)^10` -/ def kibiU (U : UnitSystem α) : α := two U ^ (10 : Int)
/-- `mebi(U) = two(U)^20` -/ def mebiU (U : UnitSystem α) : α := two U ^ (20 : Int)
/-- `gibi(U) = two(U)^30` -/ def gibiU (U : UnitSystem α) : α := two U ^ (30 : Int)
/-- `tebi(U) = two(U)^40` -/ def tebiU (U : UnitSystem α) : α := two U ^ (40 : Int)
/-- `pebi(U) = two(U)^50` -/ def pebiU (U : UnitSystem α) : α := two U ^ (50 : Int)
/-- `exbi(U) = two(U)^60` -/ def exbiU (U : UnitSystem α) : α := two U ^ (60 : Int)
/-- `zebi(U) = (Constant(1.0)*two(U))^70` -/ def zebiU (U : UnitSystem α) : α := (flit 1.0 * two U) ^ (70 : Int)
/-- `yobi(U) = (Constant(1.0)*two(U))^80` -/ def yobiU (U : UnitSystem α) : α := (flit 1.0 * two U) ^ (80 : Int)
end prefixes

section units
variable (U : UnitSystem α)

/-- `steradian(U) = solidangle(one(U),U,Metric)` -/ def steradian : α := cv .solidangle (oneU U) U (Metric α)
/-- `spatian(U) = angle(one(U),U,MetricSpatian)` -/ def spatian : α := cv .angle (oneU U) U (MetricSpatian α)
/-- `gradian(U) = angle(one(U),U,MetricGradian)` -/ def gradian : α := cv .angle (oneU U) U (MetricGradian α)
/-- `degree(U) = angle(one(U),U,MetricDegree)` -/ def degree : α := cv .angle (oneU U) U (MetricDegree α)
/-- `squaredegree(U) = solidangle(one(U),U,MetricDegree)` -/
def squaredegree : α := cv .solidangle (oneU U) U (MetricDegree α)
/-- `arcminute(U) = angle(one(U),U,MetricArcminute)` -/
def arcminute : α := cv .angle (oneU U) U (MetricArcminute α)
/-- `arcsecond(U) = angle(one(U),U,MetricArcsecond)` -/
def arcsecond : α := cv .angle (oneU U) U (MetricArcsecond α)
/-- `bradian(U) = angle(turn(U)/two(U)^8,U,Metric)` (double-applies the angle unit) -/
def bradian : α := cv .angle (turn U / two U ^ (8 : Int)) U (Metric α)

/-- `second(U) = time(one(U),U,Metric)` -/ def second : α := cv .time (oneU U) U (Metric α)
/-- `minute(U) = two(U)^2*three(U)*five(U)*second(U)` -/
def minute : α := two U ^ (2 : Int) * three U * five U * second U
/-- `hour(U) = two(U)^2*three(U)*five(U)*minute(U)` -/
def hour : α := two U ^ (2 : Int) * three U * five U * minute U
/-- `day(U) = two(U)^3*three(U)*hour(U)` -/ def day : α := two U ^ (3 : Int) * three U * hour U
/-- `year(U) = aⱼ*day(U)` -/ def year : α := ms α .aⱼ * day U
/-- `apm(U) = one(U)/minute(U)` -/ def apm : α := oneU U / minute U
/-- `rpm(U) = turn(U)/minute(U)` -/ def rpm : α := turn U / minute U
/-- `hertz(U) = one(U)/second(U)` -/ def hertz : α := oneU U / second U

/-- `meter(U) = length(one(U),U,Metric)` -/ def meter : α := cv .length (oneU U) U (Metric α)
/-- `earthmeter(U) = length(one(U),U,Meridian)` -/ def earthmeter : α := cv .length (oneU U) U (Meridian α)
/-- `angstrom(U) = hecto(U)*pico(U)*meter(U)` -/ def angstrom : α := hectoU U * picoU U * meter U
/-- `foot(U) = length(one(U),U,English)` -/ def foot : α := cv .length (oneU U) U (English α)
/-- `inch(U) = length(one(U),U,IPS)` -/ def inch : α := cv .length (oneU U) U (IPS α)
/-- `yard(U) = three(U)*foot(U)` -/ def yard : α := three U * foot U
/-- `surveyfoot(U) = length(one(U),U,Survey)` -/ def surveyfoot : α := cv .length (oneU U) U (Survey α)
/-- `statutemile(U) = length(two(U)^5*three(U)*five(U)*eleven(U),U,Survey)` -/
def statutemile : α := cv .length (two U ^ (5 : Int) * three U * five U * eleven U) U (Survey α)
/-- `nauticalmile(U) = length(one(U),U,Nautical)` -/ def nauticalmile : α := cv .length (oneU U) U (Nautical α)
/-- `astronomicalunit(U) = length(𝟏,U,IAU)` -/ def astronomicalunit : α := cv .length one U (IAU α)
/-- `lunardistance(U) = length(𝟏,U,IAUE)` -/ def lunardistance : α := cv .length one U (IAUE α)
/-- `jupiterdistance(U) = length(𝟏,U,IAUJ)` -/ def jupiterdistance : α := cv .length one U (IAUJ α)
/-- `mile(U) = length(two(U)^5*three(U)*five(U)*eleven(U),U,English)` -/
def mile : α := cv .length (two U ^ (5 : Int) * three U * five U * eleven U) U (English α)
/-- `admiraltymile(U) = length(two(U)^6*five(U)*nineteen(U),U,English)` -/
def admiraltymile : α := cv .length (two U ^ (6 : Int) * five U * nineteen U) U (English α)
/-- `meridianmile(U) = length(two(U)^4*five(U)^5/three(U)^3,U,Metric)` -/
def meridianmile : α := cv .length (two U ^ (4 : Int) * five U ^ (5 : Int) / three U ^ (3 : Int)) U (Metric α)
/-- `lightyear(U) = year(U)*lightspeed(U)` -/ def lightyear : α := year U * lightspeed U
/-- `parsec(U) = astronomicalunit(U)*two(U)^7*three(U)^4*five(U)^3/turn(U)` -/
def parsec : α := astronomicalunit U * two U ^ (7 : Int) * three U ^ (4 : Int) * five U ^ (3 : Int) / turn U
/-- `radarmile(U) = two(U)*nauticalmile(U)/lightspeed(U)` -/
def radarmile : α := two U * nauticalmile U / lightspeed U

/-- `barn(U) = area((two(U)*five(U))^-28,U,Metric)` -/
def barn : α := cv .area ((two U * five U) ^ (-28 : Int)) U (Metric α)
/-- `hectare(U) = area(hecto(U)*hecto(U),U,Metric)` -/ def hectare : α := cv .area (hectoU U * hectoU U) U (Metric α)
/-- `acre(U) = area(two(U)^-7/five(U),U,MPH)` -/ def acre : α := cv .area (two U ^ (-7 : Int) / five U) U (MPH α)
/-- `surveyacre(U) = area(two(U)^3*three(U)^2*five(U)*eleven(U)^2,U,Survey)` -/
def surveyacre : α :=
  cv .area (two U ^ (3 : Int) * three U ^ (2 : Int) * five U * eleven U ^ (2 : Int)) U (Survey α)

/-- `gallon(U) = volume(three(U)*seven(U)*eleven(U),U,IPS)` -/
def gallon : α := cv .volume (three U * seven U * eleven U) U (IPS α)
/-- `liter(U) = volume(inv((two(U)*five(U))^3),U,Metric)` -/
def liter : α := cv .volume (UnitAlg.inv ((two U * five U) ^ (3 : Int))) U (Metric α)
/-- `quart(U) = gallon(U)/two(U)^2` -/ def quart : α := gallon U / two U ^ (2 : Int)
/-- `pint(U) = quart(U)/two(U)` -/ def pint : α := quart U / two U
/-- `cup(U) = pint(U)/two(U)` -/ def cup : α := pint U / two U
/-- `fluidounce(U) = cup(U)/two(U)^3` -/ def fluidounce : α := cup U / two U ^ (3 : Int)
/-- `teaspoon(U) = five(U)*milli(U)*liter(U)` -/ def teaspoon : α := five U * milliU U * liter U
/-- `tablespoon(U) = three(U)*teaspoon(U)` -/ def tablespoon : α := three U * teaspoon U

/-- `bubnoff(U) = meter(U)/year(U)` -/ def bubnoff : α := meter U / year U
/-- `ips(U) = inch(U)/second(U)` -/ def ips : α := inch U / second U
/-- `fps(U) = foot(U)/second(U)` -/ def fps : α := foot U / second U
/-- `fpm(U) = foot(U)/minute(U)` -/ def fpm : α := foot U / minute U
/-- `ms(U) = meter(U)/second(U)` -/ def msU : α := meter U / second U
/-- `kmh(U) = kilo(U)*meter(U)/hour(U)` -/ def kmh : α := kiloU U * meter U / hour U
/-- `mph(U) = mile(U)/hour(U)` -/ def mph : α := mile U / hour U
/-- `knot(U) = nauticalmile(U)/hour(U)` -/ def knot : α := nauticalmile U / hour U
/-- `mps(U) = mile(U)/second(U)` -/ def mps : α := mile U / second U

/-- `pound(U) = mass(one(U),U,English)` -/ def pound : α := cv .mass (oneU U) U (English α)
/-- `grain(U) = milli(U)*pound(U)/seven(U)` -/ def grain : α := milliU U * pound U / seven U
/-- `gram(U) = mass(one(U),U,Gauss)` -/ def gram : α := cv .mass (oneU U) U (Gauss α)
/-- `earthgram(U) = mass(milli(U),U,Meridian)` -/ def earthgram : α := cv .mass (milliU U) U (Meridian α)
/-- `kilogram(U) = mass(one(U),U,Metric)` -/ def kilogram : α := cv .mass (oneU U) U (Metric α)
/-- `tonne(U) = mass(kilo(U),U,Metric)` -/ def tonne : α := cv .mass (kiloU U) U (Metric α)
/-- `ton(U) = mass(two(U)*kilo(U),U,English)` -/ def ton : α := cv .mass (two U * kiloU U) U (English α)
/-- `ounce(U) = mass(two(U)^-4,U,English)` -/ def ounce : α := cv .mass (two U ^ (-4 : Int)) U (English α)
/-- `slug(U) = mass(one(U),U,British)` -/ def slugU : α := cv .mass (oneU U) U (British α)
/-- `slinch(U) = mass(one(U),U,IPS)` -/ def slinch : α := cv .mass (oneU U) U (IPS α)
/-- `hyl(U) = mass(one(U),U,Gravitational)` -/ def hyl : α := cv .mass (oneU U) U (Gravitational α)

/-- `dyne(U) = force(one(U),U,Gauss)` -/ def dyne : α := cv .force (oneU U) U (Gauss α)
/-- `newton(U) = force(one(U),U,Metric)` -/ def newton : α := cv .force (oneU U) U (Metric α)
/-- `poundal(U) = force(one(U),U,FPS)` -/ def poundal : α := cv .force (oneU U) U (FPS α)
/-- `poundforce(U) = force(one(U),U,English)` -/ def poundforce : α := cv .force (oneU U) U (English α)
/-- `kilopond(U) = force(one(U),U,Engineering)` -/ def kilopond : α := cv .force (oneU U) U (Engineering α)

/-- `pascal(U) = pressure(one(U),U,Metric)` -/ def pascal : α := cv .pressure (oneU U) U (Metric α)
/-- `bar(U) = pressure(hecto(U)*kilo(U),U,Metric)` -/ def bar : α := cv .pressure (hectoU U * kiloU U) U (Metric α)
/-- `barye(U) = pressure(one(U),U,Gauss)` -/ def barye : α := cv .pressure (oneU U) U (Gauss α)
/-- `psi(U) = pressure(one(U),U,IPS)` -/ def psi : α := cv .pressure (oneU U) U (IPS α)
/-- `technicalatmosphere(U) = kilopond(U)/(centi(U)*meter(U))^2` -/
def technicalatmosphere : α := kilopond U / (centiU U * meter U) ^ (2 : Int)
/-- `atmosphere(U) = pressure(atm,U,Metric)` -/ def atmosphere : α := cv .pressure (ms α .atm) U (Metric α)
/-- `inchmercury(U) = pressure(inHg,U,Metric)` (Julia's `inHg` is inverted) -/
def inchmercury : α := cv .pressure (ms α .inHg) U (Metric α)
/-- `torr(U) = pressure(atm/(two(U)^3*five(U)*nineteen(U)),U,Metric)` -/
def torr : α := cv .pressure (ms α .atm / (two U ^ (3 : Int) * five U * nineteen U)) U (Metric α)

/-- `electronvolt(U) = elementarycharge(U)*electricpotential(one(U),U,SI2019)` -/
def electronvolt : α := elementarycharge U * cv .electricpotential (oneU U) U (SI2019 α)
/-- `erg(U) = energy(one(U),U,Gauss)` -/ def erg : α := cv .energy (oneU U) U (Gauss α)
/-- `joule(U) = energy(one(U),U,Metric)` -/ def joule : α := cv .energy (oneU U) U (Metric α)
/-- `footpound(U) = poundforce(U)*foot(U)` -/ def footpound : α := poundforce U * foot U
/-- `meancalorie(U) = energy(two(U)^2*five(U)*three(U)^2/fourtythree(U),U,InternationalMean)` -/
def meancalorie : α :=
  cv .energy (two U ^ (2 : Int) * five U * three U ^ (2 : Int) / fourtythree U) U (InternationalMean α)
/-- `kilocalorie(U) = energy(two(U)^5*five(U)^4*three(U)^2/fourtythree(U),U,International)` -/
def kilocalorie : α :=
  cv .energy (two U ^ (5 : Int) * five U ^ (4 : Int) * three U ^ (2 : Int) / fourtythree U) U (International α)
/-- `calorie(U) = kilocalorie(U)/(two(U)*five(U))^3` -/
def calorie : α := kilocalorie U / (two U * five U) ^ (3 : Int)
/-- `earthcalorie(U) = molaramount(temperature(calorie(U),Metric,Meridian),Metric,Meridian)` -/
def earthcalorie : α :=
  cv .molaramount (cv .temperature (calorie U) (Metric α) (Meridian α)) (Metric α) (Meridian α)
/-- `thermalunit(U) = mass(temperature(kilocalorie(U),Metric,English),Metric,English)` -/
def thermalunit : α :=
  cv .mass (cv .temperature (kilocalorie U) (Metric α) (English α)) (Metric α) (English α)
/-- `tontnt(U) = giga(U)*calorie(U)` -/ def tontnt : α := gigaU U * calorie U
/-- `gasgallon(U) = two(U)*three(U)*nineteen(U)*kilo(U)*thermalunit(U)` -/
def gasgallon : α := two U * three U * nineteen U * kiloU U * thermalunit U

/-- `watt(U) = power(one(U),U,Metric)` -/ def watt : α := cv .power (oneU U) U (Metric α)
/-- `tonsrefrigeration(U) = frequency(two(U)*five(U)/three(U),U,Metric)*thermalunit(U)` -/
def tonsrefrigeration : α := cv .frequency (two U * five U / three U) U (Metric α) * thermalunit U
/-- `boilerhorsepower(U) = frequency(Constant(1339)/(two(U)^4*three(U)^2),U,Metric)*thermalunit(U)` -/
def boilerhorsepower : α :=
  cv .frequency (ilit 1339 / (two U ^ (4 : Int) * three U ^ (2 : Int))) U (Metric α) * thermalunit U
/-- `thermalconductivity_water(U)` (unexported in Julia) -/
def thermalconductivity_water : α :=
  cv .thermalconductivity ((two U ^ (2 : Int) * three U * five U) ^ (2 : Int) / thermalunit U) U (Metric α)
/-- `horsepower(U) = power(two(U)*five(U)^2*eleven(U),U,British)` -/
def horsepower : α := cv .power (two U * five U ^ (2 : Int) * eleven U) U (British α)
/-- `horsepowerwatt(U) = power(two(U)^4*three(U)^3/five(U)*normal(tau(U)),U,British)` -/
def horsepowerwatt : α := cv .power (two U ^ (4 : Int) * three U ^ (3 : Int) / five U * tau U) U (British α)
/-- `horsepowermetric(U) = power(three(U)*five(U)^2,U,Gravitational)` -/
def horsepowermetric : α := cv .power (three U * five U ^ (2 : Int)) U (Gravitational α)
/-- `electricalhorsepower(U) = power(Constant(746),U,Metric)` -/
def electricalhorsepower : α := cv .power (ilit 746) U (Metric α)

/-- `coulomb(U) = charge(one(U),U,Metric)` -/ def coulomb : α := cv .charge (oneU U) U (Metric α)
/-- `ampere(U) = current(one(U),U,Metric)` -/ def ampere : α := cv .current (oneU U) U (Metric α)
/-- `volt(U) = electricpotential(one(U),U,Metric)` -/ def volt : α := cv .electricpotential (oneU U) U (Metric α)
/-- `henry(U) = inductance(one(U),U,Metric)` -/ def henry : α := cv .inductance (oneU U) U (Metric α)
/-- `ohm(U) = resistance(one(U),U,Metric)` -/ def ohm : α := cv .resistance (oneU U) U (Metric α)
/-- `siemens(U) = conductance(one(U),U,Metric)` -/ def siemens : α := cv .conductance (oneU U) U (Metric α)
/-- `farad(U) = capacitance(one(U),U,Metric)` -/ def farad : α := cv .capacitance (oneU U) U (Metric α)
/-- `weber(U) = magneticflux(one(U),U,Metric)` -/ def weber : α := cv .magneticflux (oneU U) U (Metric α)
/-- `tesla(U) = magneticfluxdensity(one(U),U,Metric)` -/
def tesla : α := cv .magneticfluxdensity (oneU U) U (Metric α)
/-- `abcoulomb(U) = charge(one(U),U,EMU)` -/ def abcoulomb : α := cv .charge (oneU U) U (EMU α)
/-- `abampere(U) = current(one(U),U,EMU)` -/ def abampere : α := cv .current (oneU U) U (EMU α)
/-- `abvolt(U) = electricpotential(one(U),U,EMU)` -/ def abvolt : α := cv .electricpotential (oneU U) U (EMU α)
/-- `abhenry(U) = inductance(one(U),U,EMU)` -/ def abhenry : α := cv .inductance (oneU U) U (EMU α)
/-- `abohm(U) = resistance(one(U),U,EMU)` -/ def abohm : α := cv .resistance (oneU U) U (EMU α)
/-- `abmho(U) = conductance(one(U),U,EMU)` -/ def abmho : α := cv .conductance (oneU U) U (EMU α)
/-- `abfarad(U) = capacitance(one(U),U,EMU)` -/ def abfarad : α := cv .capacitance (oneU U) U (EMU α)
/-- `maxwell(U) = magneticflux(one(U),U,EMU)` -/ def maxwell : α := cv .magneticflux (oneU U) U (EMU α)
/-- `gauss(U) = magneticfluxdensity(one(U),U,EMU)` -/ def gauss : α := cv .magneticfluxdensity (oneU U) U (EMU α)
/-- `oersted(U) = magneticfield(one(U),U,EMU)` -/ def oersted : α := cv .magneticfield (oneU U) U (EMU α)
/-- `gilbert(U) = abampere(U)/two(U)/turn(U)` -/ def gilbert : α := abampere U / two U / turn U
/-- `statcoulomb(U) = charge(one(U),U,ESU)` -/ def statcoulomb : α := cv .charge (oneU U) U (ESU α)
/-- `statampere(U) = current(one(U),U,ESU)` -/ def statampere : α := cv .current (oneU U) U (ESU α)
/-- `statvolt(U) = electricpotential(one(U),U,ESU)` -/ def statvolt : α := cv .electricpotential (oneU U) U (ESU α)
/-- `stathenry(U) = inductance(one(U),U,ESU)` -/ def stathenry : α := cv .inductance (oneU U) U (ESU α)
/-- `statohm(U) = resistance(one(U),U,ESU)` -/ def statohm : α := cv .resistance (oneU U) U (ESU α)
/-- `statmho(U) = conductance(one(U),U,ESU)` -/ def statmho : α := cv .conductance (oneU U) U (ESU α)
/-- `statfarad(U) = capacitance(one(U),U,ESU)` -/ def statfarad : α := cv .capacitance (oneU U) U (ESU α)
/-- `statweber(U) = magneticflux(one(U),U,ESU)` -/ def statweber : α := cv .magneticflux (oneU U) U (ESU α)
/-- `stattesla(U) = magneticfluxdensity(one(U),U,ESU)` -/
def stattesla : α := cv .magneticfluxdensity (oneU U) U (ESU α)
/-- `earthcoulomb(U) = charge(one(U),U,Meridian)` -/ def earthcoulomb : α := cv .charge (oneU U) U (Meridian α)

/-- `kelvin(U) = temperature(one(U),U,Metric)` -/ def kelvin : α := cv .temperature (oneU U) U (Metric α)
/-- `rankine(U) = temperature(one(U),U,English)` -/ def rankine : α := cv .temperature (oneU U) U (English α)
/-- `celsius(U) = temperature(T₀,U,Metric)` -/ def celsius : α := cv .temperature (ms α .T₀) U (Metric α)
/-- `fahrenheit(U) = temperature(Constant(459.67),U,English)` -/
def fahrenheit : α := cv .temperature (flit 459.67) U (English α)
/-- `sealevel(U) = temperature(T₀+𝟑*𝟓,U,Metric)` -/
def sealevel : α := cv .temperature (ms α .T₀ + c3 α * c5 α) U (Metric α)
/-- `boiling(U) = temperature(T₀+Constant(99.9839),U,Metric)` -/
def boiling : α := cv .temperature (ms α .T₀ + flit 99.9839) U (Metric α)

/-- `mole(U) = molaramount(one(U),U,Metric)` -/ def mole : α := cv .molaramount (oneU U) U (Metric α)
/-- `earthmole(U) = molaramount(one(U),U,Meridian)` -/ def earthmole : α := cv .molaramount (oneU U) U (Meridian α)
/-- `poundmole(U) = molaramount(one(U),U,English)` -/ def poundmole : α := cv .molaramount (oneU U) U (English α)
/-- `slugmole(U) = molaramount(one(U),U,British)` -/ def slugmole : α := cv .molaramount (oneU U) U (British α)
/-- `slinchmole(U) = molaramount(one(U),U,IPS)` -/ def slinchmole : α := cv .molaramount (oneU U) U (IPS α)
/-- `katal(U) = catalysis(one(U),U,Metric)` -/ def katal : α := cv .catalysis (oneU U) U (Metric α)

/-- `lumen(U) = luminousflux(one(U),U,Metric)` -/ def lumen : α := cv .luminousflux (oneU U) U (Metric α)
/-- `candela(U) = luminousintensity(one(U),U,Metric)` -/
def candela : α := cv .luminousintensity (oneU U) U (Metric α)
/-- `lux(U) = illuminance(one(U),U,Metric)` -/ def lux : α := cv .illuminance (oneU U) U (Metric α)
/-- `footcandle(U) = illuminance(one(U),U,English)` -/ def footcandle : α := cv .illuminance (oneU U) U (English α)
/-- `phot(U) = illuminance(one(U),U,Gauss)` -/ def phot : α := cv .illuminance (oneU U) U (Gauss α)
/-- `nit(U) = luminance(one(U),U,Metric)` -/ def nit : α := cv .luminance (oneU U) U (Metric α)
/-- `apostilb(U) = luminance(two(U)/turn(U),U,Metric)` -/
def apostilb : α := cv .luminance (two U / turn U) U (Metric α)
/-- `stilb(U) = luminance(one(U),U,Gauss)` -/ def stilb : α := cv .luminance (oneU U) U (Gauss α)
/-- `lambert(U) = luminance(two(U)/turn(U),U,Gauss)` -/ def lambert : α := cv .luminance (two U / turn U) U (Gauss α)
/-- `footlambert(U) = luminance(two(U)/turn(U),U,English)` -/
def footlambert : α := cv .luminance (two U / turn U) U (English α)
/-- `bril(U) = centi(U)*nano(U)*lambert(U)` -/ def bril : α := centiU U * nanoU U * lambert U
/-- `talbot(U) = luminousenergy(one(U),U,Metric)` -/ def talbot : α := cv .luminousenergy (oneU U) U (Metric α)
/-- `lumerg(U) = luminousenergy(centi(U)^2*milli(U),U,CGS)` -/
def lumerg : α := cv .luminousenergy (centiU U ^ (2 : Int) * milliU U) U (Gauss α)
/-- `rayleigh(U) = deka(U)*giga(U)*photonirradiance(one(U),U,Metric)` -/
def rayleigh : α := dekaU U * gigaU U * cv .photonirradiance (oneU U) U (Metric α)
/-- `flick(U) = giga(U)*radiance(deka(U),U,Metric)*length(one(U),Metric,U)` -/
def flick : α := gigaU U * cv .radiance (dekaU U) U (Metric α) * cv .length (oneU U) (Metric α) U

/-- `kayser(U) = wavenumber(one(U),U,Gauss)` -/ def kayser : α := cv .wavenumber (oneU U) U (Gauss α)
/-- `diopter(U) = angularwavenumber(one(U),U,Metric)` -/
def diopter : α := cv .angularwavenumber (oneU U) U (Metric α)
/-- `gforce(U) = specificforce(one(U),U,English)` -/ def gforce : α := cv .specificforce (oneU U) U (English α)
/-- `galileo(U) = specificforce(one(U),U,Gauss)` -/ def galileo : α := cv .specificforce (oneU U) U (Gauss α)
/-- `eotvos(U) = specificforce(nano(U),U,Gauss)/length(one(U),U,Gauss)` -/
def eotvos : α := cv .specificforce (nanoU U) U (Gauss α) / cv .length (oneU U) U (Gauss α)
/-- `darcy(U) = area(milli(U)/normal(atmosphere(Metric)),U,Gauss)` -/
def darcy : α := cv .area (milliU U / atmosphere (Metric α)) U (Gauss α)
/-- `poise(U) = viscosity(one(U),U,Gauss)` -/ def poise : α := cv .viscosity (oneU U) U (Gauss α)
/-- `reyn(U) = viscosity(one(U),U,IPS)` -/ def reyn : α := cv .viscosity (oneU U) U (IPS α)
/-- `stokes(U) = diffusivity(one(U),U,Gauss)` -/ def stokes : α := cv .diffusivity (oneU U) U (Gauss α)
/-- `rayl(U) = specificimpedance(one(U),U,Metric)` -/ def rayl : α := cv .specificimpedance (oneU U) U (Metric α)
/-- `mpge(U) = mile(U)/gasgallon(U)` -/ def mpge : α := mile U / gasgallon U
/-- `langley(U) = calorie(U)/(centi(U)*meter(U))^2` -/
def langley : α := calorie U / (centiU U * meter U) ^ (2 : Int)
/-- `jansky(U) = fluence((Constant(1.0)*deci(U))^26,U,Metric)` -/
def jansky : α := cv .fluence ((flit 1.0 * deciU U) ^ (26 : Int)) U (Metric α)
/-- `solarflux(U) = hecto(U)^2*jansky(U)` -/ def solarflux : α := hectoU U ^ (2 : Int) * jansky U
/-- `curie(U) = Constant(37)*giga(U)*hertz(U)` -/ def curie : α := ilit 37 * gigaU U * hertz U
/-- `gray(U) = energy(one(U),U,Metric)/mass(one(U),U,Metric)` -/
def gray : α := cv .energy (oneU U) U (Metric α) / cv .mass (oneU U) U (Metric α)
/-- `rem(U) = centi(U)*gray(U)` -/ def remU : α := centiU U * gray U
/-- `roentgen(U) = chargedensity(one(U),U,ESU)/density(Constant(1.293),U,Metric)` -/
def roentgen : α := cv .chargedensity (oneU U) U (ESU α) / cv .density (flit 1.293) U (Metric α)

end units

/-! ### Derived physical constants (`physics.jl:41-59`) -/

section physics
variable (U : UnitSystem α)

/-- `hyperfine(U) = frequency(ΔνCs,U,Metric)` -/
def hyperfine : α := cv .frequency (ms α .ΔνCs) U (Metric α)
/-- `hubble(U) = time(one(U),Hubble,U)` -/
def hubble : α := cv .time (oneU U) (Hubble α) U
/-- `cosmological(U,C) = three(U)*darkenergydensity(C)*(hubble(U)/lightspeed(U,C))^2` -/
def cosmological (C : Coupling α := U.C) : α :=
  three U * C.darkenergydensity * (hubble U / lightspeedC U C) ^ (2 : Int)
/-- `loschmidt(U,P=atmosphere(U),T=T₀*temperature(SI2019,U)) = P/T/boltzmann(U)` -/
def loschmidt (P : α := atmosphere U) (T : α := ms α .T₀ * Convert.temperature (SI2019 α) U) : α :=
  P / T / boltzmann U
/-- `amagat(U) = loschmidt(U)/avogadro(U)` -/ def amagat : α := loschmidt U / avogadro U
/-- `wienwavelength(U) = planck(U)*lightspeed(U)/boltzmann(U)/Constant(4.965114231744276303)` -/
def wienwavelength : α := planck U * lightspeed U / boltzmann U / flit 4.965114231744276303
/-- `wienfrequency(U) = Constant(2.821439372122078893)*boltzmann(U)/planck(U)` -/
def wienfrequency : α := flit 2.821439372122078893 * boltzmann U / planck U
/-- `eddington(U) = mass(one(U),U,Cosmological)` -/
def eddington : α := cv .mass (oneU U) U (Cosmological α)
/-- `solarmass(U) = mass(GM☉/G,U,Metric)` -/
def solarmass : α := cv .mass (GMsun α / G α) U (Metric α)
/-- `earthmass(U) = mass(GME/G,U,Metric)` -/
def earthmass : α := cv .mass (ms α .GME / G α) U (Metric α)
/-- `jupitermass(U) = mass(GMJ/G,U,Metric)` -/
def jupitermass : α := cv .mass (ms α .GMJ / G α) U (Metric α)
/-- `lunarmass(U) = earthmass(U)/μE☾` -/ def lunarmass : α := earthmass U / ms α .μE
/-- `earthradius(U) = sqrt(earthmass(U)*gravitation(U)/gforce(U))` -/
def earthradius : α := UnitAlg.sqrt (earthmass U * gravitation U / gforce U)
/-- `greatcircle(U) = normal(turn(U))*earthradius(U)` -/ def greatcircle : α := turn U * earthradius U
/-- `mechanicalheat(U) = molargas(U)*normal(calorie(Metric)/molargas(Metric))` -/
def mechanicalheat : α := molargas U * (calorie (Metric α) / molargas (Metric α))
/-- `gaussgravitation(U) = sqrt(normal(gravitation(IAU)))*radian(U)/day(U)` -/
def gaussgravitation : α := UnitAlg.sqrt (gravitation (IAU α)) * radian U / day U
/-- `gaussianyear(U) = turn(U)/gaussgravitation(U)` -/ def gaussianyear : α := turn U / gaussgravitation U
/-- `siderealyear(U) = gaussianyear(U)/normal(sqrt(solarmass(IAU)+earthmass(IAU)+lunarmass(IAU)))` -/
def siderealyear : α :=
  gaussianyear U / UnitAlg.sqrt (solarmass (IAU α) + earthmass (IAU α) + lunarmass (IAU α))
/-- `gaussianmonth(U) = tau(U)*sqrt(LD^3/GME)*time(Metric,U)` -/
def gaussianmonth : α :=
  tau U * UnitAlg.sqrt (ms α .LD ^ (3 : Int) / ms α .GME) * Convert.time (Metric α) U
/-- `siderealmonth(U) = gaussianmonth(U)/normal(sqrt(earthmass(IAUE)+lunarmass(IAUE)))` -/
def siderealmonth : α := gaussianmonth U / UnitAlg.sqrt (earthmass (IAUE α) + lunarmass (IAUE α))
/-- `synodicmonth(U) = inv(inv(siderealmonth(U))-inv(siderealyear(U)))` -/
def synodicmonth : α := UnitAlg.inv (UnitAlg.inv (siderealmonth U) - UnitAlg.inv (siderealyear U))
/-- `jovianyear(U)` (`physics.jl:59`; only meaningful in IAU systems) -/
def jovianyear : α :=
  day U * UnitAlg.sqrt (jupiterdistance U ^ (3 : Int) / solarmass U / gravitation U) * turn U / radian U /
    UnitAlg.sqrt (solarmass (IAU α) + jupitermass (IAU α))

end physics

/-! ### Conversion helpers (`kinematic.jl:20-41`, `thermodynamic.jl:32-39`) -/

/-- `kilograms(m, U=English) = mass(m, Metric, U)`: from `U`'s mass unit to kg. -/
def kilograms (m : α) (U : UnitSystem α := English α) : α := Conv.convert .mass m (Metric α) U
/-- `slugs(m, U=Metric) = mass(m, English, U)` (despite the name, English's mass unit is lbm). -/
def slugs (m : α) (U : UnitSystem α := Metric α) : α := Conv.convert .mass m (English α) U
/-- `feet(d, U=Metric) = length(d, English, U)` -/
def feet (d : α) (U : UnitSystem α := Metric α) : α := Conv.convert .length d (English α) U
/-- `meters(d, U=English) = length(d, Metric, U)` -/
def meters (d : α) (U : UnitSystem α := English α) : α := Conv.convert .length d (Metric α) U
/-- `moles(N, U=Metric) = N/avogadro(U)` -/
def moles (n : α) (U : UnitSystem α := Metric α) : α := n / avogadro U
/-- `molecules(n, U=Metric) = n*avogadro(U)` -/
def molecules (n : α) (U : UnitSystem α := Metric α) : α := n * avogadro U

end UnitSystems
