import UnitSystems.Derived

/-!
# Name tables

Julia exposes every constant, physics quantity and unit as a function of the
unit system (`boltzmann(U)`, `foot(U)`, …) grouped in the tuples
`Dimensionless`, `Constants`, `Physics`, `Derived` (`UnitSystems.jl:22-27`).
`scalarFunctions` is that registry (name ↦ function, in Julia order), generic in
the scalar; `moduleConstants` lists the module-level numbers
(`UnitSystems.jl:316-344`, `initdata.jl:15-28`, `systems.jl:28-72`).
-/

namespace UnitSystems

open FieldConstants UnitAlg

variable {α : Type} [UnitAlg α]

/-- Julia `Dimensionless` (`UnitSystems.jl:23`). -/
def dimensionlessFunctions : List (String × (UnitSystem α → α)) :=
  [("coupling", coupling), ("finestructure", finestructure), ("electronunit", electronunit),
   ("protonunit", protonunit), ("protonelectron", protonelectron),
   ("darkenergydensity", darkenergydensity)]

/-- Julia `Constants` (`UnitSystems.jl:24`), one-argument forms. -/
def constantFunctions : List (String × (UnitSystem α → α)) :=
  [("lightspeed", lightspeed), ("planck", planck), ("planckreduced", planckreduced),
   ("electronmass", electronmass), ("molarmass", molarmass), ("boltzmann", boltzmann),
   ("vacuumpermeability", vacuumpermeability), ("rationalization", rationalization),
   ("lorentz", lorentz), ("luminousefficacy", luminousefficacy), ("gravity", gravity),
   ("radian", radian)]

/-- Julia `Physics` (`UnitSystems.jl:25`), with the system's own coupling. -/
def physicsFunctions : List (String × (UnitSystem α → α)) :=
  [("turn", turn), ("spat", spat), ("dalton", fun U => dalton U), ("protonmass", fun U => protonmass U),
   ("planckmass", fun U => planckmass U), ("gravitation", fun U => gravitation U),
   ("gaussgravitation", gaussgravitation), ("einstein", fun U => einstein U),
   ("hartree", fun U => hartree U), ("rydberg", fun U => rydberg U), ("bohr", fun U => bohr U),
   ("electronradius", fun U => electronradius U), ("avogadro", fun U => avogadro U),
   ("molargas", fun U => molargas U), ("stefan", fun U => stefan U),
   ("radiationdensity", fun U => radiationdensity U),
   ("vacuumpermittivity", fun U => vacuumpermittivity U),
   ("electrostatic", fun U => electrostatic U), ("magnetostatic", magnetostatic),
   ("biotsavart", fun U => biotsavart U), ("elementarycharge", fun U => elementarycharge U),
   ("faraday", fun U => faraday U), ("vacuumimpedance", fun U => vacuumimpedance U),
   ("conductancequantum", fun U => conductancequantum U), ("klitzing", fun U => klitzing U),
   ("josephson", fun U => josephson U), ("magneticfluxquantum", fun U => magneticfluxquantum U),
   ("magneton", fun U => magneton U)]

/-- Julia `Derived` (`UnitSystems.jl:26-40`), minus the undefined `neper`, `bel`, `decibel`. -/
def derivedFunctions : List (String × (UnitSystem α → α)) :=
  [("hyperfine", hyperfine), ("loschmidt", fun U => loschmidt U), ("wienwavelength", wienwavelength),
   ("wienfrequency", wienfrequency), ("mechanicalheat", mechanicalheat), ("eddington", eddington),
   ("solarmass", solarmass), ("jupitermass", jupitermass), ("earthmass", earthmass),
   ("lunarmass", lunarmass), ("earthradius", earthradius), ("greatcircle", greatcircle),
   ("radarmile", radarmile), ("hubble", hubble), ("cosmological", fun U => cosmological U),
   ("steradian", steradian), ("spatian", spatian), ("degree", degree), ("squaredegree", squaredegree),
   ("gradian", gradian), ("bradian", bradian), ("arcminute", arcminute), ("arcsecond", arcsecond),
   ("second", second), ("minute", minute), ("hour", hour), ("day", day),
   ("gaussianmonth", gaussianmonth), ("siderealmonth", siderealmonth), ("synodicmonth", synodicmonth),
   ("year", year), ("gaussianyear", gaussianyear), ("siderealyear", siderealyear),
   ("jovianyear", jovianyear), ("angstrom", angstrom), ("inch", inch), ("foot", foot),
   ("surveyfoot", surveyfoot), ("yard", yard), ("meter", meter), ("earthmeter", earthmeter),
   ("mile", mile), ("statutemile", statutemile), ("meridianmile", meridianmile),
   ("admiraltymile", admiraltymile), ("nauticalmile", nauticalmile), ("lunardistance", lunardistance),
   ("astronomicalunit", astronomicalunit), ("jupiterdistance", jupiterdistance),
   ("lightyear", lightyear), ("parsec", parsec), ("barn", barn), ("hectare", hectare), ("acre", acre),
   ("surveyacre", surveyacre), ("liter", liter), ("gallon", gallon), ("quart", quart), ("pint", pint),
   ("cup", cup), ("fluidounce", fluidounce), ("teaspoon", teaspoon), ("tablespoon", tablespoon),
   ("bubnoff", bubnoff), ("ips", ips), ("fps", fps), ("fpm", fpm), ("ms", msU), ("kmh", kmh),
   ("mph", mph), ("knot", knot), ("mps", mps), ("grain", grain), ("gram", gram),
   ("earthgram", earthgram), ("kilogram", kilogram), ("tonne", tonne), ("ton", ton),
   ("pound", pound), ("ounce", ounce), ("slug", slugU), ("slinch", slinch), ("hyl", hyl),
   ("dyne", dyne), ("newton", newton), ("poundal", poundal), ("poundforce", poundforce),
   ("kilopond", kilopond), ("psi", psi), ("pascal", pascal), ("bar", bar), ("barye", barye),
   ("technicalatmosphere", technicalatmosphere), ("atmosphere", atmosphere),
   ("inchmercury", inchmercury), ("torr", torr), ("electronvolt", electronvolt), ("erg", erg),
   ("joule", joule), ("footpound", footpound), ("calorie", calorie), ("kilocalorie", kilocalorie),
   ("meancalorie", meancalorie), ("earthcalorie", earthcalorie), ("thermalunit", thermalunit),
   ("gasgallon", gasgallon), ("tontnt", tontnt), ("watt", watt), ("horsepower", horsepower),
   ("horsepowerwatt", horsepowerwatt), ("horsepowermetric", horsepowermetric),
   ("electricalhorsepower", electricalhorsepower), ("tonsrefrigeration", tonsrefrigeration),
   ("boilerhorsepower", boilerhorsepower), ("coulomb", coulomb), ("earthcoulomb", earthcoulomb),
   ("ampere", ampere), ("volt", volt), ("henry", henry), ("ohm", ohm), ("siemens", siemens),
   ("farad", farad), ("weber", weber), ("tesla", tesla), ("abcoulomb", abcoulomb),
   ("abampere", abampere), ("abvolt", abvolt), ("abhenry", abhenry), ("abohm", abohm),
   ("abmho", abmho), ("abfarad", abfarad), ("maxwell", maxwell), ("gauss", gauss),
   ("oersted", oersted), ("gilbert", gilbert), ("statcoulomb", statcoulomb),
   ("statampere", statampere), ("statvolt", statvolt), ("stathenry", stathenry),
   ("statohm", statohm), ("statmho", statmho), ("statfarad", statfarad), ("statweber", statweber),
   ("stattesla", stattesla), ("kelvin", kelvin), ("rankine", rankine), ("celsius", celsius),
   ("fahrenheit", fahrenheit), ("sealevel", sealevel), ("boiling", boiling), ("mole", mole),
   ("earthmole", earthmole), ("poundmole", poundmole), ("slugmole", slugmole),
   ("slinchmole", slinchmole), ("katal", katal), ("amagat", amagat), ("lumen", lumen),
   ("candela", candela), ("lux", lux), ("phot", phot), ("footcandle", footcandle), ("nit", nit),
   ("apostilb", apostilb), ("stilb", stilb), ("lambert", lambert), ("footlambert", footlambert),
   ("bril", bril), ("talbot", talbot), ("lumerg", lumerg), ("hertz", hertz), ("apm", apm),
   ("rpm", rpm), ("kayser", kayser), ("diopter", diopter), ("rayleigh", rayleigh),
   ("flick", flick), ("gforce", gforce), ("galileo", galileo), ("eotvos", eotvos),
   ("darcy", darcy), ("poise", poise), ("reyn", reyn), ("stokes", stokes), ("rayl", rayl),
   ("mpge", mpge), ("langley", langley), ("jansky", jansky), ("solarflux", solarflux),
   ("curie", curie), ("gray", gray), ("roentgen", roentgen), ("rem", remU)]

/-- System prefixes and other unexported one-argument functions. -/
def extraFunctions : List (String × (UnitSystem α → α)) :=
  [("amagat", amagat), ("thermalconductivity_water", thermalconductivity_water),
   ("deka", dekaU), ("hecto", hectoU), ("kilo", kiloU), ("mega", megaU), ("giga", gigaU),
   ("tera", teraU), ("peta", petaU), ("exa", exaU), ("zetta", zettaU), ("yotta", yottaU),
   ("deci", deciU), ("centi", centiU), ("milli", milliU), ("micro", microU), ("nano", nanoU),
   ("pico", picoU), ("femto", femtoU), ("atto", attoU), ("zepto", zeptoU), ("yocto", yoctoU),
   ("kibi", kibiU), ("mebi", mebiU), ("gibi", gibiU), ("tebi", tebiU), ("pebi", pebiU),
   ("exbi", exbiU), ("zebi", zebiU), ("yobi", yobiU), ("one", oneU), ("zero", zeroU)]

/-- Every one-argument function of a system, by Julia name. -/
def scalarFunctions : List (String × (UnitSystem α → α)) :=
  dimensionlessFunctions ++ constantFunctions ++ physicsFunctions ++ derivedFunctions ++ extraFunctions

/-- Julia `sackurtetrode(U, P=atmosphere(U), T=kelvin(U), m=dalton(U))`
(`initdata.jl:30`), the Sackur–Tetrode entropy constant (not a monomial, so it
exists for `Num` only). -/
def sackurtetrode (U : UnitSystem Num) (P : Num := atmosphere U) (T : Num := kelvin U)
    (m : Num := dalton U) : Num :=
  let e52 : Num := .c (.float (JuliaBase.F64.exp 2.5))
  let inner := e52 * boltzmann U *
    UnitAlg.sqrt (boltzmann U / gravity U / turn U / planckreduced U ^ (2 : Int)) ^ (3 : Int)
  let arg := inner * (T / P * UnitAlg.sqrt (m * T) ^ (3 : Int))
  ⟨arg.v.log, arg.const⟩

/-- Module-level numeric constants of UnitSystems (Julia names). -/
def moduleConstants : List (String × Num) :=
  let N := Num
  [("g₀", ms N .g₀), ("atm", ms N .atm), ("T₀", ms N .T₀), ("ft", ms N .ft), ("ftUS", ms N .ftUS),
   ("lb", ms N .lb), ("inHg", ms N .inHg), ("Ωᵢₜ", ms N .Ωᵢₜ), ("Vᵢₜ", ms N .Vᵢₜ),
   ("ΔνCs", ms N .ΔνCs), ("Kcd", ms N .Kcd), ("mP", ms N .mP), ("αinv", ms N .αinv),
   ("R∞", ms N .Rinf), ("NA", ms N .NA), ("kB", ms N .kB), ("𝘩", ms N .hh), ("𝘤", ms N .cc),
   ("𝘦", ms N .ee), ("α", ms N .α), ("μₑᵤ", ms N .μₑᵤ), ("μₚᵤ", ms N .μₚᵤ), ("μE☾", ms N .μE),
   ("RK1990", ms N .RK1990), ("KJ1990", ms N .KJ1990), ("Rᵤ2014", ms N .Rᵤ2014),
   ("RK2014", ms N .RK2014), ("KJ2014", ms N .KJ2014), ("GME", ms N .GME), ("GMJ", ms N .GMJ),
   ("kG", ms N .kG), ("H0", ms N .H0), ("ΩΛ", ms N .ΩΛ), ("aⱼ", ms N .aⱼ), ("au", ms N .au),
   ("LD", ms N .LD), ("JD", ms N .JD), ("zetta", ms N .zetta), ("zepto", ms N .zepto),
   ("yotta", ms N .yotta), ("yocto", ms N .yocto), ("τ", UnitAlg.tau),
   ("deka", deka N), ("byte", byte N), ("sixty", sixty N), ("hecto", hecto N), ("kilo", kilo N),
   ("mega", mega N), ("giga", giga N), ("tera", tera N), ("peta", peta N), ("exa", exa N),
   ("deci", deci N), ("centi", centi N), ("milli", milli N), ("micro", micro N), ("nano", nano N),
   ("pico", pico N), ("femto", femto N), ("atto", atto N), ("kibi", kibi N), ("mebi", mebi N),
   ("gibi", gibi N), ("tebi", tebi N), ("pebi", pebi N), ("exbi", exbi N), ("zebi", zebi N),
   ("yobi", yobi N), ("fur", fur N), ("°R", degR N), ("K", degK N), ("HOUR", HOUR N),
   ("k", kGauss N), ("mₑ", mₑ N), ("μ₀", μ₀ N), ("ħ", ħ N), ("μₚₑ", μₚₑ N), ("μₑₚ", μₑₚ N),
   ("Rᵤ", Rᵤ N), ("αL", αL N), ("αG", αG N), ("Mᵤ", Mᵤ N), ("pc", pc N), ("G", G N),
   ("DAY", DAY N), ("nm", nm N), ("GM☉", GMsun N), ("th", th N), ("ΛC", ΛC N), ("lc", lc N),
   ("mc", mc N), ("ρΛ", ρΛ N), ("𝘦ₙ", eₙ N), ("ς", ς N), ("lcq", lcq N), ("mcq", mcq N),
   ("𝘦ᵣ", eᵣ N), ("tcq", tcq N), ("em", em N), ("mi", mi N),
   ("slug", ms N .lb * ms N .g₀ / ms N .ft), ("lbm", ms N .g₀ / ms N .ft),
   ("lbmUS", ms N .g₀ / ms N .ftUS), ("rankine", degR N), ("kelvin", degK N),
   ("ħ1990", planckreduced (Conventional N)), ("ħ2014", planckreduced (CODATA N)),
   ("mₑ1990", electronmass (Conventional N)), ("mₑ2014", electronmass (CODATA N)),
   ("δμ₀", μ₀ N - .p (.float (4.0 * 3.141592653589793 * 1e-7))),
   ("ly", ms N .aⱼ * ms N .cc * DAY N), ("mₛ", GMsun N / G N), ("GG", G N),
   ("RK", klitzing (SI2019 N)), ("KJ", josephson (SI2019 N)), ("eV", electronvolt (SI2019 N)),
   ("κ", einstein (SI2019 N)), ("σ", stefan (SI2019 N)), ("μB", magneton (SI2019 N)),
   ("ε₀", vacuumpermittivity (SI2019 N)), ("kₑ", electrostatic (SI2019 N)),
   ("mₚ", protonmass (SI2019 N)), ("Da", dalton (SI2019 N)), ("𝔉", faraday (SI2019 N)),
   ("Φ₀", magneticfluxquantum (SI2019 N)), ("Z₀", vacuumimpedance (SI2019 N)),
   ("G₀", conductancequantum (SI2019 N)), ("Eₕ", hartree (SI2019 N)), ("a₀", bohr (SI2019 N)),
   ("rₑ", electronradius (SI2019 N)),
   ("RH", ms N .Rinf * protonmass (SI2019 N) / (electronmass (SI2019 N) + protonmass (SI2019 N))),
   ("Ry", ms N .hh * ms N .cc * ms N .Rinf),
   ("ℓP", Convert.length (PlanckGauss N) (SI2019 N)), ("tP", Convert.time (PlanckGauss N) (SI2019 N)),
   ("TP", Convert.temperature (PlanckGauss N) (SI2019 N)),
   ("lS", Convert.length (Stoney N) (SI2019 N)), ("tS", Convert.time (Stoney N) (SI2019 N)),
   ("mS", Convert.mass (Stoney N) (SI2019 N)), ("qS", Convert.charge (Stoney N) (SI2019 N)),
   ("lA", Convert.length (Hartree N) (SI2019 N)), ("tA", Convert.time (Hartree N) (SI2019 N)),
   ("mA", Convert.mass (Hartree N) (SI2019 N)), ("qA", Convert.charge (Hartree N) (SI2019 N)),
   ("lQCD", Convert.length (QCD N) (SI2019 N)), ("tQCD", Convert.time (QCD N) (SI2019 N)),
   ("mQCD", Convert.mass (QCD N) (SI2019 N)), ("BTU", thermalunit (British N)),
   ("BTUJ", thermalunit (SI2019 N)), ("HP", horsepower (Metric N)), ("gal", gallon (Metric N)),
   ("kcal", kilocalorie (SI2019 N)), ("cal", calorie (SI2019 N))]

end UnitSystems
