import Tests.Similitude.Common

/-!
# Similitude: the exact constants group

Against `oracle/golden/similitude/constants.json`: the 44 generators, random
monomials with every coefficient kind, `factorize` of integers and floats, the
named constants of `initdata.jl` evaluated over `Scalar`, and Julia's `+`/`-`
rules for constants. Printed strings must match exactly and `product` bit for
bit.
-/

namespace Tests.SimilitudeTests

open Lean Tests.Units FieldConstants FieldAlgebra UnitSystems Similitude

/-- `initdata.jl` module constants, by Julia name, evaluated over `Scalar`. -/
def namedConstants : List (String × Scalar) :=
  let S := Scalar
  [("mₑ", mₑ S), ("μ₀", μ₀ S), ("ħ", ħ S), ("αinv", ms S .αinv), ("αG", αG S), ("Mᵤ", Mᵤ S),
   ("μₚₑ", μₚₑ S), ("μₑₚ", μₑₚ S), ("Rᵤ", Rᵤ S), ("G", G S), ("GM☉", GMsun S), ("pc", pc S),
   ("em", em S), ("nm", nm S), ("fur", fur S), ("°R", degR S), ("K", degK S), ("k", kGauss S),
   ("th", th S), ("ΛC", ΛC S), ("lc", lc S), ("mc", mc S), ("ρΛ", ρΛ S), ("𝘦ₙ", eₙ S), ("ς", ς S),
   ("lcq", lcq S), ("mcq", mcq S), ("tcq", tcq S), ("𝘦ᵣ", eᵣ S), ("LD", ms S .LD), ("JD", ms S .JD),
   ("milli", milli S), ("kilo", kilo S), ("mega", mega S), ("giga", giga S), ("kibi", kibi S),
   ("zetta", ms S .zetta), ("zepto", ms S .zepto), ("yotta", ms S .yotta), ("yocto", ms S .yocto),
   ("DAY", DAY S), ("HOUR", HOUR S), ("deka", deka S), ("hecto", hecto S), ("centi", centi S),
   ("nano", nano S), ("zebi", zebi S), ("αL", UnitSystems.αL S)]

/-- Check a printed value and its float value against a golden row `[…, show, bits]`. -/
def checkValue (s : Suite) (what : String) (got : Scalar) (shown : Json) (bits : Json) : Suite :=
  let want := str shown
  let s := s.check (got.toString == want) fun _ => s!"{what}: got {got}, want {want}"
  match goldFloat? bits with
  | some f => s.check (sameBits got.toFloat f) fun _ =>
      s!"{what}: product {hexOf got.toFloat}, want {hexOf f}"
  | none => s

/-- Run the constants-group checks. -/
def constantsSuite : IO Suite := do
  let j ← loadJson "similitude/constants.json"
  let mut s : Suite := { name := "constants group" }
  for r in arr (fld j "basis") do
    let i := (int (idx r 0)).toNat - 1
    if h : i < 44 then
      s := checkValue s s!"basis {i + 1}" (.grp (Consts.gen i h)) (idx r 1) (idx r 2)
  for r in arr (fld j "random") do
    let g := constsOf r
    if str (idx r 2) == "ERROR" then
      -- `φ`/`γ` to a negative integer power: Julia throws `DomainError`, the port gives `NaN`
      s := s.check g.product.isNaN fun _ => s!"random {str (idx r 0)}: expected NaN"
    else
      s := checkValue s s!"random {str (idx r 0)}" (.grp g) (idx r 2) (idx r 3)
  for r in arr (fld j "factorize_int") do
    let x := int (idx r 0)
    s := checkValue s s!"factorize({x})" (.grp (Consts.factorize x)) (idx r 1) (idx r 2)
  for r in arr (fld j "factorize_float") do
    let x := hexFloat (idx r 0)
    s := checkValue s s!"factorize({x})" (.grp (Consts.factorizeF x)) (idx r 1) (idx r 2)
  for r in arr (fld j "named") do
    let nm := str (idx r 0)
    match namedConstants.lookup nm with
    | some v => s := checkValue s nm v (idx r 1) (idx r 2)
    | none => s := s.check false fun _ => s!"no Lean constant {nm}"
  for r in arr (fld j "addsub") do
    let a := Scalar.grp (constsOf (idx r 0))
    let b := Scalar.grp (constsOf (idx r 1))
    let (sum, dif) := (str (idx r 2), str (idx r 3))
    s := s.check ((a + b).toString == sum) fun _ => s!"{a} + {b}: got {a + b}, want {sum}"
    s := s.check ((a - b).toString == dif) fun _ => s!"{a} - {b}: got {a - b}, want {dif}"
  return s

end Tests.SimilitudeTests
