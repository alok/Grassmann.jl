import UnitSystems.Dim
import UnitSystems.Registry

/-!
# The exponent model: unit systems whose constants are their own dimensions

Every UnitSystems formula is generic in the scalar (`UnitAlg`). Instantiated
with `HalfDim`, an exponent vector where multiplication adds exponents, powers
scale them and `sqrt` halves them, the formulas compute *dimensions* instead of
numbers: numeric literals and measured constants are dimensionless, and the
dimension of a quantity `q` is `q(Natural, U)` for the symbolic system `U` whose
constants carry their USQ dimensions (Similitude's `Unified`,
`Similitude.jl:157`).

Exponents are half-integers in general (a charge ratio is a square root), so
`HalfDim` stores twice each exponent as an `Int`: exact, and cheap enough for
the kernel to evaluate whole conversion chains in `decide` proofs
(`UnitSystems.DimProofs`).

`usqToConst` is Similitude's `UnitSystem(d)` (`dimension.jl:466-493`): the
exponents over the eleven defining constants of a quantity of USQ dimension `d`.
-/

namespace UnitSystems

/-- Eleven half-integer exponents, stored doubled. Interpreted either as a USQ
dimension (`F M L T Q Θ N J A R C`) or as exponents over the defining constants
(`kB ħ 𝘤 μ₀ mₑ Mᵤ Kcd θ λ αL g₀`). -/
structure HalfDim where
  /-- slot 0 (F / kB), doubled -/ a0 : Int := 0
  /-- slot 1 (M / ħ), doubled -/ a1 : Int := 0
  /-- slot 2 (L / 𝘤), doubled -/ a2 : Int := 0
  /-- slot 3 (T / μ₀), doubled -/ a3 : Int := 0
  /-- slot 4 (Q / mₑ), doubled -/ a4 : Int := 0
  /-- slot 5 (Θ / Mᵤ), doubled -/ a5 : Int := 0
  /-- slot 6 (N / Kcd), doubled -/ a6 : Int := 0
  /-- slot 7 (J / θ), doubled -/ a7 : Int := 0
  /-- slot 8 (A / λ), doubled -/ a8 : Int := 0
  /-- slot 9 (R / αL), doubled -/ a9 : Int := 0
  /-- slot 10 (C / g₀), doubled -/ a10 : Int := 0
  deriving DecidableEq, Inhabited

namespace HalfDim

/-- Pointwise binary operation. -/
@[inline] def zip (f : Int → Int → Int) (x y : HalfDim) : HalfDim :=
  ⟨f x.a0 y.a0, f x.a1 y.a1, f x.a2 y.a2, f x.a3 y.a3, f x.a4 y.a4, f x.a5 y.a5,
   f x.a6 y.a6, f x.a7 y.a7, f x.a8 y.a8, f x.a9 y.a9, f x.a10 y.a10⟩

/-- Pointwise map. -/
@[inline] def map (f : Int → Int) (x : HalfDim) : HalfDim :=
  ⟨f x.a0, f x.a1, f x.a2, f x.a3, f x.a4, f x.a5, f x.a6, f x.a7, f x.a8, f x.a9, f x.a10⟩

/-- The doubled exponents of a USQ dimension. -/
def ofDim (d : Dim) : HalfDim :=
  let e (n : Nat) : Int := ((n : Int) - dimBias) / 6
  ⟨e d.F, e d.M, e d.L, e d.T, e d.Q, e d.Θ, e d.N, e d.J, e d.A, e d.R, e d.C⟩

/-- The doubled exponents as a list. -/
def toList (x : HalfDim) : List Int := [x.a0, x.a1, x.a2, x.a3, x.a4, x.a5, x.a6, x.a7, x.a8, x.a9, x.a10]

/-- Unit vector `2·eᵢ` (exponent one in slot `i`). -/
def basis (i : Nat) : HalfDim :=
  let e (j : Nat) : Int := if i == j then 2 else 0
  ⟨e 0, e 1, e 2, e 3, e 4, e 5, e 6, e 7, e 8, e 9, e 10⟩

instance : ToString HalfDim :=
  ⟨fun x => toString (x.toList.map fun (v : Int) => if v % 2 == 0 then toString (v / 2) else s!"{v}/2")⟩

end HalfDim

/-- The exponent model of UnitSystems' formulas: products add exponents,
literals and measured constants are dimensionless, `unit(…)` snaps are
identities and Julia's `+` of equal dimensions returns its left operand. -/
instance : UnitAlg HalfDim where
  mul := HalfDim.zip (· + ·)
  div := HalfDim.zip (· - ·)
  add x _ := x
  sub x _ := x
  beq x y := decide (x = y)
  default := {}
  inv := HalfDim.map (- ·)
  lpow x n := HalfDim.map (n * ·) x
  sqrt := HalfDim.map (· / 2)
  ilit _ := {}
  flit _ := {}
  tau := {}
  measured _ := {}
  snap x _ := x
  isOne x := decide (x = {})
  ident x y := decide (x = y)
  eqFloat _ _ := false

/-- The dimensionless coupling. -/
def trivialCoupling : Coupling HalfDim := ⟨{}, {}, {}, {}, {}⟩

/-- Similitude's `Unified` system: each constant carries its USQ dimension
(`Similitude.jl:157`): `kB: FLΘ⁻¹`, `ħ: FLTA⁻¹`, `𝘤: LT⁻¹`, `μ₀: FT²Q⁻²R⁻¹C²`,
`mₑ: M`, `Mᵤ: MN⁻¹`, `Kcd: F⁻¹L⁻¹TJ`, `θ: A`, `λ: R`, `αL: C⁻¹`, `g₀: F⁻¹MLT⁻²`. -/
def unifiedUSQ : UnitSystem HalfDim :=
  open USQ in
  { kB := .ofDim (F * L / Θ), ħ := .ofDim (F * L * T / A), c := .ofDim (L / T),
    μ₀ := .ofDim (F * T ^ 2 * C ^ 2 / (Q ^ 2 * R)), mₑ := .ofDim M, Mᵤ := .ofDim (M / N),
    Kcd := .ofDim (T * J / (F * L)), θ := .ofDim A, lam := .ofDim R, αL := .ofDim C⁻¹,
    g₀ := .ofDim (M * L / (F * T ^ 2)), C := trivialCoupling }

/-- The symbolic system whose constants are the eleven basis vectors: formulas
evaluated in it give exponents over `kB ħ 𝘤 μ₀ mₑ Mᵤ Kcd θ λ αL g₀`. -/
def unifiedConst : UnitSystem HalfDim :=
  { kB := .basis 0, ħ := .basis 1, c := .basis 2, μ₀ := .basis 3, mₑ := .basis 4,
    Mᵤ := .basis 5, Kcd := .basis 6, θ := .basis 7, lam := .basis 8, αL := .basis 9,
    g₀ := .basis 10, C := trivialCoupling }

/-- Similitude's fundamental isomorphism `UnitSystem(d)` (`dimension.jl:466-493`):
the doubled exponents over the eleven constants of a quantity with USQ
dimension `d`, so that `ratio = ∏ₖ (cₖ(S)/cₖ(U))^eₖ`. -/
def usqToConst (d : Dim) : HalfDim :=
  match d.toInts with
  | [F, M, L, T, Q, Θ, N, J, A, R, C] =>
    ⟨2 * -Θ, 2 * (L + T - F - J) + Q, 2 * (3 * F + 2 * Θ + 4 * J - L - 2 * T) - Q, -Q,
     2 * (M + Θ + N + 2 * (F + J) - L - T), 2 * -N, 2 * J, 2 * (L + T + A - F - J) + Q, 2 * R - Q,
     2 * -(Q + C), 2 * (L + T - Θ - 2 * (F + J))⟩
  | _ => {}

/-- The inverse direction: USQ dimension of a product of constants, `Σₖ eₖ·dim(cₖ)`
(the matrix `Dc` of `docs/port-notes/unitsystems.md` §4.6), on doubled vectors. -/
def constToUsq (e : HalfDim) : HalfDim :=
  let cs := [unifiedUSQ.kB, unifiedUSQ.ħ, unifiedUSQ.c, unifiedUSQ.μ₀, unifiedUSQ.mₑ, unifiedUSQ.Mᵤ,
    unifiedUSQ.Kcd, unifiedUSQ.θ, unifiedUSQ.lam, unifiedUSQ.αL, unifiedUSQ.g₀]
  (e.toList.zip cs).foldl (fun acc (k, v) => HalfDim.zip (· + ·) acc (HalfDim.map (fun x => k * x / 2) v)) {}

/-- The dimension a formula computes: evaluate it on the `Unified` system. -/
def dimOf (f : UnitSystem HalfDim → HalfDim) : HalfDim := f unifiedUSQ

/-- The exponents over the defining constants a formula computes. -/
def constExpsOf (f : UnitSystem HalfDim → HalfDim) : HalfDim := f unifiedConst

/-- Dimension of a conversion factor `q(U,S)`: `q(Natural, Unified)`. -/
def Conv.dimModel (q : Conv) : HalfDim := q.factor (Natural HalfDim) unifiedUSQ

/-- Constant exponents of a conversion factor: `q(Natural, constants)`. -/
def Conv.constModel (q : Conv) : HalfDim := q.factor (Natural HalfDim) unifiedConst

/-- Doubled USQ exponents of every monomial one-argument function, recovered from the
oracle by a log-linear fit (`oracle/unitsystems/dims.jl`). -/
def scalarDimTable : List (String × HalfDim) := [
  ("coupling", ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("finestructure", ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("electronunit", ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("protonunit", ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("protonelectron", ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("darkenergydensity", ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("lightspeed", ⟨0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0⟩),
  ("planck", ⟨2, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0⟩),
  ("planckreduced", ⟨2, 0, 2, 2, 0, 0, 0, 0, -2, 0, 0⟩),
  ("electronmass", ⟨0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("molarmass", ⟨0, 2, 0, 0, 0, 0, -2, 0, 0, 0, 0⟩),
  ("boltzmann", ⟨2, 0, 2, 0, 0, -2, 0, 0, 0, 0, 0⟩),
  ("vacuumpermeability", ⟨2, 0, 0, 4, -4, 0, 0, 0, 0, -2, 4⟩),
  ("rationalization", ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0⟩),
  ("lorentz", ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2⟩),
  ("luminousefficacy", ⟨-2, 0, -2, 2, 0, 0, 0, 2, 0, 0, 0⟩),
  ("gravity", ⟨-2, 2, 2, -4, 0, 0, 0, 0, 0, 0, 0⟩),
  ("radian", ⟨0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0⟩),
  ("turn", ⟨0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0⟩),
  ("spat", ⟨0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0⟩),
  ("dalton", ⟨0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("protonmass", ⟨0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("planckmass", ⟨0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("gravitation", ⟨2, -4, 4, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("gaussgravitation", ⟨0, 0, 0, -2, 0, 0, 0, 0, 2, 0, 0⟩),
  ("einstein", ⟨2, -4, -4, 8, 0, 0, 0, 0, 0, 0, 0⟩),
  ("hartree", ⟨2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("rydberg", ⟨0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("bohr", ⟨0, 0, 2, 0, 0, 0, 0, 0, -2, 0, 0⟩),
  ("electronradius", ⟨0, 0, 2, 0, 0, 0, 0, 0, -2, 0, 0⟩),
  ("avogadro", ⟨0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0⟩),
  ("molargas", ⟨2, 0, 2, 0, 0, -2, -2, 0, 0, 0, 0⟩),
  ("stefan", ⟨2, 0, -2, -2, 0, -8, 0, 0, 0, 0, 0⟩),
  ("radiationdensity", ⟨2, 0, -4, 0, 0, -8, 0, 0, 0, 0, 0⟩),
  ("vacuumpermittivity", ⟨-2, 0, -4, 0, 4, 0, 0, 0, 0, 2, 0⟩),
  ("electrostatic", ⟨2, 0, 4, 0, -4, 0, 0, 0, 0, 0, 0⟩),
  ("magnetostatic", ⟨2, 0, 0, 4, -4, 0, 0, 0, 0, 0, 0⟩),
  ("biotsavart", ⟨2, 0, 0, 4, -4, 0, 0, 0, 0, 0, 2⟩),
  ("elementarycharge", ⟨0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0⟩),
  ("faraday", ⟨0, 0, 0, 0, 2, 0, -2, 0, 0, 0, 0⟩),
  ("vacuumimpedance", ⟨2, 0, 2, 2, -4, 0, 0, 0, 0, 0, 0⟩),
  ("conductancequantum", ⟨-2, 0, -2, -2, 4, 0, 0, 0, 0, 0, 0⟩),
  ("klitzing", ⟨2, 0, 2, 2, -4, 0, 0, 0, 0, 0, 0⟩),
  ("josephson", ⟨-2, 0, -2, -2, 2, 0, 0, 0, 0, 0, -2⟩),
  ("magneticfluxquantum", ⟨2, 0, 2, 2, -2, 0, 0, 0, 0, 0, 2⟩),
  ("magneton", ⟨2, -2, 2, 2, 2, 0, 0, 0, -2, 0, -2⟩),
  ("hyperfine", ⟨0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0⟩),
  ("loschmidt", ⟨0, 0, -6, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("wienwavelength", ⟨0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0⟩),
  ("wienfrequency", ⟨0, 0, 0, -2, 0, -2, 0, 0, 0, 0, 0⟩),
  ("mechanicalheat", ⟨2, 0, 2, 0, 0, -2, -2, 0, 0, 0, 0⟩),
  ("eddington", ⟨0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("solarmass", ⟨0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("jupitermass", ⟨0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("earthmass", ⟨0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("lunarmass", ⟨0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("earthradius", ⟨0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("greatcircle", ⟨0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0⟩),
  ("radarmile", ⟨0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0⟩),
  ("hubble", ⟨0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0⟩),
  ("cosmological", ⟨0, 0, -4, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("steradian", ⟨0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0⟩),
  ("spatian", ⟨0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0⟩),
  ("degree", ⟨0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0⟩),
  ("squaredegree", ⟨0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0⟩),
  ("gradian", ⟨0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0⟩),
  ("bradian", ⟨0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0⟩),
  ("arcminute", ⟨0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0⟩),
  ("arcsecond", ⟨0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0⟩),
  ("second", ⟨0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0⟩),
  ("minute", ⟨0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0⟩),
  ("hour", ⟨0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0⟩),
  ("day", ⟨0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0⟩),
  ("gaussianmonth", ⟨0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0⟩),
  ("siderealmonth", ⟨0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0⟩),
  ("synodicmonth", ⟨0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0⟩),
  ("year", ⟨0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0⟩),
  ("gaussianyear", ⟨0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0⟩),
  ("siderealyear", ⟨0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0⟩),
  ("jovianyear", ⟨-1, 1, 1, 2, 0, 0, 0, 0, 0, 0, 0⟩),
  ("angstrom", ⟨0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("inch", ⟨0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("foot", ⟨0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("surveyfoot", ⟨0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("yard", ⟨0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("meter", ⟨0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("earthmeter", ⟨0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("mile", ⟨0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("statutemile", ⟨0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("meridianmile", ⟨0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("admiraltymile", ⟨0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("nauticalmile", ⟨0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("lunardistance", ⟨0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("astronomicalunit", ⟨0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("jupiterdistance", ⟨0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("lightyear", ⟨0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("parsec", ⟨0, 0, 2, 0, 0, 0, 0, 0, -2, 0, 0⟩),
  ("barn", ⟨0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("hectare", ⟨0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("acre", ⟨0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("surveyacre", ⟨0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("liter", ⟨0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("gallon", ⟨0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("quart", ⟨0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("pint", ⟨0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("cup", ⟨0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("fluidounce", ⟨0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("teaspoon", ⟨0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("tablespoon", ⟨0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("bubnoff", ⟨0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0⟩),
  ("ips", ⟨0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0⟩),
  ("fps", ⟨0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0⟩),
  ("fpm", ⟨0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0⟩),
  ("ms", ⟨0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0⟩),
  ("kmh", ⟨0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0⟩),
  ("mph", ⟨0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0⟩),
  ("knot", ⟨0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0⟩),
  ("mps", ⟨0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0⟩),
  ("grain", ⟨0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("gram", ⟨0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("earthgram", ⟨0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("kilogram", ⟨0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("tonne", ⟨0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("ton", ⟨0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("pound", ⟨0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("ounce", ⟨0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("slug", ⟨0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("slinch", ⟨0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("hyl", ⟨0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("dyne", ⟨2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("newton", ⟨2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("poundal", ⟨2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("poundforce", ⟨2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("kilopond", ⟨2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("psi", ⟨2, 0, -4, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("pascal", ⟨2, 0, -4, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("bar", ⟨2, 0, -4, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("barye", ⟨2, 0, -4, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("technicalatmosphere", ⟨2, 0, -4, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("atmosphere", ⟨2, 0, -4, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("inchmercury", ⟨2, 0, -4, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("torr", ⟨2, 0, -4, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("electronvolt", ⟨2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("erg", ⟨2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("joule", ⟨2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("footpound", ⟨2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("calorie", ⟨2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("kilocalorie", ⟨2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("meancalorie", ⟨2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("earthcalorie", ⟨2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("thermalunit", ⟨2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("gasgallon", ⟨2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("tontnt", ⟨2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("watt", ⟨2, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0⟩),
  ("horsepower", ⟨2, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0⟩),
  ("horsepowerwatt", ⟨2, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0⟩),
  ("horsepowermetric", ⟨2, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0⟩),
  ("electricalhorsepower", ⟨2, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0⟩),
  ("tonsrefrigeration", ⟨2, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0⟩),
  ("boilerhorsepower", ⟨2, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0⟩),
  ("coulomb", ⟨0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0⟩),
  ("earthcoulomb", ⟨0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0⟩),
  ("ampere", ⟨0, 0, 0, -2, 2, 0, 0, 0, 0, 0, 0⟩),
  ("volt", ⟨2, 0, 2, 0, -2, 0, 0, 0, 0, 0, 0⟩),
  ("henry", ⟨2, 0, 2, 4, -4, 0, 0, 0, 0, 0, 0⟩),
  ("ohm", ⟨2, 0, 2, 2, -4, 0, 0, 0, 0, 0, 0⟩),
  ("siemens", ⟨-2, 0, -2, -2, 4, 0, 0, 0, 0, 0, 0⟩),
  ("farad", ⟨-2, 0, -2, 0, 4, 0, 0, 0, 0, 0, 0⟩),
  ("weber", ⟨2, 0, 2, 2, -2, 0, 0, 0, 0, 0, 2⟩),
  ("tesla", ⟨2, 0, -2, 2, -2, 0, 0, 0, 0, 0, 2⟩),
  ("abcoulomb", ⟨0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0⟩),
  ("abampere", ⟨0, 0, 0, -2, 2, 0, 0, 0, 0, 0, 0⟩),
  ("abvolt", ⟨2, 0, 2, 0, -2, 0, 0, 0, 0, 0, 0⟩),
  ("abhenry", ⟨2, 0, 2, 4, -4, 0, 0, 0, 0, 0, 0⟩),
  ("abohm", ⟨2, 0, 2, 2, -4, 0, 0, 0, 0, 0, 0⟩),
  ("abmho", ⟨-2, 0, -2, -2, 4, 0, 0, 0, 0, 0, 0⟩),
  ("abfarad", ⟨-2, 0, -2, 0, 4, 0, 0, 0, 0, 0, 0⟩),
  ("maxwell", ⟨2, 0, 2, 2, -2, 0, 0, 0, 0, 0, 2⟩),
  ("gauss", ⟨2, 0, -2, 2, -2, 0, 0, 0, 0, 0, 2⟩),
  ("oersted", ⟨0, 0, -2, -2, 2, 0, 0, 0, 0, 2, -2⟩),
  ("gilbert", ⟨0, 0, 0, -2, 2, 0, 0, 0, -2, 0, 0⟩),
  ("statcoulomb", ⟨0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0⟩),
  ("statampere", ⟨0, 0, 0, -2, 2, 0, 0, 0, 0, 0, 0⟩),
  ("statvolt", ⟨2, 0, 2, 0, -2, 0, 0, 0, 0, 0, 0⟩),
  ("stathenry", ⟨2, 0, 2, 4, -4, 0, 0, 0, 0, 0, 0⟩),
  ("statohm", ⟨2, 0, 2, 2, -4, 0, 0, 0, 0, 0, 0⟩),
  ("statmho", ⟨-2, 0, -2, -2, 4, 0, 0, 0, 0, 0, 0⟩),
  ("statfarad", ⟨-2, 0, -2, 0, 4, 0, 0, 0, 0, 0, 0⟩),
  ("statweber", ⟨2, 0, 2, 2, -2, 0, 0, 0, 0, 0, 2⟩),
  ("stattesla", ⟨2, 0, -2, 2, -2, 0, 0, 0, 0, 0, 2⟩),
  ("kelvin", ⟨0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0⟩),
  ("rankine", ⟨0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0⟩),
  ("celsius", ⟨0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0⟩),
  ("fahrenheit", ⟨0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0⟩),
  ("sealevel", ⟨0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0⟩),
  ("boiling", ⟨0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0⟩),
  ("mole", ⟨0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0⟩),
  ("earthmole", ⟨0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0⟩),
  ("poundmole", ⟨0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0⟩),
  ("slugmole", ⟨0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0⟩),
  ("slinchmole", ⟨0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0⟩),
  ("katal", ⟨0, 0, 0, -2, 0, 0, 2, 0, 0, 0, 0⟩),
  ("amagat", ⟨0, 0, -6, 0, 0, 0, 2, 0, 0, 0, 0⟩),
  ("lumen", ⟨0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0⟩),
  ("candela", ⟨0, 0, 0, 0, 0, 0, 0, 2, -4, 0, 0⟩),
  ("lux", ⟨0, 0, -4, 0, 0, 0, 0, 2, 0, 0, 0⟩),
  ("phot", ⟨0, 0, -4, 0, 0, 0, 0, 2, 0, 0, 0⟩),
  ("footcandle", ⟨0, 0, -4, 0, 0, 0, 0, 2, 0, 0, 0⟩),
  ("nit", ⟨0, 0, -4, 0, 0, 0, 0, 2, -4, 0, 0⟩),
  ("apostilb", ⟨0, 0, -4, 0, 0, 0, 0, 2, -6, 0, 0⟩),
  ("stilb", ⟨0, 0, -4, 0, 0, 0, 0, 2, -4, 0, 0⟩),
  ("lambert", ⟨0, 0, -4, 0, 0, 0, 0, 2, -6, 0, 0⟩),
  ("footlambert", ⟨0, 0, -4, 0, 0, 0, 0, 2, -6, 0, 0⟩),
  ("bril", ⟨0, 0, -4, 0, 0, 0, 0, 2, -6, 0, 0⟩),
  ("talbot", ⟨0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0⟩),
  ("lumerg", ⟨0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0⟩),
  ("hertz", ⟨0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0⟩),
  ("apm", ⟨0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0⟩),
  ("rpm", ⟨0, 0, 0, -2, 0, 0, 0, 0, 2, 0, 0⟩),
  ("kayser", ⟨0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("diopter", ⟨0, 0, -2, 0, 0, 0, 0, 0, 2, 0, 0⟩),
  ("rayleigh", ⟨0, 0, -4, 2, 0, 0, 0, 0, 0, 0, 0⟩),
  ("flick", ⟨2, 0, -4, -2, 0, 0, 0, 0, -4, 0, 0⟩),
  ("gforce", ⟨2, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("galileo", ⟨2, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("eotvos", ⟨2, -2, -2, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("darcy", ⟨0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("poise", ⟨2, 0, -4, 2, 0, 0, 0, 0, 0, 0, 0⟩),
  ("reyn", ⟨2, 0, -4, 2, 0, 0, 0, 0, 0, 0, 0⟩),
  ("stokes", ⟨0, 0, 4, -2, 0, 0, 0, 0, 0, 0, 0⟩),
  ("rayl", ⟨2, 0, -6, 2, 0, 0, 0, 0, 0, 0, 0⟩),
  ("mpge", ⟨-2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("langley", ⟨2, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("jansky", ⟨2, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("solarflux", ⟨2, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("curie", ⟨0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0⟩),
  ("gray", ⟨2, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("roentgen", ⟨0, -2, 0, 0, 2, 0, 0, 0, 0, 0, 0⟩),
  ("rem", ⟨2, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("thermalconductivity_water", ⟨0, 0, -2, -2, 0, -2, 0, 0, 0, 0, 0⟩)]

/-- Doubled exponents over the eleven defining constants of every monomial
one-argument function (same fit). -/
def scalarConstTable : List (String × HalfDim) := [
  ("coupling", ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("finestructure", ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("electronunit", ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("protonunit", ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("protonelectron", ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("darkenergydensity", ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("lightspeed", ⟨0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("planck", ⟨0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0⟩),
  ("planckreduced", ⟨0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("electronmass", ⟨0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0⟩),
  ("molarmass", ⟨0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0⟩),
  ("boltzmann", ⟨2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("vacuumpermeability", ⟨0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0⟩),
  ("rationalization", ⟨0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0⟩),
  ("lorentz", ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0⟩),
  ("luminousefficacy", ⟨0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0⟩),
  ("gravity", ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2⟩),
  ("radian", ⟨0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0⟩),
  ("turn", ⟨0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0⟩),
  ("spat", ⟨0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0⟩),
  ("dalton", ⟨0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0⟩),
  ("protonmass", ⟨0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0⟩),
  ("planckmass", ⟨0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0⟩),
  ("gravitation", ⟨0, 2, 2, 0, -4, 0, 0, 2, 0, 0, 0⟩),
  ("gaussgravitation", ⟨0, -2, 4, 0, 2, 0, 0, 0, 0, 0, -2⟩),
  ("einstein", ⟨0, 2, -6, 0, -4, 0, 0, 2, 0, 0, 0⟩),
  ("hartree", ⟨0, 0, 4, 0, 2, 0, 0, 0, 0, 0, -2⟩),
  ("rydberg", ⟨0, -2, 2, 0, 2, 0, 0, -2, 0, 0, -2⟩),
  ("bohr", ⟨0, 2, -2, 0, -2, 0, 0, 0, 0, 0, 2⟩),
  ("electronradius", ⟨0, 2, -2, 0, -2, 0, 0, 0, 0, 0, 2⟩),
  ("avogadro", ⟨0, 0, 0, 0, -2, 2, 0, 0, 0, 0, 0⟩),
  ("molargas", ⟨2, 0, 0, 0, -2, 2, 0, 0, 0, 0, 0⟩),
  ("stefan", ⟨8, -6, -4, 0, 0, 0, 0, -6, 0, 0, 0⟩),
  ("radiationdensity", ⟨8, -6, -6, 0, 0, 0, 0, -6, 0, 0, 0⟩),
  ("vacuumpermittivity", ⟨0, 0, -4, -2, 0, 0, 0, 0, 0, -4, 0⟩),
  ("electrostatic", ⟨0, 0, 4, 2, 0, 0, 0, 0, 2, 4, 0⟩),
  ("magnetostatic", ⟨0, 0, 0, 2, 0, 0, 0, 0, 2, 4, 0⟩),
  ("biotsavart", ⟨0, 0, 0, 2, 0, 0, 0, 0, 2, 2, 0⟩),
  ("elementarycharge", ⟨0, 1, -1, -1, 0, 0, 0, 1, -1, -2, 0⟩),
  ("faraday", ⟨0, 1, -1, -1, -2, 2, 0, 1, -1, -2, 0⟩),
  ("vacuumimpedance", ⟨0, 0, 2, 2, 0, 0, 0, 0, 2, 4, 0⟩),
  ("conductancequantum", ⟨0, 0, -2, -2, 0, 0, 0, 0, -2, -4, 0⟩),
  ("klitzing", ⟨0, 0, 2, 2, 0, 0, 0, 0, 2, 4, 0⟩),
  ("josephson", ⟨0, -1, -1, -1, 0, 0, 0, -1, -1, 0, 0⟩),
  ("magneticfluxquantum", ⟨0, 1, 1, 1, 0, 0, 0, 1, 1, 0, 0⟩),
  ("magneton", ⟨0, 3, -1, -1, -2, 0, 0, 1, -1, 0, 0⟩),
  ("hyperfine", ⟨0, -2, 4, 0, 2, 0, 0, -2, 0, 0, -2⟩),
  ("loschmidt", ⟨0, -6, 6, 0, 6, 0, 0, -6, 0, 0, -6⟩),
  ("wienwavelength", ⟨-2, 2, 2, 0, 0, 0, 0, 2, 0, 0, 0⟩),
  ("wienfrequency", ⟨2, -2, 0, 0, 0, 0, 0, -2, 0, 0, 0⟩),
  ("mechanicalheat", ⟨2, 0, 0, 0, -2, 2, 0, 0, 0, 0, 0⟩),
  ("eddington", ⟨0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0⟩),
  ("solarmass", ⟨0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0⟩),
  ("jupitermass", ⟨0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0⟩),
  ("earthmass", ⟨0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0⟩),
  ("lunarmass", ⟨0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0⟩),
  ("earthradius", ⟨0, 2, -2, 0, -2, 0, 0, 2, 0, 0, 2⟩),
  ("greatcircle", ⟨0, 2, -2, 0, -2, 0, 0, 4, 0, 0, 2⟩),
  ("radarmile", ⟨0, 2, -4, 0, -2, 0, 0, 2, 0, 0, 2⟩),
  ("hubble", ⟨0, -2, 4, 0, 2, 0, 0, -2, 0, 0, -2⟩),
  ("cosmological", ⟨0, -4, 4, 0, 4, 0, 0, -4, 0, 0, -4⟩),
  ("steradian", ⟨0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0⟩),
  ("spatian", ⟨0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0⟩),
  ("degree", ⟨0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0⟩),
  ("squaredegree", ⟨0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0⟩),
  ("gradian", ⟨0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0⟩),
  ("bradian", ⟨0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0⟩),
  ("arcminute", ⟨0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0⟩),
  ("arcsecond", ⟨0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0⟩),
  ("second", ⟨0, 2, -4, 0, -2, 0, 0, 2, 0, 0, 2⟩),
  ("minute", ⟨0, 2, -4, 0, -2, 0, 0, 2, 0, 0, 2⟩),
  ("hour", ⟨0, 2, -4, 0, -2, 0, 0, 2, 0, 0, 2⟩),
  ("day", ⟨0, 2, -4, 0, -2, 0, 0, 2, 0, 0, 2⟩),
  ("gaussianmonth", ⟨0, 2, -4, 0, -2, 0, 0, 2, 0, 0, 2⟩),
  ("siderealmonth", ⟨0, 2, -4, 0, -2, 0, 0, 2, 0, 0, 2⟩),
  ("synodicmonth", ⟨0, 2, -4, 0, -2, 0, 0, 2, 0, 0, 2⟩),
  ("year", ⟨0, 2, -4, 0, -2, 0, 0, 2, 0, 0, 2⟩),
  ("gaussianyear", ⟨0, 2, -4, 0, -2, 0, 0, 2, 0, 0, 2⟩),
  ("siderealyear", ⟨0, 2, -4, 0, -2, 0, 0, 2, 0, 0, 2⟩),
  ("jovianyear", ⟨0, 4, -8, 0, -4, 0, 0, 4, 0, 0, 5⟩),
  ("angstrom", ⟨0, 2, -2, 0, -2, 0, 0, 2, 0, 0, 2⟩),
  ("inch", ⟨0, 2, -2, 0, -2, 0, 0, 2, 0, 0, 2⟩),
  ("foot", ⟨0, 2, -2, 0, -2, 0, 0, 2, 0, 0, 2⟩),
  ("surveyfoot", ⟨0, 2, -2, 0, -2, 0, 0, 2, 0, 0, 2⟩),
  ("yard", ⟨0, 2, -2, 0, -2, 0, 0, 2, 0, 0, 2⟩),
  ("meter", ⟨0, 2, -2, 0, -2, 0, 0, 2, 0, 0, 2⟩),
  ("earthmeter", ⟨0, 2, -2, 0, -2, 0, 0, 2, 0, 0, 2⟩),
  ("mile", ⟨0, 2, -2, 0, -2, 0, 0, 2, 0, 0, 2⟩),
  ("statutemile", ⟨0, 2, -2, 0, -2, 0, 0, 2, 0, 0, 2⟩),
  ("meridianmile", ⟨0, 2, -2, 0, -2, 0, 0, 2, 0, 0, 2⟩),
  ("admiraltymile", ⟨0, 2, -2, 0, -2, 0, 0, 2, 0, 0, 2⟩),
  ("nauticalmile", ⟨0, 2, -2, 0, -2, 0, 0, 2, 0, 0, 2⟩),
  ("lunardistance", ⟨0, 2, -2, 0, -2, 0, 0, 2, 0, 0, 2⟩),
  ("astronomicalunit", ⟨0, 2, -2, 0, -2, 0, 0, 2, 0, 0, 2⟩),
  ("jupiterdistance", ⟨0, 2, -2, 0, -2, 0, 0, 2, 0, 0, 2⟩),
  ("lightyear", ⟨0, 2, -2, 0, -2, 0, 0, 2, 0, 0, 2⟩),
  ("parsec", ⟨0, 2, -2, 0, -2, 0, 0, 0, 0, 0, 2⟩),
  ("barn", ⟨0, 4, -4, 0, -4, 0, 0, 4, 0, 0, 4⟩),
  ("hectare", ⟨0, 4, -4, 0, -4, 0, 0, 4, 0, 0, 4⟩),
  ("acre", ⟨0, 4, -4, 0, -4, 0, 0, 4, 0, 0, 4⟩),
  ("surveyacre", ⟨0, 4, -4, 0, -4, 0, 0, 4, 0, 0, 4⟩),
  ("liter", ⟨0, 6, -6, 0, -6, 0, 0, 6, 0, 0, 6⟩),
  ("gallon", ⟨0, 6, -6, 0, -6, 0, 0, 6, 0, 0, 6⟩),
  ("quart", ⟨0, 6, -6, 0, -6, 0, 0, 6, 0, 0, 6⟩),
  ("pint", ⟨0, 6, -6, 0, -6, 0, 0, 6, 0, 0, 6⟩),
  ("cup", ⟨0, 6, -6, 0, -6, 0, 0, 6, 0, 0, 6⟩),
  ("fluidounce", ⟨0, 6, -6, 0, -6, 0, 0, 6, 0, 0, 6⟩),
  ("teaspoon", ⟨0, 6, -6, 0, -6, 0, 0, 6, 0, 0, 6⟩),
  ("tablespoon", ⟨0, 6, -6, 0, -6, 0, 0, 6, 0, 0, 6⟩),
  ("bubnoff", ⟨0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("ips", ⟨0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("fps", ⟨0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("fpm", ⟨0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("ms", ⟨0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("kmh", ⟨0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("mph", ⟨0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("knot", ⟨0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("mps", ⟨0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0⟩),
  ("grain", ⟨0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0⟩),
  ("gram", ⟨0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0⟩),
  ("earthgram", ⟨0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0⟩),
  ("kilogram", ⟨0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0⟩),
  ("tonne", ⟨0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0⟩),
  ("ton", ⟨0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0⟩),
  ("pound", ⟨0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0⟩),
  ("ounce", ⟨0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0⟩),
  ("slug", ⟨0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0⟩),
  ("slinch", ⟨0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0⟩),
  ("hyl", ⟨0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0⟩),
  ("dyne", ⟨0, -2, 6, 0, 4, 0, 0, -2, 0, 0, -4⟩),
  ("newton", ⟨0, -2, 6, 0, 4, 0, 0, -2, 0, 0, -4⟩),
  ("poundal", ⟨0, -2, 6, 0, 4, 0, 0, -2, 0, 0, -4⟩),
  ("poundforce", ⟨0, -2, 6, 0, 4, 0, 0, -2, 0, 0, -4⟩),
  ("kilopond", ⟨0, -2, 6, 0, 4, 0, 0, -2, 0, 0, -4⟩),
  ("psi", ⟨0, -6, 10, 0, 8, 0, 0, -6, 0, 0, -8⟩),
  ("pascal", ⟨0, -6, 10, 0, 8, 0, 0, -6, 0, 0, -8⟩),
  ("bar", ⟨0, -6, 10, 0, 8, 0, 0, -6, 0, 0, -8⟩),
  ("barye", ⟨0, -6, 10, 0, 8, 0, 0, -6, 0, 0, -8⟩),
  ("technicalatmosphere", ⟨0, -6, 10, 0, 8, 0, 0, -6, 0, 0, -8⟩),
  ("atmosphere", ⟨0, -6, 10, 0, 8, 0, 0, -6, 0, 0, -8⟩),
  ("inchmercury", ⟨0, -6, 10, 0, 8, 0, 0, -6, 0, 0, -8⟩),
  ("torr", ⟨0, -6, 10, 0, 8, 0, 0, -6, 0, 0, -8⟩),
  ("electronvolt", ⟨0, 0, 4, 0, 2, 0, 0, 0, 0, 0, -2⟩),
  ("erg", ⟨0, 0, 4, 0, 2, 0, 0, 0, 0, 0, -2⟩),
  ("joule", ⟨0, 0, 4, 0, 2, 0, 0, 0, 0, 0, -2⟩),
  ("footpound", ⟨0, 0, 4, 0, 2, 0, 0, 0, 0, 0, -2⟩),
  ("calorie", ⟨0, 0, 4, 0, 2, 0, 0, 0, 0, 0, -2⟩),
  ("kilocalorie", ⟨0, 0, 4, 0, 2, 0, 0, 0, 0, 0, -2⟩),
  ("meancalorie", ⟨0, 0, 4, 0, 2, 0, 0, 0, 0, 0, -2⟩),
  ("earthcalorie", ⟨0, 0, 4, 0, 2, 0, 0, 0, 0, 0, -2⟩),
  ("thermalunit", ⟨0, 0, 4, 0, 2, 0, 0, 0, 0, 0, -2⟩),
  ("gasgallon", ⟨0, 0, 4, 0, 2, 0, 0, 0, 0, 0, -2⟩),
  ("tontnt", ⟨0, 0, 4, 0, 2, 0, 0, 0, 0, 0, -2⟩),
  ("watt", ⟨0, -2, 8, 0, 4, 0, 0, -2, 0, 0, -4⟩),
  ("horsepower", ⟨0, -2, 8, 0, 4, 0, 0, -2, 0, 0, -4⟩),
  ("horsepowerwatt", ⟨0, -2, 8, 0, 4, 0, 0, -2, 0, 0, -4⟩),
  ("horsepowermetric", ⟨0, -2, 8, 0, 4, 0, 0, -2, 0, 0, -4⟩),
  ("electricalhorsepower", ⟨0, -2, 8, 0, 4, 0, 0, -2, 0, 0, -4⟩),
  ("tonsrefrigeration", ⟨0, -2, 8, 0, 4, 0, 0, -2, 0, 0, -4⟩),
  ("boilerhorsepower", ⟨0, -2, 8, 0, 4, 0, 0, -2, 0, 0, -4⟩),
  ("coulomb", ⟨0, 1, -1, -1, 0, 0, 0, 1, -1, -2, 0⟩),
  ("earthcoulomb", ⟨0, 1, -1, -1, 0, 0, 0, 1, -1, -2, 0⟩),
  ("ampere", ⟨0, -1, 3, -1, 2, 0, 0, -1, -1, -2, -2⟩),
  ("volt", ⟨0, -1, 5, 1, 2, 0, 0, -1, 1, 2, -2⟩),
  ("henry", ⟨0, 2, -2, 2, -2, 0, 0, 2, 2, 4, 2⟩),
  ("ohm", ⟨0, 0, 2, 2, 0, 0, 0, 0, 2, 4, 0⟩),
  ("siemens", ⟨0, 0, -2, -2, 0, 0, 0, 0, -2, -4, 0⟩),
  ("farad", ⟨0, 2, -6, -2, -2, 0, 0, 2, -2, -4, 2⟩),
  ("weber", ⟨0, 1, 1, 1, 0, 0, 0, 1, 1, 0, 0⟩),
  ("tesla", ⟨0, -3, 5, 1, 4, 0, 0, -3, 1, 0, -4⟩),
  ("abcoulomb", ⟨0, 1, -1, -1, 0, 0, 0, 1, -1, -2, 0⟩),
  ("abampere", ⟨0, -1, 3, -1, 2, 0, 0, -1, -1, -2, -2⟩),
  ("abvolt", ⟨0, -1, 5, 1, 2, 0, 0, -1, 1, 2, -2⟩),
  ("abhenry", ⟨0, 2, -2, 2, -2, 0, 0, 2, 2, 4, 2⟩),
  ("abohm", ⟨0, 0, 2, 2, 0, 0, 0, 0, 2, 4, 0⟩),
  ("abmho", ⟨0, 0, -2, -2, 0, 0, 0, 0, -2, -4, 0⟩),
  ("abfarad", ⟨0, 2, -6, -2, -2, 0, 0, 2, -2, -4, 2⟩),
  ("maxwell", ⟨0, 1, 1, 1, 0, 0, 0, 1, 1, 0, 0⟩),
  ("gauss", ⟨0, -3, 5, 1, 4, 0, 0, -3, 1, 0, -4⟩),
  ("oersted", ⟨0, -3, 5, -1, 4, 0, 0, -3, 1, 0, -4⟩),
  ("gilbert", ⟨0, -1, 3, -1, 2, 0, 0, -3, -1, -2, -2⟩),
  ("statcoulomb", ⟨0, 1, -1, -1, 0, 0, 0, 1, -1, -2, 0⟩),
  ("statampere", ⟨0, -1, 3, -1, 2, 0, 0, -1, -1, -2, -2⟩),
  ("statvolt", ⟨0, -1, 5, 1, 2, 0, 0, -1, 1, 2, -2⟩),
  ("stathenry", ⟨0, 2, -2, 2, -2, 0, 0, 2, 2, 4, 2⟩),
  ("statohm", ⟨0, 0, 2, 2, 0, 0, 0, 0, 2, 4, 0⟩),
  ("statmho", ⟨0, 0, -2, -2, 0, 0, 0, 0, -2, -4, 0⟩),
  ("statfarad", ⟨0, 2, -6, -2, -2, 0, 0, 2, -2, -4, 2⟩),
  ("statweber", ⟨0, 1, 1, 1, 0, 0, 0, 1, 1, 0, 0⟩),
  ("stattesla", ⟨0, -3, 5, 1, 4, 0, 0, -3, 1, 0, -4⟩),
  ("kelvin", ⟨-2, 0, 4, 0, 2, 0, 0, 0, 0, 0, -2⟩),
  ("rankine", ⟨-2, 0, 4, 0, 2, 0, 0, 0, 0, 0, -2⟩),
  ("celsius", ⟨-2, 0, 4, 0, 2, 0, 0, 0, 0, 0, -2⟩),
  ("fahrenheit", ⟨-2, 0, 4, 0, 2, 0, 0, 0, 0, 0, -2⟩),
  ("sealevel", ⟨-2, 0, 4, 0, 2, 0, 0, 0, 0, 0, -2⟩),
  ("boiling", ⟨-2, 0, 4, 0, 2, 0, 0, 0, 0, 0, -2⟩),
  ("mole", ⟨0, 0, 0, 0, 2, -2, 0, 0, 0, 0, 0⟩),
  ("earthmole", ⟨0, 0, 0, 0, 2, -2, 0, 0, 0, 0, 0⟩),
  ("poundmole", ⟨0, 0, 0, 0, 2, -2, 0, 0, 0, 0, 0⟩),
  ("slugmole", ⟨0, 0, 0, 0, 2, -2, 0, 0, 0, 0, 0⟩),
  ("slinchmole", ⟨0, 0, 0, 0, 2, -2, 0, 0, 0, 0, 0⟩),
  ("katal", ⟨0, -2, 4, 0, 4, -2, 0, -2, 0, 0, -2⟩),
  ("amagat", ⟨0, -6, 6, 0, 8, -2, 0, -6, 0, 0, -6⟩),
  ("lumen", ⟨0, -2, 8, 0, 4, 0, 2, -2, 0, 0, -4⟩),
  ("candela", ⟨0, -2, 8, 0, 4, 0, 2, -6, 0, 0, -4⟩),
  ("lux", ⟨0, -6, 12, 0, 8, 0, 2, -6, 0, 0, -8⟩),
  ("phot", ⟨0, -6, 12, 0, 8, 0, 2, -6, 0, 0, -8⟩),
  ("footcandle", ⟨0, -6, 12, 0, 8, 0, 2, -6, 0, 0, -8⟩),
  ("nit", ⟨0, -6, 12, 0, 8, 0, 2, -10, 0, 0, -8⟩),
  ("apostilb", ⟨0, -6, 12, 0, 8, 0, 2, -12, 0, 0, -8⟩),
  ("stilb", ⟨0, -6, 12, 0, 8, 0, 2, -10, 0, 0, -8⟩),
  ("lambert", ⟨0, -6, 12, 0, 8, 0, 2, -12, 0, 0, -8⟩),
  ("footlambert", ⟨0, -6, 12, 0, 8, 0, 2, -12, 0, 0, -8⟩),
  ("bril", ⟨0, -6, 12, 0, 8, 0, 2, -12, 0, 0, -8⟩),
  ("talbot", ⟨0, 0, 4, 0, 2, 0, 2, 0, 0, 0, -2⟩),
  ("lumerg", ⟨0, 0, 4, 0, 2, 0, 2, 0, 0, 0, -2⟩),
  ("hertz", ⟨0, -2, 4, 0, 2, 0, 0, -2, 0, 0, -2⟩),
  ("apm", ⟨0, -2, 4, 0, 2, 0, 0, -2, 0, 0, -2⟩),
  ("rpm", ⟨0, -2, 4, 0, 2, 0, 0, 0, 0, 0, -2⟩),
  ("kayser", ⟨0, -2, 2, 0, 2, 0, 0, -2, 0, 0, -2⟩),
  ("diopter", ⟨0, -2, 2, 0, 2, 0, 0, 0, 0, 0, -2⟩),
  ("rayleigh", ⟨0, -2, 0, 0, 2, 0, 0, -2, 0, 0, -2⟩),
  ("flick", ⟨0, -8, 14, 0, 10, 0, 0, -12, 0, 0, -10⟩),
  ("gforce", ⟨0, -2, 6, 0, 2, 0, 0, -2, 0, 0, -4⟩),
  ("galileo", ⟨0, -2, 6, 0, 2, 0, 0, -2, 0, 0, -4⟩),
  ("eotvos", ⟨0, -4, 8, 0, 4, 0, 0, -4, 0, 0, -6⟩),
  ("darcy", ⟨0, 4, -4, 0, -4, 0, 0, 4, 0, 0, 4⟩),
  ("poise", ⟨0, -4, 6, 0, 6, 0, 0, -4, 0, 0, -6⟩),
  ("reyn", ⟨0, -4, 6, 0, 6, 0, 0, -4, 0, 0, -6⟩),
  ("stokes", ⟨0, 2, 0, 0, -2, 0, 0, 2, 0, 0, 2⟩),
  ("rayl", ⟨0, -6, 8, 0, 8, 0, 0, -6, 0, 0, -8⟩),
  ("mpge", ⟨0, 2, -6, 0, -4, 0, 0, 2, 0, 0, 4⟩),
  ("langley", ⟨0, -4, 8, 0, 6, 0, 0, -4, 0, 0, -6⟩),
  ("jansky", ⟨0, -4, 8, 0, 6, 0, 0, -4, 0, 0, -6⟩),
  ("solarflux", ⟨0, -4, 8, 0, 6, 0, 0, -4, 0, 0, -6⟩),
  ("curie", ⟨0, -2, 4, 0, 2, 0, 0, -2, 0, 0, -2⟩),
  ("gray", ⟨0, 0, 4, 0, 0, 0, 0, 0, 0, 0, -2⟩),
  ("roentgen", ⟨0, 1, -1, -1, -2, 0, 0, 1, -1, -2, 0⟩),
  ("rem", ⟨0, 0, 4, 0, 0, 0, 0, 0, 0, 0, -2⟩),
  ("thermalconductivity_water", ⟨2, -4, 2, 0, 2, 0, 0, -4, 0, 0, -2⟩)]

end UnitSystems
