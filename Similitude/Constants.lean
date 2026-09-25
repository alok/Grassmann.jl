import FieldAlgebra
import UnitSystems

/-!
# The exact constants group and the USQ dimension group

Similitude replaces UnitSystems' `Float64` constants by exact elements of a free
abelian group on 44 generators (`dimension.jl:164-221`): the 33 measured or
defined physical constants (`kB`, `NA`, `𝘩`, `𝘤`, …, `GMJ`), the mathematical
constants `φ γ ℯ τ` and the primes `2 3 5 7 11 19 43`, with an optional scalar
coefficient. `Consts` is that group (`FieldAlgebra.Group constantsBasis`), so
unit-system constants and conversion factors are exact monomials such as
`kB⋅NA⋅𝘩⋅𝘤⁻¹R∞⋅α⁻²μₑᵤ⁻¹2⁴5³`, evaluated to `Float64` only for display.

`USQ` (`usqBasis`) is the 11-generator dimension group `F M L T Q Θ N J A R C`
used for the *display* of dimensions and their images under unit-system
homomorphisms (whose exponents may be halves).

Numeric evaluation (`Consts.product`) follows Julia's generated `product`
(`FieldAlgebra.jl:717-734`) factor by factor: a left fold over the 37
non-integer generators, times the fold over the primes times the coefficient,
with Julia's own `^` kernels, so printed values agree digit for digit.
-/

namespace Similitude

open FieldConstants FieldAlgebra UnitSystems

/-- The USQ dimension basis `F M L T Q Θ N J A R C` (`dimension.jl:144-156`). -/
def usqBasis : Basis where
  name := "USQ"
  n := 11
  text := #["F", "M", "L", "T", "Q", "Θ", "N", "J", "A", "R", "C"]
  charNames := true

/-- Display names of the 44 constant generators (`dimension.jl:220`). -/
def constantsNames : Array String :=
  #["kB", "NA", "𝘩", "𝘤", "𝘦", "Kcd", "ΔνCs", "R∞", "α", "μₑᵤ", "μₚᵤ", "ΩΛ", "H0", "g₀", "aⱼ", "au",
    "ft", "ftUS", "lb", "T₀", "atm", "inHg", "RK90", "KJ90", "RK", "KJ", "Rᵤ2014", "Ωᵢₜ", "Vᵢₜ", "kG",
    "mP", "GME", "GMJ", "φ", "γ", "ℯ", "τ", "2", "3", "5", "7", "11", "19", "43"]

/-- LaTeX names of the generators (`usqlatex`, `dimension.jl:157`; index 3 is
`\hbar` in Julia although the generator is Planck's `𝘩`). -/
def constantsLatex : Array String :=
  #["\\text{k}_\\text{B}", "\\text{N}_\\text{A}", "\\hbar", "\\text{c}", "\\text{e}",
    "\\text{K}_\\text{cd}", "\\Delta\\nu_\\text{Cs}", "\\text{R}_{\\infty}", "\\alpha", "\\mu_\\text{eu}",
    "\\mu_\\text{pu}", "\\Omega_{\\Lambda}", "\\text{H}_0", "\\text{g}_0", "\\text{a}_\\text{j}", "\\text{au}",
    "\\text{ft}", "\\text{ft}_\\text{US}", "\\text{lb}", "\\text{T}_0", "\\text{atm}", "\\text{in}_\\text{Hg}",
    "{\\text{R}_\\text{K}^{90}}", "{\\text{K}_\\text{J}^{90}}", "\\text{R}_\\text{K}", "\\text{K}_\\text{J}",
    "\\text{R}_\\text{u}", "\\Omega_\\text{it}", "\\text{V}_\\text{it}", "\\text{k}_\\text{G}", "\\text{m}_\\text{P}",
    "\\text{GM}_\\text{E}", "\\text{GM}_\\text{J}", "\\varphi", "\\gamma", "e", "\\tau", "2", "3", "5", "7",
    "11", "19", "43"]

/-- The 44-generator constants basis (Julia `@group2 Constants`). -/
def constantsBasis : Basis where
  name := "Constants"
  n := 44
  text := constantsNames
  charNames := false
  unit := "𝟏"
  latex := constantsLatex

/-- A USQ dimension group element (Julia `Group{:USQ}`). -/
abbrev USQGroup := Group usqBasis

/-- An exact physical constant (Julia `Group{:Constants}`). -/
abbrev Consts := Group constantsBasis

/-- Numeric values of the 44 generators, in basis order. -/
def genValues : Array GenValue :=
  let m (x : Measured) : GenValue := .const x.value.toFloat
  #[m .kB, m .NA, m .hh, m .cc, m .ee, m .Kcd, m .ΔνCs, m .Rinf, m .α, m .μₑᵤ, m .μₚᵤ, m .ΩΛ, m .H0,
    m .g₀, m .aⱼ, m .au, m .ft, m .ftUS, m .lb, m .T₀, m .atm, m .inHg, m .RK1990, m .KJ1990,
    m .RK2014, m .KJ2014, m .Rᵤ2014, m .Ωᵢₜ, m .Vᵢₜ, m .kG, m .mP, m .GME, m .GMJ,
    .irrational 1.618033988749895, .irrational 0.5772156649015329, .euler, .const 6.283185307179586,
    .prime 2, .prime 3, .prime 5, .prime 7, .prime 11, .prime 19, .prime 43]

namespace Consts

/-- The `i`-th generator (0-based). -/
def gen (i : Nat) (h : i < 44 := by decide) : Consts := Group.gen ⟨i, h⟩

/-- Julia `product(g)` for the constants group (`FieldAlgebra.jl:717-734`):
`((kB^e₁·NA^e₂)·…·τ^e₃₇) · (((2.0^e₃₈·3.0^e₃₉)·…·43.0^e₄₄) · c)`
(`FieldAlgebra.productWith`: the primes are the integer literals). -/
def product (g : Consts) : Float := productWith genValues g

/-- Julia `factorize(x::Int, Val(:Constants))`: the primes `2 3 5 7 11 19 43`
become generators, the remaining cofactor is the coefficient
(`12 ↦ 2²3`, `-12 ↦ 2²3⋅-1`, `13 ↦ 13`). -/
def factorize (x : Int) : Consts := factorizeWith genValues x

/-- Julia `factorize(x::Float64, Val(:Constants))`: integral floats factor as
integers; otherwise powers of `τ = 2π` are extracted (`4π ↦ τ⋅2`) and the rest
is the coefficient (`π ↦ 3.141592653589793`). -/
def factorizeF (x : Float) : Consts :=
  if x.isFinite && x.floor == x && x.abs < 9.223372036854775807e18 then
    factorize (x.toInt64.toInt)
  else
    let τ := 6.283185307179586
    let rec go (x : Float) (i : Nat) : Nat → Float × Nat
      | 0 => (x, i)
      | f + 1 =>
        if x == 0.0 then (x, 0)
        else if JuliaBase.F64.rem x τ == 0.0 then go (JuliaBase.F64.div x τ) (i + 1) f else (x, i)
    let (x, e) := go x 0 64
    Group.mk' (.exact (Vector.ofFn fun j => if j.1 == 36 then (e : Rat) else 0)) (.float x)

/-- The generator of a measured constant (`UnitSystems.jl:316-331` names mapped
to the basis; `αinv = inv(α)`, `LD`, `JD` and the large prefixes are exact
integers, `μE☾` a float coefficient; `Similitude.jl:128-129`, `constant.jl:56`). -/
def ofMeasured : Measured → Consts
  | .kB => gen 0 | .NA => gen 1 | .hh => gen 2 | .cc => gen 3 | .ee => gen 4 | .Kcd => gen 5
  | .ΔνCs => gen 6 | .Rinf => gen 7 | .α => gen 8 | .αinv => (gen 8)⁻¹ | .μₑᵤ => gen 9
  | .μₚᵤ => gen 10 | .ΩΛ => gen 11 | .H0 => gen 12 | .g₀ => gen 13 | .aⱼ => gen 14 | .au => gen 15
  | .ft => gen 16 | .ftUS => gen 17 | .lb => gen 18 | .T₀ => gen 19 | .atm => gen 20
  | .inHg => gen 21 | .RK1990 => gen 22 | .KJ1990 => gen 23 | .RK2014 => gen 24 | .KJ2014 => gen 25
  | .Rᵤ2014 => gen 26 | .Ωᵢₜ => gen 27 | .Vᵢₜ => gen 28 | .kG => gen 29 | .mP => gen 30
  | .GME => gen 31 | .GMJ => gen 32
  | .μE => factorizeF 81.300568   -- a `FieldConstants.Constant` in Similitude (see `Scalar.measured`)
  | .LD => factorize 384399 * (gen 37 * gen 39) ^ (3 : Int)
  | .JD => factorize 778479 * (gen 37 * gen 39) ^ (6 : Int)
  | .zetta => (gen 37 * gen 39) ^ (21 : Int)
  | .zepto => (gen 37 * gen 39) ^ (-21 : Int)
  | .yotta => (gen 37 * gen 39) ^ (24 : Int)
  | .yocto => (gen 37 * gen 39) ^ (-24 : Int)

end Consts

/-- Constants print with their value: `kB⋅NA = 8.31446261815324` (`dimension.jl:211`). -/
instance : GroupProduct constantsBasis := ⟨fun g => some (JuliaBase.F64.showString (Consts.product g))⟩

/-- FieldAlgebra's `showlatex(g)` for a constant (`FieldAlgebra.jl:247-291`):
the LaTeX monomial and ` = ` its value (`\hbar\cdot \text{c}^{-1}… = 9.1… \times 10^{-31}`). -/
def Consts.latex (g : Consts) : String :=
  g.latexPre ++ " = " ++ specialPrintFloat (Consts.product g)

/-- Julia `===` of two coefficients: same kind and same value (bits for floats). -/
def coefIdent : Coef → Coef → Bool
  | .int a, .int b => a == b
  | .rat a, .rat b => a == b
  | .float a, .float b => a.toBits == b.toBits
  | _, _ => false

/-- Julia `===` of two groups of the same basis: identical exponent vectors (same
element type) and identical coefficients. -/
def Consts.ident (a b : Consts) : Bool :=
  coefIdent a.c b.c && match a.v, b.v with
    | .int u, .int v => u == v
    | .exact u, .exact v => u == v
    | .int _, .exact _ | .exact _, .int _ => a.v.toRats? == b.v.toRats?
    | .float u, .float v => (List.finRange 44).all fun i => (u.get i).toBits == (v.get i).toBits
    | _, _ => false

end Similitude
