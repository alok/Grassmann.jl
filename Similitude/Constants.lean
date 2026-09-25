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

open FieldConstants FieldConstants.Julia FieldAlgebra UnitSystems

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

/-- How a generator is evaluated numerically in `product`. -/
inductive GenValue where
  /-- a `FieldConstants.Constant{x}` (Float payload) -/
  | const (x : Float)
  /-- an `Irrational` evaluated by `power_by_squaring` (`φ`, `γ`) -/
  | irrational (x : Float)
  /-- `ℯ`: `ℯ^x = exp(x)` -/
  | euler
  /-- an integer (evaluated as `float(p)^e`) -/
  | prime (p : Nat)
  deriving Inhabited

/-- Numeric values of the 44 generators, in basis order. -/
def genValues : Array GenValue :=
  let m (x : Measured) : GenValue := .const x.value.toFloat
  #[m .kB, m .NA, m .hh, m .cc, m .ee, m .Kcd, m .ΔνCs, m .Rinf, m .α, m .μₑᵤ, m .μₚᵤ, m .ΩΛ, m .H0,
    m .g₀, m .aⱼ, m .au, m .ft, m .ftUS, m .lb, m .T₀, m .atm, m .inHg, m .RK1990, m .KJ1990,
    m .RK2014, m .KJ2014, m .Rᵤ2014, m .Ωᵢₜ, m .Vᵢₜ, m .kG, m .mP, m .GME, m .GMJ,
    .irrational 1.618033988749895, .irrational 0.5772156649015329, .euler, .const 6.283185307179586,
    .prime 2, .prime 3, .prime 5, .prime 7, .prime 11, .prime 19, .prime 43]

/-- `value^e` with Julia's semantics for the generator kind and exponent type
(`Float64^Int` is `pow_body`, `Float64^Rational` is `x^(p/q)`, `φ^n` is
`power_by_squaring` (a `DomainError` for `n < 0`, here `NaN`), `ℯ^x = exp(x)`). -/
def GenValue.pow (g : GenValue) (e : Expo) : Float :=
  match g, e.makeint with
  | .const x, .int n => powInt x n
  | .const x, e => Julia.pow x e.toFloat
  | .prime p, .int n => powInt (Float.ofNat p) n
  | .prime p, e => Julia.pow (Float.ofNat p) e.toFloat
  | .irrational x, .int n => if n < 0 then nan else powerBySquaring x n.toNat
  | .irrational x, e => Julia.pow x e.toFloat
  | .euler, e => Julia.exp e.toFloat

namespace Consts

/-- The `i`-th generator (0-based). -/
def gen (i : Nat) (h : i < 44 := by decide) : Consts := Group.gen ⟨i, h⟩

/-- Julia `product(g)` for the constants group (`FieldAlgebra.jl:717-734`):
`((kB^e₁·NA^e₂)·…·τ^e₃₇) · (((2.0^e₃₈·3.0^e₃₉)·…·43.0^e₄₄) · c)`. -/
def product (g : Consts) : Float :=
  let idx := List.finRange 44
  let term (i : Fin 44) : Float := (genValues[i.1]!).pow (g.v.get i)
  let nonint := (idx.take 37).map term
  let ints := (idx.drop 37).map term
  let foldl1 : List Float → Float
    | [] => 1.0
    | x :: xs => xs.foldl (· * ·) x
  foldl1 nonint * (foldl1 ints * g.c.toFloat)

/-- Julia `factorfind(x, k)` on integers: strip the factor `k`, counting it. -/
def factorfind (x : Int) (k : Int) : Int × Nat := go x 0 128
where
  go (x : Int) (i : Nat) : Nat → Int × Nat
    | 0 => (x, i)
    | f + 1 => if x == 0 then (x, 0) else if x.tmod k == 0 then go (x.tdiv k) (i + 1) f else (x, i)

/-- Julia `factorize(x::Int, Val(:Constants))`: the primes `2 3 5 7 11 19 43`
become generators, the remaining cofactor is the coefficient
(`12 ↦ 2²3`, `-12 ↦ 2²3⋅-1`, `13 ↦ 13`). -/
def factorize (x : Int) : Consts :=
  let primes : List (Nat × Int) := [(37, 2), (38, 3), (39, 5), (40, 7), (41, 11), (42, 19), (43, 43)]
  let (x, exps) := primes.foldl (fun (x, acc) (i, p) =>
    let (x', e) := factorfind x p
    (x', acc.push (i, e))) (x, (#[] : Array (Nat × Nat)))
  let v : Vector Rat 44 := Vector.ofFn fun j =>
    match exps.find? (·.1 == j.1) with
    | some (_, e) => (e : Rat)
    | none => 0
  Group.mk' (.exact v) (.int x)

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

/-- Julia `*(a::Real, g::Group)` = `times(factorize(a), g)` for a Julia number. -/
def scaleBy (a : Coef) (g : Consts) : Consts :=
  match a with
  | .int n => factorize n * g
  | .float x => factorizeF x * g
  | .rat q => g.scale (.rat q)

/-- Julia's `^(a::Group, b::Integer)` for a *non-literal* integer (the power in
`ratio_calc`): exponents scale, the coefficient is `coef^b` in Julia arithmetic
(`Float64^Int` is `pow_body`, even for negative `b`). -/
def npowRaw (a : Consts) (b : Int) : Consts :=
  let c := match a.c with
    | .int x => if b ≥ 0 then Coef.int (x ^ b.toNat) else .float (powInt (Float.ofInt x) b)
    | .rat q => if b ≥ 0 then .rat (q ^ b.toNat) else .rat (q⁻¹ ^ (-b).toNat)
    | .float x => .float (powInt x b)
  Group.mk' (a.v.smul b) c

/-- Julia `+` of constants (`dimension.jl:112-120`): equal exponents add
coefficients (equal coefficients give `𝟐*a`), otherwise the floating-point sum
(here refactorized, as Julia does when it is multiplied back into a group). -/
def add (a b : Consts) : Consts :=
  if a.v.beq b.v then
    if a.c == b.c then gen 37 * a else Group.mk' a.v (a.c.add b.c)
  else factorizeF (a.product + b.product)

/-- Julia `-` of constants (`dimension.jl:121-129`). -/
def sub (a b : Consts) : Consts :=
  if a.v.beq b.v then
    if a.c == b.c then factorize 0 else Group.mk' a.v (a.c.add b.c.neg)
  else factorizeF (a.product - b.product)

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
  | .μE => factorizeF 81.300568
  | .LD => factorize 384399 * (gen 37 * gen 39) ^ (3 : Int)
  | .JD => factorize 778479 * (gen 37 * gen 39) ^ (6 : Int)
  | .zetta => (gen 37 * gen 39) ^ (21 : Int)
  | .zepto => (gen 37 * gen 39) ^ (-21 : Int)
  | .yotta => (gen 37 * gen 39) ^ (24 : Int)
  | .yocto => (gen 37 * gen 39) ^ (-24 : Int)

end Consts

/-- Constants print with their value: `kB⋅NA = 8.31446261815324` (`dimension.jl:211`). -/
instance : GroupProduct constantsBasis := ⟨fun g => some (JuliaBase.F64.showString (Consts.product g))⟩

/-- Similitude's exact scalar: UnitSystems' formulas over `Consts` compute exact
unit-system constants and conversion factors. -/
instance : UnitAlg Consts where
  mul := Group.mul
  div := Group.div
  add := Consts.add
  sub := Consts.sub
  beq := Group.beq
  default := Group.one
  inv := Group.inv
  lpow := Group.zpow
  sqrt := Group.sqrt
  ilit := Consts.factorize
  flit := Consts.factorizeF
  tau := Consts.gen 36
  measured := Consts.ofMeasured
  snap x _ := x
  isOne := Group.isOne
  ident := Group.beq
  eqFloat x f := Consts.product x == f

end Similitude
