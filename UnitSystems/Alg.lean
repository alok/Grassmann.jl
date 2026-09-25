import FieldConstants

/-!
# Scalars of a unit system

UnitSystems.jl stores the eleven defining constants of a unit system as
`FieldConstants.Constant` type parameters, and its downstream packages reuse the
very same formulas with other number types in those slots: Similitude with exact
products of physical constants, MeasureSystems with uncertain measurements.
Julia gets this by textually re-including `initdata.jl`
(`Similitude.jl:133-155`, `MeasureSystems.jl:395-422`).

The Lean port writes every formula once, generic over a scalar with the
`UnitAlg` interface, and instantiates it:

* `JNum` (this package): Julia `Float64`/`Int64` payloads with Julia's promotion,
  `literal_pow` and `unit` snapping, reproducing UnitSystems' numbers bit for bit;
* exact constant groups (Similitude) and measured groups (MeasureSystems);
* an exponent model (`UnitSystems.Dims`) in which every formula computes its own
  physical dimension, used to *prove* the dimension of each of the 131
  conversion chains.

`Measured` names the measured/defined inputs of `UnitSystems.jl:316-331`
(Unicode names that are not Lean identifiers use Julia's ASCII aliases: `hh` for
`𝘩`, `cc` for `𝘤`, `ee` for `𝘦`, `Rinf` for `R∞`, `μE` for `μE☾`).
-/

namespace UnitSystems

open FieldConstants

/-- The measured or defined constants of UnitSystems (`UnitSystems.jl:316-331`). -/
inductive Measured where
  | g₀ | atm | T₀ | ft | ftUS | lb | inHg | Ωᵢₜ | Vᵢₜ | ΔνCs | Kcd | mP | αinv | α | Rinf
  | NA | kB | hh | cc | ee | μₑᵤ | μₚᵤ | μE | RK1990 | KJ1990 | Rᵤ2014 | RK2014 | KJ2014
  | GME | GMJ | kG | H0 | ΩΛ | aⱼ | au | LD | JD | zetta | zepto | yotta | yocto
  deriving DecidableEq, Repr, Inhabited

/-- Julia source value of each measured constant as a `Float64`/`Int64` payload
(`UnitSystems.jl:316-331`; `α = inv(αinv)`). -/
def Measured.value : Measured → JNum
  | .g₀ => .float 9.80665
  | .atm => .float 101325.0
  | .T₀ => .float 273.15
  | .ft => .float 0.3048
  | .ftUS => .float (1200.0 / 3937.0)
  | .lb => .float 0.45359237
  | .inHg => .float (1.0 / 3386.389)
  | .Ωᵢₜ => .float 1.000495
  | .Vᵢₜ => .float 1.00033
  | .ΔνCs => .float 9192631770.0
  | .Kcd => .float (683.0 * 555.016 / 555.0)
  | .mP => .float 2.176434e-8
  | .αinv => .float 137.035999084
  | .α => .float (1.0 / 137.035999084)
  | .Rinf => .float 10973731.5681601
  | .NA => .float 6.02214076e23
  | .kB => .float 1.380649e-23
  | .hh => .float 6.62607015e-34
  | .cc => .float 299792458.0
  | .ee => .float 1.602176634e-19
  | .μₑᵤ => .float (1.0 / 1822.888486209)
  | .μₚᵤ => .float 1.007276466621
  | .μE => .float 81.300568
  | .RK1990 => .float 25812.807
  | .KJ1990 => .float 4.835979e14
  | .Rᵤ2014 => .float 8.3144598
  | .RK2014 => .float 25812.8074555
  | .KJ2014 => .float 4.835978525e14
  | .GME => .float 398600441.8e6
  | .GMJ => .float 1.26686534e17
  | .kG => .float 3548.18761
  | .H0 => .float 67.66
  | .ΩΛ => .float 0.6889
  | .aⱼ => .float 365.25
  | .au => .float 149597870.7e3
  | .LD => .float 384399e3
  | .JD => .float 778479e6
  | .zetta => .float 1e21
  | .zepto => .float 1e-21
  | .yotta => .float 1e24
  | .yocto => .float 1e-24

/-- A scalar that can fill the slots of a unit system: Julia's
`Constant`/`Quantity`/`Measurement` payloads. The operations are Julia's
*literal* ones (`x^n` is `literal_pow`, `unit(x, y)` snaps near-one factors).

`special` enables UnitSystems' dispatch on exact parameter values (the
`Coupling` overrides of `UnitSystems.jl:377-397` and the IAU snaps of
`kinematic.jl:45-67`), which in Julia only fire for `Constant` parameters. -/
class UnitAlg (α : Type) extends Mul α, Div α, Add α, Sub α, BEq α, Inhabited α where
  /-- Julia `inv` -/
  inv : α → α
  /-- literal integer power `x^n` -/
  lpow : α → Int → α
  /-- Julia `sqrt` -/
  sqrt : α → α
  /-- `Constant(n)` for an integer literal -/
  ilit : Int → α
  /-- `Constant(x)` for a float literal -/
  flit : Float → α
  /-- `τ = Constant(2π)` -/
  tau : α
  /-- a measured or defined constant -/
  measured : Measured → α
  /-- Julia `UnitSystems.unit(x, y)`: snap `x` to `y` when within `eps^0.9` -/
  snap : α → α → α
  /-- Julia `isone` -/
  isOne : α → Bool
  /-- Julia `===` on stored parameters (type-level identity in Julia) -/
  ident : α → α → Bool
  /-- `x == f` for a float literal `f` -/
  eqFloat : α → Float → Bool
  /-- value dispatch of UnitSystems is live for this scalar -/
  special : Bool := false
  /-- a plain (non-`Constant`) integer literal, as in Julia's `2𝘩` -/
  plit : Int → α := ilit

namespace UnitAlg
variable {α : Type} [UnitAlg α]

/-- `𝟏 = Constant(1)`. -/
@[inline] def one : α := ilit 1
/-- `unit(x) = unit(x, 1)`. -/
@[inline] def unit (x : α) : α := snap x one

end UnitAlg

instance {α : Type} [UnitAlg α] : Inv α := ⟨UnitAlg.inv⟩
instance {α : Type} [UnitAlg α] : HPow α Int α := ⟨UnitAlg.lpow⟩

/-- Julia's `Constant` arithmetic on `Float64`/`Int64` payloads, tracking plain
numbers produced by the value-dispatch overrides (`FieldConstants.Num`). -/
instance : UnitAlg Num where
  inv := Num.inv
  lpow := Num.lpow
  sqrt := Num.sqrt
  ilit n := .c (.int (Int64.ofInt n))
  flit x := .c (.float x)
  tau := .c (.float 6.283185307179586)
  measured m := .c m.value
  snap := Num.snap
  isOne x := x.v.isOne
  ident := Num.ident
  eqFloat x f := x.toFloat == f
  special := true
  plit n := .p (.int (Int64.ofInt n))

end UnitSystems
