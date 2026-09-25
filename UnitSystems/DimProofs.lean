import UnitSystems.DimModel

/-!
# Kernel-checked dimensions of every UnitSystems formula

Each theorem evaluates the *actual* Lean conversion chains, physics formulas and
unit definitions in the exponent model (`UnitSystems.DimModel`) inside the
kernel (`decide`), and compares them with tables recovered independently from
the Julia oracle (`oracle/unitsystems/dims.jl`: a log-linear fit of Julia's
numbers, cross-checked with Similitude's `evaldim`). A transcription error in
any of the 131 chains or 240 one-argument functions breaks the build.

`conv_const_iso` is the port's version of the theorem of
`docs/port-notes/unitsystems.md` §4.6: UnitSystems' 131 hand-written chains
agree with Similitude's closed-form map `UnitSystem(d)` from USQ dimensions to
exponents over the defining constants.
-/

namespace UnitSystems

/-- Every conversion chain `q(U,S)` has its Julia USQ dimension. -/
theorem conv_dims : ∀ q ∈ Conv.all, q.dimModel = HalfDim.ofDim q.dim := by decide

/-- Every conversion chain's exponents over the defining constants are Similitude's
`UnitSystem(dim q)` (`dimension.jl:466-493`). -/
theorem conv_const_iso : ∀ q ∈ Conv.all, q.constModel = usqToConst q.dim := by decide

/-- `usqToConst` is inverted by the constants' dimension matrix `Dc` on the
eleven base dimensions (so it is an isomorphism of the exponent lattices). -/
theorem usqToConst_inverse :
    ∀ d ∈ [USQ.F, USQ.M, USQ.L, USQ.T, USQ.Q, USQ.Θ, USQ.N, USQ.J, USQ.A, USQ.R, USQ.C],
      constToUsq (usqToConst d) = HalfDim.ofDim d := by decide

/-- Every monomial one-argument function (constants, physics, 193 units, prefixes)
has the USQ dimension the oracle fit recovers. -/
theorem scalar_dims :
    ∀ p ∈ scalarDimTable, ((scalarFunctions (α := HalfDim)).lookup p.1).map dimOf = some p.2 := by
  decide

/-- … and the oracle's exponents over the defining constants. -/
theorem scalar_const :
    ∀ p ∈ scalarConstTable, ((scalarFunctions (α := HalfDim)).lookup p.1).map constExpsOf = some p.2 := by
  decide

/-! ### Documented Julia quirks, pinned as theorems -/

/-- `photonirradiance = 1/(length·speed)` has dimension `L⁻²T`, not `L⁻²T⁻¹`
(`kinematic.jl:120`; the Wolfram kernel agrees, so it is upstream's choice). -/
theorem photonirradiance_dim : Conv.photonirradiance.dimModel = .ofDim (USQ.T / USQ.L ^ 2) := by
  decide

/-- `specificmagnetization` is inverted: `mass/magneticmoment` (`electromagnetic.jl:65`). -/
theorem specificmagnetization_dim :
    Conv.specificmagnetization.dimModel = .ofDim (USQ.M * USQ.Q / (USQ.F * USQ.L ^ 2 * USQ.T * USQ.C)) := by
  decide

/-- `bradian(U) = angle(turn(U)/two(U)^8,U,Metric)` applies the angle unit twice:
dimension `A²` (`derived.jl:24`). -/
theorem bradian_dim : dimOf bradian = .ofDim (USQ.A ^ 2) := by decide

/-- `parsec` divides by `turn(U)`: dimension `LA⁻¹` (`derived.jl:63`). -/
theorem parsec_dim : dimOf parsec = .ofDim (USQ.L / USQ.A) := by decide

/-- `jovianyear` is only meaningful in IAU systems: its dimension is
`F^(-1/2) M^(1/2) L^(1/2) T` (`physics.jl:59`). -/
theorem jovianyear_dim : dimOf jovianyear = ⟨-1, 1, 1, 2, 0, 0, 0, 0, 0, 0, 0⟩ := by decide

/-- The elementary charge is a charge, `Q` (`UnitSystems.jl:289`). -/
theorem elementarycharge_dim : dimOf (fun U => elementarycharge U) = .ofDim USQ.Q := by decide

/-- Planck's constant is an action `FLT` (with the angle unit folded in by `turn`). -/
theorem planck_dim : dimOf planck = .ofDim (USQ.F * USQ.L * USQ.T) := by decide

end UnitSystems
