/-
  Grassmann/MultivectorDA.lean - Dense Float multivectors backed by `DataArray`

  This is a numerics-first representation intended for hot paths where:
  - the scalar type is `Float`
  - we want contiguous coefficient storage (2^n floats)
  - we care about allocation patterns and destructive updates

  The existing `Multivector sig F` (function `Fin → F`) remains the proof-friendly
  representation. `MultivectorDA` is the "runtime buffer" form.
-/
import Grassmann.DataArray
import Grassmann.Multivector

namespace Grassmann

variable {n : ℕ} {sig : Signature n}

/-- Dense Float multivector with coefficients stored in a `DataArray`.

Invariant (by convention): `coeffs.size = 2^n`. -/
structure MultivectorDA (sig : Signature n) where
  coeffs : DataArray

namespace MultivectorDA

@[inline] private def size (n : Nat) : Nat := 2 ^ n

/-! ### Constructors -/

@[inline] def zero : MultivectorDA sig :=
  ⟨DataArray.zeros (size n)⟩

@[inline] def scalar (x : Float) : MultivectorDA sig :=
  ⟨(DataArray.zeros (size n)).set! 0 x⟩

@[inline] def one : MultivectorDA sig := scalar 1.0

/-! ### Accessors -/

@[inline] def coeffIdx (m : MultivectorDA sig) (idx : Nat) : Float :=
  m.coeffs.get! idx

@[inline] def coeffFin (m : MultivectorDA sig) (i : Fin (2 ^ n)) : Float :=
  m.coeffs.get! i.val

@[inline] def scalarPart (m : MultivectorDA sig) : Float :=
  m.coeffs.get! 0

/-! ### Conversions -/

@[inline] def toMultivector (m : MultivectorDA sig) : Multivector sig Float :=
  ⟨fun i => m.coeffs.get! i.val⟩

@[inline] def ofMultivector (m : Multivector sig Float) : MultivectorDA sig :=
  let arr : Array Float := Array.ofFn (n := 2 ^ n) fun i => m.coeffs i
  ⟨DataArray.ofArray arr⟩

instance : Coe (MultivectorDA sig) (Multivector sig Float) := ⟨toMultivector⟩

end MultivectorDA

end Grassmann
