/-
  Grassmann/MVDense.lean - Dense interoperability for packed MV

  The packed runtime in `Grassmann.MV` deliberately avoids importing the dense
  reference representation and its proof-oriented typeclass instances.  This
  opt-in module provides conversions and coercions for clients that need to
  compare or combine the two representations.
-/
import Grassmann.MV
import Grassmann.Multivector

namespace Grassmann
namespace MV

variable {n : ℕ} {sig : Signature n} {p : Parity}

/-! ### Dense Conversions -/

/-- Convert to the proof-friendly dense `Multivector` representation. -/
@[inline]
def toMultivector (m : MV sig p) : Multivector sig Float :=
  ⟨fun i =>
    let mask := i.val
    if Parity.containsMask p mask then
      let pi := packIdx n p mask
      m.coeffs.get! pi
    else 0.0⟩

/-- Dense conversion exposes the same coefficients as `MV.coeff` on in-range masks. -/
theorem toMultivector_coeff (m : MV sig p) (i : Fin (2 ^ n)) :
    (toMultivector m).coeffs i = m.coeff i.val := by
  unfold toMultivector coeff
  have hmask : i.val < 2 ^ n := i.isLt
  by_cases hparity : Parity.containsMask p i.val = true
  · simp [hmask, hparity]
  · have hparity_false : Parity.containsMask p i.val = false := by
      cases h : Parity.containsMask p i.val <;> simp_all
    simp [hmask, hparity_false]

/-- Dense conversion has zero coefficients at blades outside the packed parity. -/
theorem toMultivector_coeff_of_wrong_parity (m : MV sig p) {i : Fin (2 ^ n)}
    (hparity : Parity.containsMask p i.val = false) :
    (toMultivector m).coeffs i = 0.0 := by
  rw [toMultivector_coeff]
  exact coeff_of_wrong_parity m hparity

/-- Dense conversion reads the packed coefficient at blades inside the packed parity. -/
theorem toMultivector_coeff_of_parity (m : MV sig p) {i : Fin (2 ^ n)}
    (hparity : Parity.containsMask p i.val = true) :
    (toMultivector m).coeffs i = m.coeffs.get! (packIdx n p i.val) := by
  unfold toMultivector
  simp [hparity]

/-- Convert from a proof-friendly dense `Multivector`. -/
@[inline]
def ofMultivector (m : Multivector sig Float) (p : Parity) : MV sig p :=
  let sz := storageSize n p
  let coeffs := DataArray.ofArray ((Array.range sz).map fun pi =>
    let mask := unpackIdx n p pi
    if hmask : mask < 2 ^ n then
      m.coeffs ⟨mask, hmask⟩
    else
      0.0)
  (ofDataArray? sig p coeffs).getD (zero sig p)

instance instCoeEvenToMV : Coe (MV sig .even) (Multivector sig Float) :=
  ⟨toMultivector⟩

instance instCoeOddToMV : Coe (MV sig .odd) (Multivector sig Float) :=
  ⟨toMultivector⟩

instance instCoeFullToMV : Coe (MV sig .full) (Multivector sig Float) :=
  ⟨toMultivector⟩

end MV
end Grassmann
