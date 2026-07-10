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
      let pi := packIdxValid n p mask
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
  cases p <;> simp_all [packIdx, packIdxValid, i.isLt]

/-- Tail-recursive dense ingress for identity-indexed full storage. -/
private def ofMultivectorFullAux (m : @& Multivector sig Float) (i : Nat) :
    (remaining : Nat) → i + remaining ≤ 2 ^ n → FloatArray → FloatArray
  | 0, _hbound, out => out
  | remaining + 1, hbound, out =>
      have hmask : i < 2 ^ n := by omega
      have hnext : i + 1 + remaining ≤ 2 ^ n := by omega
      ofMultivectorFullAux m (i + 1) remaining hnext
        (out.push (m.coeffs ⟨i, hmask⟩))

private theorem ofMultivectorFullAux_size (m : Multivector sig Float) (i remaining : Nat)
    (hbound : i + remaining ≤ 2 ^ n) (out : FloatArray) :
    (ofMultivectorFullAux m i remaining hbound out).size = out.size + remaining := by
  induction remaining generalizing i out with
  | zero => simp [ofMultivectorFullAux]
  | succ remaining ih =>
      simp only [ofMultivectorFullAux]
      rw [ih]
      simp [FloatArray.push, FloatArray.size, Nat.add_comm,
        Nat.add_left_comm]

/-- Tail-recursive dense ingress for even or odd packed storage. -/
private def ofMultivectorPackedAux (p : Parity)
    (m : @& Multivector sig Float) (i : Nat) :
    (remaining : Nat) → i + remaining ≤ storageSize n p → FloatArray → FloatArray
  | 0, _hbound, out => out
  | remaining + 1, hbound, out =>
      have hi : i < storageSize n p := by omega
      let mask := unpackIdxValid n p i
      have hmask : mask < 2 ^ n := unpackIdxValid_lt n p i hi
      have hnext : i + 1 + remaining ≤ storageSize n p := by omega
      ofMultivectorPackedAux p m (i + 1) remaining hnext
        (out.push (m.coeffs ⟨mask, hmask⟩))

private theorem ofMultivectorPackedAux_size (p : Parity) (m : Multivector sig Float)
    (i remaining : Nat) (hbound : i + remaining ≤ storageSize n p) (out : FloatArray) :
    (ofMultivectorPackedAux p m i remaining hbound out).size = out.size + remaining := by
  induction remaining generalizing i out with
  | zero => simp [ofMultivectorPackedAux]
  | succ remaining ih =>
      simp only [ofMultivectorPackedAux]
      rw [ih]
      simp [FloatArray.push, FloatArray.size, Nat.add_comm,
        Nat.add_left_comm]

/-- Convert from a proof-friendly dense `Multivector`.

The dense coefficient closure is consumed synchronously into one native result
buffer and does not escape in the packed value, so the input can be borrowed.
This differs intentionally from `toMultivector`, whose returned closure owns
the packed value that it captures. -/
@[inline]
def ofMultivector (m : @& Multivector sig Float) (p : Parity) : MV sig p :=
  match p with
  | .full =>
      let sz := storageSize n .full
      let coeffs := ofMultivectorFullAux m 0 sz (by simp [sz, storageSize])
        (FloatArray.emptyWithCapacity sz)
      have hsize : coeffs.size = storageSize n .full := by
        dsimp only [coeffs]
        rw [ofMultivectorFullAux_size]
        simp [sz, FloatArray.emptyWithCapacity, FloatArray.size]
      ofDataArray sig .full coeffs hsize
  | .even =>
      let sz := storageSize n .even
      let coeffs := ofMultivectorPackedAux .even m 0 sz (by simp [sz])
        (FloatArray.emptyWithCapacity sz)
      have hsize : coeffs.size = storageSize n .even := by
        dsimp only [coeffs]
        rw [ofMultivectorPackedAux_size]
        simp [sz, FloatArray.emptyWithCapacity, FloatArray.size]
      ofDataArray sig .even coeffs hsize
  | .odd =>
      let sz := storageSize n .odd
      let coeffs := ofMultivectorPackedAux .odd m 0 sz (by simp [sz])
        (FloatArray.emptyWithCapacity sz)
      have hsize : coeffs.size = storageSize n .odd := by
        dsimp only [coeffs]
        rw [ofMultivectorPackedAux_size]
        simp [sz, FloatArray.emptyWithCapacity, FloatArray.size]
      ofDataArray sig .odd coeffs hsize

instance instCoeEvenToMV : Coe (MV sig .even) (Multivector sig Float) :=
  ⟨toMultivector⟩

instance instCoeOddToMV : Coe (MV sig .odd) (Multivector sig Float) :=
  ⟨toMultivector⟩

instance instCoeFullToMV : Coe (MV sig .full) (Multivector sig Float) :=
  ⟨toMultivector⟩

end MV
end Grassmann
