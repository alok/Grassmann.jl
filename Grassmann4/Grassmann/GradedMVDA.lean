/-
  Grassmann/GradedMVDA.lean - Grade-tracked Float kernels on `DataArray`

  `GradedMV` (in `GradeSet.lean`) is a dependent-type wrapper that carries a
  compile-time grade-set upper bound. In the long term, that information should
  *pay for itself* by selecting sparse kernels that iterate only over grades
  known to be potentially non-zero.

  This file provides the same idea for the `DataArray` (`FloatArray`) backend:
  keep runtime storage contiguous and fast, while using dependent grade metadata
  to skip provably-zero work.
-/
import Grassmann.MultivectorDA
import Grassmann.BladeIndex
import Grassmann.SignTables

namespace Grassmann

variable {n : ℕ} {sig : Signature n}

namespace MultivectorDA

@[inline] private def sizeFull (n : Nat) : Nat := 2 ^ n

/-- Sparse geometric product for `MultivectorDA`.

This iterates only over the provided index lists. It uses cached `SignTable`s for
canonical small signatures when available, falling back to `geometricSign`.
-/
def geometricProductSparseArray (a b : MultivectorDA sig)
    (aIdx bIdx : Array (Fin (2 ^ n))) : MultivectorDA sig := Id.run do
  let mut out : DataArray := DataArray.zeros (sizeFull n)
  match Grassmann.cachedSignTable (n := n) sig with
  | some table =>
      for i in aIdx do
        let ai := a.coeffs.get! i.val
        for j in bIdx do
          let sign := table.lookup i.val j.val
          if sign != 0 then
            let resIdx := i.val ^^^ j.val
            let bj := b.coeffs.get! j.val
            let coeff := ai * bj
            let contrib := if sign < 0 then -coeff else coeff
            let old := out.get! resIdx
            out := out.set! resIdx (old + contrib)
      return ⟨out⟩
  | none =>
      for i in aIdx do
        let bi : Blade sig := ⟨BitVec.ofNat n i.val⟩
        let ai := a.coeffs.get! i.val
        for j in bIdx do
          let bjBlade : Blade sig := ⟨BitVec.ofNat n j.val⟩
          let sign := geometricSign sig bi bjBlade
          if sign != 0 then
            let resIdx := i.val ^^^ j.val
            let bj := b.coeffs.get! j.val
            let coeff := ai * bj
            let contrib := if sign < 0 then -coeff else coeff
            let old := out.get! resIdx
            out := out.set! resIdx (old + contrib)
      return ⟨out⟩

end MultivectorDA

/-! ## GradedMVDA

Zero-cost wrapper around `MultivectorDA` carrying a type-level `GradeSet`.
The grade set is an *upper bound* (may be larger than the true support).
-/

structure GradedMVDA (sig : Signature n) (grades : GradeSet) where
  mv : MultivectorDA sig

namespace GradedMVDA

variable {gs gs1 gs2 : GradeSet}

/-- Forget grade information. -/
@[inline] def toMultivectorDA (gm : GradedMVDA sig gs) : MultivectorDA sig := gm.mv

/-- Widen grade information (always safe: upper bounds only get looser). -/
@[inline] def widen (gm : GradedMVDA sig gs) (gs' : GradeSet) :
    GradedMVDA sig (gs.union gs') :=
  ⟨gm.mv⟩

/-- Scalar (grade 0). -/
@[inline] def scalar (x : Float) : GradedMVDA sig GradeSet.scalar :=
  ⟨MultivectorDA.scalar (sig := sig) (n := n) x⟩

/-- Sparse geometric product driven by compile-time grade sets. -/
@[inline]
def mulSparse (a : GradedMVDA sig gs1) (b : GradedMVDA sig gs2) :
    GradedMVDA sig (geometricGradeSet gs1 gs2 n) :=
  let aIdx := gradeSetIndicesFastArray n gs1
  let bIdx := gradeSetIndicesFastArray n gs2
  ⟨MultivectorDA.geometricProductSparseArray (sig := sig) (n := n) a.mv b.mv aIdx bIdx⟩

instance : HMul (GradedMVDA sig gs1) (GradedMVDA sig gs2)
    (GradedMVDA sig (geometricGradeSet gs1 gs2 n)) where
  hMul := mulSparse (sig := sig) (n := n) (gs1 := gs1) (gs2 := gs2)

end GradedMVDA

instance {gs : GradeSet} : CoeTC (GradedMVDA sig gs) (MultivectorDA sig) :=
  ⟨fun gm => gm.mv⟩

end Grassmann

