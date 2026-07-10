/-
  Grassmann/ReprTheorems.lean - unsafe representation theorem drafts

  WARNING: This module is explicitly proof-only and axiom-backed.  Its theorem
  statements are preserved as migration targets, but their current `[BEq F]`
  assumptions are underspecified: an arbitrary `BEq` need not agree with
  equality, so the statements are not valid as written.  Do not import this
  module from computational code or from `Grassmann.Reference`.
-/
import Grassmann.Repr
import Grassmann.Proof

open Grassmann.Proof

namespace Grassmann

variable {n : ℕ} {sig : Signature n} {F : Type*}

/-! ## Draft conversion theorems

These names remain available to explicit proof-development imports while the
statements are strengthened (for example with lawful equality assumptions)
and the placeholder proofs are replaced.
-/

theorem denseToSparse_add [Ring F] [BEq F] (a b : Multivector sig F) :
    denseToSparse (a.add b) = (denseToSparse a).add (denseToSparse b) := by
  sorry_proof

theorem denseToSparse_mul [Ring F] [BEq F] (a b : Multivector sig F) :
    denseToSparse (a * b) = (denseToSparse a) * (denseToSparse b) := by
  sorry_proof

theorem sparseToDense_add [Ring F] [BEq F] (a b : MultivectorS sig F) :
    sparseToDense (a.add b) = (sparseToDense a).add (sparseToDense b) := by
  sorry_proof

theorem sparseToDense_mul [Ring F] [BEq F] (a b : MultivectorS sig F) :
    sparseToDense (a * b) = (sparseToDense a) * (sparseToDense b) := by
  sorry_proof

theorem roundtrip_dense_sparse [Ring F] [BEq F] (m : Multivector sig F) :
    sparseToDense (denseToSparse m) = m := by
  sorry_proof

end Grassmann
