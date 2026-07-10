/-
  Grassmann/ReferenceSoundnessTests.lean - Reference-import soundness firewall

  This compile-only module verifies that the opt-in reference surface retains
  executable Float arithmetic without reintroducing false algebraic laws or
  exposing the proof-placeholder axioms.
-/
import Grassmann.Reference
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Field.Defs

namespace Grassmann
namespace ReferenceSoundnessTests

set_option linter.hashCommand false

/-- Local name avoids the `R3 { ... }` command syntax exported by the DSL. -/
private abbrev TestR3 : Signature 3 := Signature.euclidean 3

/-! ## Negative soundness firewall -/

/-- `import Grassmann.Reference` must not manufacture ring laws for IEEE Float. -/
example : True := by
  fail_if_success
    let _ := (inferInstance : Ring Float)
  trivial

/-- `import Grassmann.Reference` must not manufacture field laws for IEEE Float. -/
example : True := by
  fail_if_success
    let _ := (inferInstance : Field Float)
  trivial

/-- The proof-placeholder axiom must not be reachable through the reference API. -/
example : True := by
  fail_if_success exact Grassmann.Proof.sorryProofAxiom
  trivial

/-- The data-placeholder axiom must not be reachable through the reference API. -/
example : Nat := by
  fail_if_success exact Grassmann.Proof.sorryDataAxiom
  exact 0

/-! ## Positive computational capabilities -/

#synth Zero Float
#synth One Float
#synth OfNat Float 2
#synth Add Float
#synth Sub Float
#synth Neg Float
#synth Mul Float
#synth Div Float
#synth BEq Float
#synth CoeffOps Float

#synth (GAlgebra TestR3 (Multivector TestR3 Float) Float)
#synth (GAlgebra TestR3 (MultivectorS TestR3 Float) Float)
#synth (GAlgebra TestR3 (TruncatedMV TestR3 2 Float) Float)

/-! ## Genuine-ring compatibility -/

#synth Ring Int
#synth CoeffOps Int
#synth (GAlgebra TestR3 (Multivector TestR3 Int) Int)
#synth (GAlgebra TestR3 (MultivectorS TestR3 Int) Int)
#synth (GAlgebra TestR3 (TruncatedMV TestR3 2 Int) Int)

/-! ## IEEE behavior and representative computations -/

/- Concrete witness that Float addition is not associative. -/
#guard
  let a : Float := 1e20
  let b : Float := -1e20
  let c : Float := 3.14
  (a + b) + c != a + (b + c)

/- Dense Float multiplication remains executable. -/
#guard
  let e1Dense : Multivector TestR3 Float :=
    Multivector.basis ⟨0, by decide⟩
  let e2Dense : Multivector TestR3 Float :=
    Multivector.basis ⟨1, by decide⟩
  let e12Dense := e1Dense * e2Dense
  e12Dense.coeff (e12 : Blade TestR3) == 1.0 &&
    (e2Dense * e1Dense).coeff (e12 : Blade TestR3) == -1.0

/- Sparse Float multiplication remains executable. -/
#guard
  let e1Sparse : MultivectorS TestR3 Float :=
    MultivectorS.basis ⟨0, by decide⟩
  let e2Sparse : MultivectorS TestR3 Float :=
    MultivectorS.basis ⟨1, by decide⟩
  let e12Sparse := e1Sparse * e2Sparse
  e12Sparse.coeff 3 == 1.0 && e12Sparse.nnz == 1

/- Grade-truncated Float multiplication remains executable. -/
#guard
  let e1Truncated : TruncatedMV TestR3 2 Float :=
    TruncatedMV.basis ⟨0, by decide⟩
  let e2Truncated : TruncatedMV TestR3 2 Float :=
    TruncatedMV.basis ⟨1, by decide⟩
  let e12Truncated := TruncatedMV.geometricProduct e1Truncated e2Truncated
  e12Truncated.coeff 3 == 1.0 && e12Truncated.nnz == 1

/- Dense, sparse, and truncated conversions preserve representative Float coefficients. -/
#guard
  let e1Dense : Multivector TestR3 Float :=
    Multivector.basis ⟨0, by decide⟩
  let e2Dense : Multivector TestR3 Float :=
    Multivector.basis ⟨1, by decide⟩
  let dense := (e1Dense.smul 2.0).add (e2Dense.smul (-3.0))
  let sparse := denseToSparse dense
  let truncated : TruncatedMV TestR3 2 Float := sparseToTruncated sparse
  let sparseBack := truncatedToSparse truncated
  let denseBack := sparseToDense sparseBack
  sparse.coeff 1 == 2.0 && sparse.coeff 2 == -3.0 &&
    truncated.coeff 1 == 2.0 && truncated.coeff 2 == -3.0 &&
    sparseBack.coeff 1 == 2.0 && sparseBack.coeff 2 == -3.0 &&
    denseBack.coeff (e1 : Blade TestR3) == 2.0 &&
    denseBack.coeff (e2 : Blade TestR3) == -3.0

/- Exact-ring dense, sparse, and truncated multiplication remains available. -/
#guard
  let e1Dense : Multivector TestR3 Int :=
    Multivector.basis ⟨0, by decide⟩
  let e1Sparse : MultivectorS TestR3 Int :=
    MultivectorS.basis ⟨0, by decide⟩
  let e1Truncated : TruncatedMV TestR3 2 Int :=
    TruncatedMV.basis ⟨0, by decide⟩
  (e1Dense * e1Dense).scalarPart == 1 &&
    (e1Sparse * e1Sparse).scalarPart == 1 &&
    (TruncatedMV.geometricProduct e1Truncated e1Truncated).scalarPart == 1

end ReferenceSoundnessTests
end Grassmann
