/-
  Grassmann/Proof.lean - explicitly opt-in proof placeholders

  This module provides sorry_proof and sorry_data macros following the
  SciLean pattern for separating computation from proof obligations.

  Importing this module adds axioms to the environment.  Supported
  computational modules must not import it transitively.  In particular, this
  module deliberately provides no `Ring Float` or `Field Float` instance:
  IEEE-754 arithmetic does not satisfy those structures' laws.

  Reference: https://github.com/lecopivo/SciLean
-/

namespace Grassmann.Proof

/-! ## Sorry Proof Infrastructure

The sorry_proof macro allows stating theorems without blocking compilation.
Unlike regular sorry, this clearly marks intentional proof gaps vs bugs.
-/

/-- Axiom for proof obligations we intend to discharge later.
    Using a dedicated axiom makes it easy to:
    1. Search for remaining proof obligations
    2. Track which theorems are "proven" vs "stated"
    3. Avoid mixing sorry for proofs vs sorry for code -/
axiom sorryProofAxiom {P : Prop} : P

/-- Axiom for data that we haven't implemented yet.
    Similar to sorry_proof but for terms instead of proofs. -/
axiom sorryDataAxiom {α : Type _} : α

/-- sorry_proof as a term (for direct use in expressions) -/
macro "sorry_proof" : term => `(sorryProofAxiom)

/-- sorry_proof as a tactic (for use in proof mode) -/
macro "sorry_proof" : tactic => `(tactic| exact sorry_proof)

/-- sorry_data for placeholder data values -/
macro "sorry_data" : term => `(sorryDataAxiom)

/-- sorry_data as a tactic for term-mode goals -/
macro "sorry_data" : tactic => `(tactic| exact sorry_data)

/-! ## Proof Status Tracking

We define attributes to track proof status for auditing.
-/

/-- Attribute marking theorems with complete proofs -/
macro "proven" : attr => `(attr| simp)  -- placeholder, could be custom attribute

/-- Attribute marking theorems stated but not proven -/
macro "stated" : attr => `(attr| simp)  -- placeholder

/-! ## Tolerance-based Float Comparisons

Since Float equality is unreliable, we provide tolerance-based operations.
-/

/-- Approximate equality for Float -/
def Float.approxEq (a b : Float) (tol : Float := 1e-10) : Bool :=
  Float.abs (a - b) < tol

/-- Approximate zero check -/
def Float.approxZero (a : Float) (tol : Float := 1e-10) : Bool :=
  Float.abs a < tol

end Grassmann.Proof
