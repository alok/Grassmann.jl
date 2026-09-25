/-
The proofs suite (docs/PROOFS.md):

* `Tests.Proofs.Axioms`: compile-time audit that the flagship theorems use only
  Lean's standard axioms;
* `Tests.Proofs.Model`: the compiled implementation against the run-time
  specification model on random inputs in spaces beyond the `decide` range;
* `Tests.Proofs.TacticExamples`: the `clifford` tactic on the identities of
  docs/TACTICS.md (compile-time).
-/
import Tests.Proofs.Axioms
import Tests.Proofs.Model
import Tests.Proofs.TacticExamples

/-- Run the proofs suite; returns `(passed, failed)`. -/
def Tests.Proofs.runAll : IO (Nat × Nat) := Tests.Proofs.run
