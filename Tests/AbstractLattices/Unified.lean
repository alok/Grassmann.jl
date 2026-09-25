import DeMorgan
import Dendriform
import Grassmann
import Tests.DeMorgan

/-!
One `∧`/`∨` across the stack (Julia: `∧ === wedge`, `∨ === vee` are single generic
functions of AbstractLattices extended by every package). AbstractTensors' `Wedge`/`Vee` are
aliases of `AbstractLattices.HWedge`/`HVee`, so the scoped `∧`/`∨` of AbstractLattices,
AbstractTensors and Grassmann all reach Bool, DeMorgan's truth values and tables, Dendriform's
grafting and Grassmann's products. Compile-time checks only.
-/

namespace LatticeUnifiedTests

/-! ## One class family -/

example : @AbstractTensors.Wedge = @AbstractLattices.HWedge := rfl
example : @AbstractTensors.Vee = @AbstractLattices.HVee := rfl
example : @AbstractTensors.wedge = @AbstractLattices.HWedge.wedge := rfl
example : @Grassmann.Wedge = @AbstractLattices.HWedge := rfl
example : AbstractTensors.wedge true false = false := by decide
example : AbstractTensors.vee true false = true := by decide

/-! ## `open AbstractLattices`: DeMorgan and Dendriform without Grassmann -/

section
open AbstractLattices DeMorgan

-- DeMorgan README table 2 (README.md:27-41), written with `∧`
#guard TruthTable.render (truthtable p q r in ((p ⇒ q) ∧ (q ⇒ r)) ⇒ (p ⇒ r)) == Tests.DeMorgan.readme2
example : (TruthValues.ofNat 2 0b0011 ∧ TruthValues.ofNat 2 0b0101).toNat = 1 := by decide
example : (TruthValues.ofNat 2 0b0011 ∨ TruthValues.ofNat 2 0b0101).toNat = 7 := by decide
-- De Morgan's law with the lattice notation
#guard (List.range 16).all fun a => (List.range 16).all fun b =>
  let p := TruthValues.ofNat 2 a
  let q := TruthValues.ofNat 2 b
  (p ∧ q).not == (p.not ∨ q.not)

-- Dendriform grafting `l ∨ r` (DF/arithmetic.jl:38-57)
example : (Dendriform.Tree.leaf ∨ Dendriform.Tree.leaf) = Dendriform.Tree.node .leaf .leaf := rfl
example : ((Dendriform.Tree.leaf ∨ Dendriform.Tree.leaf) ∨ Dendriform.Tree.leaf).deg = 2 := rfl

-- core `∧`/`∨` on propositions still elaborate
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := ⟨hp, hq⟩
example : (1 = 1) ∨ False := Or.inl rfl
-- Bool lattices through the function names (`a ∧ b` on two Bools is ambiguous: use `&&`)
example : wedge true false = false := rfl
end

/-! ## `open Grassmann`: the exterior product and the lattices share `∧` -/

section
open Grassmann DeMorgan

example : (TruthValues.ofNat 2 0b0011 ∧ TruthValues.ofNat 2 0b0101).toNat = 1 := by decide
example : (Dendriform.Tree.leaf ∨ Dendriform.Tree.leaf) = Dendriform.Tree.node .leaf .leaf := rfl
#guard toString ((Chain.ofList? (V := ℝ3) (G := 1) [(1 : Int), 2, 3]).get! ∧
  (Chain.ofList? (V := ℝ3) (G := 1) [(4 : Int), 5, 6]).get! : Chain ℝ3 2 Int) == "-3v₁₂ - 6v₁₃ - 3v₂₃"
end

end LatticeUnifiedTests
