/-
The `grassmann` lemma set: the laws of `Grassmann.Spec` as `grind` lemmas.

`grind [grassmann]` combines them with `grind`'s non-commutative ring
normalizer for `Cl g` (`Cl.instRing`) and its commutative ring solver for the
coefficients. What is in the set, and how it fires:

* **involutions** (normalization rules of the default `grind` set, see
  below): reversion, grade involution and Clifford conjugation pushed through
  `+ - * • ∧`, and evaluated on `0`, `1`, scalars and generators;
  `~~x = x`, `x̂̂ = x`; on vectors (`=`, conditional): `ṽ = v`, `v̂ = -v`;
* **generators** (`=`): `eᵢ² = gᵢ`, `eᵢ eⱼ = -eⱼ eᵢ` (`i ≠ j`, decided by
  `grind`);
* **vectors** (`=`, conditional on `IsGrade 1`): the Clifford relation
  `v² = B(v,v)`, `u v = B(u,v) + u ∧ v`, `u v + v u = 2B(u,v)`,
  `u ∧ v = -(v ∧ u)`, `v ∧ v = 0`;
* **grades** (backward, `←`): `IsGrade k` of `0`, sums, negations,
  differences, scalar multiples, scalars (`k = 0`) and generators (`k = 1`),
  so `IsGrade 1 (a • e₁ + b • e₂)` is derived when a vector lemma needs it;
  `∧` of homogeneous elements and graded commutativity fire on existing
  `∧`-terms whose factors are known to be homogeneous (multi-patterns);
* **sandwiches**: with `R̃ R = 1` sandwiching is
  multiplicative and (with `R R̃ = 1`) an isometry on vectors; the grade
  preservation theorems for even `R` (2-torsion-free rings).

Associativity is left to the ring normalizer; for identities that need a
product re-bracketed inside a larger term, add `Cl.mul_assoc`
(`grind [grassmann, Cl.mul_assoc]`). Coordinate computations in a concrete
space are the `clifford` tactic's job (docs/TACTICS.md).
-/
import Grassmann.Spec.GrindAttr
import Grassmann.Spec.Ring
import Grassmann.Spec.Sandwich

namespace Grassmann.Spec.Cl

/-! ## Involutions: normalization rules

Pushing reversion, grade involution and Clifford conjugation inward is a
terminating, confluent rewrite system, so it runs in `grind`'s preprocessor
(`[grind norm]`; normalization rules can only be attached to the default
`grind` attribute). Products then reach the non-commutative ring normalizer
with the involutions on their atoms: `~(x y z) = z̃ ỹ x̃` is plain `grind`.
These rules only touch terms built from `Cl.reverse`, `Cl.involute` and
`Cl.clifford`, and only in modules that import this one. -/

attribute [grind norm] reverse_mul reverse_add reverse_neg reverse_sub reverse_smul reverse_zero
  reverse_one reverse_scalar reverse_gen reverse_reverse reverse_wedge
attribute [grind norm] involute_mul involute_add involute_neg involute_sub involute_smul involute_zero
  involute_one involute_scalar involute_gen involute_involute involute_wedge
attribute [grind norm] clifford_eq

/-! ## Involutions of homogeneous elements -/

attribute [grassmann =] reverse_of_vector involute_of_vector

/-! ## Generators and vectors -/

attribute [grassmann =] gen_mul_self gen_mul_gen_comm
attribute [grassmann =] mul_self_of_vector mul_add_mul_swap wedge_self_of_vector wedge_comm_vec
  contract_of_vector

/-! ## Grades -/

attribute [grassmann ←] IsGrade.zero IsGrade.add IsGrade.neg IsGrade.sub IsGrade.smul isGrade_scalar
  isGrade_gen isGrade_proj

grind_pattern [grassmann] isGrade_wedge => wedge x y, IsGrade p x, IsGrade q y
grind_pattern [grassmann] wedge_comm_of_even => wedge x y, IsGrade p x, IsGrade q y
grind_pattern [grassmann] wedge_comm_of_odd => wedge x y, IsGrade p x, IsGrade q y

/-! ## Sandwiches -/

attribute [grassmann =] sandwich_mul sandwich_scalar sandwich_sq_of_vector proj_sandwich_of_even
attribute [grassmann ←] isGrade_sandwich_of_even

end Grassmann.Spec.Cl
