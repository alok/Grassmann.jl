import Grassmann.Spec.Sum
import Grassmann.Spec.Twisted
import Grassmann.Spec.Clifford
import Grassmann.Spec.Exterior
import Grassmann.Spec.Involution
import Grassmann.Spec.Hodge
import Grassmann.Spec.Vector
import Grassmann.Spec.Contraction
import Grassmann.Spec.Ring

/-!
# Grassmann.Spec: a proved specification of the geometric algebra

A small, readable model of the Clifford algebra of a diagonal metric over any
commutative ring (`Lean.Grind.CommRing`), independent of the implementation's
data structures, with its laws proved in every dimension (docs/PROOFS.md):

* `Grassmann.Spec.Sum`: finite sums over the `2ⁿ` blades (`bsum`), with
  Fubini and xor-translation invariance;
* `Grassmann.Spec.Twisted`: twisted convolution over `(ℤ/2)ⁿ`, associative for
  every 2-cocycle (`twist_assoc`);
* `Grassmann.Spec.Clifford`: `Cl g`, the geometric product as an explicit sum
  with the reordering sign and metric factors; `mul_assoc`, unit and
  distributive laws, `eᵢ² = gᵢ`, `eᵢeⱼ = -eⱼeᵢ`, the blade table
  `blade_mul_blade`.
* `Grassmann.Spec.Exterior`: the exterior product (the zero-metric product),
  its associativity, grades and projections, `isGrade_wedge` and graded
  commutativity `wedge_comm` (`x ∧ y = (-1)^{pq} y ∧ x`);
* `Grassmann.Spec.Involution`: reversion (`reverse_mul`: `~(xy) = ~y ~x`),
  grade involution and Clifford conjugation;
* `Grassmann.Spec.Hodge`: the right complement and the Hodge star
  (`⋆x = ~x I`), `e_a ∧ !e_a = I`, and the double complements
  `!!x = (-1)^{k(n-k)} x`, `⋆⋆x = (-1)^{k(n-k)} det(g) x`;
* `Grassmann.Spec.Vector`: the Clifford relation `v² = q(v)` for vectors,
  `uv = B(u,v) + u ∧ v` and `uv + vu = 2B(u,v)`, over every commutative ring
  (characteristic 2 included);
* `Grassmann.Spec.Contraction`: Julia's contraction `x ⋅ y = ⟨~y x⟩_{p-q}` and
  the regressive product `∨` (De Morgan dual of `∧`, associative);
* `Grassmann.Spec.Ring`: `Cl g` is a `Lean.Grind.Ring`, so `grind` normalizes
  multivector expressions as non-commutative polynomials.

`Grassmann.Proofs` links this model to the kernels of the implementation.
-/
