import Grassmann.Spec.Sum
import Grassmann.Spec.Twisted
import Grassmann.Spec.Clifford

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

`Grassmann.Proofs` links this model to the kernels of the implementation.
-/
