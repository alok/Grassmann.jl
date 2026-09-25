import Grassmann.Tactic.Coord
import Grassmann.Tactic.Clifford

/-!
# Grassmann.Tactic: proof automation for the specification model

* `Grassmann.Tactic.Coord`: reflection of multivector expressions of a
  concrete space (`MExpr`) and their dense coordinates as polynomials
  (`Poly`), with the soundness theorems `eq_of_coords` and `coords_of_eq`;
* `Grassmann.Tactic.Clifford`: the `clifford` tactic (and `clifford_nf`),
  which decides identities between multivector expressions of a concrete space
  (numeral dimension, any metric, coefficients in any commutative ring,
  symbolic scalars and multivectors allowed) by blade extensionality and
  `grind`'s ring normalization.

docs/TACTICS.md documents the tactics and the `grind` extension of the
specification algebra.
-/
