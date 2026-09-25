/-
The `grassmann` lemma set for `grind`.

`register_grind_attr` must run in a module of its own (like
`register_simp_attr`); the lemmas are tagged in `Grassmann.Spec.Grind`. Use it
as `grind [grassmann]` (the default `grind` set plus these lemmas) or
`grind only [grassmann]`.
-/
import Lean.Meta.Tactic.Grind

namespace Grassmann.Spec.GrindAttr

/-- The Clifford-algebra laws of `Grassmann.Spec` as `grind` lemmas:
involutions of products, generator relations, the Clifford relation for
vectors, graded commutativity of `∧`, grades of products and sums, and the
sandwich identities (docs/TACTICS.md). -/
register_grind_attr grassmann

end Grassmann.Spec.GrindAttr
