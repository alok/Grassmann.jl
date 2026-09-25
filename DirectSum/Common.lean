/-
Common spaces (DirectSum.jl `src/DirectSum.jl:442-450`, DESIGN.md §3).

`ℝ0 … ℝ9` are Julia's `Submanifold(n)` handles of the `Int n` spaces (printed
`⟨111⟩`), while `ℝ^n` is the `Signature` `⟨+++⟩`; both are Euclidean and have
identical products. The named algebras are `abbrev`s of structure literals so
instances keyed on them are found after reducible unfolding.
-/
import DirectSum.Parse

namespace DirectSum

/-- Julia `ℝ0 = Submanifold(0)`. -/
abbrev ℝ0 : TensorBundle := V!"0"
/-- Julia `ℝ1 = Submanifold(1)`. -/
abbrev ℝ1 : TensorBundle := V!"1"
/-- Julia `ℝ2 = Submanifold(2)`, printed `⟨11⟩`. -/
abbrev ℝ2 : TensorBundle := V!"2"
/-- Julia `ℝ3 = Submanifold(3)`, printed `⟨111⟩`. -/
abbrev ℝ3 : TensorBundle := V!"3"
/-- Julia `ℝ4 = Submanifold(4)`, printed `⟨1111⟩`. -/
abbrev ℝ4 : TensorBundle := V!"4"
/-- Julia `ℝ5 = Submanifold(5)`. -/
abbrev ℝ5 : TensorBundle := V!"5"
/-- Julia `ℝ6 = Submanifold(6)`. -/
abbrev ℝ6 : TensorBundle := V!"6"
/-- Julia `ℝ7 = Submanifold(7)`. -/
abbrev ℝ7 : TensorBundle := V!"7"
/-- Julia `ℝ8 = Submanifold(8)`. -/
abbrev ℝ8 : TensorBundle := V!"8"
/-- Julia `ℝ9 = Submanifold(9)`. -/
abbrev ℝ9 : TensorBundle := V!"9"

/-- ASCII alias of `ℝ2`. -/
abbrev R2 : TensorBundle := ℝ2
/-- ASCII alias of `ℝ3`. -/
abbrev R3 : TensorBundle := ℝ3
/-- ASCII alias of `ℝ4`. -/
abbrev R4 : TensorBundle := ℝ4
/-- ASCII alias of `ℝ5`. -/
abbrev R5 : TensorBundle := ℝ5

/-- Spacetime algebra `Cl(1,3)` with signature `-+++` (Julia `S"-+++"`). -/
abbrev STA : TensorBundle := S!"-+++"
/-- Plane projective geometric algebra: degenerate `e₁² = 0`, `D"0,1,1"`. -/
abbrev PGA2 : TensorBundle := D!"0,1,1"
/-- Space projective geometric algebra: `D"0,1,1,1"`. -/
abbrev PGA3 : TensorBundle := D!"0,1,1,1"
/-- Plane conformal geometric algebra `S"∞∅++"`. -/
abbrev CGA2 : TensorBundle := S!"∞∅++"
/-- Space conformal geometric algebra `S"∞∅+++"`. -/
abbrev CGA3 : TensorBundle := S!"∞∅+++"

end DirectSum
