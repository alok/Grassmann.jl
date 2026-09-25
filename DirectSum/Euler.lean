/-
Blade-level predicates and counts (DirectSum.jl `src/generic.jl:44-45, 121-122`, Leibniz.jl
`src/generic.jl:14-30, 81-84, 166-186`): the tangent `order`, `isinf`/`isorigin` of a blade,
`symmetricsplit`, Julia's `≅` (same grade, order and tangent order), and the Euler
characteristic `χ` with its grade counts `count_gdims`.

`χ` keeps Julia's sign, which is the opposite of its docstring (`χ = -Σₚ (-1)ᵖ bₚ`, Leibniz
quirk Q10; Grassmann's goldens depend on it): a nonzero term of Grassmann grade `g` has
`χ = 1` for odd `g` and `-1` for even `g`, and a graded element has
`χ = Σ_{t=1}^{N+1} B[t] (-1)^t` over its 1-based grade counts `B`.

Julia defect fixed: `isorigin(e)` reads `e[hasinf(V)+1]`, the metric of a generator of the
*blade*, so it is `true` for every single-generator blade of a space with an origin
(`isorigin(v∞) = isorigin(v₁) = true` in `S"∞∅++"`); the port tests the `∅` generator.
-/
import DirectSum.Blade

namespace DirectSum

open Bits

namespace TensorBundle

variable (V : TensorBundle)

/-- Julia `order(V) = diffvars(V)` (`Leibniz.jl src/generic.jl:15`). -/
@[inline] def order : Nat := V.diffvars

/-- Julia `order(e)` of a basis blade (`DirectSum.jl src/generic.jl:44`): the number of its
tangent generators (`0` in a space without tangent variables). -/
@[inline] def orderOf (b : UInt64) : Nat := if V.diffvars > 0 then popcount (b &&& V.diffmask) else 0

/-- Julia `isinf(e)` of a basis blade (`DirectSum.jl src/generic.jl:121`): `e` is the single
generator `∞`. -/
@[inline] def isinfBlade (b : UInt64) : Bool := V.bladeHasInf b && popcount b == 1

/-- Julia `isorigin(e)` of a basis blade (`DirectSum.jl src/generic.jl:122`), corrected: `e` is
the single generator `∅`. -/
@[inline] def isoriginBlade (b : UInt64) : Bool := V.bladeHasOrigin b && popcount b == 1

/-- Julia `symmetricsplit(V, a)` (`Leibniz.jl src/generic.jl:81-84`): the tangent bits of `a`,
split into the `∂` and `ϵ` blocks for a dyadic space (the second component is `0` otherwise). -/
def symmetricsplit (a : UInt64) : UInt64 × UInt64 :=
  let sm := a &&& V.diffmask
  if V.isdyadic then (sm &&& V.diffmaskV, sm &&& V.diffmaskW) else (sm, 0)

/-- Julia `a ≅ b` for basis blades (`Leibniz.jl src/generic.jl:30`): the same Grassmann grade,
tangent order and (for both in `V`) tangent order bound `diffmode`. -/
@[inline] def sameKind (a b : UInt64) : Bool :=
  V.gradeOf a == V.gradeOf b && V.orderOf a == V.orderOf b

/-- Julia `χ(V, b, t)` of a nonzero term on blade `b` (`Leibniz.jl src/generic.jl:173`): `1` for
an odd Grassmann grade, `-1` for an even one. -/
@[inline] def chiBlade (b : UInt64) : Int := if popcount (b &&& ~~~V.diffmask) % 2 == 1 then 1 else -1

/-- Julia `count_gdims` of a list of nonzero blades (`Leibniz.jl src/generic.jl:176-186`): the
number of them in each Grassmann grade `0 … n` (length `n + 1`). -/
def countGdims (bs : Array UInt64) : Array Nat :=
  bs.foldl (fun out b => out.modify (popcount (b &&& ~~~V.diffmask)) (· + 1)) (Array.replicate (V.n + 1) 0)

end TensorBundle

/-- Julia `χ(t) = Σ_{t=1}^{N+1} B[t]·(-1)^t` from grade counts `B` (Leibniz quirk Q10: the
opposite of the docstring's `Σₚ (-1)ᵖ bₚ`). -/
def eulerChar (counts : Array Nat) : Int :=
  counts.zipIdx.foldl (fun acc (c, i) => if (i + 1) % 2 == 0 then acc + c else acc - c) 0

namespace Submanifold

variable {V : TensorBundle} {G H : Nat}

/-- Julia `order(e)`: the number of tangent generators of the blade. -/
@[inline] def order (b : Submanifold V G) : Nat := V.orderOf b.bits

/-- Julia `isinf(e)`: the blade is `v∞`. -/
@[inline] def isinf (b : Submanifold V G) : Bool := V.isinfBlade b.bits

/-- Julia `isorigin(e)` (corrected): the blade is `v∅`. -/
@[inline] def isorigin (b : Submanifold V G) : Bool := V.isoriginBlade b.bits

/-- Julia `a ≅ b` on blades of one space. -/
@[inline] def sameKind (a : Submanifold V G) (b : Submanifold V H) : Bool := V.sameKind a.bits b.bits

/-- Julia `χ(e)` of a unit blade. -/
@[inline] def chi (b : Submanifold V G) : Int := V.chiBlade b.bits

/-- Julia `count_gdims(e)` of a unit blade: `1` at its Grassmann grade. -/
@[inline] def countGdims (b : Submanifold V G) : Array Nat := V.countGdims #[b.bits]

end Submanifold

/-- Julia `a ≅ b` (same grade, order and tangent order); scoped in `DirectSum`. -/
scoped infix:50 " ≅ " => fun a b => Submanifold.sameKind a b = true

end DirectSum
