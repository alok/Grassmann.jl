/-
Integer range builders (Julia `StaticVectors.jl src/StaticVectors.jl:72-93`).

These are **data**, not indices: they keep Julia's 1-based values. Code that
feeds them back in as `Values` indices must subtract 1.
-/
import StaticVectors.Values

namespace StaticVectors

/-- Length of Julia's `countvalues(a, b)`: `max(0, b - a + 1)`. -/
def countLen (a b : Int) : Nat := (b - a + 1).toNat

/-- Julia `countvalues(a, b)` (`SV/StaticVectors.jl:72`): `Values(a:b...)`,
i.e. `[a, a+1, …, b]`, empty when `b < a`. -/
def countvalues (a b : Int) : Values Int (countLen a b) :=
  Values.ofFn fun i => a + i.1

/-- Length of `evenvalues(a, b)`: `⌊(b - a)/2⌋ + 1` when `b ≥ a`, else `0`.

Julia computes `((b-a)÷2)+1` with truncating division, which is wrong for
`b = a-1` (length 1 for an empty range: MethodError) and for `b ≤ a-4`
(negative length: DimensionMismatch) (bug B17). We return the length of the
range `a:2:b` in every case, which agrees with Julia wherever Julia works. -/
def evenLen (a b : Int) : Nat := if a ≤ b then ((b - a) / 2 + 1).toNat else 0

/-- Julia `evenvalues(a, b)`, alias `evens` (`SV/StaticVectors.jl:86`):
`[a, a+2, …]` up to `b`. -/
def evenvalues (a b : Int) : Values Int (evenLen a b) :=
  Values.ofFn fun i => a + 2 * i.1

/-- Julia `evens` (alias of `evenvalues`). -/
abbrev evens (a b : Int) : Values Int (evenLen a b) := evenvalues a b

@[simp] theorem get_countvalues (a b : Int) (i : Fin (countLen a b)) :
    (countvalues a b).get i = a + i.1 := by simp [countvalues]

@[simp] theorem get_evenvalues (a b : Int) (i : Fin (evenLen a b)) :
    (evenvalues a b).get i = a + 2 * i.1 := by simp [evenvalues]

example : (countvalues 1 4).toList = [1, 2, 3, 4] := by decide
example : (countvalues 3 1).toList = [] := by decide
example : (countvalues (-2) 2).toList = [-2, -1, 0, 1, 2] := by decide
example : (evenvalues 0 5).toList = [0, 2, 4] := by decide
example : (evenvalues 1 6).toList = [1, 3, 5] := by decide
example : (evenvalues 0 6).toList = [0, 2, 4, 6] := by decide
example : (evenvalues 2 2).toList = [2] := by decide
example : (evenvalues 4 2).toList = [] := by decide
example : (evenvalues (-3) 3).toList = [-3, -1, 1, 3] := by decide
example : (evens 2 7).toList = [2, 4, 6] := by decide
-- Julia errors on these (B17); the Lean versions are the (empty) ranges.
example : (evenvalues 3 2).toList = [] := by decide
example : (evenvalues 6 2).toList = [] := by decide

end StaticVectors
