import AbstractAnalysis

/-!
Compile-time checks of the pointwise arithmetic of AbstractAnalysis's function families and
countable arrays (src/AbstractAnalysis.jl:103-175): `FunctionVector` `-`, `/`, `^` and the
scalar forms, `FunctionArray`/`FunctionMatrix` (`eval`, `term`, `map`, `ofVector`, `+ - * /`,
the size as the pointwise `min`), `CountableArray` `/`, `^` and the index grids `grid`/`gridN`.
The expected values follow from the definitions (every operation is pointwise), so no oracle
is needed; the Float values are exact (small integers and powers of two).
-/

open _root_.AbstractAnalysis

namespace Tests.AbstractAnalysis.Families

/-- `x ↦ x + i`. -/
def fa : FunctionVector Float Float := ⟨fun x i => x + Float.ofNat i, 5⟩
/-- `x ↦ 2i`. -/
def fb : FunctionVector Float Float := ⟨fun _ i => 2 * Float.ofNat i, 3⟩

-- `FunctionVector`: `(a - b)(x)[i] = x + i - 2i`, `(a / b)(x)[i] = (x + i)/(2i)`, `a ^ b`
#guard ((fa - fb).eval 1.0).f 2 == -1.0 && (fa - fb).len == 3
#guard ((fa / fb).eval 2.0).f 2 == 1.0
#guard ((fa ^ fb).eval 1.0).f 1 == 4.0
-- scalar forms
#guard ((fa - (1.0 : Float)).eval 0.0).f 3 == 2.0 && (((1.0 : Float) - fa).eval 0.0).f 3 == -2.0
#guard ((fa / (2.0 : Float)).eval 0.0).f 3 == 1.5 && (((6.0 : Float) / fa).eval 0.0).f 3 == 2.0
#guard ((fa ^ (2.0 : Float)).eval 0.0).f 3 == 9.0 && (((2.0 : Float) ^ fa).eval 0.0).f 3 == 8.0
#guard ((fa + (1.0 : Float)).eval 0.0).f 3 == 4.0 && ((fa * (2.0 : Float)).eval 0.0).f 3 == 6.0
-- `withLen`, `term`, `map`, `powers`
#guard (fa.withLen 9).len == 9 && fa.term 4 1.0 == 5.0 && ((fa.map (· * 10)).eval 0.0).f 2 == 20.0
#guard ((FunctionVector.powers 4).eval 2.0).f 3 == 8.0 && (FunctionVector.powers 4).len == 4

/-- `x ↦ x·i·j` on a `3 × 4` grid. -/
def fm : FunctionMatrix Float Float := ⟨fun x i => x * Float.ofNat i[0] * Float.ofNat i[1], #v[3, 4]⟩
/-- `x ↦ i + j` on a `5 × 2` grid. -/
def fn : FunctionMatrix Float Float := ⟨fun _ i => Float.ofNat (i[0] + i[1]), #v[5, 2]⟩

-- `FunctionArray`: evaluation, terms, the pointwise ops and the `min` size
#guard (fm.eval 2.0).f #v[2, 3] == 12.0 && (fm.eval 2.0).size == #v[3, 4]
#guard fm.term #v[3, 4] 0.5 == 6.0
#guard ((fm + fn).eval 1.0).f #v[2, 2] == 8.0 && (fm + fn).size == #v[3, 2]
#guard ((fm - fn).eval 1.0).f #v[2, 2] == 0.0
#guard ((fm * fn).eval 1.0).f #v[1, 2] == 6.0
#guard ((fm / fn).eval 1.0).f #v[3, 1] == 0.75
#guard (((2.0 : Float) * fm).eval 1.0).f #v[1, 1] == 2.0 && ((fm.map (· + 1)).eval 1.0).f #v[1, 1] == 2.0
#guard ((FunctionArray.ofVector fa).eval 1.0).f #v[2] == 3.0 && (FunctionArray.ofVector fa).size == #v[5]

/-- `i ↦ i + j` on a `2 × 3` grid. -/
def ca : CountableArray Float 2 := ⟨fun i => Float.ofNat (i[0] + i[1]), #v[2, 3]⟩
/-- `i ↦ 2` on a `2 × 2` grid. -/
def cb : CountableArray Float 2 := ⟨fun _ => 2.0, #v[2, 2]⟩

-- `CountableArray` `/` and `^`, array and scalar forms
#guard (ca / cb).f #v[1, 1] == 1.0 && (ca / cb).size == #v[2, 2]
#guard (ca ^ cb).f #v[2, 1] == 9.0
#guard (ca / (2.0 : Float)).f #v[2, 2] == 2.0 && ((8.0 : Float) / ca).f #v[1, 1] == 4.0
#guard (ca ^ (2.0 : Float)).f #v[1, 2] == 9.0 && ((2.0 : Float) ^ ca).f #v[1, 2] == 8.0
#guard (ca.toRows) == #[#[2.0, 3.0, 4.0], #[3.0, 4.0, 5.0]]
-- index grids: `CountableArray(n, m)` and `CountableArray(n...)` of any rank
#guard (CountableArray.grid 2 3).f #v[2, 3] == (2, 3) && (CountableArray.grid 2 3).size == #v[2, 3]
#guard (CountableArray.gridN #v[2, 3, 4]).f #v[1, 2, 3] == #v[1, 2, 3]
#guard (CountableArray.gridN #v[2, 3, 4]).size == #v[2, 3, 4]

end Tests.AbstractAnalysis.Families
