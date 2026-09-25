import Clifford.Sparse
import Clifford.MultiGrade

/-!
# Clifford

Lean port of chakravala/Clifford.jl: sparse graded storage over the `Grassmann` static layer
(port-notes/applied-misc.md §1.3, §2.3, §4.3). Upstream the package only defines `greet()`; its
`SparseChain`/`MultiGrade` code is never loaded and targets an old Grassmann API, so the port
implements the intended semantics and checks them against Grassmann's dense containers.

* `Clifford.SparseChain V G α`: a grade-`G` element as sorted `(index, value)` pairs; `+ - *`,
  involutions and complements; `toChain`, `toMultivector`.
* `Clifford.chainValues`: Julia's `chainvalues` densify rule (`fill_limit = 0.5`).
* `Clifford.MultiGrade V α`: the nonzero homogeneous parts in ascending grade, each dense or
  sparse; the grade mask, `+ - *`, involutions, complements (grade `g ↦ n - g`), accessors
  (`scalar`, `vector`, `volume`, `isScalar`, `isVector`, `terms`, `value`), `compress`.

```lean
open Grassmann Clifford in
#eval toString (SparseChain.ofTerms [(0b0001, (1 : Int)), (0b0100, -2)] : SparseChain ℝ3 1 Int)
-- "1v₁ - 2v₃"
```
-/
