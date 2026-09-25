import DirectSum.Bits
import DirectSum.Space
import DirectSum.Show
import DirectSum.SpaceOps
import DirectSum.Parse
import DirectSum.Common
import DirectSum.Parity
import DirectSum.BladeAlgebra
import DirectSum.Compat
import DirectSum.Blade
import DirectSum.Names
import DirectSum.Derived
import DirectSum.Ops
import DirectSum.Proofs

/-!
# DirectSum: the space and basis-blade layer

Port of DirectSum.jl and the blade-level half of Grassmann.jl `src/parity.jl`
(DESIGN.md §3; port-notes/directsum.md, grassmann-parity.md). Everything is a
pure function of a space value `V : TensorBundle` and `UInt64` blade masks
(bit `k-1` ⇔ generator `k`), exact over `Rat`.

## Map of the public API (what the Grassmann core builds on)

* **Spaces** (`DirectSum.Space`, `SpaceOps`, `Parse`, `Common`, `Show`):
  `Metric`, `TensorBundle` (`V.n`, `V.grade`, `V.isdiag`, `V.hasconformal`,
  `V.diffmask`, the metric views `V.sigBits`/`V.metricAt`/`V.gram`), the
  constructors `TensorBundle.sig`/`diag`/`metricTensor`/`euclidean`/`ofCode`,
  literals `S!"-+++"`, `D!"1,2,-3"`, `V!"∞∅+++"`, `ℝ^n`, the space algebra
  `V′`, `V ⊕ W`, `V.tangent μ ν`, and Julia-exact display (`toString`,
  `showHandle`, `bladeLabel`). Common spaces: `ℝ2 … ℝ9`, `STA`, `PGA2`,
  `PGA3`, `CGA2`, `CGA3`.
* **Index tables** (`Leibniz.Combinatorics`): `Leibniz.indexBasis n g`,
  `indexBasisAll`, `indexEven`, `indexOdd` (Julia storage orders) and the
  0-based ranks `bladeRank`, `basisRank`, `spinRank`, `antiRank` with their
  inverses `unrank`, `basisAt`, `spinAt`, `antiAt`; `choose`/`binomial`.
* **Blades**: `Submanifold V G` (static grade, runtime mask) and `SubSpace V`.
* **Blade rules**: `TensorBundle.mul`/`wedge`/`vee`/`contraction`/complements
  (`DirectSum.BladeAlgebra`) and the derived operators
  (`DirectSum.Derived`), all returning `BladeResult` (Julia's result kind:
  `𝟎`, bare blade, `Single`, sum, or tangent-nested).
* **Kernel interface** (`DirectSum.Ops`): operations as data (`BinOp`,
  `UnOp`), `apply₂`/`apply₁`, exact term lists `terms₂`/`terms₁`
  (`BladeTerm`: bits, `Rat` coefficient, tangent `z`), container `Layout`s
  and product plans `plan₂`/`plan₁` (`PlanEntry`: `out[ic] += coef·x[ia]·y[ib]`)
  for code generation and fallback kernels, and `chainResult` (DESIGN §4.2
  result containers).
* **Julia compatibility** (`DirectSum.Compat`): the bug-compatible
  `paritygeometric` used only to classify documented oracle defects.
-/
