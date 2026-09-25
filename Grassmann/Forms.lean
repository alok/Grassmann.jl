import Grassmann.Forms.Mat
import Grassmann.Forms.Operator
import Grassmann.Forms.Compound
import Grassmann.Forms.Outermorphism
import Grassmann.Forms.Diagonal
import Grassmann.Forms.Roots
import Grassmann.Forms.Eigen
import Grassmann.Forms.Dyadic
import Grassmann.Forms.Spectral
import Grassmann.Forms.MatFun
import Grassmann.Forms.Cayley
import Grassmann.Forms.Show
import Grassmann.Forms.Eval
import Grassmann.Forms.Lie
import Grassmann.Forms.Simplex

/-!
# Grassmann.Forms: linear algebra of Grassmann elements

Port of Grassmann.jl `src/forms.jl` (and the determinant/simplex part of
`src/composite.jl`); port-notes/grassmann-forms.md.

## Map

* `Grassmann.Forms.Mat`: dense column-major matrices over packed coefficients
  (a `FloatArray` at `Float`), with Julia-order multiply-accumulate loops.
* `Grassmann.Forms.Operator`: `TensorOperator V ld W lc α` (Julia
  `TensorOperator{V,W,<:ld{V,<:lc{W}}}`), `Endomorphism`, `Simplex`; application
  `T x`, `T * x`, `T ⋅ x`, row application `x ⋅ T`, composition, transpose,
  trace, diagonal, uniform scalings, bilinear forms, `bivector`, `companion`.
* `Grassmann.Forms.Compound`: compounds `Λᵍ T`, `∧(T)`, `det`, the Cramer
  adjugate/cofactor/inverse/solve, pseudo-inverses.
* `Grassmann.Forms.Outermorphism`: `Outermorphism V W α`, the compounds of a
  grade-1 map acting on every grade, `Spinor`, `CoSpinor` and `Multivector`.
* `Grassmann.Forms.Diagonal`: `DiagonalOperator V l α`, `DiagonalMorphism`,
  `DiagonalOutermorphism`.
* `Grassmann.Forms.Roots`: Julia's closed-form roots of monic polynomials of
  degree ≤ 4 (`monicroots`, `monicrootsreal`, `monicrootscomplex`, `quartic`,
  `cubicmax`) and the `Spectrum` result type.
* `Grassmann.Forms.Eigen`: the dense real eigensolver standing in for LAPACK
  (symmetric `tred2`/`tql2`, general `orthes`/`hqr2`).
* `Grassmann.Forms.Dyadic`: `Dyadic`, `Projector`, `SpectralOperator`.
* `Grassmann.Forms.Spectral`: `characteristic`, `eigpolys`, `sylvester`,
  `eigmults`, `eigvals*`, `eigen*`, `vandermonde`, `discriminant*`.
* `Grassmann.Forms.MatFun`: `exp`, `expm1` (Grassmann's Padé), `log`.
* `Grassmann.Forms.Cayley`: `operator(t, G)`, `gradedoperator`, `metrictensor`,
  `metricextensor`, `antimetrictensor`, Cayley tables.
* `Grassmann.Forms.Show`: Julia's 2-arg and 3-arg display, `printtex`, `alltex`.
* `Grassmann.Forms.Eval`: multilinear evaluation `t(y…)`, subspace projection and
  embedding, `vecdot`.
* `Grassmann.Forms.Lie`: multilinear Lie brackets.
* `Grassmann.Forms.Simplex`: `affineframe`, `mean`, `barycenter`, `centroid`,
  `detsimplex`, `volume`, `∈`, barycentric `gradient`, `gradienthat`, `area`,
  `findfirst`/`findlast`/`findall`.

## Performance

Operators store their entries in one column-major `FloatArray` (at `Float`); the
application, composition and row-application loops are tail-recursive strided dots
specialised at the coefficient type. The determinant family runs the reference
wedge kernels in the Euclidean space of the codomain's dimension.
-/
