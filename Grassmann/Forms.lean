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
import Grassmann.Forms.Fit
import Grassmann.Fields
import Grassmann.Calculus

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
  `eigmults`, `eigvals*`, `eigvecs*`, `eigen*`, `vandermonde`, `discriminant*`, and the
  polynomial roots of any degree (`roots*`, `monicroots*`: the closed forms of
  `Forms.Roots` up to degree 4, the companion matrix's eigenvalues beyond).
* `Grassmann.Forms.Fit`: `polynom`, `approx`, the least-squares Vandermonde fit
  `vandermonde(x, y, N)` and `vandermondeinterp`.
* `Grassmann.Fields` (imported here): `points`, `chainfield`, `vectorfield`/`pointfield`,
  the sampled curves and vector fields of versors, on the `↑`/`↓` maps of
  `Grassmann.Composite.Project`.
* `Grassmann.Calculus` (imported here): `V(∇)` (`nabla`, `nablaM` with tangent spaces),
  `∂`/`boundary`, `d`/`differential`, `δ`/`codifferential`, `gradient`, `divergence`, `curl`
  and the simplex boundary `∧(ω)⋅v1`.
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

## Fidelity

The goldens of `oracle/forms/gen.jl` (Grassmann 0.8.46) agree **bit for bit** for the
integer and floating-point operator algebra (the Cramer inverse, `\`, `det`, compounds,
characteristic polynomials, `eigpolys`, Grassmann's Padé `exp`, the display strings and
Julia's `summary` types), and to rounding for iterative numerics (LAPACK eigenvalues,
matrix `log`, the Viète roots through `acos`/`cos`). Julia defects that are fixed here
rather than replicated are listed in the module docs (`transpose` of non-grade-1
operators, `T ⋅ D`, `D ⋅ CoSpinor`, `diag` of a `CoSpinor` operator, the non-square
outermorphism's sign on grades ≥ 2, `==`, the 1×1 adjugate, `det(::SpectralOperator)`,
`P[i,j]`, subspace projection with `lowerbits`, the 2-D spinor eigenvalues).

## Performance

Operators store their entries in one column-major `FloatArray` at `Float` (no boxing);
the application, composition and row-application loops are tail-recursive strided dots
specialised at the coefficient type, unrolled for `2 × 2` to `4 × 4`. The determinant
family runs DirectSum's wedge plans (cached per dimension, Julia's accumulation order),
with straight-line forms of the plans in 2-4 dimensions.

Measured (Apple M4 Max, compiled, `Float`, ns per call; Julia 1.13 with Grassmann
0.8.46, whose isbits tuples are stack-allocated and fully unrolled):

| operation | `n = 3` Lean | Julia | `n = 4` Lean | Julia | `n = 6` Lean | Julia |
|---|---|---|---|---|---|---|
| `T * x` | 20 | 0.7 | 24 | 1.9 | 75 | 3.1 |
| `T * U` | 26 | 2.7 | 37 | 2.8 | 350 | 24 |
| `det` | 42 | 1.7 | 44 | 5.2 | 920 | 19 |
| `inv` | 110 | 6.3 | 215 | 13 | 2180 | 151 |
| `exp` | 1050 | 59 | 1650 | 158 | 7900 | 412 |
| `O * M` (outermorphism on a multivector) | 290 | 2.7 | 400 | 2.0 | 1550 | 89 |
| `outermorphism(T)` | 2600 | 410 | 6900 | 1400 | 52000 | 34500 |

Every result allocates a fresh `FloatArray`; Julia's results live on the stack.
-/
