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
import Grassmann.Forms.Literal
import Grassmann.Fields
import Grassmann.Calculus
import Grassmann.Calculus.Simplicial

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
  and the simplex boundary `∧(ω)⋅v1`; `Grassmann.Calculus.Simplicial` (imported here):
  `skeleton`, `𝒫`, `subcomplex`, `collapse`, `chain`, `path`, `count_gdims`, `χ`, `betti`.
* `Grassmann.Forms.MatFun`: `exp`, `expm1` (Grassmann's Padé), `log`; of outermorphisms,
  dyadics and projectors too.
* `Grassmann.Forms.Literal`: the operator literals `op![…]`, `endo![…]`, `outer![…]`,
  `spectral![…]` (Julia `@TensorOperator`, `@Endomorphism`, `@Outermorphism`,
  `@SpectralOperator`), shape-checked at elaboration.
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

Operators store their entries in one column-major `FloatArray` at `Float` (no boxing). The
determinant family (`det`, the Cramer `inv`, `adjugate`, `solve`), the compounds, the
characteristic polynomials, the `5 × 5`/`6 × 6` products and the outermorphism application
on multivectors of `n = 3, 4` are straight-line code generated from the generic algorithms
(`oracle/forms/GenUnrolled.lean`, bit-identical to them: `Tests/Forms/Unrolled.lean`); the
rest are tail-recursive strided dots specialised at the coefficient type. Small products write
their results in place, the Padé `exp` updates its temporaries in place, and `eigvals` runs
the Hessenberg QR iteration without eigenvectors (a tail-recursive, unboxed sweep).

Measured by the `forms` bench suite (`Bench/Forms.lean`, its Julia twin
`oracle/bench/forms.jl`; Apple M4 Max, ns per operation, `K = 64` random operators;
Julia 1.13, Grassmann 0.8.46, whose isbits results are stack-allocated):

| operation | `n = 3` Lean | Julia | `n = 4` Lean | Julia | `n = 5` Lean | Julia | `n = 6` Lean | Julia |
|---|---|---|---|---|---|---|---|---|
| `T * x` | 16 | 1.2 | 20 | 3.8 | 23 | 5.3 | 28 | 6.8 |
| `T * U` | 19 | 30 | 25 | 42 | 64 | 53 | 109 | 72 |
| `det` | 4.3 | 1.9 | 6.7 | 7.2 | 14 | 10 | 27 | 20 |
| `inv` | 30 | 33 | 41 | 88 | 82 | 119 | 154 | 207 |
| `adjugate` | 27 | 26 | 41 | 89 | 75 | 122 | 150 | 202 |
| `solve` (Cramer `T \ x`) | 25 | 3.7 | 27 | 13 | 44 | 99 | 97 | 215 |
| `characteristic` | 28 | 5.3 | 25 | 24 | 38 | 251 | 90 | 834 |
| `exp` | 257 | 101 | 413 | 176 | 924 | 302 | 1553 | 446 |
| `eigvals` | 143 | 26 | 336 | 202 | 8451 | 4102 | 12272 | 5267 |
| `outermorphism(T)` | 210 | 112 | 364 | 249 | 945 | 605 | 3163 | 1686 |
| `O * M` | 27 | 5.2 | 60 | 14 | 458 | 48 | 1264 | 220 |

The documented Cramer solve `A \ b` of a `5 × 5` dyadic operator (`docs/src/tutorials/
dyadic-tensors.md:54-75`, 72 ns there) is 61 ns (Julia 89 ns on the same machine). The
remaining gaps are allocation-bound: every result is a fresh `FloatArray` (a push per entry
where the size is not an input's), Julia's live in registers.
-/
