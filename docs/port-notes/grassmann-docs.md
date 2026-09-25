# Grassmann.jl — docs, tests & extensions porting spec (golden corpus)

Scope of this report: `README.md`, `docs/src/*.md` (index, design, algebra, library, references, videos, tutorials/*), `docs/make.jl`, `test/*.jl`, `ext/*.jl`, `Project.toml` of `/Users/alokbeniwal/chakravala/Grassmann.jl` (master, version 0.8.47). The source (`src/*.jl`) is cited wherever the docs make a claim that must be pinned to an implementation, but the deep src walk-through belongs to the sibling `src` reports.

## 0. Provenance, oracle setup and artifacts

* Master clone: `/Users/alokbeniwal/chakravala/Grassmann.jl` (`Project.toml:4` → `version = "0.8.47"`).
* Oracle: Julia 1.13.0, registered Grassmann **0.8.46**, AbstractTensors 0.8.11, DirectSum 0.8.21, Leibniz 0.3.0, StaticVectors 1.0.9, Makie 0.24.15 / CairoMakie 0.15.15, GeometryBasics 0.5.13 (env `scratchpad/juliaenv`).
* Dependency clones vs registered versions: DirectSum identical; Leibniz differs by one import line (`Leibniz.jl:31`); AbstractTensors adds two `Base.angle(t,g)` methods at master `:441-442` — so every dependency line cited below (all ≤ 440 in AbstractTensors) is valid for the clones in `/Users/alokbeniwal/chakravala/` too.
* 0.8.46 vs master diff is **only** three added `==` methods in `src/forms.jl` (master lines 506, 658, 754: `==` for `DiagonalOperator`, `TensorOperator`, `Outermorphism`). All other `src` files are byte-identical, so every oracle output below is valid for master, and every `src` line cited below is a master line. (For forms.jl lines > 505 the registered package is shifted by -2/-4/-6.)
* `test/runtests.jl` passes completely on the oracle (all top-level `@test`s + 7 issue testsets + `Test isapprox` 31 + `method: scalar` 6 + `Field: Float64` 18998 assertions, ~75 s).
* Artifacts written next to this report (all regenerable):
  * `notes/grassmann-docs-goldens/transcripts/*.txt` — REPL transcripts of every doc example re-run on the oracle (`out_readme_design.txt`, `out_algebra.txt`, `out_tutorials.txt`, `out_probe*.txt`).
  * `notes/grassmann-docs-goldens/blade_tables.json` — prototype oracle dump: for 17 signatures, every blade×blade result of `∧ ∨ * > < >> << ⋅ ⊘ >>>` and every blade result of `complementright complementleft ⋆ complementlefthodge reverse involute clifford metric`, as sparse `[bitmask, coeff]` lists in Multivector order (schema in §9).
  * `notes/grassmann-docs-goldens/plots/*.png` + `readme_plot_goldens.json` — CairoMakie renders of all 12 README/algebra.md visualization examples (visually match `paper/img/*.png`) plus sampled numeric values of the underlying curves / vector fields.
  * `notes/grassmann-docs-goldens/exports_inventory.md` — machine-generated table of all 316 exported names (reproduced in §2.3).
  * `notes/grassmann-docs-goldens/scripts/` — `runner.jl` / `runner_g.jl` (REPL emulator: evaluates a block file, prints `julia> ` transcript using `show(IOContext(io,:limit=>true), MIME"text/plain"(), x)`), block files, `render_readme_plots.jl`, `oracle_tables.jl`, `inventory_md.jl`.
  * Run any of them with `julia --startup-file=no --project=scratchpad/juliaenv <script> <args>`.

## 1. Purpose & scope

`README.md:5-24` / `docs/src/index.md:14-20`: Grassmann.jl is "⟨Grassmann-Clifford-Hodge⟩ multilinear differential geometric algebra": computations based on multilinear algebra and spin groups using the extended geometric algebra known as Grassmann-Clifford-Hodge algebra. Operations: exterior (`∧`), regressive (`∨`), inner/contraction, geometric (`*`), Hodge star (`⋆`), boundary (`∂`). Code generation (Julia `@generated`) enables concise syntax. Multivector types are parametric over a `K`-module value `V` from DirectSum.jl (tangent vector spaces, conformal projective geometry), and the abstract type system `TensorAlgebra{V}` comes from AbstractTensors.jl. "Abstract vector space type operations happen at compile-time" (`README.md:24`).

Docs site layout (`docs/make.jl:14-27`): Home=`index.md`, Design=`design.md`, Algebra=`algebra.md`, Videos=`videos.md`, Library=`library.md` (pure `@autodocs` over `AbstractTensors, DirectSum, Grassmann, Leibniz`, `library.md:7-9`), AGPL, Tutorials=`install.md`, `quick-start.md`, `algebra-of-space.md`, References. **`tutorials/dyadic-tensors.md` exists but is not listed in `make.jl` (orphan page)**; it is still harvested below. `videos.md` and `references.md` contain only links/badges/ASCII art (nothing to port). `agpl.md` is the license.

What the port must reproduce (from the docs' own "Definition" lists, `README.md:160-264`, `algebra.md:242-432`): the `TensorAlgebra` type zoo; unary operations (grade selection, involutions, complements, metric application, norms, parts); binary products; operator/linear-algebra layer (`TensorOperator`, `Endomorphism`, `Outermorphism`, `Projector`, `Dyadic`, `det`, `inv`, eigen stuff, polynomial roots); calculus (`∇`, `d`, `∂`, `δ`), conformal/projective up/down maps, simplicial helpers, and the plotting glue (`points`, `vectorfield`/`chainfield`).

## 2. Public API inventory

### 2.1 Export statements (all in master)

| file:line | exported names |
|---|---|
| `src/Grassmann.jl:26` | `⊕, ℝ, @V_str, @S_str, @D_str, Manifold, Submanifold, Signature, DiagonalForm, value` |
| `src/Grassmann.jl:27` | `@basis, @basis_str, @dualbasis, @dualbasis_str, @mixedbasis, @mixedbasis_str, Λ` |
| `src/Grassmann.jl:28` | `ℝ0 … ℝ9, mdims, tangent, metric, antimetric, cometric` |
| `src/Grassmann.jl:29` | `hodge, wedge, vee, complement, dot, antidot, istangent, Values, divergence, grad` |
| `src/Grassmann.jl:60` | `cayley, hyperplanes, points, TensorAlgebra` |
| `src/Grassmann.jl:70` | `𝕚, 𝕛, 𝕜` (defined `:71` as `hyperplanes(ℝ3)`) |
| `src/Grassmann.jl:75-76` | `∇, Δ, ∂, d, δ, ↑, ↓, differential, codifferential, boundary, project, reject, nabla, Nabla, Laplacian` |
| `src/Grassmann.jl:232` | `skeleton, 𝒫, collapse, subcomplex, chain, path` |
| `src/Grassmann.jl:291` | `column, columns` |
| `src/Grassmann.jl:309` | `scalarfield, vectorfield, pointfield, chainfield, rectanglefield` |
| `src/multivectors.jl:15-19` | `TensorTerm, TensorGraded, TensorMixed, Scalar, GradedVector, Bivector, Trivector, Submanifold, Single, Multivector, Spinor, SparseChain, MultiGrade, ChainBundle, Zero, One, Chain, Phasor, Quaternion, GaussianInteger, AbstractSpinor, AntiSpinor, AbstractReal, AbstractComplex, AbstractRational, ScalarFloat, ScalarIrrational, AbstractInteger, AbstractBool, AbstractSigned, AbstractUnsigned, CoSpinor, Simplex` |
| `src/multivectors.jl:27` | `UniformScaling, I, isdiag, det, tr, ⋅, cross, ×, contraction, points` |
| `src/multivectors.jl:278` | `Multiplex` |
| `src/multivectors.jl:824-826` | `Couple`, `PseudoCouple` (loop `for couple ∈ (:Couple,:PseudoCouple) … export $couple`) |
| `src/multivectors.jl:965-969` | `gdims, tdims, betti, χ, unit, ∠, radius, istensor, isgraded, isterm, pseudoscalar, basis, grade, pseudograde, antigrade, hasinf, hasorigin, scalar, norm, unitnorm, valuetype, isscalar, vector, isvector, indices, imaginary, unitize, geomabs, bivector, isbivector, trivector, istrivector, isvolume, antiabs, antiabs2, realvalue, imagvalue, unitangle, phase, amplitude, complexify, vectorize, polarize` |
| `src/multivectors.jl:1079` | `quaternion, quatvalue, quatvalues` |
| `src/parity.jl:22-23` | `complementleft, complementright, ⋆, complementlefthodge, complementrighthodge, complementleftanti, complementrightanti` |
| `src/parity.jl:28` | `involute, clifford, pseudoreverse, antireverse, odd, even, angular, radial, ₊, ₋, ǂ` |
| `src/algebra.jl:23-24` | `∗, ⊛, ⊖, ∧, ∨, ⟑, wedgedot, veedot, ⊗, ⨼, ⨽, ⊙, ⊠, ⟂, ∥, ⊘, sandwich, pseudosandwich, antisandwich, cosandwich` |
| `src/algebra.jl:28` | `⟇` |
| `src/composite.jl:15-20` | `exph, log_fast, logh_fast, pseudoexp, pseudolog, pseudometric, pseudodot, @pseudo, pseudoabs, pseudoabs2, pseudosqrt, pseudocbrt, pseudoinv, pseudoscalar, pseudocos, pseudosin, pseudotan, pseudocosh, pseudosinh, pseudotanh, coabs, coabs2, cosqrt, cocbrt, coinv, coscalar, coexp, colog, cometric, codot, @co, cocos, cosin, cotan, cocosh, cosinh, cotanh, vandermonde, pfaffian, invdet, adjugate, cofactor, volumes, compound, companion` |
| `src/composite.jl:905` | `affineframe` |
| `src/composite.jl:962-966` | loop `for op ∈ (:mean,:centroid,:barycenter,:curl)` → `export $op, $ops` (`mean, means, centroid, centroids, barycenter, barycenters, curl, curls`; `$ops(m,p) = $op.(getindex.(Ref(p),m))`) |
| `src/composite.jl:1092` | `roots, rootsreal, rootscomplex, monicroots, monicrootsreal, monicrootscomplex` |
| `src/forms.jl:4-11` | `TensorNested, Projector, Dyadic, Proj, outer, operator, gerschgorin, diag, DiagonalOperator, TensorOperator, Endomorphism, Outermorphism, outermorphism, sylvester, characteristic, eigen, eigvecs, eigvals, eigpolys, eigprods, eigmults, eigvalsreal, eigvalscomplex, eigvecsreal, eigvecscomplex, eigenreal, eigencomplex, discriminant, disc, discriminantreal, discreal, discriminantcomplex, disccomplex, MetricTensor, metrictensor, metricextensor, InducedMetric, vandermondereal, vandermondecomplex, @TensorOperator, @Endomorphism, @Outermorphism, @SpectralOperator` |
| `src/forms.jl:384` | `SpectralOperator` |
| `src/forms.jl:483` | `DiagonalMorphism, DiagonalOutermorphism` |
| `src/forms.jl:728` | `@Outermorphism` |
| `src/forms.jl:1545` | `𝓛, Lie, LieBracket, LieDerivative, bracket` |

**Exported but undefined in 0.8.46/master** (do not port as-is; either drop or define): `MultiGrade`, `SparseChain`, `angular`, `radial`, `coscalar`, `eigprods`, `pseudodot` (AbstractTensors defines `pseudodot` but Grassmann's export shadows it as undefined in `names(Grassmann)`), `⟂`.

### 2.2 Operator / alias table (unicode ↔ ASCII ↔ semantics)

Wiring lives in AbstractTensors (registered 0.8.11 `src/AbstractTensors.jl:257-315`), Grassmann adds methods. Verified on the oracle (§6.10).

| unicode | ASCII / canonical fn | semantics (as implemented) | defined |
|---|---|---|---|
| `∧` | `wedge` | exterior product; grade G+L; zero if blades overlap | AbstractLattices; Grassmann `algebra.jl` (e.g. `:1327` loop) |
| `∨` | `vee`, also binary `&` | regressive product, DeMorgan: `∨(ω...) = ⋆⁻¹(∧(⋆.(ω)...))`; grade G+L−n | `algebra.jl:155-199` |
| `*`, `⟑`, `⊖` | `times`, `wedgedot` | geometric (Clifford) product | AbstractTensors `:314` `const ⊖,⟑,times = wedgedot` |
| `⋅`, `|` (binary), `>`, `⨽` | `dot`, `contraction(a,b)` | right (Grassmann) interior contraction `a∨⋆b`, grade G−L | AbstractTensors `:264-266`; `algebra.jl:209-272` |
| `<`, `⨼` | `contraction(b,a)` | left contraction (swapped args) | AbstractTensors `:258,:261` |
| `>>` | `contraction(~a,b)` | "conventional" right contraction (reverse left arg) | AbstractTensors `:260` |
| `<<` | `contraction(b,~a)` | "conventional" left contraction | AbstractTensors `:259` |
| `⊛` | – | scalar product `scalar(contraction(a,b))` | AbstractTensors `:257` |
| `∗` | – | reversed geometric product `(~a)⟑b` | AbstractTensors `:256` |
| `×` | `cross` | `⋆(ω∧η)` | docstring `algebra.jl:280-285` |
| `⊘` | `sandwich` | `reverse(y)*x*involute(y)` (**no inverse**, see §4.6) | `algebra.jl:313-349` |
| `>>>` | – | `y*x*clifford(y)` (traditional sandwich, rotor on the left) | `algebra.jl:351-387` |
| `⋆` | `hodge`, `complementrighthodge` | Hodge right complement `~ω*I` (metric) | AbstractTensors `:312-313` |
| `!` | `complement`, `complementright` | Euclidean (metric-free) Grassmann right complement | AbstractTensors `:310-311` |
| unary `|x` | `hodge(x)` | Julia's parser has no prefix `|` (`|a` is a ParseError); only the call form `Base.:|(x)` works — treat as dead syntax | AbstractTensors `:315` |
| `~` | `reverse` | reversion | `parity.jl:27` imports |
| `'` | `adjoint` | dual space / conjugation (`V'` flips signature) | `multivectors.jl:1237` |
| `⊗` | – | `Dyadic(a,b)` for graded args; scalar × graded = `*` | `algebra.jl:150-152` |
| `⊙` | – | symmetrization `∑σ ∏ω/K!` (**broken**: needs `permutations`, `UndefVarError`) | `algebra.jl:296` |
| `⊠` | – | anti-symmetrization (**broken**, same reason) | `algebra.jl:303-311` |
| `⟇` | `veedot` | `complementleft(complementright(a)*complementright(b))` | `algebra.jl:391` |
| `antidot`, `codot`, `pseudodot` | `expansion` | `complementleft(contraction(!a,!b))` | `algebra.jl:396`, AbstractTensors `:314` |
| `∥` | – | `iszero(a∧b)` (parallel test) | `algebra.jl:401` |
| `↑` | `project` | up-projection (Riemann sphere / CGA) | `Grassmann.jl:164-190,212` |
| `↓` | `reject` | down-projection | `Grassmann.jl:192-212` |
| `∂` | `boundary` | `ω⋅V(∇)`; for `Chain{V,1,Chain{W,1}}`: `∧(ω)⋅Λ(W).v1` | `Grassmann.jl:109-110` |
| `d` | `differential` | `V(∇)∧ω` | `Grassmann.jl:111` |
| `δ` | `codifferential` | `-∂(ω)` | `Grassmann.jl:112` |
| `∇` | `nabla` | `Nabla` const (Leibniz); `V(∇)` builds the vector field | Leibniz; `Grassmann.jl:88-107` |
| `Δ` | `Laplacian` | Leibniz Laplacian const (**no longer callable as simplicial `Δ`**; breaks `𝒫`, `subcomplex`, doc `χ(Δ(ω))`) | Leibniz |
| `χ` | – | Euler characteristic (Leibniz) | Leibniz |
| `𝒫` | – | `Δ(t,Val{false}())` (broken, see Δ) | `Grassmann.jl:259` |
| `∠` | `Phasor` | type alias | `multivectors.jl:871` |
| `𝕚,𝕛,𝕜` | `hyperplanes(ℝ3)` | `(v₂₃, -v₁₃, v₁₂)` (anti-Hamilton: `𝕚𝕛 = -𝕜`) | `Grassmann.jl:71` |
| `𝓛`, `Lie` | `LieBracket()` | Lie bracket object | `forms.jl:1547-1552` |
| `₊ ₋ ǂ` | postfix ops | `AbstractTensors.Postfix` constants (even/odd/…) | AbstractTensors |
| `/` `\` | – | `a/b = a⟑inv(b)`, `a\b = inv(a)⟑b` | AbstractTensors `:318-323` |
| `^` | – | `b^t = exp(t⟑log(b))` for number base; integer powers via `literal_pow` (`x^2=x*x`, `x^-1=inv(x)`) | AbstractTensors `:324`; `algebra.jl:409-416` |

String macros / constructors (DirectSum, re-exported): `S"…"` Signature (`DirectSum.jl:432`), `D"…"` DiagonalForm (`:436`), `V"…"` generic (`:428`), `basis"…"`, `dualbasis"…"`, `mixedbasis"…"` (`basis.jl:94,110,128`), `@basis M [sig vec cov duo dif]` (`basis.jl:88`), `@dualbasis` (`:106`), `@mixedbasis` (`:122`).

### 2.3 Complete exported-name table (machine generated, 316 rows)

Columns: name; kind (with method count on the oracle); defining module; canonical function name when the export is an alias; definition sites (Grassmann sites translated to master line numbers, dependency sites are registered-version paths `Pkg.jl/src/file.jl:line`); first ~260 chars of the docstring. "–" = none.

| # | name | kind | origin | alias (canonical fn name) | definition sites (master or registered dep) | docstring summary |
|---|---|---|---|---|---|---|
| 1 | `@D_str` | macro (1 m) | DirectSum |  | DirectSum.jl/src/DirectSum.jl:436 |  |
| 2 | `@Endomorphism` | macro (1 m) | Grassmann |  | Grassmann.jl/src/forms.jl:580 |  |
| 3 | `@Outermorphism` | macro (1 m) | Grassmann |  | Grassmann.jl/src/forms.jl:729 |  |
| 4 | `@S_str` | macro (1 m) | DirectSum |  | DirectSum.jl/src/DirectSum.jl:432 |  |
| 5 | `@SpectralOperator` | macro (1 m) | Grassmann |  | Grassmann.jl/src/forms.jl:392 |  |
| 6 | `@TensorOperator` | macro (1 m) | Grassmann |  | Grassmann.jl/src/forms.jl:577 |  |
| 7 | `@V_str` | macro (1 m) | DirectSum |  | DirectSum.jl/src/DirectSum.jl:428 |  |
| 8 | `@basis` | macro (6 m) | DirectSum |  | DirectSum.jl/src/basis.jl:88 | Generates `Submanifold` elements having `Manifold` specified by `V`. As a result of this macro, all of the `Submanifold{V,G}` elements generated by that `TensorBundle` become available in the local workspace with the specified naming. The first argument provid… |
| 9 | `@basis_str` | macro (1 m) | DirectSum |  | DirectSum.jl/src/basis.jl:94 |  |
| 10 | `@co` | macro (1 m) | AbstractTensors |  | AbstractTensors.jl/src/AbstractTensors.jl:498 | Use the macro `@co` to make a pseudoscalar `complement` variant of any functions: Now `comyfun(x) = complementleft(myfun(complementright(x)))` is defined. Now `comyproduct(a,b) = complementleft(myproduct(!a,!b))` is defined. |
| 11 | `@dualbasis` | macro (4 m) | DirectSum |  | DirectSum.jl/src/basis.jl:106 | Generates `Submanifold` elements having `Manifold` specified by `V'`. As a result of this macro, all of the `Submanifold{V',G}` elements generated by that `TensorBundle` become available in the local workspace with the specified naming. The first argument prov… |
| 12 | `@dualbasis_str` | macro (1 m) | DirectSum |  | DirectSum.jl/src/basis.jl:110 |  |
| 13 | `@mixedbasis` | macro (6 m) | DirectSum |  | DirectSum.jl/src/basis.jl:122 | Generates `Submanifold` elements having `Manifold` specified by `V⊕V'`. As a result of this macro, all of the `Submanifold{V⊕V',G}` elements generated by that `TensorBundle` become available in the local workspace with the specified naming. The first argum… |
| 14 | `@mixedbasis_str` | macro (1 m) | DirectSum |  | DirectSum.jl/src/basis.jl:128 |  |
| 15 | `@pseudo` | macro (1 m) | AbstractTensors |  | AbstractTensors.jl/src/AbstractTensors.jl:523 | Use the macro `@pseudo` to make a pseudoscalar `complement` variant of any functions: Now `pseudomyfun(x) = complementleft(myfun(complementright(x)))` is defined. Now `pseudomyproduct(a,b) = complementleft(myproduct(!a,!b))` is defined. |
| 16 | `AbstractBool` | type | ? |  | Grassmann.jl/src/multivectors.jl:981 |  |
| 17 | `AbstractComplex` | type | ? |  |  |  |
| 18 | `AbstractInteger` | type | ? |  | Grassmann.jl/src/multivectors.jl:982 |  |
| 19 | `AbstractRational` | type | ? |  |  |  |
| 20 | `AbstractReal` | type | ? |  | Grassmann.jl/src/multivectors.jl:979 |  |
| 21 | `AbstractSigned` | type | ? |  | Grassmann.jl/src/multivectors.jl:983 |  |
| 22 | `AbstractSpinor` | type | Grassmann |  | Grassmann.jl/src/multivectors.jl:414 | Elements of `TensorAlgebra` having non-homogenous grade being a spinor in the abstract. |
| 23 | `AbstractUnsigned` | type | ? |  | Grassmann.jl/src/multivectors.jl:984 |  |
| 24 | `AntiSpinor` | type | Grassmann |  | Grassmann.jl/src/multivectors.jl:456 |  |
| 25 | `Bivector` | type | AbstractTensors |  |  | Graded `bivector` elements of a `Manifold` instance `V` with scalar field `T`. |
| 26 | `Chain` | type | Grassmann |  | Grassmann.jl/src/multivectors.jl:68 | Chain type with pseudoscalar `V::Manifold`, grade/rank `G::Int`, scalar field `T::Type`. |
| 27 | `ChainBundle` | type | Grassmann |  | Grassmann.jl/src/multivectors.jl:211 | Subsets of a bundle cross-section over a `Manifold` topology. |
| 28 | `CoSpinor` | type | Grassmann |  |  | PsuedoSpinor (`odd` grade) type with pseudoscalar `V::Manifold` and scalar `T::Type`. |
| 29 | `Couple` | type | Grassmann |  | Grassmann.jl/src/multivectors.jl:656 | Pair of values with `V::Manifold`, basis `B::Submanifold`, scalar field of `T::Type`. |
| 30 | `DiagonalForm` | type | DirectSum |  | DirectSum.jl/src/DirectSum.jl:193 |  |
| 31 | `DiagonalMorphism` | type | Grassmann |  |  |  |
| 32 | `DiagonalOperator` | type | Grassmann |  | Grassmann.jl/src/forms.jl:476 |  |
| 33 | `DiagonalOutermorphism` | type | Grassmann |  |  |  |
| 34 | `Dyadic` | type | Grassmann |  | Grassmann.jl/src/forms.jl:440 |  |
| 35 | `Endomorphism` | type | Grassmann |  |  |  |
| 36 | `GaussianInteger` | type | Grassmann |  |  |  |
| 37 | `GradedVector` | type | AbstractTensors |  |  | Graded `vector` elements of a `Manifold` instance `V` with scalar field `T`. |
| 38 | `Grassmann` | module | Grassmann |  | `src/Grassmann.jl:1` | – (module itself; `names(Grassmann)` includes it) |
| 39 | `I` | const ::UniformScaling{Bool} | Grassmann |  |  | An object of type [`UniformScaling`](@ref), representing an identity matrix of any size. # Examples |
| 40 | `InducedMetric` | type | Grassmann |  | Grassmann.jl/src/forms.jl:1692 |  |
| 41 | `Laplacian` | type | Leibniz |  | Leibniz.jl/src/Leibniz.jl:163 | Abstract `laplacian` as second-order `Derivation{Bool,2}` is `Laplacian` operator dispatch. |
| 42 | `Lie` | const ::LieBracket | Grassmann |  | Grassmann.jl/src/forms.jl:1552 |  |
| 43 | `LieBracket` | type | Grassmann |  | Grassmann.jl/src/forms.jl:1547 |  |
| 44 | `LieDerivative` | type | Grassmann |  | Grassmann.jl/src/forms.jl:1548 |  |
| 45 | `Manifold` | type | AbstractTensors |  | AbstractTensors.jl/src/AbstractTensors.jl:49 | Basis parameter locally homeomorphic to `V::Submanifold{M}` T-module product topology. |
| 46 | `MetricTensor` | type | Grassmann |  | Grassmann.jl/src/forms.jl:1603 |  |
| 47 | `MultiGrade` | **exported but UNDEFINED in 0.8.46** | – | – |  | – |
| 48 | `Multiplex` | type | Grassmann |  |  |  |
| 49 | `Multivector` | type | Grassmann |  | Grassmann.jl/src/multivectors.jl:229 | Chain type with pseudoscalar `V::Manifold` and scalar field `T::Type`. |
| 50 | `Nabla` | type | Leibniz |  | Leibniz.jl/src/Leibniz.jl:162 | Abstract `nabla` as first-order `Derivation{Bool,1}` is `Nabla` operator dispatch. |
| 51 | `One` | type | DirectSum |  |  | Unit quantity `One` of the `Grassmann` algebra over `V`. |
| 52 | `Outermorphism` | type | Grassmann |  | Grassmann.jl/src/forms.jl:714 |  |
| 53 | `Phasor` | type | Grassmann |  | Grassmann.jl/src/multivectors.jl:852 | Magnitude/phase angle with `V::Manifold`, frequency `B::Type`, and amplitude `T::Type`. |
| 54 | `Proj` | type | Grassmann |  | Grassmann.jl/src/forms.jl:382 |  |
| 55 | `Projector` | type | Grassmann |  | Grassmann.jl/src/forms.jl:374 |  |
| 56 | `PseudoCouple` | type | Grassmann |  | Grassmann.jl/src/multivectors.jl:677 | Pair of values with `V::Manifold`, basis `B::Submanifold`, pseudoscalar of `T::Type`. |
| 57 | `Quaternion` | type | Grassmann |  |  |  |
| 58 | `Scalar` | type | AbstractTensors |  |  | Graded `scalar` elements of a `Manifold` instance `V` with scalar field `T`. |
| 59 | `ScalarFloat` | type | ? |  | Grassmann.jl/src/multivectors.jl:986 |  |
| 60 | `ScalarIrrational` | type | ? |  | Grassmann.jl/src/multivectors.jl:987 |  |
| 61 | `Signature` | type | DirectSum |  | DirectSum.jl/src/DirectSum.jl:131 |  |
| 62 | `Simplex` | type | Grassmann |  |  |  |
| 63 | `Single` | type | DirectSum |  | DirectSum.jl/src/DirectSum.jl:457 | Single type with pseudoscalar `V::Manifold`, grade/rank `G::Int`, `B::Submanifold{V,G}`, field `T::Type`. |
| 64 | `SparseChain` | **exported but UNDEFINED in 0.8.46** | – | – |  | – |
| 65 | `SpectralOperator` | type | Grassmann |  |  |  |
| 66 | `Spinor` | type | Grassmann |  |  | Spinor (`even` grade) type with pseudoscalar `V::Manifold` and scalar field `T::Type`. |
| 67 | `Submanifold` | type | DirectSum |  | DirectSum.jl/src/DirectSum.jl:252 | Basis type with pseudoscalar `V::Manifold`, grade/rank `G::Int`, bits `B::UInt64`. |
| 68 | `TensorAlgebra` | type | AbstractTensors |  | AbstractTensors.jl/src/AbstractTensors.jl:32 | Universal root tensor type with `Manifold` instance `V` with scalar field `T`. |
| 69 | `TensorGraded` | type | AbstractTensors |  | AbstractTensors.jl/src/AbstractTensors.jl:64 | Grade `G` elements of a `Manifold` instance `V` with scalar field `T`. |
| 70 | `TensorMixed` | type | AbstractTensors |  | AbstractTensors.jl/src/AbstractTensors.jl:124 | Elements of `Manifold` instance `V` having non-homogenous grade with scalar field `T`. |
| 71 | `TensorNested` | type | Grassmann |  | Grassmann.jl/src/forms.jl:298 |  |
| 72 | `TensorOperator` | type | Grassmann |  | Grassmann.jl/src/forms.jl:555 |  |
| 73 | `TensorTerm` | type | AbstractTensors |  | AbstractTensors.jl/src/AbstractTensors.jl:108 | Single coefficient for grade `G` of a `Manifold` instance `V` with scalar field `T`. |
| 74 | `Trivector` | type | AbstractTensors |  |  | Graded `trivector` elements of a `Manifold` instance `V` with scalar field `T`. |
| 75 | `UniformScaling` | type | LinearAlgebra |  |  | Generically sized uniform scaling operator defined as a scalar times the identity operator, `λ*I`. Although without an explicit `size`, it acts similarly to a matrix in many cases and includes support for some indexing. See also [`I`](@ref). !!! compat "Julia… |
| 76 | `Values` | type | StaticVectors |  |  |  |
| 77 | `Zero` | type | DirectSum |  | DirectSum.jl/src/DirectSum.jl:563 | Null quantity `Zero` of the `Grassmann` algebra over `V`. |
| 78 | `adjugate` | function (6 m) | Grassmann |  | Grassmann.jl/src/composite.jl:796<br>Grassmann.jl/src/composite.jl:854<br>Grassmann.jl/src/forms.jl:526<br>Grassmann.jl/src/forms.jl:529 |  |
| 79 | `affineframe` | function (8 m) | Grassmann |  | Grassmann.jl/src/forms.jl:1711<br>Grassmann.jl/src/composite.jl:904<br>Grassmann.jl/src/composite.jl:899<br>Grassmann.jl/src/composite.jl:900 |  |
| 80 | `amplitude` | function (4 m) | Grassmann |  | Grassmann.jl/src/multivectors.jl:903<br>Grassmann.jl/src/multivectors.jl:904<br>Grassmann.jl/src/multivectors.jl:905 |  |
| 81 | `angular` | **exported but UNDEFINED in 0.8.46** | – | – |  | – |
| 82 | `antiabs` | function (2 m) | AbstractTensors | `coabs` | AbstractTensors.jl/src/AbstractTensors.jl:540<br>AbstractTensors.jl/src/AbstractTensors.jl:543 | Complemented `abs` defined as `complementleft(abs(complementright(t)))`. |
| 83 | `antiabs2` | function (2 m) | AbstractTensors | `coabs2` | AbstractTensors.jl/src/AbstractTensors.jl:540<br>AbstractTensors.jl/src/AbstractTensors.jl:543 | Complemented `abs2` defined as `complementleft(abs2(complementright(t)))`. |
| 84 | `antidot` | function (3 m) | AbstractTensors | `expansion` | Grassmann.jl/src/algebra.jl:396 |  |
| 85 | `antigrade` | function (7 m) | Leibniz | `pseudograde` | Leibniz.jl/src/generic.jl:152<br>DirectSum.jl/src/generic.jl:112<br>Leibniz.jl/src/generic.jl:153 |  |
| 86 | `antimetric` | function (27 m) | AbstractTensors | `cometric` | Grassmann.jl/src/products.jl:1639<br>Grassmann.jl/src/forms.jl:1026<br>Grassmann.jl/src/products.jl:1637<br>Grassmann.jl/src/products.jl:1636 |  |
| 87 | `antireverse` | function (9 m) | DirectSum | `pseudoreverse` | Grassmann.jl/src/products.jl:1830<br>Grassmann.jl/src/products.jl:1820<br>Grassmann.jl/src/products.jl:1823<br>Grassmann.jl/src/products.jl:1901 | Anti-reverse of an element: ~ω = (-1)^(pseudograde(ω)*(pseudograde(ω)-1)/2)*ω |
| 88 | `antisandwich` | function (2 m) | AbstractTensors |  | AbstractTensors.jl/src/AbstractTensors.jl:566<br>AbstractTensors.jl/src/AbstractTensors.jl:567 | Defined as `complementleft(complementright(R)>>>complementright(x))`. |
| 89 | `barycenter` | function (3 m) | Grassmann |  | Grassmann.jl/src/composite.jl:938<br>Grassmann.jl/src/composite.jl:939<br>Grassmann.jl/src/forms.jl:1713 |  |
| 90 | `barycenters` | function (1 m) | Grassmann |  | Grassmann.jl/src/composite.jl:969 |  |
| 91 | `basis` | function (7 m) | AbstractTensors |  | Grassmann.jl/src/multivectors.jl:829 |  |
| 92 | `betti` | function (1 m) | Grassmann |  | Grassmann.jl/src/Grassmann.jl:153 | Compute combinatoric Betti numbers based on the `count_gdims` and `boundary_rank` methods. |
| 93 | `bivector` | function (10 m) | AbstractTensors |  | Grassmann.jl/src/forms.jl:614<br>Grassmann.jl/src/multivectors.jl:1119<br>Grassmann.jl/src/multivectors.jl:1120<br>Grassmann.jl/src/multivectors.jl:1122 | Return the bivector (rank 2) part of any `TensorAlgebra` element. |
| 94 | `boundary` | function (2 m) | Leibniz |  | Grassmann.jl/src/Grassmann.jl:109<br>Grassmann.jl/src/Grassmann.jl:110 |  |
| 95 | `bracket` | function (6 m) | Grassmann |  | Grassmann.jl/src/forms.jl:1561<br>Grassmann.jl/src/forms.jl:1562<br>Grassmann.jl/src/forms.jl:1563<br>Grassmann.jl/src/forms.jl:1564 |  |
| 96 | `cayley` | function (10 m) | Grassmann |  | Grassmann.jl/src/forms.jl:827<br>Grassmann.jl/src/forms.jl:826<br>Grassmann.jl/src/forms.jl:825<br>Grassmann.jl/src/forms.jl:824 | Compute the `cayley` table with `op(a,b)` for each `Submanifold` basis of `V`. |
| 97 | `centroid` | function (2 m) | Grassmann |  | Grassmann.jl/src/composite.jl:940<br>Grassmann.jl/src/composite.jl:941 |  |
| 98 | `centroids` | function (1 m) | Grassmann |  | Grassmann.jl/src/composite.jl:969 |  |
| 99 | `chain` | function (2 m) | Grassmann |  | Grassmann.jl/src/Grassmann.jl:242 |  |
| 100 | `chainfield` | function (4 m) | Grassmann |  | Grassmann.jl/src/Grassmann.jl:314<br>Grassmann.jl/src/Grassmann.jl:327 |  |
| 101 | `characteristic` | function (7 m) | Grassmann |  | Grassmann.jl/src/forms.jl:1464<br>Grassmann.jl/src/forms.jl:1441<br>Grassmann.jl/src/forms.jl:1442<br>Grassmann.jl/src/forms.jl:1445 |  |
| 102 | `clifford` | function (11 m) | AbstractTensors |  | Grassmann.jl/src/products.jl:1830<br>Grassmann.jl/src/products.jl:1864<br>Grassmann.jl/src/products.jl:1820<br>Grassmann.jl/src/products.jl:1826 | Clifford conjugate of an element: clifford(ω) = involute(reverse(ω)) |
| 103 | `coabs` | function (2 m) | AbstractTensors |  | AbstractTensors.jl/src/AbstractTensors.jl:540<br>AbstractTensors.jl/src/AbstractTensors.jl:543 | Complemented `abs` defined as `complementleft(abs(complementright(t)))`. |
| 104 | `coabs2` | function (2 m) | AbstractTensors |  | AbstractTensors.jl/src/AbstractTensors.jl:540<br>AbstractTensors.jl/src/AbstractTensors.jl:543 | Complemented `abs2` defined as `complementleft(abs2(complementright(t)))`. |
| 105 | `cocbrt` | function (2 m) | AbstractTensors |  | AbstractTensors.jl/src/AbstractTensors.jl:540<br>AbstractTensors.jl/src/AbstractTensors.jl:543 | Complemented `cbrt` defined as `complementleft(cbrt(complementright(t)))`. |
| 106 | `cocos` | function (2 m) | AbstractTensors |  | AbstractTensors.jl/src/AbstractTensors.jl:540<br>AbstractTensors.jl/src/AbstractTensors.jl:543 | Complemented `cos` defined as `complementleft(cos(complementright(t)))`. |
| 107 | `cocosh` | function (2 m) | AbstractTensors |  | AbstractTensors.jl/src/AbstractTensors.jl:540<br>AbstractTensors.jl/src/AbstractTensors.jl:543 | Complemented `cosh` defined as `complementleft(cosh(complementright(t)))`. |
| 108 | `codifferential` | function (1 m) | Leibniz |  | Grassmann.jl/src/Grassmann.jl:112 |  |
| 109 | `codot` | function (3 m) | AbstractTensors | `expansion` | Grassmann.jl/src/algebra.jl:396 |  |
| 110 | `coexp` | function (2 m) | AbstractTensors |  | AbstractTensors.jl/src/AbstractTensors.jl:540<br>AbstractTensors.jl/src/AbstractTensors.jl:543 | Complemented `exp` defined as `complementleft(exp(complementright(t)))`. |
| 111 | `cofactor` | function (5 m) | Grassmann |  | Grassmann.jl/src/composite.jl:805<br>Grassmann.jl/src/composite.jl:855<br>Grassmann.jl/src/forms.jl:525<br>Grassmann.jl/src/forms.jl:608 |  |
| 112 | `coinv` | function (2 m) | AbstractTensors |  | AbstractTensors.jl/src/AbstractTensors.jl:540<br>AbstractTensors.jl/src/AbstractTensors.jl:543 | Complemented `inv` defined as `complementleft(inv(complementright(t)))`. |
| 113 | `collapse` | function (1 m) | Grassmann |  | Grassmann.jl/src/Grassmann.jl:240 |  |
| 114 | `colog` | function (1 m) | AbstractTensors |  | AbstractTensors.jl/src/AbstractTensors.jl:540 | Complemented `log` defined as `complementleft(log(complementright(t)))`. |
| 115 | `column` | function (2 m) | Grassmann |  | Grassmann.jl/src/Grassmann.jl:293 |  |
| 116 | `columns` | function (3 m) | Grassmann |  | Grassmann.jl/src/Grassmann.jl:294 |  |
| 117 | `cometric` | function (27 m) | AbstractTensors |  | Grassmann.jl/src/products.jl:1639<br>Grassmann.jl/src/forms.jl:1026<br>Grassmann.jl/src/products.jl:1637<br>Grassmann.jl/src/products.jl:1636 |  |
| 118 | `companion` | function (3 m) | Grassmann |  | Grassmann.jl/src/forms.jl:830<br>Grassmann.jl/src/forms.jl:831<br>Grassmann.jl/src/forms.jl:829 |  |
| 119 | `complement` | function (23 m) | Base | `!` | Grassmann.jl/src/products.jl:1338<br>Grassmann.jl/src/forms.jl:1026<br>Grassmann.jl/src/products.jl:1333<br>Grassmann.jl/src/products.jl:1371 | Predicate function negation: when the argument of `!` is a function, it returns a composed function which computes the boolean negation of `f`. See also [`∘`](@ref). # Examples !!! compat "Julia 1.9" Starting with Julia 1.9, `!f` returns a [`ComposedFunction… |
| 120 | `complementleft` | function (12 m) | AbstractTensors |  | Grassmann.jl/src/forms.jl:1026<br>Grassmann.jl/src/products.jl:1338<br>Grassmann.jl/src/products.jl:1371<br>Grassmann.jl/src/products.jl:1333 | Euclidean metric variant Grassmann left complement. |
| 121 | `complementleftanti` | function (1 m) | AbstractTensors |  | DirectSum.jl/src/operations.jl:334 |  |
| 122 | `complementlefthodge` | function (21 m) | AbstractTensors |  | Grassmann.jl/src/products.jl:1338<br>Grassmann.jl/src/forms.jl:1026<br>Grassmann.jl/src/products.jl:1371<br>Grassmann.jl/src/products.jl:1333 | Grassmann-Hodge left complement: ⋆'ω = I∗'ω |
| 123 | `complementright` | function (23 m) | Base | `!` | Grassmann.jl/src/products.jl:1338<br>Grassmann.jl/src/forms.jl:1026<br>Grassmann.jl/src/products.jl:1333<br>Grassmann.jl/src/products.jl:1371 | Euclidean metric variant of Grassmann right complement. |
| 124 | `complementrightanti` | function (1 m) | AbstractTensors |  | DirectSum.jl/src/operations.jl:333 |  |
| 125 | `complementrighthodge` | function (25 m) | AbstractTensors |  | Grassmann.jl/src/products.jl:1338<br>Grassmann.jl/src/forms.jl:1026<br>Grassmann.jl/src/products.jl:1371<br>Grassmann.jl/src/products.jl:1333 | Grassmann-Hodge right complement: ⋆ω = ω∗I |
| 126 | `complexify` | function (14 m) | Grassmann |  | Grassmann.jl/src/multivectors.jl:1049<br>Grassmann.jl/src/multivectors.jl:1046<br>Grassmann.jl/src/multivectors.jl:1047<br>Grassmann.jl/src/multivectors.jl:1048 |  |
| 127 | `compound` | function (9 m) | Grassmann |  | Grassmann.jl/src/forms.jl:587<br>Grassmann.jl/src/forms.jl:586<br>Grassmann.jl/src/composite.jl:716<br>Grassmann.jl/src/composite.jl:717 |  |
| 128 | `contraction` | function (158 m) | AbstractTensors |  | Grassmann.jl/src/products.jl:797<br>Grassmann.jl/src/forms.jl:934<br>Grassmann.jl/src/forms.jl:948<br>Grassmann.jl/src/forms.jl:941 | Interior (right) contraction product: ω⋅η = ω∨⋆η |
| 129 | `cosandwich` | function (2 m) | AbstractTensors |  | AbstractTensors.jl/src/AbstractTensors.jl:557<br>AbstractTensors.jl/src/AbstractTensors.jl:558 | Defined as `complementleft(sandwich(complementright(x),complementright(R)))`. |
| 130 | `coscalar` | **exported but UNDEFINED in 0.8.46** | – | – |  | – |
| 131 | `cosin` | function (2 m) | AbstractTensors |  | AbstractTensors.jl/src/AbstractTensors.jl:540<br>AbstractTensors.jl/src/AbstractTensors.jl:543 | Complemented `sin` defined as `complementleft(sin(complementright(t)))`. |
| 132 | `cosinh` | function (2 m) | AbstractTensors |  | AbstractTensors.jl/src/AbstractTensors.jl:540<br>AbstractTensors.jl/src/AbstractTensors.jl:543 | Complemented `sinh` defined as `complementleft(sinh(complementright(t)))`. |
| 133 | `cosqrt` | function (2 m) | AbstractTensors |  | AbstractTensors.jl/src/AbstractTensors.jl:540<br>AbstractTensors.jl/src/AbstractTensors.jl:543 | Complemented `sqrt` defined as `complementleft(sqrt(complementright(t)))`. |
| 134 | `cotan` | function (2 m) | AbstractTensors |  | AbstractTensors.jl/src/AbstractTensors.jl:540<br>AbstractTensors.jl/src/AbstractTensors.jl:543 | Complemented `tan` defined as `complementleft(tan(complementright(t)))`. |
| 135 | `cotanh` | function (2 m) | AbstractTensors |  | AbstractTensors.jl/src/AbstractTensors.jl:540<br>AbstractTensors.jl/src/AbstractTensors.jl:543 | Complemented `tanh` defined as `complementleft(tanh(complementright(t)))`. |
| 136 | `cross` | function (4 m) | LinearAlgebra |  | Leibniz.jl/src/Leibniz.jl:149<br>Leibniz.jl/src/Leibniz.jl:150<br>AbstractTensors.jl/src/AbstractTensors.jl:349 | Compute the cross product of two 3-vectors. # Examples Cross product: ω×η = ⋆(ω∧η) |
| 137 | `curl` | function (4 m) | Grassmann |  | Grassmann.jl/src/composite.jl:943<br>Grassmann.jl/src/composite.jl:944<br>Grassmann.jl/src/forms.jl:1714<br>Grassmann.jl/src/composite.jl:945 |  |
| 138 | `curls` | function (1 m) | Grassmann |  | Grassmann.jl/src/composite.jl:969 |  |
| 139 | `d` | function (1 m) | Leibniz | `differential` | Grassmann.jl/src/Grassmann.jl:111 |  |
| 140 | `det` | function (40 m) | LinearAlgebra |  | Grassmann.jl/src/composite.jl:952<br>Grassmann.jl/src/composite.jl:953<br>Grassmann.jl/src/forms.jl:416<br>Grassmann.jl/src/forms.jl:409 | Matrix determinant. See also: [`logdet`](@ref) and [`logabsdet`](@ref). # Examples Note that, in general, `det` computes a floating-point approximation of the determinant, even for integer matrices, typically via Gaussian elimination. Julia includes an exact a… |
| 141 | `diag` | function (27 m) | LinearAlgebra |  | Grassmann.jl/src/forms.jl:642<br>Grassmann.jl/src/forms.jl:648<br>Grassmann.jl/src/forms.jl:651<br>Grassmann.jl/src/forms.jl:654 | The `k`th diagonal of a matrix, as a vector. See also [`diagm`](@ref), [`diagind`](@ref), [`Diagonal`](@ref), [`isdiag`](@ref). # Examples |
| 142 | `differential` | function (1 m) | Leibniz |  | Grassmann.jl/src/Grassmann.jl:111 |  |
| 143 | `disc` | function (2 m) | Grassmann | `discriminant` | Grassmann.jl/src/forms.jl:1534<br>Grassmann.jl/src/forms.jl:1533 |  |
| 144 | `disccomplex` | function (1 m) | Grassmann | `discriminantcomplex` | Grassmann.jl/src/forms.jl:1540 |  |
| 145 | `discreal` | function (1 m) | Grassmann | `discriminantreal` | Grassmann.jl/src/forms.jl:1537 |  |
| 146 | `discriminant` | function (2 m) | Grassmann |  | Grassmann.jl/src/forms.jl:1534<br>Grassmann.jl/src/forms.jl:1533 |  |
| 147 | `discriminantcomplex` | function (1 m) | Grassmann |  | Grassmann.jl/src/forms.jl:1540 |  |
| 148 | `discriminantreal` | function (1 m) | Grassmann |  | Grassmann.jl/src/forms.jl:1537 |  |
| 149 | `divergence` | function (3 m) | Grassmann |  | Grassmann.jl/src/composite.jl:946<br>Grassmann.jl/src/composite.jl:947<br>Grassmann.jl/src/composite.jl:948 |  |
| 150 | `dot` | function (66 m) | LinearAlgebra |  | AbstractTensors.jl/src/AbstractTensors.jl:265<br>AbstractTensors.jl/src/AbstractTensors.jl:445<br>AbstractTensors.jl/src/AbstractTensors.jl:297 | Compute the dot product between two vectors. For complex vectors, the first vector is conjugated. `dot` also works on arbitrary iterable objects, including arrays of any dimension, as long as `dot` is defined on the elements. `dot` is semantically equivalent t… |
| 151 | `eigen` | function (27 m) | LinearAlgebra |  | Grassmann.jl/src/forms.jl:1428<br>Grassmann.jl/src/forms.jl:1330<br>Grassmann.jl/src/forms.jl:1331 | Compute the eigenvalue decomposition of `A`, returning an [`Eigen`](@ref) factorization object `F` which contains the eigenvalues in `F.values` and the normalized eigenvectors in the columns of the matrix `F.vectors`. This corresponds to solving an eigenvalue … |
| 152 | `eigencomplex` | function (3 m) | Grassmann |  | Grassmann.jl/src/forms.jl:1330<br>Grassmann.jl/src/forms.jl:1331<br>Grassmann.jl/src/forms.jl:1436 |  |
| 153 | `eigenreal` | function (3 m) | Grassmann |  | Grassmann.jl/src/forms.jl:1330<br>Grassmann.jl/src/forms.jl:1331<br>Grassmann.jl/src/forms.jl:1432 |  |
| 154 | `eigmults` | function (2 m) | Grassmann |  | Grassmann.jl/src/forms.jl:1228<br>Grassmann.jl/src/forms.jl:1229 |  |
| 155 | `eigpolys` | function (16 m) | Grassmann |  | Grassmann.jl/src/forms.jl:1265<br>Grassmann.jl/src/forms.jl:1266<br>Grassmann.jl/src/forms.jl:1267<br>Grassmann.jl/src/forms.jl:1271 |  |
| 156 | `eigprods` | **exported but UNDEFINED in 0.8.46** | – | – |  | – |
| 157 | `eigvals` | function (27 m) | LinearAlgebra |  | Grassmann.jl/src/forms.jl:1351<br>Grassmann.jl/src/forms.jl:1352<br>Grassmann.jl/src/forms.jl:1349<br>Grassmann.jl/src/forms.jl:1374 | Return the eigenvalues of `A`. For general non-symmetric matrices it is possible to specify how the matrix is balanced before the eigenvalue calculation. The `permute`, `scale`, and `sortby` keywords are the same as for [`eigen`](@ref). # Examples For a scalar… |
| 158 | `eigvalscomplex` | function (7 m) | Grassmann |  | Grassmann.jl/src/forms.jl:1330<br>Grassmann.jl/src/forms.jl:1331<br>Grassmann.jl/src/forms.jl:1395<br>Grassmann.jl/src/forms.jl:1396 |  |
| 159 | `eigvalsreal` | function (3 m) | Grassmann |  | Grassmann.jl/src/forms.jl:1330<br>Grassmann.jl/src/forms.jl:1331<br>Grassmann.jl/src/forms.jl:1384 |  |
| 160 | `eigvecs` | function (22 m) | LinearAlgebra |  | Grassmann.jl/src/forms.jl:1338<br>Grassmann.jl/src/forms.jl:1335<br>Grassmann.jl/src/forms.jl:1336<br>Grassmann.jl/src/forms.jl:1337 | Return a matrix `M` whose columns are the eigenvectors of `A`. (The `k`th eigenvector can be obtained from the slice `M[:, k]`.) If the optional vector of eigenvalues `eigvals` is specified, `eigvecs` returns the specific corresponding eigenvectors. # Examples… |
| 161 | `eigvecscomplex` | function (7 m) | Grassmann |  | Grassmann.jl/src/forms.jl:1330<br>Grassmann.jl/src/forms.jl:1331<br>Grassmann.jl/src/forms.jl:1345<br>Grassmann.jl/src/forms.jl:1346 |  |
| 162 | `eigvecsreal` | function (6 m) | Grassmann |  | Grassmann.jl/src/forms.jl:1330<br>Grassmann.jl/src/forms.jl:1331<br>Grassmann.jl/src/forms.jl:1340<br>Grassmann.jl/src/forms.jl:1341 |  |
| 163 | `even` | function (8 m) | AbstractTensors |  | Grassmann.jl/src/parity.jl:496<br>Grassmann.jl/src/parity.jl:498<br>Grassmann.jl/src/parity.jl:485<br>Grassmann.jl/src/parity.jl:494 | Selects the `even` part `(t+involute(t))/2` and is defined by even grade. |
| 164 | `exph` | function (2 m) | Grassmann |  | Grassmann.jl/src/composite.jl:572 |  |
| 165 | `gdims` | function (5 m) | AbstractTensors |  | DirectSum.jl/src/grade.jl:23<br>AbstractTensors.jl/src/AbstractTensors.jl:181<br>DirectSum.jl/src/grade.jl:22 | Dimensionality of the grade `G` of `V` for that `TensorAlgebra`. |
| 166 | `geomabs` | function (2 m) | AbstractTensors |  | AbstractTensors.jl/src/AbstractTensors.jl:452<br>AbstractTensors.jl/src/AbstractTensors.jl:453 | Geometric norm defined as `geomabs(t) = abs(t) + coabs(t)`. |
| 167 | `gerschgorin` | function (3 m) | Grassmann |  | Grassmann.jl/src/forms.jl:1519<br>Grassmann.jl/src/forms.jl:1520<br>Grassmann.jl/src/forms.jl:1521 |  |
| 168 | `grad` | function (3 m) | Grassmann | `gradient` | Grassmann.jl/src/composite.jl:814<br>Grassmann.jl/src/composite.jl:856<br>Grassmann.jl/src/composite.jl:942 |  |
| 169 | `grade` | function (15 m) | Leibniz |  | Grassmann.jl/src/multivectors.jl:670<br>Grassmann.jl/src/multivectors.jl:697<br>Grassmann.jl/src/multivectors.jl:444<br>Grassmann.jl/src/multivectors.jl:315 |  |
| 170 | `hasinf` | function (6 m) | Leibniz |  | Leibniz.jl/src/generic.jl:54<br>Leibniz.jl/src/generic.jl:63<br>DirectSum.jl/src/generic.jl:115 |  |
| 171 | `hasorigin` | function (7 m) | Leibniz |  | Leibniz.jl/src/generic.jl:57<br>Leibniz.jl/src/generic.jl:61<br>Leibniz.jl/src/generic.jl:64 |  |
| 172 | `hodge` | function (25 m) | AbstractTensors | `complementrighthodge` | Grassmann.jl/src/products.jl:1338<br>Grassmann.jl/src/forms.jl:1026<br>Grassmann.jl/src/products.jl:1371<br>Grassmann.jl/src/products.jl:1333 | Grassmann-Hodge right complement: ⋆ω = ω∗I |
| 173 | `hyperplanes` | function (1 m) | Grassmann |  | Grassmann.jl/src/Grassmann.jl:62 |  |
| 174 | `imaginary` | function (4 m) | Grassmann |  | Grassmann.jl/src/multivectors.jl:1136<br>Grassmann.jl/src/multivectors.jl:1137<br>Grassmann.jl/src/multivectors.jl:1138<br>Grassmann.jl/src/multivectors.jl:1139 |  |
| 175 | `imagvalue` | function (4 m) | Grassmann |  | Grassmann.jl/src/multivectors.jl:823<br>Grassmann.jl/src/multivectors.jl:828<br>Grassmann.jl/src/multivectors.jl:869 |  |
| 176 | `indices` | function (3 m) | Leibniz |  | Leibniz.jl/src/indices.jl:106<br>Leibniz.jl/src/indices.jl:116<br>DirectSum.jl/src/DirectSum.jl:401 | Computes the indices at which a binary number `b` has bits equal to 1. The `N` argument (optional) specifies the length of the binary representation. |
| 177 | `invdet` | function (7 m) | Grassmann |  | Grassmann.jl/src/composite.jl:774<br>Grassmann.jl/src/composite.jl:853<br>Grassmann.jl/src/forms.jl:414<br>Grassmann.jl/src/forms.jl:530 |  |
| 178 | `involute` | function (12 m) | AbstractTensors |  | Grassmann.jl/src/products.jl:1830<br>Grassmann.jl/src/products.jl:1864<br>Grassmann.jl/src/products.jl:1820<br>Grassmann.jl/src/products.jl:1823 | Involute of an element: ~ω = (-1)^grade(ω)*ω |
| 179 | `isbivector` | function (3 m) | AbstractTensors |  | Grassmann.jl/src/multivectors.jl:1142 |  |
| 180 | `isdiag` | function (15 m) | LinearAlgebra |  | Grassmann.jl/src/forms.jl:1672 | Test whether a matrix is diagonal in the sense that `iszero(A[i,j])` is true unless `i == j`. Note that it is not necessary for `A` to be square; if you would also like to check that, you need to check that `size(A, 1) == size(A, 2)`. # Examples |
| 181 | `isgraded` | function (2 m) | AbstractTensors |  | AbstractTensors.jl/src/AbstractTensors.jl:72<br>AbstractTensors.jl/src/AbstractTensors.jl:73 | Test whether `t` is some subtype of `TensorGraded`. |
| 182 | `isscalar` | function (5 m) | AbstractTensors |  | Grassmann.jl/src/multivectors.jl:1147<br>Grassmann.jl/src/multivectors.jl:1146<br>Grassmann.jl/src/multivectors.jl:1140 |  |
| 183 | `istangent` | function (3 m) | Leibniz |  | Leibniz.jl/src/generic.jl:44<br>Leibniz.jl/src/generic.jl:36<br>Leibniz.jl/src/generic.jl:39 |  |
| 184 | `istensor` | function (2 m) | AbstractTensors |  | AbstractTensors.jl/src/AbstractTensors.jl:41<br>AbstractTensors.jl/src/AbstractTensors.jl:42 | Test whether `t` is some subtype of `TensorAlgebra`. |
| 185 | `isterm` | function (2 m) | AbstractTensors |  | AbstractTensors.jl/src/AbstractTensors.jl:115<br>AbstractTensors.jl/src/AbstractTensors.jl:116 | Test whether `t` is some subtype of `TensorTerm`. |
| 186 | `istrivector` | function (2 m) | AbstractTensors |  | Grassmann.jl/src/multivectors.jl:1143 |  |
| 187 | `isvector` | function (3 m) | AbstractTensors |  | Grassmann.jl/src/multivectors.jl:1141 |  |
| 188 | `isvolume` | function (3 m) | AbstractTensors |  | Grassmann.jl/src/multivectors.jl:1144 |  |
| 189 | `log_fast` | function (4 m) | Grassmann |  | Grassmann.jl/src/composite.jl:397<br>Grassmann.jl/src/composite.jl:575 |  |
| 190 | `logh_fast` | function (4 m) | Grassmann |  | Grassmann.jl/src/composite.jl:398<br>Grassmann.jl/src/composite.jl:575 |  |
| 191 | `mdims` | function (8 m) | AbstractTensors |  | Grassmann.jl/src/multivectors.jl:218<br>Grassmann.jl/src/multivectors.jl:217 | Dimensionality of the pseudoscalar `V` of that `TensorAlgebra`. |
| 192 | `mean` | function (4 m) | Grassmann |  | Grassmann.jl/src/composite.jl:936<br>Grassmann.jl/src/composite.jl:935<br>Grassmann.jl/src/composite.jl:937<br>Grassmann.jl/src/forms.jl:1712 |  |
| 193 | `means` | function (1 m) | Grassmann |  | Grassmann.jl/src/composite.jl:969 |  |
| 194 | `metric` | function (23 m) | Leibniz |  | Grassmann.jl/src/products.jl:1639<br>Grassmann.jl/src/forms.jl:1026<br>Grassmann.jl/src/products.jl:1724<br>Grassmann.jl/src/products.jl:1637 |  |
| 195 | `metricextensor` | function (1 m) | Grassmann |  | Grassmann.jl/src/forms.jl:1597 |  |
| 196 | `metrictensor` | function (5 m) | Grassmann |  | Grassmann.jl/src/forms.jl:1583<br>Grassmann.jl/src/forms.jl:1629<br>Grassmann.jl/src/forms.jl:1630<br>Grassmann.jl/src/forms.jl:1582 |  |
| 197 | `monicroots` | function (8 m) | Grassmann |  | Grassmann.jl/src/composite.jl:1115<br>Grassmann.jl/src/composite.jl:1182<br>Grassmann.jl/src/composite.jl:1114<br>Grassmann.jl/src/composite.jl:1127 |  |
| 198 | `monicrootscomplex` | function (7 m) | Grassmann |  | Grassmann.jl/src/composite.jl:1218<br>Grassmann.jl/src/composite.jl:1219<br>Grassmann.jl/src/composite.jl:1216<br>Grassmann.jl/src/composite.jl:1220 |  |
| 199 | `monicrootsreal` | function (6 m) | Grassmann |  | Grassmann.jl/src/composite.jl:1195<br>Grassmann.jl/src/composite.jl:1193<br>Grassmann.jl/src/composite.jl:1196<br>Grassmann.jl/src/composite.jl:1197 |  |
| 200 | `nabla` | const ::Nabla | Grassmann |  | Leibniz.jl/src/Leibniz.jl:156 | Abstract `nabla` as first-order `Derivation{Bool,1}` is `Nabla` operator dispatch. |
| 201 | `norm` | function (17 m) | LinearAlgebra |  | AbstractTensors.jl/src/AbstractTensors.jl:442<br>AbstractTensors.jl/src/AbstractTensors.jl:367<br>StaticVectors.jl/src/linalg.jl:96 | For any iterable container `A` (including arrays of any dimension) of numbers (or any element type for which `norm` is defined), compute the `p`-norm (defaulting to `p=2`) as if `A` were a vector of the corresponding length. The `p`-norm is defined as $$ \\|A\… |
| 202 | `odd` | function (8 m) | AbstractTensors |  | Grassmann.jl/src/parity.jl:497<br>Grassmann.jl/src/parity.jl:499<br>Grassmann.jl/src/parity.jl:495<br>Grassmann.jl/src/parity.jl:492 | Selects the `odd` part `(t-involute(t))/2` and is defined by odd grade. |
| 203 | `operator` | function (8 m) | Grassmann |  | Grassmann.jl/src/forms.jl:1183<br>Grassmann.jl/src/forms.jl:1182<br>Grassmann.jl/src/forms.jl:1186<br>Grassmann.jl/src/forms.jl:1201 |  |
| 204 | `outer` | function (3 m) | Grassmann |  | Grassmann.jl/src/forms.jl:883<br>Grassmann.jl/src/forms.jl:884<br>Grassmann.jl/src/forms.jl:885 |  |
| 205 | `outermorphism` | function (4 m) | Grassmann |  | Grassmann.jl/src/forms.jl:521<br>Grassmann.jl/src/forms.jl:719<br>Grassmann.jl/src/forms.jl:736<br>Grassmann.jl/src/forms.jl:1190 |  |
| 206 | `path` | function (1 m) | Grassmann |  | Grassmann.jl/src/Grassmann.jl:256 |  |
| 207 | `pfaffian` | function (4 m) | Grassmann |  | Grassmann.jl/src/composite.jl:887<br>Grassmann.jl/src/composite.jl:888<br>Grassmann.jl/src/forms.jl:592<br>Grassmann.jl/src/forms.jl:741 |  |
| 208 | `phase` | function (10 m) | Grassmann |  | Grassmann.jl/src/multivectors.jl:895<br>Grassmann.jl/src/multivectors.jl:896<br>Grassmann.jl/src/multivectors.jl:899<br>Grassmann.jl/src/multivectors.jl:900 |  |
| 209 | `pointfield` | function (0 m) | Grassmann |  |  |  |
| 210 | `points` | function (5 m) | Grassmann |  | Grassmann.jl/src/multivectors.jl:221<br>Grassmann.jl/src/multivectors.jl:222<br>Grassmann.jl/src/multivectors.jl:223<br>Grassmann.jl/src/Grassmann.jl:68 |  |
| 211 | `polarize` | function (20 m) | Grassmann |  | Grassmann.jl/src/multivectors.jl:1064<br>Grassmann.jl/src/multivectors.jl:1063<br>Grassmann.jl/src/multivectors.jl:1054<br>Grassmann.jl/src/multivectors.jl:1058 |  |
| 212 | `project` | function (3 m) | Grassmann |  | Grassmann.jl/src/Grassmann.jl:181<br>Grassmann.jl/src/Grassmann.jl:186<br>Grassmann.jl/src/Grassmann.jl:164 | Canonical up-`project` operation from the space `V`, based on either Euclidean projective geometry, or the Riemann sphere, or conformal geometric algebra, or potentially other future canonical specifications. Optional arguments expose lower-level building bloc… |
| 213 | `pseudoabs` | function (2 m) | AbstractTensors |  | AbstractTensors.jl/src/AbstractTensors.jl:540<br>AbstractTensors.jl/src/AbstractTensors.jl:543 | Complemented `abs` defined as `complementleft(abs(complementright(t)))`. |
| 214 | `pseudoabs2` | function (2 m) | AbstractTensors |  | AbstractTensors.jl/src/AbstractTensors.jl:540<br>AbstractTensors.jl/src/AbstractTensors.jl:543 | Complemented `abs2` defined as `complementleft(abs2(complementright(t)))`. |
| 215 | `pseudocbrt` | function (2 m) | AbstractTensors |  | AbstractTensors.jl/src/AbstractTensors.jl:540<br>AbstractTensors.jl/src/AbstractTensors.jl:543 | Complemented `cbrt` defined as `complementleft(cbrt(complementright(t)))`. |
| 216 | `pseudocos` | function (2 m) | AbstractTensors |  | AbstractTensors.jl/src/AbstractTensors.jl:540<br>AbstractTensors.jl/src/AbstractTensors.jl:543 | Complemented `cos` defined as `complementleft(cos(complementright(t)))`. |
| 217 | `pseudocosh` | function (2 m) | AbstractTensors |  | AbstractTensors.jl/src/AbstractTensors.jl:540<br>AbstractTensors.jl/src/AbstractTensors.jl:543 | Complemented `cosh` defined as `complementleft(cosh(complementright(t)))`. |
| 218 | `pseudodot` | **exported but UNDEFINED in 0.8.46** | – | – | AbstractTensors.jl/src/AbstractTensors.jl:314 | – |
| 219 | `pseudoexp` | function (2 m) | AbstractTensors |  | AbstractTensors.jl/src/AbstractTensors.jl:540<br>AbstractTensors.jl/src/AbstractTensors.jl:543 | Complemented `exp` defined as `complementleft(exp(complementright(t)))`. |
| 220 | `pseudograde` | function (7 m) | Leibniz |  | Leibniz.jl/src/generic.jl:152<br>DirectSum.jl/src/generic.jl:112<br>Leibniz.jl/src/generic.jl:153 |  |
| 221 | `pseudoinv` | function (2 m) | AbstractTensors |  | AbstractTensors.jl/src/AbstractTensors.jl:540<br>AbstractTensors.jl/src/AbstractTensors.jl:543 | Complemented `inv` defined as `complementleft(inv(complementright(t)))`. |
| 222 | `pseudolog` | function (1 m) | AbstractTensors |  | AbstractTensors.jl/src/AbstractTensors.jl:540 | Complemented `log` defined as `complementleft(log(complementright(t)))`. |
| 223 | `pseudometric` | function (27 m) | AbstractTensors | `cometric` | Grassmann.jl/src/products.jl:1639<br>Grassmann.jl/src/forms.jl:1026<br>Grassmann.jl/src/products.jl:1637<br>Grassmann.jl/src/products.jl:1636 |  |
| 224 | `pseudoreverse` | function (9 m) | DirectSum |  | Grassmann.jl/src/products.jl:1830<br>Grassmann.jl/src/products.jl:1820<br>Grassmann.jl/src/products.jl:1823<br>Grassmann.jl/src/products.jl:1901 | Anti-reverse of an element: ~ω = (-1)^(pseudograde(ω)*(pseudograde(ω)-1)/2)*ω |
| 225 | `pseudosandwich` | function (2 m) | AbstractTensors | `cosandwich` | AbstractTensors.jl/src/AbstractTensors.jl:557<br>AbstractTensors.jl/src/AbstractTensors.jl:558 | Defined as `complementleft(sandwich(complementright(x),complementright(R)))`. |
| 226 | `pseudoscalar` | function (9 m) | AbstractTensors |  | Grassmann.jl/src/multivectors.jl:1130<br>Grassmann.jl/src/multivectors.jl:1131<br>Grassmann.jl/src/multivectors.jl:1132<br>Grassmann.jl/src/multivectors.jl:1134 | Return the pseudoscalar (full rank) part of any `TensorAlgebra` element. |
| 227 | `pseudosin` | function (2 m) | AbstractTensors |  | AbstractTensors.jl/src/AbstractTensors.jl:540<br>AbstractTensors.jl/src/AbstractTensors.jl:543 | Complemented `sin` defined as `complementleft(sin(complementright(t)))`. |
| 228 | `pseudosinh` | function (2 m) | AbstractTensors |  | AbstractTensors.jl/src/AbstractTensors.jl:540<br>AbstractTensors.jl/src/AbstractTensors.jl:543 | Complemented `sinh` defined as `complementleft(sinh(complementright(t)))`. |
| 229 | `pseudosqrt` | function (2 m) | AbstractTensors |  | AbstractTensors.jl/src/AbstractTensors.jl:540<br>AbstractTensors.jl/src/AbstractTensors.jl:543 | Complemented `sqrt` defined as `complementleft(sqrt(complementright(t)))`. |
| 230 | `pseudotan` | function (2 m) | AbstractTensors |  | AbstractTensors.jl/src/AbstractTensors.jl:540<br>AbstractTensors.jl/src/AbstractTensors.jl:543 | Complemented `tan` defined as `complementleft(tan(complementright(t)))`. |
| 231 | `pseudotanh` | function (2 m) | AbstractTensors |  | AbstractTensors.jl/src/AbstractTensors.jl:540<br>AbstractTensors.jl/src/AbstractTensors.jl:543 | Complemented `tanh` defined as `complementleft(tanh(complementright(t)))`. |
| 232 | `quaternion` | function (14 m) | Grassmann |  | Grassmann.jl/src/multivectors.jl:1082<br>Grassmann.jl/src/multivectors.jl:1086<br>Grassmann.jl/src/multivectors.jl:1085<br>Grassmann.jl/src/multivectors.jl:1080 |  |
| 233 | `quatvalue` | function (3 m) | Grassmann |  | Grassmann.jl/src/multivectors.jl:1088<br>Grassmann.jl/src/multivectors.jl:1089<br>Grassmann.jl/src/multivectors.jl:1087 |  |
| 234 | `quatvalues` | function (3 m) | Grassmann | `quatvalue` | Grassmann.jl/src/multivectors.jl:1088<br>Grassmann.jl/src/multivectors.jl:1089<br>Grassmann.jl/src/multivectors.jl:1087 |  |
| 235 | `radial` | **exported but UNDEFINED in 0.8.46** | – | – |  | – |
| 236 | `radius` | function (12 m) | Grassmann |  | Grassmann.jl/src/multivectors.jl:913<br>Grassmann.jl/src/multivectors.jl:912<br>Grassmann.jl/src/multivectors.jl:906<br>Grassmann.jl/src/multivectors.jl:907 |  |
| 237 | `realvalue` | function (4 m) | Grassmann |  | Grassmann.jl/src/multivectors.jl:822<br>Grassmann.jl/src/multivectors.jl:827<br>Grassmann.jl/src/multivectors.jl:868 |  |
| 238 | `rectanglefield` | function (3 m) | Grassmann |  | Grassmann.jl/src/Grassmann.jl:348 |  |
| 239 | `reject` | function (3 m) | Grassmann |  | Grassmann.jl/src/Grassmann.jl:209<br>Grassmann.jl/src/Grassmann.jl:210<br>Grassmann.jl/src/Grassmann.jl:192 | Canonical down-`reject` operation from the space `V`, based on either Euclidean projective geometry, or the Riemann sphere, or conformal geometric algebra, or potentially other future canonical specifications. Optional arguments expose lower-level building blo… |
| 240 | `roots` | function (6 m) | Grassmann |  | Grassmann.jl/src/composite.jl:1095<br>Grassmann.jl/src/composite.jl:1096<br>Grassmann.jl/src/composite.jl:1099<br>Grassmann.jl/src/composite.jl:1094 |  |
| 241 | `rootscomplex` | function (6 m) | Grassmann |  | Grassmann.jl/src/composite.jl:1106<br>Grassmann.jl/src/composite.jl:1107<br>Grassmann.jl/src/composite.jl:1110<br>Grassmann.jl/src/composite.jl:1105 |  |
| 242 | `rootsreal` | function (3 m) | Grassmann |  | Grassmann.jl/src/composite.jl:1102<br>Grassmann.jl/src/composite.jl:1103<br>Grassmann.jl/src/composite.jl:1101 |  |
| 243 | `sandwich` | function (23 m) | AbstractTensors |  | Grassmann.jl/src/algebra.jl:315<br>Grassmann.jl/src/algebra.jl:319<br>Grassmann.jl/src/algebra.jl:330<br>Grassmann.jl/src/algebra.jl:338 |  |
| 244 | `scalar` | function (15 m) | AbstractTensors |  | Grassmann.jl/src/forms.jl:593<br>Grassmann.jl/src/multivectors.jl:1110<br>Grassmann.jl/src/multivectors.jl:1111<br>Grassmann.jl/src/multivectors.jl:1107 | Return the scalar (rank 0) part of any `TensorAlgebra` element. |
| 245 | `scalarfield` | function (1 m) | Grassmann |  | Grassmann.jl/src/Grassmann.jl:315 |  |
| 246 | `skeleton` | function (6 m) | Grassmann |  | Grassmann.jl/src/Grassmann.jl:261<br>Grassmann.jl/src/Grassmann.jl:265<br>Grassmann.jl/src/Grassmann.jl:275 |  |
| 247 | `subcomplex` | function (2 m) | Grassmann |  | Grassmann.jl/src/Grassmann.jl:260 |  |
| 248 | `sylvester` | function (2 m) | Grassmann |  | Grassmann.jl/src/forms.jl:1224<br>Grassmann.jl/src/forms.jl:1225 |  |
| 249 | `tangent` | function (6 m) | DirectSum |  | DirectSum.jl/src/generic.jl:128<br>DirectSum.jl/src/generic.jl:129 |  |
| 250 | `tdims` | function (3 m) | AbstractTensors |  | AbstractTensors.jl/src/AbstractTensors.jl:172<br>AbstractTensors.jl/src/AbstractTensors.jl:170<br>AbstractTensors.jl/src/AbstractTensors.jl:171 | Dimensionality of the superalgebra of `V` for that `TensorAlgebra`. |
| 251 | `tr` | function (29 m) | LinearAlgebra |  | Grassmann.jl/src/forms.jl:318<br>Grassmann.jl/src/forms.jl:321<br>Grassmann.jl/src/forms.jl:314<br>Grassmann.jl/src/forms.jl:313 | Matrix trace. Sums the diagonal elements of `M`. # Examples |
| 252 | `trivector` | function (7 m) | AbstractTensors |  | Grassmann.jl/src/multivectors.jl:1124<br>Grassmann.jl/src/multivectors.jl:1125<br>Grassmann.jl/src/multivectors.jl:1126<br>Grassmann.jl/src/multivectors.jl:1127 | Return the trivector (rank 3) part of any `TensorAlgebra` element. |
| 253 | `unit` | function (2 m) | AbstractTensors |  | AbstractTensors.jl/src/AbstractTensors.jl:460<br>AbstractTensors.jl/src/AbstractTensors.jl:461 | Normalization defined as `unit(t) = t/abs(t)`. |
| 254 | `unitangle` | function (10 m) | Grassmann |  | Grassmann.jl/src/multivectors.jl:887<br>Grassmann.jl/src/multivectors.jl:888<br>Grassmann.jl/src/multivectors.jl:886<br>Grassmann.jl/src/multivectors.jl:885 |  |
| 255 | `unitize` | function (2 m) | AbstractTensors | `counit` | AbstractTensors.jl/src/AbstractTensors.jl:468<br>AbstractTensors.jl/src/AbstractTensors.jl:469 | Pseudo-normalization defined as `unitize(t) = t/value(coabs(t))`. |
| 256 | `unitnorm` | function (2 m) | AbstractTensors |  | AbstractTensors.jl/src/AbstractTensors.jl:477<br>AbstractTensors.jl/src/AbstractTensors.jl:478 | Geometric normalization defined as `unitnorm(t) = t/norm(geomabs(t))`. |
| 257 | `value` | function (26 m) | AbstractTensors |  | Grassmann.jl/src/multivectors.jl:225<br>Grassmann.jl/src/multivectors.jl:1093<br>Grassmann.jl/src/forms.jl:501<br>Grassmann.jl/src/multivectors.jl:1096 | Returns the internal `Values` representation of a `TensorAlgebra` element. |
| 258 | `valuetype` | function (4 m) | AbstractTensors |  | AbstractTensors.jl/src/AbstractTensors.jl:221<br>AbstractTensors.jl/src/AbstractTensors.jl:222<br>AbstractTensors.jl/src/AbstractTensors.jl:223 | Returns type of a `TensorAlgebra` element value's internal representation. |
| 259 | `vandermonde` | function (7 m) | Grassmann |  | Grassmann.jl/src/composite.jl:862<br>Grassmann.jl/src/composite.jl:871<br>Grassmann.jl/src/composite.jl:863<br>Grassmann.jl/src/composite.jl:872 |  |
| 260 | `vandermondecomplex` | function (1 m) | Grassmann |  | Grassmann.jl/src/forms.jl:1532 |  |
| 261 | `vandermondereal` | function (1 m) | Grassmann |  | Grassmann.jl/src/forms.jl:1531 |  |
| 262 | `vector` | function (9 m) | AbstractTensors |  | Grassmann.jl/src/multivectors.jl:1114<br>Grassmann.jl/src/multivectors.jl:1115<br>Grassmann.jl/src/multivectors.jl:1117<br>Grassmann.jl/src/multivectors.jl:1118 | Return the vector (rank 1) part of any `TensorAlgebra` element. |
| 263 | `vectorfield` | function (0 m) | Grassmann | `pointfield` |  |  |
| 264 | `vectorize` | function (7 m) | Grassmann |  | Grassmann.jl/src/multivectors.jl:1068<br>Grassmann.jl/src/multivectors.jl:1069<br>Grassmann.jl/src/multivectors.jl:1070<br>Grassmann.jl/src/multivectors.jl:1071 |  |
| 265 | `vee` | function (93 m) | AbstractLattices |  | Grassmann.jl/src/products.jl:1132<br>Grassmann.jl/src/algebra.jl:189<br>Grassmann.jl/src/products.jl:763<br>Grassmann.jl/src/products.jl:1174 |  |
| 266 | `veedot` | function (3 m) | AbstractTensors |  | Grassmann.jl/src/algebra.jl:391 |  |
| 267 | `volumes` | function (2 m) | Grassmann |  | Grassmann.jl/src/composite.jl:932<br>Grassmann.jl/src/composite.jl:933 |  |
| 268 | `wedge` | function (117 m) | AbstractLattices |  | Grassmann.jl/src/products.jl:1133<br>Grassmann.jl/src/products.jl:1134<br>Grassmann.jl/src/algebra.jl:115<br>Grassmann.jl/src/algebra.jl:122 |  |
| 269 | `wedgedot` | function (105 m) | AbstractTensors |  | Grassmann.jl/src/products.jl:714<br>Grassmann.jl/src/forms.jl:1008<br>Grassmann.jl/src/forms.jl:1006<br>Grassmann.jl/src/forms.jl:1007 |  |
| 270 | `×` | function (4 m) | LinearAlgebra | `cross` | Leibniz.jl/src/Leibniz.jl:149<br>Leibniz.jl/src/Leibniz.jl:150<br>AbstractTensors.jl/src/AbstractTensors.jl:349 | Compute the cross product of two 3-vectors. # Examples Cross product: ω×η = ⋆(ω∧η) |
| 271 | `ǂ` | const ::AbstractTensors.Postfix{:ǂ} | Grassmann |  |  |  |
| 272 | `Δ` | const ::Laplacian | Grassmann |  | Leibniz.jl/src/Leibniz.jl:155 | Abstract `laplacian` as second-order `Derivation{Bool,2}` is `Laplacian` operator dispatch. |
| 273 | `Λ` | type | DirectSum |  | DirectSum.jl/src/basis.jl:206 |  |
| 274 | `δ` | function (1 m) | Leibniz | `codifferential` | Grassmann.jl/src/Grassmann.jl:112 |  |
| 275 | `χ` | function (5 m) | Leibniz |  | Grassmann.jl/src/multivectors.jl:1232<br>Grassmann.jl/src/multivectors.jl:1233 | Compute the Euler characteristic χ = ∑ₚ(-1)ᵖbₚ. |
| 276 | `₊` | const ::AbstractTensors.Postfix{:₊} | Grassmann |  |  |  |
| 277 | `₋` | const ::AbstractTensors.Postfix{:₋} | Grassmann |  |  |  |
| 278 | `ℝ` | const ::Signature{1, 0, 0x0000000000000000, 0, 0, 1} | Grassmann |  | DirectSum.jl/src/DirectSum.jl:443 |  |
| 279 | `ℝ0` | const ::One{0} | Grassmann |  |  |  |
| 280 | `ℝ1` | const ::Submanifold{1, 1, 0x0000000000000001} | Grassmann |  |  |  |
| 281 | `ℝ2` | const ::Submanifold{2, 2, 0x0000000000000003} | Grassmann |  |  |  |
| 282 | `ℝ3` | const ::Submanifold{3, 3, 0x0000000000000007} | Grassmann |  |  |  |
| 283 | `ℝ4` | const ::Submanifold{4, 4, 0x000000000000000f} | Grassmann |  |  |  |
| 284 | `ℝ5` | const ::Submanifold{5, 5, 0x000000000000001f} | Grassmann |  |  |  |
| 285 | `ℝ6` | const ::Submanifold{6, 6, 0x000000000000003f} | Grassmann |  |  |  |
| 286 | `ℝ7` | const ::Submanifold{7, 7, 0x000000000000007f} | Grassmann |  |  |  |
| 287 | `ℝ8` | const ::Submanifold{8, 8, 0x00000000000000ff} | Grassmann |  |  |  |
| 288 | `ℝ9` | const ::Submanifold{9, 9, 0x00000000000001ff} | Grassmann |  |  |  |
| 289 | `↑` | function (3 m) | Grassmann | `project` | Grassmann.jl/src/Grassmann.jl:181<br>Grassmann.jl/src/Grassmann.jl:186<br>Grassmann.jl/src/Grassmann.jl:164 | Canonical up-`project` operation from the space `V`, based on either Euclidean projective geometry, or the Riemann sphere, or conformal geometric algebra, or potentially other future canonical specifications. Optional arguments expose lower-level building bloc… |
| 290 | `↓` | function (3 m) | Grassmann | `reject` | Grassmann.jl/src/Grassmann.jl:209<br>Grassmann.jl/src/Grassmann.jl:210<br>Grassmann.jl/src/Grassmann.jl:192 | Canonical down-`reject` operation from the space `V`, based on either Euclidean projective geometry, or the Riemann sphere, or conformal geometric algebra, or potentially other future canonical specifications. Optional arguments expose lower-level building blo… |
| 291 | `∂` | function (2 m) | Leibniz | `boundary` | Grassmann.jl/src/Grassmann.jl:109<br>Grassmann.jl/src/Grassmann.jl:110 |  |
| 292 | `∇` | const ::Nabla | Grassmann |  | Grassmann.jl/src/Grassmann.jl:92 | Abstract `nabla` as first-order `Derivation{Bool,1}` is `Nabla` operator dispatch. |
| 293 | `∗` | function (7 m) | AbstractTensors |  | AbstractTensors.jl/src/AbstractTensors.jl:257<br>AbstractTensors.jl/src/AbstractTensors.jl:289<br>AbstractTensors.jl/src/AbstractTensors.jl:290 | Reversed geometric product: ω∗η = (~ω)*η |
| 294 | `∠` | type | Grassmann |  | Grassmann.jl/src/multivectors.jl:871 |  |
| 295 | `∥` | function (1 m) | Grassmann |  | Grassmann.jl/src/algebra.jl:401 |  |
| 296 | `∧` | function (117 m) | AbstractLattices | `wedge` | Grassmann.jl/src/products.jl:1133<br>Grassmann.jl/src/products.jl:1134<br>Grassmann.jl/src/algebra.jl:115<br>Grassmann.jl/src/algebra.jl:122 | Exterior product as defined by the anti-symmetric quotient Λ≡⊗/~ |
| 297 | `∨` | function (93 m) | AbstractLattices | `vee` | Grassmann.jl/src/products.jl:1132<br>Grassmann.jl/src/algebra.jl:189<br>Grassmann.jl/src/products.jl:763<br>Grassmann.jl/src/products.jl:1174 | Regressive product as defined by the DeMorgan's law: ∨(ω...) = ⋆⁻¹(∧(⋆.(ω)...)) |
| 298 | `⊕` | function (7 m) | DirectSum |  | Grassmann.jl/src/forms.jl:597 |  |
| 299 | `⊖` | function (105 m) | AbstractTensors | `wedgedot` | Grassmann.jl/src/products.jl:714<br>Grassmann.jl/src/forms.jl:1008<br>Grassmann.jl/src/forms.jl:1006<br>Grassmann.jl/src/forms.jl:1007 |  |
| 300 | `⊗` | function (10 m) | AbstractTensors |  | Grassmann.jl/src/multivectors.jl:199<br>Grassmann.jl/src/multivectors.jl:198<br>Grassmann.jl/src/multivectors.jl:197<br>Grassmann.jl/src/algebra.jl:151 |  |
| 301 | `⊘` | function (23 m) | AbstractTensors | `sandwich` | Grassmann.jl/src/algebra.jl:315<br>Grassmann.jl/src/algebra.jl:319<br>Grassmann.jl/src/algebra.jl:330<br>Grassmann.jl/src/algebra.jl:338 | General sandwich product: ω⊘η = reverse(η)⊖ω⊖involute(η) For normalized even grade η it is ω⊘η = (~η)⊖ω⊖η |
| 302 | `⊙` | function (1 m) | AbstractTensors |  | Grassmann.jl/src/algebra.jl:294 | Symmetrization projection: ⊙(ω...) = ∑(∏(σ.(ω)...))/factorial(length(ω)) |
| 303 | `⊛` | function (7 m) | AbstractTensors |  | AbstractTensors.jl/src/AbstractTensors.jl:258<br>AbstractTensors.jl/src/AbstractTensors.jl:289<br>AbstractTensors.jl/src/AbstractTensors.jl:290 |  |
| 304 | `⊠` | function (1 m) | AbstractTensors |  | Grassmann.jl/src/algebra.jl:301 | Anti-symmetrization projection: ⊠(ω...) = ∑(∏(πσ.(ω)...))/factorial(length(ω)) |
| 305 | `⋅` | function (66 m) | LinearAlgebra | `dot` | AbstractTensors.jl/src/AbstractTensors.jl:265<br>AbstractTensors.jl/src/AbstractTensors.jl:445<br>AbstractTensors.jl/src/AbstractTensors.jl:297 | Compute the dot product between two vectors. For complex vectors, the first vector is conjugated. `dot` also works on arbitrary iterable objects, including arrays of any dimension, as long as `dot` is defined on the elements. `dot` is semantically equivalent t… |
| 306 | `⋆` | function (25 m) | AbstractTensors | `complementrighthodge` | Grassmann.jl/src/products.jl:1338<br>Grassmann.jl/src/forms.jl:1026<br>Grassmann.jl/src/products.jl:1371<br>Grassmann.jl/src/products.jl:1333 | Grassmann-Hodge right complement: ⋆ω = ω∗I |
| 307 | `⟂` | **exported but UNDEFINED in 0.8.46** | – | – |  | – |
| 308 | `⟇` | function (3 m) | AbstractTensors | `veedot` | Grassmann.jl/src/algebra.jl:391 |  |
| 309 | `⟑` | function (105 m) | AbstractTensors | `wedgedot` | Grassmann.jl/src/products.jl:714<br>Grassmann.jl/src/forms.jl:1008<br>Grassmann.jl/src/forms.jl:1006<br>Grassmann.jl/src/forms.jl:1007 | Geometric algebraic product: ω⊖η = (-1)ᵖdet(ω∩η)⊗(Λ(ω⊖η)∪L(ω⊕η)) |
| 310 | `⨼` | function (6 m) | AbstractTensors |  | AbstractTensors.jl/src/AbstractTensors.jl:259<br>AbstractTensors.jl/src/AbstractTensors.jl:289<br>AbstractTensors.jl/src/AbstractTensors.jl:290 |  |
| 311 | `⨽` | function (6 m) | AbstractTensors |  | AbstractTensors.jl/src/AbstractTensors.jl:265<br>AbstractTensors.jl/src/AbstractTensors.jl:289<br>AbstractTensors.jl/src/AbstractTensors.jl:290 |  |
| 312 | `𝒫` | function (1 m) | Grassmann |  | Grassmann.jl/src/Grassmann.jl:259 |  |
| 313 | `𝓛` | const ::LieBracket | Grassmann |  | Grassmann.jl/src/forms.jl:1551 |  |
| 314 | `𝕚` | const ::Single{⟨111⟩, 2, v₂₃, Int64} | Grassmann |  | Grassmann.jl/src/Grassmann.jl:71 |  |
| 315 | `𝕛` | const ::Single{⟨111⟩, 2, v₁₃, Int64} | Grassmann |  | Grassmann.jl/src/Grassmann.jl:71 |  |
| 316 | `𝕜` | const ::Single{⟨111⟩, 2, v₁₂, Int64} | Grassmann |  | Grassmann.jl/src/Grassmann.jl:71 |  |


### 2.4 Documented semantics of the core API (README "API design overview")

The README (`README.md:194-264`) and `algebra.md:359-432` give one-line specs; reproduced here with the oracle-verified behaviour attached. Items marked **(verified)** have transcript evidence in §6.

Unary (`README.md:194-227`, `algebra.md:359-392`):

| fn | doc semantics | notes / verified behaviour |
|---|---|---|
| `Manifold(x)` | returns the `V::Submanifold{M}` parameter | |
| `mdims(x)` | dimension n of the pseudoscalar of V | (verified) `mdims(S"∞∅+") == 3` |
| `gdims(x)` / `gdims(n,g)` | dim of grade G = `binomial(n,G)` | `gdims(3,2) = 3`; `gdims(::Multivector)` has **no method** and `gdims(A,2)` hits a constructor ambiguity (MethodError) on the oracle |
| `tdims(x)` | dim of Multivector = 2^n | (verified) `tdims(A) = tdims(V) = 8` for n=3 |
| `grade(x)` / `grade(x,g)` | G of `TensorGraded{V,G}`; `grade(x,g)` = ⟨x⟩_g | (verified) also callable form `x(g)`; `m[g]` on a Multivector returns the grade-g `Values` slice |
| `istensor`, `isgraded`, `isterm` | predicates | |
| `complementright` (`!`) | Euclidean-metric Grassmann right complement | (verified) formula §4.3 |
| `complementleft` | Euclidean left complement | (verified) |
| `complementrighthodge` (`⋆`,`hodge`) | "Grassmann-Hodge right complement `reverse(x)*I`" | (verified) = complementright∘metric |
| `complementlefthodge` | "`I*reverse(x)`" | |
| `metric` | applies `metricextensor` as outermorphism | (verified) diagonal: multiply blade by ∏ g_ii |
| `cometric` | applies complement metricextensor | |
| `metrictensor` | g bilinear form | |
| `metricextensor` (README typo "metrictextensor") | outermorphism Λg | |
| `involute` | `grade(x,k)*(-1)^k` | (verified) |
| `reverse` (`~`) | `grade(x,k)*(-1)^(k(k-1)/2)` | (verified) |
| `clifford` (`conj` is NOT clifford) | `involute ∘ reverse` | (verified) `conj(A) == reverse(A)` on the oracle, `clifford` flips grades 1,2 |
| `even` / `odd` | `(x ± involute(x))/2` | (verified) |
| `real` / `imag` | `(x ± reverse(x))/2` | (verified) `imag` keeps grades 2,3 (mod 4 in {2,3}) |
| `abs` / `abs2` | `sqrt(reverse(x)*x)` / `reverse(x)*x` | **abs2 returns the full product `~x*x` (a Multivector), not its scalar part** (verified: `abs2(A) = 30 + 4v₁ + 12v₂ + 24v₃`) ; `abs` errors when `~x*x` is not invertible-scalar-like |
| `norm` | positive definite norm of coefficients | (verified) `norm(Multivector(1..8)) = √204 = 14.2828568570857` (Euclidean coefficient norm) |
| `unit` | `t/abs(t)` | (verified) |
| `scalar`, `vector`, `bivector`, `trivector`, `pseudoscalar` | grade 0,1,2,3,n parts | (verified) scalar returns a `Single` (`1v`), not a number |
| `value` / `valuetype` | internal `Values` tuple / its eltype | (verified) |

Binary (`README.md:229-234`): `+ -` from the K-module; `wedge ∧`, `vee ∨`; `>` right contraction, `<` left contraction; `*` geometric; `/` via `inv`; `⊘` sandwich and `>>>` its alternate orientation.

Operator / polynomial layer (`README.md:236-264`, `algebra.md:401-432`): `inv`, `adjugate` (transposed cofactor), `det`, `tr`, `transpose`, `compound(F,g)` (graded multilinear endomorphism Λ^g F), `outermorphism(A)`, `operator(x)` (linear representation of the multivector outermorphism, i.e. the matrix of `v ↦ v⊘x`), `companion` (companion matrix of monic `a0+…+an z^n+z^(n+1)`), `roots/rootsreal/rootscomplex(a...)` (roots of `a0+a1 z+…+an z^n`), `monicroots*`, `characteristic(A)` (coefficients of `det(A-λI)`), `eigvals/eigvalsreal/eigvalscomplex`, `eigvecs*`, `eigen*` (spectral decomposition `Σ λi Proj(ei)`), `eigpolys(A[,g])` (normalized symmetric functions of eigenvalues), `vandermonde` (`(inv(X'X)X')y` least squares), `cayley(V,∘)` (product table), `complexify` / `vectorize` (`algebra.md:434-449`).

## 3. Data representations

### 3.1 Type hierarchy (docs `README.md:160-190`, `algebra.md:242-277`; definitions in `src`)

```
TensorAlgebra{V,K}                         (AbstractTensors; <: Number !)
├─ TensorGraded{V,G,K}
│   ├─ Chain{V,G,K}          v::Values{binomial(n,G),K}          multivectors.jl:68-71  (@computed struct)
│   │    Simplex{V,T<:GradedVector,N} = Chain{V,1,T,N}            multivectors.jl:94    (column-module, nested Chain = matrix)
│   └─ TensorTerm{V,G,K}                                           single coefficient
│        ├─ Zero{V}            (prints 𝟎)                         DirectSum.jl:604
│        ├─ Submanifold{V,G,B} basis blade, no storage; One{V}=Submanifold{V,0}   DirectSum.jl:254
│        └─ Single{V,G,B,K}    v::K paired with blade B            DirectSum (show DirectSum.jl:488)
├─ TensorMixed{V,K}
│   ├─ Multivector{V,K}      v::Values{2^n,K}                    multivectors.jl:229-232
│   │    Multiplex{V,T<:Multivector,N} = Multivector{V,T,N}        multivectors.jl:277 (cayley tables)
│   └─ AbstractSpinor{V,K}                                         multivectors.jl:414
│        ├─ Spinor{V,K}      v::Values{2^(n-1),K} even grades    multivectors.jl:420-455 (loop; `@computed struct $pinor` at :422)
│        │    Quaternion{V,T}=Spinor{V,T,4}, Imaginary=Spinor{V,T,2}, LipschitzInteger   multivectors.jl:971-974
│        ├─ CoSpinor{V,K} (=AntiSpinor) odd grades, 2^(n-1)         same loop; alias :456; AntiQuaternion :973
│        ├─ Couple{V,B,K}    v::Values{2,K} = scalar + coeff·B    multivectors.jl:656-659; GaussianInteger alias :975
│        ├─ PseudoCouple{V,B,K} v::Values{2,K} = coeff·B + coeff·I   multivectors.jl:677-680
│        └─ Phasor{V,B,T}    (v::T amplitude, ω::B) polar form    multivectors.jl:852-856; ∠ alias :871
├─ Manifold{V,T}
│   ├─ ChainBundle{V,G,T,Points} (global cell geometry, cache index)  multivectors.jl:211
│   └─ TensorNested{V,T}                                           forms.jl:298
│        ├─ TensorOperator{V,W,T} (v::T nested Chain/Multivector)  forms.jl:555; Endomorphism = TensorOperator{V,V,T} :563
│        ├─ DiagonalOperator{V,T}; DiagonalMorphism (T<:Chain{V,1}), DiagonalOutermorphism (T<:Multivector)  forms.jl:476-482
│        ├─ Outermorphism{V,T<:Tuple}                              forms.jl:714
│        ├─ Projector{V,T,Λ} (= Proj; SpectralOperator when T<:Simplex)  forms.jl:374-383; `Proj(x) = x/|x| ⊗ x/|x|` (algebra.md:273-276)
│        └─ Dyadic{V,X,Y} (x ⊗ y)                                   forms.jl:440
TensorBundle{n,ℙ,g,ν,μ,Name} (DirectSum): Signature (S"…"), DiagonalForm (D"…"), MetricTensor (non-diagonal, forms.jl:1603), Int (Euclidean, Submanifold(n))
```

`TensorAlgebra <: Number` matters for the port: every Julia generic `x isa Number` catches multivectors (it bit my oracle script).

### 3.2 What is compile-time vs runtime

* `V` (the vector space/Submanifold value, including metric signs, ∞/∅ flags, dual/dyadic mode, tangent order/diffvars, subspace mask) — **type parameter** (compile-time, "byte-encoded", `README.md:112-117`).
* `G` (grade) — type parameter of `Chain`, `Single`, `Submanifold`.
* `B` (basis blade) — type parameter of `Submanifold`, `Single`, `Couple`, `PseudoCouple`; the blade is a `UInt64` bitmask inside the `Submanifold{V,G,B}` type (`dump(G4.v12)` → `Submanifold{⟨1111⟩, 2, 0x0000000000000003} v₁₂`, algebra.md:296-297).
* `K`/`T` (scalar type) — type parameter; coefficient *values* are the only runtime data. Storage is an immutable `Values` (StaticVectors `SVector` clone).
* Result *types* of products are decided at compile time from the argument types (e.g. `v1+v12` → `Multivector`, `1+v12` → `Couple`, `3v123+2v1` → `PseudoCouple`, `v1*v2` → `Submanifold v₁₂`, `v1|v2` → `Zero`, `-n*c*n` → `CoSpinor`, see §6.10 type table). The port can match this with type-level functions of (kind, grade, parity) — see §8.

### 3.3 Blade bitmask and storage ORDER conventions

* A blade of `V` with indices `i1<…<ig` has bitmask `Σ 2^(i_k-1)` (Leibniz `indexbits`/`bit2int`). `Λ(3).b` is `[v, v₁, v₂, v₃, v₁₂, v₁₃, v₂₃, v₁₂₃]` with masks `[0,1,2,4,3,5,6,7]` (blade_tables.json `basis_order`).
* **Multivector order**: grade-major (grades 0..n), within a grade the blades in **lexicographic order of index tuples** (`Combinatorics.combinations(1:n,g)`, Leibniz `utilities.jl:112-131`, `indexbasis` `:225-245`). Offsets `binomsum(n,g) = Σ_{q<g} C(n,q)` (`binomsum_calc`). E.g. n=4: `v, v₁,v₂,v₃,v₄, v₁₂,v₁₃,v₁₄,v₂₃,v₂₄,v₃₄, v₁₂₃,v₁₂₄,v₁₃₄,v₂₃₄, v₁₂₃₄` (algebra.md:294).
* `Chain{V,G}` stores exactly the grade-G block in that lexicographic order.
* `Spinor`: grades 0,2,4,… concatenated (`spinsum`), `CoSpinor`: grades 1,3,5,… (`antisum`); within grade same lexicographic order. `Spinor{V}(1,2,3,4)` in ⟨111⟩ = `1 + 2v₁₂ + 3v₁₃ + 4v₂₃`; `CoSpinor{V}(1,2,3,4)` = `1v₁ + 2v₂ + 3v₃ + 4v₁₂₃`.
* `Couple{V,B}`: `(scalar, coeff of B)`; `PseudoCouple{V,B}`: `(coeff of B, coeff of I)`.
* Index position meaning: for `S"∞∅+++"` bit0 = v∞, bit1 = v∅, then v₁…; basis order `v, v∞, v∅, v₁, v₂, v₃, v∞∅, v∞₁, …` (transcript). With only ∞: `v, v∞, v₁, …`. For `V⊕V'` (mixed): first n bits are vectors vᵢ, next n bits covectors wⁱ; order `v, v₁…v₄, w¹…w⁴, v₁₂, v₁₃, v₁₄, v₁w¹, …` (design.md:98 transcript). Tangent bundles `tangent(V,μ,ν)`: the ν differential generators ∂ₖ are extra high bits: `Λ(tangent(ℝ^2))` = `v, v₁, v₂, ∂₁, v₁₂, ∂₁v₁, ∂₁v₂, ∂₁v₁₂` (∂ printed first but stored as higher bit).
* Subspace notation: `V(i,j,…)` / `(ℝ^5)(3,5)` gives a `Submanifold` of the ambient with mask of selected indices; display `⟨__+_+⟩` (unused slots `_`), `dump` shows `Submanifold{⟨+++++⟩, 2, 0x0000000000000014}`.
* Grade-2 dyadic operators: `Chain{V,1,Chain{W,1}}` (a `Simplex`) is a column-major matrix: `m[i,j] = m[j][i]` (`multivectors.jl:99`).

### 3.4 Dimension / caching tiers (design.md:111-153)

* `Basis` (fully cached, all blades materialized) for N ≤ 8 (`algebra_limit = 8`, Leibniz `utilities.jl:104`).
* `SparseBasis` for 8 < N ≤ 22 (`sparse_limit = 22`), displayed `DirectSum.SparseBasis{⟨…⟩,2^N}(v, ..., <pseudoscalar>)`.
* `ExtendedBasis` for N > 22 up to 62 (64-bit masks; 62 = digits+lower+upper labels). `Λ(62).v32a87Ng == -1Λ(62).v2378agN` (runtests.jl:10).
* Index caches (bladeindex etc.) up to `cache_limit = 12`. Full `Multivector` allocation only for N ≤ 22.
* `@basis` for N > `algebra_limit` falls back to `generate(V)` (`basis.jl:58-63`).
* Caches are global mutable arrays filled lazily (`combo_cache`, `binomsum_cache`, `indexbasis_cache`, `*index_cache`); Julia's `@pure`/`@generated` then constant-fold them into generated code.

### 3.5 Vector-space constructors and their (distinct!) identities

| expression | display | kind |
|---|---|---|
| `ℝ^3`, `V"+++"`, `S"+++"`, `Manifold(3)` | `⟨+++⟩` | `Signature` (`ℝ^3 == V"+++" == Manifold(3)` is `true`, design.md:53) |
| `ℝ3`, `Submanifold(3)`, `@basis 3`, `basis"3"`, `Λ(3)` | `⟨111⟩` | Int-based Euclidean `Submanifold{3,3,0x7}` |
| `ℝ` | `⟨+⟩` | `Signature{1,0,0x0,0,0,1}` |
| `ℝ0` | `One{0}` | |
| `S"∞∅+++"` / `Submanifold(S"∞∅+++")` | `⟨∞∅+++⟩` / `⟨∞∅111⟩` | the Submanifold of a conformal signature prints Euclidean slots as `1` |
| `D"1,1,1,0"`, `D"0.3,2.4,1"` | `⟨1,1,1,0⟩`, `⟨0.3,2.4,1.0⟩` | `DiagonalForm` |
| `tangent(ℝ^3)`, `tangent(ℝ^3,2,3)` | `T¹⟨+++₁⟩`, `T²⟨+++₁₂₃⟩` | tangent bundle (order μ superscript after T, ν variables as subscripts) |
| `(ℝ^3)'` | `⟨---⟩'` | dual (signature flipped, `'` suffix) |
| `ℝ^3⊕(ℝ^3)'` | `⟨+++---⟩*` | mixed / mother algebra (`*` suffix) |
| `MetricTensor([1 2; 2 3])` | | non-diagonal metric (README.md:124) |

`Λ(V)` / `collect(V)` / `DirectSum.Basis(V)` produce the basis container; `.b` gives the `Values` of all blades; property access `Λ(3).v21` parses arbitrary index order and returns the signed canonical blade (`-1v₁₂`), `Λ(4).v4321` = `v₁₂₃₄` (even permutation).

## 4. Algorithms (doc-level math, sign conventions, verified)

### 4.1 Involutions (`algebra.md:216-236`)
σ_j(ω) = Σ_k (−1)^binom(k, 2^(j−1)) ⟨ω⟩_k. `involute` = σ₁: sign (−1)^k. `reverse` = σ₂: sign (−1)^(k(k−1)/2) (pattern + + − − + + − − by grade). `clifford` = σ₂∘σ₁: sign (−1)^(k(k+1)/2) (pattern + − − + + − − +). `even/odd` = (ω ± ω̄)/2; `real/imag` = (ω ± ω̃)/2 (Z₂-gradings). Verified on `Multivector{⟨111⟩}(1,…,8)`: `~A = 1+2v₁+3v₂+4v₃−5v₁₂−6v₁₃−7v₂₃−8v₁₂₃`, `involute(A) = 1−2v₁−3v₂−4v₃+5v₁₂+6v₁₃+7v₂₃−8v₁₂₃`, `clifford(A) = 1−2v₁−3v₂−4v₃−5v₁₂−6v₁₃−7v₂₃+8v₁₂₃`.

### 4.2 Diagonal geometric product (`algebra.md:518-540`)
For blades X, Y with diagonal metric g:
```
ω_X ⊖ η_Y = (−1)^Π(X,Y) · det(g restricted to X∩Y) · v_{X Δ Y}      (Δ = symmetric difference = XOR)
```
Π(X,Y) = number of transpositions to sort the concatenation X·Y = Σ_{x∈X} #{y∈Y : y < x}. Pseudocode (bitmask a, b; n dims; g::Vector):
```
sign = +1
for each set bit i of a:                # count y<x pairs
    sign *= (-1)^(popcount(b & ((1<<i)-1)))
coef  = sign * prod(g[i] for i in bits(a & b))
result = coef * blade(a xor b)
```
Leibniz symmetric (tangent ∂ₖ) indices use multiset sum instead (`⊕`), with order truncation `∂ₖ^(μ+1)=0` (`algebra.md:175`). `v_i² = g_ii` (`algebra.md:533`). Null basis (∞,∅) is **not** diagonal: v∞²=v∅²=0, v∞⋅v∅=−1, v∞∅²=1 (Issue #19 test). Implementation strategy (verified numerically in blade_tables.json): change basis v∞ = v₊ + v₋, v∅ = (v₋ − v₊)/2 with v₊² = +1, v₋² = −1, multiply diagonally, change back. With only ∞ present it behaves as v₊ (v∞² = +1); only ∅: v∅² = −1 (blade_tables `Sinf+`, `Sorig+`).

### 4.3 Complements (`algebra.md:451-503`)
* Right complement `!` (Euclidean, metric-free), for blade `v_{i1…im}` in n dims:
  `! v_{i1…im} = (−1)^( m(m+1)/2 + Σ_j i_j ) · v_{complement indices (sorted)}`.
  Verified: `complementright(Multivector(1..8)) = 8 + 7v₁ − 6v₂ + 5v₃ + 4v₁₂ − 3v₁₃ + 2v₂₃ + 1v₁₂₃` (n=3); n=4 table in §6.10 (`!v₂ = −v₁₃₄`, `!v₁₂ = v₃₄`, `!v₁₃ = −v₂₄`, …).
* Left complement: `complementleft(ω) = (−1)^(m(n−1)) !ω` (equal to right for odd n; for n=4 `complementleft(v₁) = −v₂₃₄`).
* Hodge `⋆ = complementright ∘ metric` (`algebra.md:482-487`) = `~ω * I` for diagonal metrics. `@basis S"++-"; hodge(Multivector{V}(1..8)) = -8 - 7v₁ + 6v₂ + 5v₃ - 4v₁₂ - 3v₁₃ + 2v₂₃ + 1v₁₂₃` (verified, `algebra.md:498-503`). DiagonalForm: `@basis D"2,3,5"; ⋆v1 = 2v₂₃` while `!v1 = 1v₂₃`. Degenerate `D"1,1,1,0"`: `⋆v₄ = 0` but `!v₄ = −v₁₂₃`.
* Null basis (`algebra.md:1360-1381`): `⋆v∞ = v∞₁…ₙ`, `⋆v∅ = −v∅₁…ₙ`, `!v∞ = 2v∅₁…ₙ`, `!v∅ = −½v∞₁…ₙ` (verified `(1v∞₁₂, 2v∅₁₂, -1v∅₁₂, -0.5v∞₁₂)` in ⟨∞∅++⟩).
* Identities stated (proofs "in research papers"): `I∨ω = ω`; `⋆ω = ω̃I = I⋅ω`; `⋆⋆ω = (−1)^(m(n−m)) ω |I|²`; `(ω∨⋆ω)I = ω∧⋆ω`; `η̃⋅ω̃ = η⋅ω`; `ω⋅ω = ω̃ω`; DeMorgan `!(∨ωk) = ∧(!ωk)`. Good candidates for Lean theorems (§8).

### 4.4 Regressive, contractions, and the four contraction flavours
* `∨(ω...) = ⋆⁻¹(∧(⋆.(ω)...))` (docstring `algebra.md:177-181`), implementation comment `(-1)^(L*(L-n))*⋆(⋆a∧⋆b)` with L = grade a + grade b (`algebra.md:153`). Verified 3D table: `v₁∨v₂₃ = v`, `v₂∨v₁₃ = −v`, `v₁₂∨v₁₃ = v₁`, `v₁₃∨v₁₂ = −v₁`.
* Interior (right) contraction `ω⋅η = ω∨⋆η` (`algebra.md:505-512`, docstring `algebra.jl:204-208`); grade = G−L, zero when L > G (**`v1 > v12 = 𝟎`, `(v1+v2) > v12 = 𝟎`**). For blades: ⟨η̃ω⟩ restricted (`algebra.md:617-621` table: Grassmann right `η > ω = ⟨η̃ ω⟩_{r−s}`).
* Wiring (§2.2): `>`,`⋅`,`|`,`⨽` = right; `<`,`⨼` = `contraction(b,a)`; `>>` = `contraction(~a,b)`; `<<` = `contraction(b,~a)`. Verified: `v12 > v1 = v₂`, `v1 < v12 = v₂`, `v12 >> v1 = −v₂`, `v1 << v12 = v₂`. Full 1/2/3-D tables in §6.4.
* `vee(Chain{V}(1,2,3), hodge(Chain{V}(4,5,6)))` = `-4v` in ⟨++-⟩ (the doc's context) and `32v` in Euclidean ⟨111⟩ (`algebra.md:510`).

### 4.5 Clifford product via ⊖ recursion (`algebra.md:518-527`) and vector identities
`a_i⊖B = a_i∧B + a_i<B̃`, `B⊖a_i = B∧a_i + B̃>a_i`, then distribute. Test-suite identities that must hold exactly for vectors a,b in every signature listed in `generictests.jl:76` (`3, V"+++", S"∞+", S"∅+", V"-+++", S"∞∅+"`): `a⋅b == 0.5(ab+ba)`, `a∧b == 0.5(ab−ba)`, `ab == a⋅b + a∧b`, `ab == 2a⋅b − ba`, `aa == a⋅a`, `a² ≈ scalar(a²)`; plus associativity/distributivity (`≈`) over all basis blades + a random multivector + `B = Σ i·vᵢ`.

### 4.6 Sandwich products — docs vs code (IMPORTANT)
* Docs (`algebra.md:561-563`): `η⊘ω = ω̄⁻¹ η ω`; `η>>>ω = η ω η̄⁻¹`.
* Code (`algebra.jl:313-352`, docstring `:342-349`): `x⊘y = reverse(y)*x*involute(y)` and `y>>>x = y*x*clifford(y)` — **no inverse/normalisation**. Verified: `v1⊘(3v1) = -9v₁` (docs formula would give `-v₁`), `(3v1)>>>v1 = -9v₁`, `inv(3v1)*v2*(3v1) = -1.0v₂` vs `v2⊘(3v1) = 9v₂`. Equal only for unit versors. Port the code semantics.
* Rotation direction (`algebra.md:1172-1183`): `~R*v1*R` with `R = exp(π/4 v12)` gives `+v₂` (Euler/counter-clockwise), `R*v1*~R` gives `−v₂`. So `v1⊘R` (= `~R v1 R` for even R) is CCW, `R>>>v1` is CW. Verified: `R = exp(π/8*v12)`: `R>>>v1 = 0.707107v₁ − 0.707107v₂ + 0.0v₃`, `v1⊘R = 0.707107v₁ + 0.707107v₂ + 0.0v₃`.
* Reflection: `-n*a/n` reflects `a` in hyperplane ⊥ n (`quick-start.md:15-19`), `inv(n)*a*n` / `n\a*n` reflects along n (`algebra-of-space.md:87-93`).

### 4.7 Inverse, division, powers
* `ω⁻¹ = ω̃ (ω̃ω)⁻¹ = ω̃/|ω|²` (`algebra.md:558-559`); `η/ω = η ω⁻¹`, `η\ω = η⁻¹ω` (AbstractTensors `:318-323`).
* When `~ω*ω` is not a scalar the oracle throws `inv(<ω>) is undefined` (e.g. `inv(1+2v₁+3v₁₂)`, `inv(Multivector(1..8))`), so `abs`, `/` on such elements also throw. Vectors, Couples (`inv(1+v12) = 0.5 − 0.5v₁₂`, `inv(2+v1) = 0.4 − 0.2v₁`), rotors are fine.
* `x^2 = x*x`, `x^3`, `x^-1 = inv(x)`, `x^-2` literal fast paths (`algebra.jl:409-416`); `b^t = exp(t*log b)` for number base (verified `2^v12 = 0.7692389013639721 + 0.6389612763136348v₁₂` = cos ln2 + v₁₂ sin ln2).

### 4.8 exp / log / trig (`algebra.md:1163-1263`)
* `exp(θω)` for normalized ω: `cosh θ + ω sinh θ` if ω²=1; `cos θ + ω sin θ` if ω²=−1; `1+θω` if ω²=0. Verified (Couple results print at full precision): Euclidean `exp(0.5v1) = 1.1276259652063807 + 0.5210953054937474v₁`, `exp(0.5v12) = 0.8775825618903728 + 0.479425538604203v₁₂`; `S"-++"`: `exp(0.5v1) = 0.8775825618903728 + 0.479425538604203v₁`, `exp(0.5v12) = 1.1276259652063807 + 0.5210953054937474v₁₂`; null (⟨∞∅1⟩) `exp(0.5v∞₁) = 1.0 + 0.0v∞∅ + 0.5v∞₁ + 0.0v∅₁` (Spinor), `exp(0.5v∞∅) = 1.12763 + 0.521095v∞∅ + 0.0v∞₁ + 0.0v∅₁` (v∞∅² = +1). General case = series `exp(ω) = Σ ωⁿ/n!` (`exp(t) = one(V)+expm1(t)`, AbstractTensors `:327`).
* `log ω = Σ 2/(2n+1) ((ω−1)/(ω+1))^(2n+1)`; `cos ω = cosh(Iω)`, `sin ω = sinh(Iω)/I`, `tan = sin/cos`, `cot`, `sec`, `csc`, `asec = acos∘inv`, `acsc`, `sech`, `csch`, `asech`, `acsch`, `tanh`, `coth`, `asinh = log(ω+√(ω²+1))`, `acosh = log(ω+√(ω²−1))`, `atanh = (log(1+ω)−log(1−ω))/2`, `acoth = (log(ω+1)−log(ω−1))/2`, `asin = −I log(Iω+√(1−ω²))`, `acos = −I log(ω+I√(1−ω²))`, `atan = −I atanh(Iω)`, `acot = −I (log(ω−I)−log(ω+I))/2`. `sqrt ω = exp(log(ω)/2)` for invertible ω (`algebra.md:556`). Verified `log(exp(0.5v12)) = 4.163336342344337e-17 + 0.5v₁₂`, `sqrt(4+v12) = 2.015329455153383 + 0.24809839340235612v₁₂`.

### 4.9 Projective/conformal up/down (`src/Grassmann.jl:164-212`)
* `↑ω` (project): if V has neither ∞ nor ∅: identity. If both (CGA): `↑ω = ω + ½(ω̃⋅ω) v∞ + v∅`. If only one of them (b = v∞ or v∅; Riemann sphere / hyperbolic): `ω2 = ω̃⋅ω; iω2 = 1/(ω2+1); ↑ω = b·(ω2−1)·iω2 + 2·iω2·ω` (stereographic). Two-/three-arg variants `project(ω,b)`, `project(ω,p,m)`.
* `↓ω` (reject): CGA: `((v∞∅∧ω)⋅inv(~v∞∅)) / (−ω⋅v∞)`; single: `(~(ω∧b)⋅b)/(1−b⋅ω)`; on a `Submanifold` it returns the sub-space `V(2:n)` / `ω(3:n)`.
* Verified: `S"∞+++"`: `↑(v1+v2+v3) = 0.5v∞ + 0.5v₁ + 0.5v₂ + 0.5v₃`, `↓` of that = `0.0v∞ + 1.0v₁ + 1.0v₂ + 1.0v₃`; `S"∞∅+++"`: `↑(v1+v2+v3) = 0.0 + 1.5v∞ + 1.0v∅ + 1.0v₁ + 1.0v₂ + 1.0v₃`.

### 4.10 Calculus (`algebra.md:1098-1143`, `src/Grassmann.jl:81-112`)
* `V(∇)` (for `Signature`/`Submanifold` V with diffvars>0) builds `∇ = Σ_k ∂_k v_k` (`Grassmann.jl:88-107`); without tangent it is `Chain{V,1,Int}(ones)`: `(ℝ^3)(∇) = 1v₁ + 1v₂ + 1v₃`.
* `d ω = V(∇)∧ω`, `∂ω = ω⋅V(∇)`, `δ = −∂`; `⋆d` = curl. Boundary of the 3-simplex `∂(v₁₂₃₄) = −∂₄v₁₂₃ + ∂₃v₁₂₄ − ∂₂v₁₃₄ + ∂₁v₂₃₄` (verified, printed with a leading `0 - …`).
* Leibniz-Taylor quotient: `∂ₖ^(μ+1) = 0`; e.g. `@basis tangent(ℝ,2,2); ∂12*∂2 = 𝟎`.

### 4.11 Simplicial helpers (`src/Grassmann.jl:113-289`)
`skeleton(x)` = `absym(x) + skeleton(absym(∂x))` recursively (vertices get multiplicities), `χ` Euler characteristic via `count_gdims`, `betti(t)` = `d[k+1] − r[k] − r[k+1]` with `r = boundary_rank` (**counts, not true ranks: returns negative "Betti numbers" for S², S³**; e.g. `betti(skeleton(∂(v₁₂₃₄)))=[0,−2,0,0,0]`). `chain(t)` builds the cyclic edge chain, `path(t)` the open path. The doc example `χ(Δ(ω))` is broken because `Δ` is now the Laplacian (see §6.4); `χ(skeleton(ω))` reproduces the intended answers `(1,2),(1,0),(1,2),(1,0)`.

### 4.12 Linear systems via exterior products (`algebra.md:1042-1096`, `dyadic-tensors.md:19-77`)
`[p₁…pₙ] ∨ ⋆Σᵢ (p_{1…i−1}∧p₀∧p_{i+1…n}/p_{1…n}) vᵢ = p₀` (Cramer via wedges). Inverse: `[p₁…pₙ]⁻¹ = (Σᵢ ⋆(p_{1…i−1}∧p_{i+1…n})/((−1)^i)^(n−1) p_{1…n}) vᵢ)ᵀ`. Generated solver (dyadic-tensors.md:44-50) for N+1 = 5:
```
(x1, y1) = (t[1], t[end])
(x2, y2) = (x1 ∧ t[2], t[end - 1] ∧ y1)
(x3, y3) = (x2 ∧ t[3], t[end - 2] ∧ y2)
(x4, y4) = (x3 ∧ t[4], t[end - 3] ∧ y3)
Chain{V, 1}(getindex.(SVector(v ∧ y4, (x1 ∧ v) ∧ y3, (x2 ∧ v) ∧ y2, (x3 ∧ v) ∧ y1, x4 ∧ v) ./ (t[1] ∧ y4), 1))
```
i.e. prefix wedges xᵢ = t₁∧…∧tᵢ, suffix wedges yᵢ = t_{n−i+1}∧…∧tₙ, component k = (x_{k−1}∧b∧y_{n−k}) / (t₁∧…∧tₙ) (all pseudoscalars → divide coefficients). Point-in-simplex test `p₀ ∈ [p₁…pₙ] ⇔ ∀i sign(p_{1…n}) = sign(p_{1…i−1}∧p₀∧p_{i+1…n})`. Accuracy claim: `@TensorOperator([1 2; 3 4])\Chain(5,6) = -4.0v₁ + 4.5v₂` exact vs LAPACK `[-3.9999999999999987, 4.499999999999999]` (verified). Performance claim: 3× faster than `SMatrix` for bundles of 5×5 dyadics.

### 4.13 Quaternions (`algebra.md:1006-1040`, `multivectors.jl:1079-1100`)
`quaternion(s,i,j,k) = s + i v₁₂ − j v₁₃ + k v₂₃` (i=v₁₂, j=−v₁₃, k=v₂₃: Hamiltonian, `ijk=−1`); `quatvalues` returns `(s,i,j,k)` in that sign convention. `hyperplanes(ℝ^n)` = `[I*vₖ]` (n−1-vectors): `hyperplanes(ℝ^3) = [v₂₃, −v₁₃, v₁₂]`, and with that assignment `i²=j²=k²=−1` but `i*j*k = +1` (verified; **not** Hamilton). `R>>>x` = `R*x*~R`, `x⊘R` = `~R*x*R`; `Matrix(operator(R))` gives the 3×3 rotation for `x⊘R`.

### 4.14 Fields for plotting (`src/Grassmann.jl:309-348`, `ext/GeometryBasicsExt.jl:30`)
* `points(f, r=-2π:0.0001:2π) = vector.(f.(r))` (`Grassmann.jl:68`; 125,664 samples by default).
* `chainfield(t, V=Manifold(t), W=V) = p -> V(vector(↓(↑((V∪Manifold(t))(p)) ⊘ t)))` — the vector field used by streamplot is the *image point* `p⊘t` (after up-projection, sandwich, down-projection, restriction to V).
* `vectorfield = pointfield` (`Grassmann.jl:311`), methods only exist in GeometryBasicsExt/MeshesExt: `p -> Point(V(vector(↓(↑((V∪Manifold(t))(Chain{W,1,ptype(p)}(p.data))) ⊘ t))))` — W is the subspace the input point coordinates are interpreted in (README wave example uses `W = V(1,2,3)` which *includes v∞*).
* `scalarfield(t,ϕ)`, `chainfield(t,ϕ)` — piecewise-linear FE interpolation: locate simplex containing P (`P ∈ Pi`), barycentric `Pi\P`, dot with nodal values.

## 5. Display / printing rules (exact)

All verified against the oracle; the REPL uses `show(IOContext(io,:limit=>true), MIME"text/plain"(), x)`.

1. **Separators** (`multivectors.jl:46-58`, `showterm`): after the first term each coefficient c is printed as `" - " * show(-c)` if `c isa Real && signbit(c) && !isnan(c)` (so `-0.0` prints ` - 0.0`), else `" + " * show(c)`. With `IOContext(:compact=>true)` the separators become `-`/`+` without spaces (used for nested chains: `(1v₁+0v₂+0v₃)v₁ + …`).
2. **Coefficient/label join** (Leibniz `indices.jl:187-209`, `showvalue`): if the scalar type is "parenthesized" (Complex, Rational, symbolic — `showparens`) print `(c)` then the label; else print `show(c)`, then a `*` if `c` is not an integer and not a finite float (irrationals, `Inf`, `NaN`: `π*v₁`, `Inf*v₁ + NaN*v₂ - 0.0v₃`), or `⊗` if c is itself a TensorAlgebra; then the label. Integers print `2v₁`, `-1v₁₃`, floats `2.5v₁₂`.
3. **Compact coefficients**: `Chain`, `Multivector`, `Spinor`, `CoSpinor` wrap the io in `:compact=>true` for coefficients when the global toggle `Grassmann.compact()` is true (default, `multivectors.jl:33-44`) → Julia compact float printing (≈6 significant digits, shortest): `2.22045e-16`, `0.707107`, `3.14159`, `0.0714286`, `1.0e10`, `1.0e-10`, `0.93224`. `Couple`, `PseudoCouple`, `Single`, and scalars are printed at full precision (`1.4142135623730951 + 1.0v₁₄`, `0.3333333333333333v₁`, `0.7071067811865476 + 0.7071067811865475v₁₂`). The port needs a Julia-compatible float formatter (shortest round-trip `repr` and compact 6-digit mode, exponent as `e-16`, always keeps `.0` for integral floats).
4. **Per type**:
   * `Zero` → `𝟎`; `One{V}`/`Submanifold` → bare label (`v`, `v₁₂`); `Single` → value + label, value always printed (`1v₂₃`, `-1v`, `0v`).
   * `Chain` (`multivectors.jl:109-116`): **all** coefficients including zeros, first term via `showvalue` (sign inline: `-1v₁ - 2v₂ - 3v₃`), rest via showterm. `0v₁₂ + 0v₁₃ + 0v₂₃`.
   * `Multivector` (`:340-356`): scalar coefficient printed bare (`print(io,m.v[1])` on the compact io, so `-0.617273`, not full precision), then **only nonzero** (`!isnull`) terms; if every non-scalar coefficient is zero it prints scalar followed by `v⃖` (e.g. `1v⃖`, `0v⃖`, `0.0v⃖`).
   * `Spinor` (`:589-600`): scalar bare (compact io), then **all** even-grade terms (zeros included): `2 + 0v₁₂ + 0v₁₃ + 0v₂₃`, `-0.617273 + 0.70369v₁₂ + 0.351845v₁₃ + 0.0v₂₃`.
   * `CoSpinor` (`:601-615`): **all** odd terms, first via showvalue: `1v₁ + 2v₂ + 3v₃ + 4v₁₂₃`.
   * `Couple` (`:757-761`): `show(real)` then showterm of the B coefficient (`1 + 1v₁`, `0.5 - 0.5v₁₂`); `PseudoCouple`: showvalue(B part) then showterm(I part): `2v₁ + 3v₁₂₃`.
   * `Phasor`: `show(amplitude) * " ∠ " * angle` (`∠` without spaces under `:compact`): `Phasor(2.0, π/3)` → `2.0 ∠ 1.0471975511965976`, `∠(1.0,v12)` → `1.0 ∠ v₁₂`.
   * Nested `Chain{V,1,Chain}` (dyadic): `(2.0v₁+1.0v₂+0.0v₃+0.0v₄+0.0v₅)v₁ + (…)v₂ + …` (inner compact, parenthesized).
   * `TensorOperator/Endomorphism` text/plain (`forms.jl:669-700`): header `n×n Endomorphism{V, T}:` then a matrix whose first row is the column labels and first column the row labels, with the **pseudoscalar label in the top-left corner** (see cayley tables §6.4 and `operator(B)` §6.5); numbers aligned like Julia matrices (compact floats `0.0204082`).
   * Julia type aliases show as `Quaternion{⟨111⟩, Int64} (alias for Spinor{⟨111⟩, Int64, 4})`, `GaussianInteger{⟨111⟩, v₁₂, Int64} (alias for Couple{⟨111⟩, v₁₂, Int64})`.
5. **Blade labels** (Leibniz `indices.jl:1-60,138-185`): prefix `v` (vectors, subscripts), `w` (covectors, superscripts), `∂` (tangent derivations, subscripts), `ϵ` (dual tangent). Scalar blade prints just the prefix (`v`, `w`). Digits: index 1–9 → `₁…₉` / `¹…⁹`, 10 → `₀` / `⁰`, 11–36 → `a…z` for v (resp. `A…Z` for w), 37–62 → `A…Z` for v (resp. `a…z` for w). Special indices: ∞ → `∞`, ∅ → `∅` (`v∞∅₁₂`). ASCII identifiers created by `@basis` use plain digits/letters (`v12`, `v∞∅`, `w12`), with index 10 written `0` (e.g. `Λ(62).v32a87Ng`). Mixed blades concatenate groups: `v₁w¹`, `∂₁v₁`, `ϵ¹v₁`, `∂₁ϵ¹v₁w¹` (order: ∂/ϵ groups first, then v, then w).
6. **Manifold display**: `⟨` + (∞)(∅) + one char per slot (`+`/`-` for Signature, `1` for Int-based Euclidean Submanifold, `_` for unused slots in subspaces, comma-separated numbers for DiagonalForm) + tangent variable sub/superscripts + `⟩` + (`'` dual | `*` mixed) + optional name subscript; tangent prefix `Tᵘ` (`DirectSum.jl:175-191, 226-242`).
7. **Basis containers**: `DirectSum.Basis{⟨-++⟩,8}(v, v₁, v₂, v₃, v₁₂, v₁₃, v₂₃, v₁₂₃)`, `DirectSum.SparseBasis{⟨+++++++-------⟩*,16384}(v, ..., v₁₂₃₄₅₆₇w¹²³⁴⁵⁶⁷)`, `DirectSum.ExtendedBasis{⟨1…1⟩,4611686018427387904}(v, ..., v₁₂₃₄₅₆₇₈₉₀abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ)`. When the basis is taken of a raw `Signature` (not a Submanifold) the elements print as sub-manifolds: `collect(ℝ'⊕ℝ^3)` → `DirectSum.Basis{⟨-+++⟩,16}(⟨____⟩, ⟨-___⟩, ⟨_+__⟩, …)`.
8. `@basis` returns (and the REPL shows) the tuple `(V, v, v₁, …)`: `(⟨-++⟩, v, v₁, v₂, v₃, v₁₂, v₁₃, v₂₃, v₁₂₃)`.

## 6. Examples with expected outputs (golden corpus)

Conventions. Every code example in README/docs is listed with its verbatim doc text (which may contain the doc's claimed output) and the oracle transcript. **Status**: MATCH = oracle reproduces the doc's printed output byte-for-byte (modulo whitespace); NEW = doc shows no output (`@repl`/`@example` blocks are rendered at doc-build time), oracle output is the golden; DIFF = oracle differs from the doc text (the oracle wins unless noted); BROKEN = errors on the current version; PLOT = visualization (goldens are the numeric samples + PNGs in `notes/grassmann-docs-goldens/plots/`); NOT-RUNNABLE = needs Reduce/GaloisFields/SymPy/random data. Transcripts were produced by `scripts/runner*.jl`; `julia> ` lines are inputs, following lines the `text/plain` display. Trailing `;` suppresses output as in the REPL.

### 6.1 README.md

#### README wave streamplot (header example)
Status: **PLOT** — identical to algebra.md:1298-1302; render `plots/wave.png` (matches `paper/img/wave.png`).
Doc source `README.md:63-67` (verbatim):
````
```Julia
using Grassmann, Makie; @basis S"∞+++"
streamplot(vectorfield(exp((π/4)*(v12+v∞3)),V(2,3,4),V(1,2,3)),-1.5..1.5,-1.5..1.5,-1.5..1.5,gridsize=(10,10))
```
![paper/img/wave.png](paper/img/wave.png)
````

#### README @basis S"-++"
Status: **MATCH**
Doc source `README.md:134-137` (verbatim):
````
```julia
julia> using Grassmann; @basis S"-++" # macro or basis"-++"
(⟨-++⟩, v, v₁, v₂, v₃, v₁₂, v₁₃, v₂₃, v₁₂₃)
```
````
Oracle transcript (Grassmann 0.8.46, label `README.md:135`):
````
julia> @basis S"-++"
(⟨-++⟩, v, v₁, v₂, v₃, v₁₂, v₁₃, v₂₃, v₁₂₃)
````

#### README DirectSum.Basis(V)
Status: **MATCH**
Doc source `README.md:146-149` (verbatim):
````
```julia
julia> DirectSum.Basis(V)
DirectSum.Basis{⟨-++⟩,8}(v, v₁, v₂, v₃, v₁₂, v₁₃, v₂₃, v₁₂₃)
```
````
Oracle transcript (Grassmann 0.8.46, label `README.md:147`):
````
julia> DirectSum.Basis(V)
DirectSum.Basis{⟨-++⟩,8}(v, v₁, v₂, v₃, v₁₂, v₁₃, v₂₃, v₁₂₃)
````

#### README plane vector fields
Status: **PLOT** — renders `plots/plane-1..6.png`. Field sampled on a 7×7 grid over [-1.5,1.5]² in `plots/readme_plot_goldens.json` (key `plane-k`: `versor` display string + `samples[{p,f}]` with `f = value(chainfield(t)(Chain(p)))`). E.g. plane-1 versor `6.123233995736766e-17 + 1.0v₁₂`, f(-1.5,-1.5) = (1.5,1.5); plane-3 versor `0.9238795325112867 + 0.3826834323650898v₁₂`, f(-1.5,-1.5) = (1.1102230246251565e-16, -2.1213203435596424); plane-5 (⟨+-⟩, hyperbolic) versor `1.0193385817707588 + 0.19761362373688154v₁₂`, f(-1.5,-1.5) = (-2.221459005734865, -2.221459005734865); plane-4 versor displays `0.92388v₁ + 0.382683v₂` (a Chain, compact).
Doc source `README.md:272-285` (verbatim):
````
```Julia
using Grassmann, Makie
basis"2" # Euclidean
streamplot(vectorfield(exp(π*v12/2)),-1.5..1.5,-1.5..1.5)
streamplot(vectorfield(exp((π/2)*v12/2)),-1.5..1.5,-1.5..1.5)
streamplot(vectorfield(exp((π/4)*v12/2)),-1.5..1.5,-1.5..1.5)
streamplot(vectorfield(v1*exp((π/4)*v12/2)),-1.5..1.5,-1.5..1.5)
@basis S"+-" # Hyperbolic
streamplot(vectorfield(exp((π/8)*v12/2)),-1.5..1.5,-1.5..1.5)
streamplot(vectorfield(v1*exp((π/4)*v12/2)),-1.5..1.5,-1.5..1.5)
```
![paper/img/plane-1.png](paper/img/plane-1.png) ![paper/img/plane-2.png](paper/img/plane-2.png)
![paper/img/plane-3.png](paper/img/plane-3.png) ![paper/img/plane-4.png](paper/img/plane-4.png)
![paper/img/plane-3.png](paper/img/plane-5.png) ![paper/img/plane-4.png](paper/img/plane-6.png)
````

#### README torus / helix curves
Status: **PLOT** — renders `plots/torus.png`, `plots/helix.png`. `readme_plot_goldens.json` keys `torus`, `helix` hold 41 samples t∈linspace(-2π,2π). Spot values: torus(0) = (1,1,1); torus(2π) = (-1.0481768353996013, 0.4756012331663304, -0.9647624460121627); helix(2π) = (-1.2878427202669922, 0.5843467530972623, 40.47841755597899). Also `f(0.25) = 0.0v∞ + 1.40532v₁ + 0.158342v₂ - 1.0v₃` (⟨∞+++⟩) and `g(0.25) = 0.0 + 1.40532v₁ + 0.158342v₂ + 2.5708v₃ + 5.82587e-10v∞₁₂ - 3.5883e-11v∞₁₃ + 3.1847e-10v∞₂₃` (⟨∞∅+++⟩; note the tiny non-vector residue, why `V(3,4,5)` restriction is needed).
Doc source `README.md:287-296` (verbatim):
````
```Julia
using Grassmann, Makie
@basis S"∞+++"
f(t) = (↓(exp(π*t*((3/7)*v12+v∞3))>>>↑(v1+v2+v3)))
lines(V(2,3,4).(points(f)))
@basis S"∞∅+++"
f(t) = (↓(exp(π*t*((3/7)*v12+v∞3))>>>↑(v1+v2+v3)))
lines(V(3,4,5).(points(f)))
```
![paper/img/torus.png](paper/img/torus.png) ![paper/img/helix.png](paper/img/helix.png)
````

#### README orb streamplot
Status: **PLOT** — `plots/orb.png`; versor `t = exp((π/4)*(v12+v∞3))` displays `0.5 + 0.0v∞₁ + 0.0v∞₂ + 0.5v∞₃ + 0.5v₁₂ + 0.0v₁₃ + 0.0v₂₃ + 0.5v∞₁₂₃`; `chainfield(t,V(2,3,4))` at (0.5,0.5,0.5) = `-0.363636v₁ + 0.363636v₂ - 0.0909091v₃`; 16 samples in json key `orb`. Makie 0.24 needs `gridsize=(10,10,10)` (the doc's 2-tuple is for 2D).
Doc source `README.md:298-302` (verbatim):
````
```Julia
using Grassmann, Makie; @basis S"∞+++"
streamplot(vectorfield(exp((π/4)*(v12+v∞3)),V(2,3,4)),-1.5..1.5,-1.5..1.5,-1.5..1.5,gridsize=(10,10))
```
![paper/img/orb.png](paper/img/orb.png)
````

#### README orbit-2 curve
Status: **PLOT** — `plots/orbit-2.png`, json key `orbit-2`; orbit-2(0) = (1,1,-1).
Doc source `README.md:304-309` (verbatim):
````
```Julia
using Grassmann, Makie; @basis S"∞+++"
f(t) = ↓(exp(t*v∞*(sin(3t)*3v1+cos(2t)*7v2-sin(5t)*4v3)/2)>>>↑(v1+v2-v3))
lines(V(2,3,4).(points(f)))
```
![paper/img/orb.png](paper/img/orbit-2.png)
````

#### README orbit-4 curve
Status: **PLOT** — `plots/orbit-4.png`, json key `orbit-4`; orbit-4(2π) = (1.3635882823689522, 0.5278320450125441, -1.0715495013497132).
Doc source `README.md:311-316` (verbatim):
````
```Julia
using Grassmann, Makie; @basis S"∞+++"
f(t) = ↓(exp(t*(v12+0.07v∞*(sin(3t)*3v1+cos(2t)*7v2-sin(5t)*4v3)/2))>>>↑(v1+v2-v3))
lines(V(2,3,4).(points(f)))
```
![paper/img/orb.png](paper/img/orbit-4.png)
````

### 6.2 docs/src/design.md

#### ℝ^3 == V"+++" == Manifold(3)
Status: **NEW**
Doc source `docs/src/design.md:49-54` (verbatim):
````
```@setup ds
using DirectSum
```
```@repl ds
ℝ^3 == V"+++" == Manifold(3)
```
````
Oracle transcript (Grassmann 0.8.46, label `design.md:53`):
````
julia> ℝ^3 == V"+++" == Manifold(3)
true
````

#### @basis S"-++"
Status: **NEW**
Doc source `docs/src/design.md:67-69` (verbatim):
````
```@repl ds
using Grassmann; @basis S"-++" # macro or basis"-++"
```
````
Oracle transcript (Grassmann 0.8.46, label `design.md:68`):
````
julia> @basis S"-++"
(⟨-++⟩, v, v₁, v₂, v₃, v₁₂, v₁₃, v₂₃, v₁₂₃)
````

#### DirectSum.Basis(V)
Status: **NEW**
Doc source `docs/src/design.md:78-80` (verbatim):
````
```@repl ds
DirectSum.Basis(V)
```
````
Oracle transcript (Grassmann 0.8.46, label `design.md:79`):
````
julia> DirectSum.Basis(V)
DirectSum.Basis{⟨-++⟩,8}(v, v₁, v₂, v₃, v₁₂, v₁₃, v₂₃, v₁₂₃)
````

#### (ℝ^5)(3,5) and dump
Status: **NEW**
Doc source `docs/src/design.md:82-85` (verbatim):
````
```@repl ds
(ℝ^5)(3,5)
dump(ans)
```
````
Oracle transcript (Grassmann 0.8.46, label `design.md:83`):
````
julia> (ℝ^5)(3,5)
⟨__+_+⟩

julia> dump(ans)
Submanifold{⟨+++++⟩, 2, 0x0000000000000014} ⟨__+_+⟩
````

#### direct sum and dual
Status: **NEW**
Doc source `docs/src/design.md:89-93` (verbatim):
````
```@repl ds
V = ℝ'⊕ℝ^3
V'
W = V⊕V'
```
````
Oracle transcript (Grassmann 0.8.46, label `design.md:90`):
````
julia> V = ℝ'⊕ℝ^3
⟨-+++⟩

julia> V'
⟨+---⟩'

julia> W = V⊕V'
⟨-++++---⟩*
````

#### collect bases of V, V', W
Status: **NEW** — note that `V` here is a raw `Signature` so `collect(V)` prints sub-manifold symbols `⟨-___⟩`; the 256-element mixed basis line is the full golden.
Doc source `docs/src/design.md:95-99` (verbatim):
````
```@repl ds
collect(V) # all Submanifold vector basis elements
collect(Submanifold(V')) # all covector basis elements
collect(Submanifold(W)) # all mixed basis elements
```
````
Oracle transcript (Grassmann 0.8.46, label `design.md:96`):
````
julia> collect(V)
DirectSum.Basis{⟨-+++⟩,16}(⟨____⟩, ⟨-___⟩, ⟨_+__⟩, ⟨__+_⟩, ⟨___+⟩, ⟨-+__⟩, ⟨-_+_⟩, ⟨-__+⟩, ⟨_++_⟩, ⟨_+_+⟩, ⟨__++⟩, ⟨-++_⟩, ⟨-+_+⟩, ⟨-_++⟩, ⟨_+++⟩, ⟨-+++⟩)

julia> collect(Submanifold(V'))
DirectSum.Basis{⟨+---⟩',16}(w, w¹, w², w³, w⁴, w¹², w¹³, w¹⁴, w²³, w²⁴, w³⁴, w¹²³, w¹²⁴, w¹³⁴, w²³⁴, w¹²³⁴)

julia> collect(Submanifold(W))
DirectSum.Basis{⟨-++++---⟩*,256}(v, v₁, v₂, v₃, v₄, w¹, w², w³, w⁴, v₁₂, v₁₃, v₁₄, v₁w¹, v₁w², v₁w³, v₁w⁴, v₂₃, v₂₄, v₂w¹, v₂w², v₂w³, v₂w⁴, v₃₄, v₃w¹, v₃w², v₃w³, v₃w⁴, v₄w¹, v₄w², v₄w³, v₄w⁴, w¹², w¹³, w¹⁴, w²³, w²⁴, w³⁴, v₁₂₃, v₁₂₄, v₁₂w¹, v₁₂w², v₁₂w³, v₁₂w⁴, v₁₃₄, v₁₃w¹, v₁₃w², v₁₃w³, v₁₃w⁴, v₁₄w¹, v₁₄w², v₁₄w³, v₁₄w⁴, v₁w¹², v₁w¹³, v₁w¹⁴, v₁w²³, v₁w²⁴, v₁w³⁴, v₂₃₄, v₂₃w¹, v₂₃w², v₂₃w³, v₂₃w⁴, v₂₄w¹, v₂₄w², v₂₄w³, v₂₄w⁴, v₂w¹², v₂w¹³, v₂w¹⁴, v₂w²³, v₂w²⁴, v₂w³⁴, v₃₄w¹, v₃₄w², v₃₄w³, v₃₄w⁴, v₃w¹², v₃w¹³, v₃w¹⁴, v₃w²³, v₃w²⁴, v₃w³⁴, v₄w¹², v₄w¹³, v₄w¹⁴, v₄w²³, v₄w²⁴, v₄w³⁴, w¹²³, w¹²⁴, w¹³⁴, w²³⁴, v₁₂₃₄, v₁₂₃w¹, v₁₂₃w², v₁₂₃w³, v₁₂₃w⁴, v₁₂₄w¹, v₁₂₄w², v₁₂₄w³, v₁₂₄w⁴, v₁₂w¹², v₁₂w¹³, v₁₂w¹⁴, v₁₂w²³, v₁₂w²⁴, v₁₂w³⁴, v₁₃₄w¹, v₁₃₄w², v₁₃₄w³, v₁₃₄w⁴, v₁₃w¹², v₁₃w¹³, v₁₃w¹⁴, v₁₃w²³, v₁₃w²⁴, v₁₃w³⁴, v₁₄w¹², v₁₄w¹³, v₁₄w¹⁴, v₁₄w²³, v₁₄w²⁴, v₁₄w³⁴, v₁w¹²³, v₁w¹²⁴, v₁w¹³⁴, v₁w²³⁴, v₂₃₄w¹, v₂₃₄w², v₂₃₄w³, v₂₃₄w⁴, v₂₃w¹², v₂₃w¹³, v₂₃w¹⁴, v₂₃w²³, v₂₃w²⁴, v₂₃w³⁴, v₂₄w¹², v₂₄w¹³, v₂₄w¹⁴, v₂₄w²³, v₂₄w²⁴, v₂₄w³⁴, v₂w¹²³, v₂w¹²⁴, v₂w¹³⁴, v₂w²³⁴, v₃₄w¹², v₃₄w¹³, v₃₄w¹⁴, v₃₄w²³, v₃₄w²⁴, v₃₄w³⁴, v₃w¹²³, v₃w¹²⁴, v₃w¹³⁴, v₃w²³⁴, v₄w¹²³, v₄w¹²⁴, v₄w¹³⁴, v₄w²³⁴, w¹²³⁴, v₁₂₃₄w¹, v₁₂₃₄w², v₁₂₃₄w³, v₁₂₃₄w⁴, v₁₂₃w¹², v₁₂₃w¹³, v₁₂₃w¹⁴, v₁₂₃w²³, v₁₂₃w²⁴, v₁₂₃w³⁴, v₁₂₄w¹², v₁₂₄w¹³, v₁₂₄w¹⁴, v₁₂₄w²³, v₁₂₄w²⁴, v₁₂₄w³⁴, v₁₂w¹²³, v₁₂w¹²⁴, v₁₂w¹³⁴, v₁₂w²³⁴, v₁₃₄w¹², v₁₃₄w¹³, v₁₃₄w¹⁴, v₁₃₄w²³, v₁₃₄w²⁴, v₁₃₄w³⁴, v₁₃w¹²³, v₁₃w¹²⁴, v₁₃w¹³⁴, v₁₃w²³⁴, v₁₄w¹²³, v₁₄w¹²⁴, v₁₄w¹³⁴, v₁₄w²³⁴, v₁w¹²³⁴, v₂₃₄w¹², v₂₃₄w¹³, v₂₃₄w¹⁴, v₂₃₄w²³, v₂₃₄w²⁴, v₂₃₄w³⁴, v₂₃w¹²³, v₂₃w¹²⁴, v₂₃w¹³⁴, v₂₃w²³⁴, v₂₄w¹²³, v₂₄w¹²⁴, v₂₄w¹³⁴, v₂₄w²³⁴, v₂w¹²³⁴, v₃₄w¹²³, v₃₄w¹²⁴, v₃₄w¹³⁴, v₃₄w²³⁴, v₃w¹²³⁴, v₄w¹²³⁴, v₁₂₃₄w¹², v₁₂₃₄w¹³, v₁₂₃₄w¹⁴, v₁₂₃₄w²³, v₁₂₃₄w²⁴, v₁₂₃₄w³⁴, v₁₂₃w¹²³, v₁₂₃w¹²⁴, v₁₂₃w¹³⁴, v₁₂₃w²³⁴, v₁₂₄w¹²³, v₁₂₄w¹²⁴, v₁₂₄w¹³⁴, v₁₂₄w²³⁴, v₁₂w¹²³⁴, v₁₃₄w¹²³, v₁₃₄w¹²⁴, v₁₃₄w¹³⁴, v₁₃₄w²³⁴, v₁₃w¹²³⁴, v₁₄w¹²³⁴, v₂₃₄w¹²³, v₂₃₄w¹²⁴, v₂₃₄w¹³⁴, v₂₃₄w²³⁴, v₂₃w¹²³⁴, v₂₄w¹²³⁴, v₃₄w¹²³⁴, v₁₂₃₄w¹²³, v₁₂₃₄w¹²⁴, v₁₂₃₄w¹³⁴, v₁₂₃₄w²³⁴, v₁₂₃w¹²³⁴, v₁₂₄w¹²³⁴, v₁₃₄w¹²³⁴, v₂₃₄w¹²³⁴, v₁₂₃₄w¹²³⁴)
````

#### set operations on spaces
Status: **NEW**
Doc source `docs/src/design.md:102-106` (verbatim):
````
```@repl ds
ℝ⊕ℝ' ⊇ Manifold(1)
ℝ ∩ ℝ' == Manifold(0)
ℝ ∪ ℝ' == ℝ⊕ℝ'
```
````
Oracle transcript (Grassmann 0.8.46, label `design.md:103`):
````
julia> ℝ⊕ℝ' ⊇ Manifold(1)
true

julia> ℝ ∩ ℝ' == Manifold(0)
true

julia> ℝ ∪ ℝ' == ℝ⊕ℝ'
true
````

#### Λ(7) ⊕ Λ(7)'
Status: **MATCH**
Doc source `docs/src/design.md:114-117` (verbatim):
````
```julia
julia> Λ(7) ⊕ Λ(7)'
DirectSum.SparseBasis{⟨+++++++-------⟩*,16384}(v, ..., v₁₂₃₄₅₆₇w¹²³⁴⁵⁶⁷)
```
````
Oracle transcript (Grassmann 0.8.46, label `design.md:115`):
````
julia> Λ(7) ⊕ Λ(7)'
DirectSum.SparseBasis{⟨+++++++-------⟩*,16384}(v, ..., v₁₂₃₄₅₆₇w¹²³⁴⁵⁶⁷)
````

#### Λ(62)
Status: **NEW** — Int-based Euclidean manifold of dimension 62 prints as 62 `1` characters.
Doc source `docs/src/design.md:124-132` (verbatim):
````
```@repl ds
Λ(62)
Λ(62).v32a87Ng
```
The 62 indices require full alpha-numeric labeling with lower-case and capital letters. This now allows you to reach up to ``4,611,686,018,427,387,904`` dimensions with Julia `using Grassmann`. Then the volume element is
```@example
using DirectSum # hide
DirectSum.printindices(stdout,DirectSum.indices(UInt(2^62-1))) # hide
```
````
Oracle transcript (Grassmann 0.8.46, label `design.md:125`):
````
julia> Λ(62)
DirectSum.ExtendedBasis{⟨11111111111111111111111111111111111111111111111111111111111111⟩,4611686018427387904}(v, ..., v₁₂₃₄₅₆₇₈₉₀abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ)

julia> Λ(62).v32a87Ng
-1v₂₃₇₈agN
````
Oracle transcript (Grassmann 0.8.46, label `design.md:131`):
````
julia> DirectSum.printindices(stdout,DirectSum.indices(UInt(2^62-1)))
v₁₂₃₄₅₆₇₈₉₀abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ
````

#### Λ(22)
Status: **DIFF** — doc prints `⟨++++++++++++++++++++++⟩`, oracle prints `⟨1111111111111111111111⟩` (Int-based manifold display changed); count/labels match.
Doc source `docs/src/design.md:136-139` (verbatim):
````
```julia
julia> Λ(22)
DirectSum.SparseBasis{⟨++++++++++++++++++++++⟩,4194304}(v, ..., v₁₂₃₄₅₆₇₈₉₀abcdefghijkl)
```
````
Oracle transcript (Grassmann 0.8.46, label `extra: design.md:137 (Λ(22) heavy)`):
````
julia> Λ(22)
DirectSum.SparseBasis{⟨1111111111111111111111⟩,4194304}(v, ..., v₁₂₃₄₅₆₇₈₉₀abcdefghijkl)
````

#### Λ(ℝ^22 ⊕ ℝ^22')
Status: **NEW**
Doc source `docs/src/design.md:144-147` (verbatim):
````
```@repl ds
V = ℝ^22
Λ(V+V')
```
````
Oracle transcript (Grassmann 0.8.46, label `design.md:145`):
````
julia> V = ℝ^22
⟨++++++++++++++++++++++⟩

julia> Λ(V+V')
DirectSum.ExtendedBasis{⟨++++++++++++++++++++++----------------------⟩*,17592186044416}(v, ..., v₁₂₃₄₅₆₇₈₉₀abcdefghijklw¹²³⁴⁵⁶⁷⁸⁹⁰ABCDEFGHIJKL)
````

#### interop pseudo-code
Status: **DIFF** — oracle probe: `∧` across ℝ^2 and ℝ^3 works via union, `*` throws `unsupported transformation`.
Doc source `docs/src/design.md:171-182` (verbatim):
````
```julia
function op(::TensorAlgebra{V},::TensorAlgebra{V}) where V
    # well defined operations if V is shared
end # but what if V ≠ W in the input types?

function op(a::TensorAlgebra{V},b::TensorAlgebra{W}) where {V,W}
    VW = V ∪ W        # VectorSpace type union
    op(VW(a),VW(b))   # makes call well-defined
end # this option is automatic with interop(a,b)

# alternatively for evaluation of forms, VW(a)(VW(b))
```
````
Oracle transcript (Grassmann 0.8.46, label `design.md:172 interop`):
````
julia> a = Λ(ℝ^2).v1 + Λ(ℝ^2).v2
1v₁ + 1v₂

julia> b = Λ(ℝ^3).v3
v₃

julia> a ∧ b
0v₁₂ - 1v₁₃ - 1v₂₃

julia> a * b
ERROR: unsupported transformation
````

### 6.3 docs/src/algebra.md (non-table examples)

#### StaticVectors Values addition
Status: **MATCH**
Doc source `docs/src/algebra.md:25-33` (verbatim):
````
```julia
julia> using StaticVectors

julia> Values(1,2,3) + Values(2,3,4)
3-element Values{3, Int64} with indices SOneTo(3):
 3
 5
 7
```
````
Oracle transcript (Grassmann 0.8.46, label `algebra.md:28`):
````
julia> Values(1,2,3) + Values(2,3,4)
3-element Values{3, Int64} with indices SOneTo(3):
 3
 5
 7
````

#### Λ of bundles
Status: **NEW**
Doc source `docs/src/algebra.md:147-156` (verbatim):
````
```@setup ga
using Grassmann
```
```@repl ga
Λ(ℝ^3)

Λ(tangent(ℝ^2))

Λ(tangent((ℝ^0)',3,3))
```
````
Oracle transcript (Grassmann 0.8.46, label `algebra.md:151`):
````
julia> Λ(ℝ^3)
DirectSum.Basis{⟨+++⟩,8}(v, v₁, v₂, v₃, v₁₂, v₁₃, v₂₃, v₁₂₃)

julia> Λ(tangent(ℝ^2))
DirectSum.Basis{T¹⟨++₁⟩,8}(v, v₁, v₂, ∂₁, v₁₂, ∂₁v₁, ∂₁v₂, ∂₁v₁₂)

julia> Λ(tangent((ℝ^0)',3,3))
DirectSum.Basis{T³⟨¹²³⟩',8}(w, ϵ₁, ϵ₂, ϵ₃, ϵ₁₂, ϵ₁₃, ϵ₂₃, ϵ₁₂₃)
````

#### indices
Status: **NEW**
Doc source `docs/src/algebra.md:169-171` (verbatim):
````
```@repl ga
indices(Λ(3).v12)
```
````
Oracle transcript (Grassmann 0.8.46, label `algebra.md:170`):
````
julia> indices(Λ(3).v12)
2-element Vector{Int64}:
 1
 2
````

#### Submanifold(4) / collect / dump / Chain type
Status: **MATCH**
Doc source `docs/src/algebra.md:280-306` (verbatim):
````

In `Grassmann`, a standard vector space is initialized with `Submanifold(N)`.
```julia
julia> V = Submanifold(4)
⟨1111⟩
```
The type parameters of `Submanifold{V, G, B}` are encoded with integers.
```julia
julia> dump(V)
Submanifold{4, 4, 0x000000000000000f} ⟨1111⟩
```
Calling `collect(V)` or `Λ(V)` produces a `DirectSum.Basis`.
```julia
julia> G4 = collect(V)
DirectSum.Basis{⟨1111⟩,16}(v, v₁, v₂, v₃, v₄, v₁₂, v₁₃, v₁₄, v₂₃, v₂₄, v₃₄, v₁₂₃, v₁₂₄, v₁₃₄, v₂₃₄, v₁₂₃₄)

julia> dump(G4.v12)
Submanifold{⟨1111⟩, 2, 0x0000000000000003} v₁₂
```
The object `G4::DirectSum.Basis` can be used to access algebra elements.
```julia
julia> G4.v12 + 2G4.v14
1v₁₂ + 0v₁₃ + 2v₁₄ + 0v₂₃ + 0v₂₄ + 0v₃₄

julia> typeof(G4.v12 + G4.v14)
Chain{⟨1111⟩, 2, Int64, 6}
```
````
Oracle transcript (Grassmann 0.8.46, label `algebra.md:283`):
````
julia> V = Submanifold(4)
⟨1111⟩

julia> dump(V)
Submanifold{4, 4, 0x000000000000000f} ⟨1111⟩

julia> G4 = collect(V)
DirectSum.Basis{⟨1111⟩,16}(v, v₁, v₂, v₃, v₄, v₁₂, v₁₃, v₁₄, v₂₃, v₂₄, v₃₄, v₁₂₃, v₁₂₄, v₁₃₄, v₂₃₄, v₁₂₃₄)

julia> dump(G4.v12)
Submanifold{⟨1111⟩, 2, 0x0000000000000003} v₁₂

julia> G4.v12 + 2G4.v14
1v₁₂ + 0v₁₃ + 2v₁₄ + 0v₂₃ + 0v₂₄ + 0v₃₄

julia> typeof(G4.v12 + G4.v14)
Chain{⟨1111⟩, 2, Int64, 6}
````

#### subalgebra V(1,4) and Couple
Status: **MATCH**
Doc source `docs/src/algebra.md:307-317` (verbatim):
````
Subalgebra generated by `V(1,4)` can be assigned to `G42`, for example.
```julia
julia> G42 = collect(V(1,4))
DirectSum.Basis{⟨1__1⟩,4}(v, v₁, v₄, v₁₄)

julia> sqrt(2) + G42.v14
1.4142135623730951 + 1.0v₁₄

julia> typeof(ans)
Couple{⟨1__1⟩, v₁₄, Float64}
```
````
Oracle transcript (Grassmann 0.8.46, label `algebra.md:309`):
````
julia> G42 = collect(V(1,4))
DirectSum.Basis{⟨1__1⟩,4}(v, v₁, v₄, v₁₄)

julia> sqrt(2) + G42.v14
1.4142135623730951 + 1.0v₁₄

julia> typeof(ans)
Couple{⟨1__1⟩, v₁₄, Float64}
````

#### @basis 3 and Quaternion alias
Status: **MATCH** — `dump(v)` → `One{⟨111⟩} v`.
Doc source `docs/src/algebra.md:318-331` (verbatim):
````
Otherwise, the `@basis` macro or `basis"..."` can assign local symbols.
```julia
julia> @basis 3
(⟨111⟩, v, v₁, v₂, v₃, v₁₂, v₁₃, v₂₃, v₁₂₃)
```
The `One{V}` type is an alias of `Submanifold{V,0}` types, e.g. try `dump(v)`.
```julia
julia> 1 + v12 - v13
1 + 1v₁₂ - 1v₁₃ + 0v₂₃

julia> typeof(ans)
Quaternion{⟨111⟩, Int64} (alias for Spinor{⟨111⟩, Int64, 4})
```
Hence, algebra elements can be created from the generating basis.
````
Oracle transcript (Grassmann 0.8.46, label `algebra.md:320`):
````
julia> @basis 3
(⟨111⟩, v, v₁, v₂, v₃, v₁₂, v₁₃, v₂₃, v₁₂₃)

julia> dump(v)
One{⟨111⟩} v

julia> 1 + v12 - v13
1 + 1v₁₂ - 1v₁₃ + 0v₂₃

julia> typeof(ans)
Quaternion{⟨111⟩, Int64} (alias for Spinor{⟨111⟩, Int64, 4})
````

#### Chain / Values / wedge / Spinor constructors
Status: **MATCH**
Doc source `docs/src/algebra.md:333-355` (verbatim):
````
The direct way to construct elements is with `Values`,
```julia
julia> Chain{V,1}(Values(4,5,6)) # Chain{V,1}(4,5,6)
4v₁ + 5v₂ + 6v₃
```
while the `value` function returns the `Values` representation
```julia
julia> value(Chain(4,5,6))
3-element Values{3, Int64} with indices SOneTo(3):
 4
 5
 6
```
where `Chain(::Vararg{<:Number,N})` auto-selects `V = Submanifold(N)`.
```julia
julia> wedge(Chain(1,2,3),Chain(4,5,6))
-3v₁₂ - 6v₁₃ - 3v₂₃
```
Constructors for `Spinor`, `CoSpinor`, `Multivector` are similar.
```julia
julia> Spinor{V}(1,2,3,4)
1 + 2v₁₂ + 3v₁₃ + 4v₂₃
```
````
Oracle transcript (Grassmann 0.8.46, label `algebra.md:335`):
````
julia> Chain{V,1}(Values(4,5,6))
4v₁ + 5v₂ + 6v₃

julia> Chain{V,1}(4,5,6)
4v₁ + 5v₂ + 6v₃

julia> value(Chain(4,5,6))
3-element Values{3, Int64} with indices SOneTo(3):
 4
 5
 6

julia> wedge(Chain(1,2,3),Chain(4,5,6))
-3v₁₂ - 6v₁₃ - 3v₂₃

julia> Spinor{V}(1,2,3,4)
1 + 2v₁₂ + 3v₁₃ + 4v₂₃
````

#### complexify / vectorize
Status: **MATCH**
Doc source `docs/src/algebra.md:434-449` (verbatim):
````
`complexify` converts two dimensional values into its complex number form.
```julia
julia> complexify(1+im)
1 + 1im

julia> complexify(Chain(1,2))
1 + 2v₁₂
```
`vectorize` converts two dimensional complex numbers into vector form.
```julia
julia> vectorize(1+2im)
1v₁ + 2v₂

julia> vectorize(Couple(1,2))
1v₁ + 2v₂
```
````
Oracle transcript (Grassmann 0.8.46, label `algebra.md:436`):
````
julia> complexify(1+im)
1 + 1im

julia> complexify(Chain(1,2))
1 + 2v₁₂

julia> vectorize(1+2im)
1v₁ + 2v₂

julia> vectorize(Couple(1,2))
1v₁ + 2v₂
````

#### complementright / complementleft / complementrighthodge
Status: **MATCH** — oracle also shows `complementlefthodge` (same values for n=3).
Doc source `docs/src/algebra.md:472-494` (verbatim):
````
- `complementright` Euclidean metric Grassmann right complement,
- `complementleft` Euclidean metric Grassmann left complement.
```julia
julia> complementright(Multivector(1,2,3,4,5,6,7,8))
8 + 7v₁ - 6v₂ + 5v₃ + 4v₁₂ - 3v₁₃ + 2v₂₃ + 1v₁₂₃

julia> complementleft(Multivector(1,2,3,4,5,6,7,8))
8 + 7v₁ - 6v₂ + 5v₃ + 4v₁₂ - 3v₁₃ + 2v₂₃ + 1v₁₂₃
```

**Definition** (Hodge ``\star`` complement).
Expressed as unary operator ``\star``, define the composition of ``\star = `` `complementright` ``\circ`` `metric` as linear operator.
```math
\star ={!\Lambda g} : \Lambda V \rightarrow \Lambda V
```
This linear operator is also called `complementrighthodge` or only `hodge`.

- `complementrighthodge` Grassmann-Hodge right complement ``\widetilde\omega I``
- `complementlefthodge` Grassmann-Hodge left complement ``I\widetilde\omega``
```julia
julia> complementrighthodge(Multivector(1,2,3,4,5,6,7,8))
8 + 7v₁ - 6v₂ + 5v₃ + 4v₁₂ - 3v₁₃ + 2v₂₃ + 1v₁₂₃
```
````
Oracle transcript (Grassmann 0.8.46, label `algebra.md:475`):
````
julia> complementright(Multivector(1,2,3,4,5,6,7,8))
8 + 7v₁ - 6v₂ + 5v₃ + 4v₁₂ - 3v₁₃ + 2v₂₃ + 1v₁₂₃

julia> complementleft(Multivector(1,2,3,4,5,6,7,8))
8 + 7v₁ - 6v₂ + 5v₃ + 4v₁₂ - 3v₁₃ + 2v₂₃ + 1v₁₂₃

julia> complementrighthodge(Multivector(1,2,3,4,5,6,7,8))
8 + 7v₁ - 6v₂ + 5v₃ + 4v₁₂ - 3v₁₃ + 2v₂₃ + 1v₁₂₃

julia> complementlefthodge(Multivector(1,2,3,4,5,6,7,8))
8 + 7v₁ - 6v₂ + 5v₃ + 4v₁₂ - 3v₁₃ + 2v₂₃ + 1v₁₂₃
````

#### hodge in S"++-"
Status: **MATCH**
Doc source `docs/src/algebra.md:496-503` (verbatim):
````
**Remark**. Original Grassmann complement is equivalent to the Hodge complement with a Euclidean metric tensor, making `metric` an `identity`.
```julia
julia> @basis S"++-"
(⟨++-⟩, v, v₁, v₂, v₃, v₁₂, v₁₃, v₂₃, v₁₂₃)

julia> hodge(Multivector{V}(1,2,3,4,5,6,7,8))
-8 - 7v₁ + 6v₂ + 5v₃ - 4v₁₂ - 3v₁₃ + 2v₂₃ + 1v₁₂₃
```
````
Oracle transcript (Grassmann 0.8.46, label `algebra.md:498`):
````
julia> @basis S"++-"
(⟨++-⟩, v, v₁, v₂, v₃, v₁₂, v₁₃, v₂₃, v₁₂₃)

julia> hodge(Multivector{V}(1,2,3,4,5,6,7,8))
-8 - 7v₁ + 6v₂ + 5v₃ - 4v₁₂ - 3v₁₃ + 2v₂₃ + 1v₁₂₃
````

#### vee with hodge (contraction)
Status: **MATCH** — the doc output `-4v` holds in the preceding `S"++-"` context; in Euclidean 3D the value is `32v` (= 1·4+2·5+3·6).
Doc source `docs/src/algebra.md:505-512` (verbatim):
````
**Definition**.
The interior contraction ``\eta\cdot\omega = \eta\vee\star\omega`` is defined in terms of the regressive product and also the Hodge complement.
By default the right contraction ``>`` is used, but there is also a left contraction ``<`` with swapped arguments ``\eta<\omega = \omega\vee\star\eta``,
and also ``\eta >> \omega = \widetilde\eta >\omega`` with ``\eta << \omega = \eta <\widetilde{\omega} ``.
```julia
julia> vee(Chain{V}(1,2,3),hodge(Chain{V}(4,5,6)))
-4v
```
````
Oracle transcript (Grassmann 0.8.46, label `algebra.md:510`):
````
julia> vee(Chain{V}(1,2,3),hodge(Chain{V}(4,5,6)))
-4v
````
Oracle transcript (Grassmann 0.8.46, label `algebra.md:510-euclid`):
````
julia> @basis 3
(⟨111⟩, v, v₁, v₂, v₃, v₁₂, v₁₃, v₂₃, v₁₂₃)

julia> vee(Chain{V}(1,2,3),hodge(Chain{V}(4,5,6)))
32v
````

#### geometric product of Chains
Status: **MATCH**
Doc source `docs/src/algebra.md:534-537` (verbatim):
````
```julia
julia> Chain(1,2,3)*Chain(4,5,6)
32 - 3v₁₂ - 6v₁₃ - 3v₂₃
```
````
Oracle transcript (Grassmann 0.8.46, label `algebra.md:535`):
````
julia> Chain(1,2,3)*Chain(4,5,6)
32 - 3v₁₂ - 6v₁₃ - 3v₂₃
````

#### Grassmann algebra laws
Status: **MATCH**
Doc source `docs/src/algebra.md:931-949` (verbatim):
````
Side note, demonstration of \verb`using Grassmann` algebra laws:

```julia
julia> basis"3"
(⟨111⟩, v, v₁, v₂, v₃, v₁₂, v₁₃, v₂₃, v₁₂₃)

julia> wedge(!v12,!v23)
-1v₁₃
```

Side note, demonstration of Grassmann algebra laws:

```julia
julia> !vee(v12,v23)
-1v₁₃

julia> wedge(v12,!v12)
1v₁₂₃
```
````
Oracle transcript (Grassmann 0.8.46, label `algebra.md:934`):
````
julia> basis"3"
(⟨111⟩, v, v₁, v₂, v₃, v₁₂, v₁₃, v₂₃, v₁₂₃)

julia> wedge(!v12,!v23)
-1v₁₃

julia> !vee(v12,v23)
-1v₁₃

julia> wedge(v12,!v12)
1v₁₂₃
````

#### quaternion generators via hyperplanes
Status: **NEW** — note `i*j*k = +1v` (not Hamilton).
Doc source `docs/src/algebra.md:1029-1035` (verbatim):
````
It is possible to assign the **quaternion** generators ``i,j,k`` with
```@repl ga
i,j,k = hyperplanes(ℝ^3)
i^2, j^2, k^2, i*j*k
-(j+k) * (j+k)
-(j+k) * i
```
````
Oracle transcript (Grassmann 0.8.46, label `algebra.md:1031`):
````
julia> i,j,k = hyperplanes(ℝ^3)
3-element Vector{Single{⟨+++⟩, 2, B, Int64} where B}:
  1v₂₃
 -1v₁₃
  1v₁₂

julia> i^2, j^2, k^2, i*j*k
(-1v, -1v, -1v, 1v)

julia> -(j+k) * (j+k)
2 + 0v₁₂ + 0v₁₃ + 0v₂₃

julia> -(j+k) * i
0 - 1v₁₂ - 1v₁₃ + 0v₂₃
````

#### basis"--" quaternions
Status: **NEW**
Doc source `docs/src/algebra.md:1036-1040` (verbatim):
````
Alternatively, another representation of the quaternions is
```@repl ga
basis"--"
v1^2, v2^2, v12^2, v1*v2*v12
```
````
Oracle transcript (Grassmann 0.8.46, label `algebra.md:1038`):
````
julia> basis"--"
(⟨--⟩, v, v₁, v₂, v₁₂)

julia> v1^2, v2^2, v12^2, v1*v2*v12
(-1v, -1v, -1v, -1v)
````

#### exact 2×2 solve
Status: **MATCH** — doc LaTeX shows `-4, 4.5`; oracle `-4.0v₁ + 4.5v₂`.
Doc source `docs/src/algebra.md:1050-1065` (verbatim):
````
**Remark**.
`Grassmann` methods for low dimensional linear systems are more numerically stable than Julia `Base.LinearAlegbra` methods and fast.
```julia
[1 2; 3 4]\[5,6] # inexact
@TensorOperator([1 2; 3 4])\Chain(5,6) # exact
```
```math
	\begin{bmatrix}
		 -3.9999999999999987 \\
		  4.499999999999999
	\end{bmatrix},
	\qquad
	\begin{bmatrix}
		-4 \\ 4.5
	\end{bmatrix}
```
````
Oracle transcript (Grassmann 0.8.46, label `algebra.md:1053`):
````
julia> [1 2; 3 4]\[5,6]
2-element Vector{Float64}:
 -3.9999999999999987
  4.499999999999999

julia> @TensorOperator([1 2; 3 4])\Chain(5,6)
-4.0v₁ + 4.5v₂
````

#### operator / inv
Status: **MATCH** — numbers match doc matrices; the oracle text form (with the `v₁₂₃` corner label) is the display golden.
Doc source `docs/src/algebra.md:1076-1095` (verbatim):
````
Consider `operator` composed with `inv`
```julia
B = v12+2v13-3v23 # using Grassmann; basis"3"
operator(B) # convert B to endomorphisim representation
inv(operator(B))
operator(inv(B))
```
```math
	\begin{bmatrix}
		4 & 12 &  -6 \\
		12 & -6 &  -4 \\
		-6 & -4 & -12
	\end{bmatrix},
	\qquad
	\begin{bmatrix}
		0.0204082 &  0.0612245 & -0.0306122 \\
		0.0612245 & -0.0306122 & -0.0204082 \\
		-0.0306122 & -0.0204082 & -0.0612245
	\end{bmatrix}
```
````
Oracle transcript (Grassmann 0.8.46, label `algebra.md:1078`):
````
julia> basis"3"
(⟨111⟩, v, v₁, v₂, v₃, v₁₂, v₁₃, v₂₃, v₁₂₃)

julia> B = v12+2v13-3v23
1v₁₂ + 2v₁₃ - 3v₂₃

julia> operator(B)
3×3 Endomorphism{⟨111⟩, Simplex{⟨111⟩, Chain{⟨111⟩, 1, Int64, 3}, 3}}:
 v₁₂₃  v₁  v₂   v₃
   v₁   4  12   -6
   v₂  12  -6   -4
   v₃  -6  -4  -12

julia> inv(operator(B))
3×3 Endomorphism{⟨111⟩, Simplex{⟨111⟩, Chain{⟨111⟩, 1, Float64, 3}, 3}}:
 v₁₂₃  v₁          v₂          v₃
   v₁   0.0204082   0.0612245  -0.0306122
   v₂   0.0612245  -0.0306122  -0.0204082
   v₃  -0.0306122  -0.0204082  -0.0612245

julia> operator(inv(B))
3×3 Endomorphism{⟨111⟩, Simplex{⟨111⟩, Chain{⟨111⟩, 1, Float64, 3}, 3}}:
 v₁₂₃  v₁          v₂          v₃
   v₁   0.0204082   0.0612245  -0.0306122
   v₂   0.0612245  -0.0306122  -0.0204082
   v₃  -0.0306122  -0.0204082  -0.0612245

julia> Matrix(operator(B))
3×3 Matrix{Int64}:
  4  12   -6
 12  -6   -4
 -6  -4  -12
````

#### ∇ as vector field
Status: **NEW**
Doc source `docs/src/algebra.md:1100-1106` (verbatim):
````
Let ``\nabla = \sum_k\partial_kv_k`` be a vector field and ``\epsilon = \sum_k\epsilon_k(x)w_k \in \Omega^1V`` be unit sums of the mixed-symmetry basis.
Elements of ``\Omega^pV`` are known as *differential* ``p``-*forms* and both ``\nabla`` and ``\epsilon`` are *tensor fields* dependent on ``x\in W``.
Another notation for a differential form is ``dx_k = \epsilon_k(x)w_k``, such that ``\epsilon_k = dx_k/w_k`` and ``\partial_k\omega(x) = \omega'(x)``.
```@repl ga
tangent(ℝ^3)(∇)
(ℝ^3)(∇)
```
````
Oracle transcript (Grassmann 0.8.46, label `algebra.md:1104`):
````
julia> tangent(ℝ^3)(∇)
0v₁₂ + 0v₁₃ + 1∂₁v₁ + 0v₂₃ + 1∂₁v₂ + 1∂₁v₃

julia> (ℝ^3)(∇)
1v₁ + 1v₂ + 1v₃
````

#### curl ⋆d
Status: **DIFF** — doc formula `(∂₂ -∂₃)dx₁ + (∂₃ -∂₁)dx₂ + (∂₁ -∂₂)dx₃` has the **opposite overall sign** of the oracle (`-1∂₂v₁ + 1∂₃v₁ …`); port must follow the oracle convention (tangent ∂ blades are stored as higher bits, so `∂ₖvⱼ` reordering carries a sign) or document the decision.
Doc source `docs/src/algebra.md:1113-1117` (verbatim):
````
Vorticity curl of vector-field:
``\star d(dx_1+dx_2+dx_3) = (∂_2 -∂_3)dx_1 + (∂_3 -∂_1)dx_2 + (∂_1 -∂_2)dx_3``.
```@repl ga
@basis tangent(ℝ^3,2,3); ⋆d(v1+v2+v3)
```
````
Oracle transcript (Grassmann 0.8.46, label `algebra.md:1116`):
````
julia> @basis tangent(ℝ^3,2,3); ⋆d(v1+v2+v3)
0 - 1∂₂v₁ + 1∂₃v₁ + 1∂₁v₂ - 1∂₃v₂ - 1∂₁v₃ + 1∂₂v₃
````

#### boundary of 3-simplex
Status: **MATCH** — oracle prints a leading `0 - …` (scalar slot of the container type).
Doc source `docs/src/algebra.md:1118-1121` (verbatim):
````
Boundary of 3-simplex, faces of simplex (oriented): ``\partial(v_{1234}) = -\partial_4v_{123}+\partial_3v_{124}-\partial_2v_{134}+\partial_1v_{234}``.
```@repl ga
∂(Λ(tangent(ℝ^4,2,4)).v1234)
```
````
Oracle transcript (Grassmann 0.8.46, label `algebra.md:1120`):
````
julia> ∂(Λ(tangent(ℝ^4,2,4)).v1234)
0 - 1∂₄v₁₂₃ + 1∂₃v₁₂₄ - 1∂₂v₁₃₄ + 1∂₁v₂₃₄
````

#### rotation direction
Status: **MATCH** — LaTeX claims exactly `-v₂` / `v₂`; oracle has 2.22045e-16 v₁ round-off.
Doc source `docs/src/algebra.md:1172-1183` (verbatim):
````
**Remark**. The sandwich must be written with reversion on the left side, otherwise the rotation is clockwise and opposite of the phase parameter convention used by Euler's formula.
For example, observe the resultant direction of rotation
```math
e^{\frac\pi4v_{12}}v_1\widetilde{e^{\frac\pi4v_{12}}} = -v_2
```
which means it is rotating in the wrong direction opposite of Euler, while
```math
\widetilde{e^{\frac\pi4v_{12}}}v_1e^{\frac\pi4v_{12}} = v_2
```
is compatible with Euler's convention.
So, sandwich must be applied with its reversion on the left side--if the standard Euler rotation direction is desired.
However, many authors follow the opposite convention of clockwise instead.
````
Oracle transcript (Grassmann 0.8.46, label `algebra.md:1175`):
````
julia> basis"2"
(⟨11⟩, v, v₁, v₂, v₁₂)

julia> exp(π/4*v12)*v1*~exp(π/4*v12)
2.22045e-16v₁ - 1.0v₂

julia> ~exp(π/4*v12)*v1*exp(π/4*v12)
2.22045e-16v₁ + 1.0v₂
````

#### Euler characteristic of simplices
Status: **BROKEN** — `Δ` now binds Leibniz `Laplacian` (not callable). `χ(skeleton(ω))` reproduces intent: `(1,2),(1,0),(1,2),(1,0)`; see the `simplicial` probe for skeleton/betti/chain/path goldens (and the bogus negative betti numbers).
Doc source `docs/src/algebra.md:1336-1344` (verbatim):
````
Let's obtain the full `skeleton` of a simplical complex ``\Delta(\omega)=\mathcal P(\omega)\backslash\Lambda^0(V)`` from the power set ``\mathcal P(\omega)`` of all vertices with each `subcomplex` ``\Delta(\partial(\omega))`` contained in the edge graph:
```math
\Delta(\omega) =  \sum_{g=1}^n\sum_{k=1}^{n\choose g}\left(\text{abs}\langle\omega\rangle_{g,k} + \Delta\left(\text{abs}\,\partial\langle\omega\rangle_{g,k}\right)\right).
```
Compute the value ``\chi(\Delta(\omega))=1`` and ``\chi(\Delta(\partial(\omega))) = \, ?`` for any simplex ``\omega``. As an exercise, also compute the corresponding `betti` numbers..
```@repl ga
[(χ(Δ(ω)),χ(Δ(∂(ω)))) for ω ∈ (Λ(ℝ5).v12,Λ(ℝ5).v123,Λ(ℝ5).v1234,Λ(ℝ5).v12345)]
```
These methods can be applied to any `Multivector` simplicial complex.
````
Oracle transcript (Grassmann 0.8.46, label `algebra.md:1342`):
````
julia> [(χ(Δ(ω)),χ(Δ(∂(ω)))) for ω ∈ (Λ(ℝ5).v12,Λ(ℝ5).v123,Λ(ℝ5).v1234,Λ(ℝ5).v12345)]
ERROR: MethodError: objects of type Laplacian are not callable.
In case you did not try calling it explicitly, check if a Laplacian has been passed as an argument to a method that expects a callable instead.
The object of type `Laplacian` exists, but no method is defined for this combination of argument types when trying to treat it as a callable object.
````
Oracle transcript (Grassmann 0.8.46, label `simplicial`):
````
julia> ω = Λ(ℝ5).v123
v₁₂₃

julia> ∂(ω)
1v₁₂ - 1v₁₃ + 0v₁₄ + 0v₁₅ + 1v₂₃ + 0v₂₄ + 0v₂₅ + 0v₃₄ + 0v₃₅ + 0v₄₅

julia> skeleton(ω)
0 + 2v₁ + 2v₂ + 2v₃ + 1v₁₂ + 1v₁₃ + 1v₂₃ + 1v₁₂₃

julia> χ(skeleton(ω))
1

julia> betti(skeleton(ω))
5-element Values{5, Int64} with indices SOneTo(5):
 1
 0
 0
 0
 0

julia> χ(skeleton(∂(ω)))
0

julia> betti(skeleton(∂(ω)))
5-element Values{5, Int64} with indices SOneTo(5):
 1
 1
 0
 0
 0

julia> subcomplex(ω)
ERROR: MethodError: objects of type Laplacian are not callable.
In case you did not try calling it explicitly, check if a Laplacian has been passed as an argument to a method that expects a callable instead.
The object of type `Laplacian` exists, but no method is defined for this combination of argument types when trying to treat it as a callable object.

julia> [(χ(skeleton(ω)),χ(skeleton(∂(ω)))) for ω ∈ (Λ(ℝ5).v12,Λ(ℝ5).v123,Λ(ℝ5).v1234,Λ(ℝ5).v12345)]
4-element Vector{Tuple{Int64, Int64}}:
 (1, 2)
 (1, 0)
 (1, 2)
 (1, 0)

julia> [betti(skeleton(∂(ω))) for ω ∈ (Λ(ℝ5).v12,Λ(ℝ5).v123,Λ(ℝ5).v1234,Λ(ℝ5).v12345)]
4-element Vector{Values{5, Int64}}:
 [2, 0, 0, 0, 0]
 [1, 1, 0, 0, 0]
 [0, -2, 0, 0, 0]
 [1, -4, -5, 0, 0]

julia> chain(Λ(ℝ5).v1234)
1v₁₂ + 0v₁₃ - 1v₁₄ + 0v₁₅ + 1v₂₃ + 0v₂₄ + 0v₂₅ + 1v₃₄ + 0v₃₅ + 0v₄₅

julia> path(Λ(ℝ5).v1234)
1v₁₂ + 0v₁₃ + 0v₁₄ + 0v₁₅ + 1v₂₃ + 0v₂₄ + 0v₂₅ + 1v₃₄ + 0v₃₅ + 0v₄₅
````

#### null basis products
Status: **NEW** — consistent with Issue #19 test; `v∞*v∅` is a Spinor so zero terms print.
Doc source `docs/src/algebra.md:1346-1359` (verbatim):
````
### Null-basis of the projective split

Let ``v_\pm^2 = \pm1`` be a basis with ``v_\infty = v_++v_-`` and ``v_\emptyset = (v_--v_+)/2``.
An embedding space ``\mathbb R^{p+1,q+1}`` carrying the action from the group ``O(p+1,q+1)`` then has
``v_\infty^2 =0``, ``v_\emptyset^2 =0``,
``v_\infty \cdot v_\emptyset = -1``,  and ``v_{\infty\emptyset}^2 = 1`` with
Lobachevskian plane ``v_{\infty\emptyset}`` having these product properties,
```@repl ga
using Grassmann; @basis S"∞∅++"
v∞^2, v∅^2, v1^2, v2^2
v∞ ⋅ v∅, v∞∅^2
v∞∅ * v∞, v∞∅ * v∅
v∞ * v∅, v∅ * v∞
```
````
Oracle transcript (Grassmann 0.8.46, label `algebra.md:1354`):
````
julia> @basis S"∞∅++"
(⟨∞∅11⟩, v, v∞, v∅, v₁, v₂, v∞∅, v∞₁, v∞₂, v∅₁, v∅₂, v₁₂, v∞∅₁, v∞∅₂, v∞₁₂, v∅₁₂, v∞∅₁₂)

julia> v∞^2, v∅^2, v1^2, v2^2
(𝟎, 𝟎, 1v, 1v)

julia> v∞ ⋅ v∅, v∞∅^2
(-1v, 1v)

julia> v∞∅ * v∞, v∞∅ * v∅
(-1v∞, 1v∅)

julia> v∞ * v∅, v∅ * v∞
(-1 + 1v∞∅ + 0v∞₁ + 0v∞₂ + 0v∅₁ + 0v∅₂ + 0v₁₂ + 0v∞∅₁₂, -1 - 1v∞∅ + 0v∞₁ + 0v∞₂ + 0v∅₁ + 0v∅₂ + 0v₁₂ + 0v∞∅₁₂)
````

#### null basis complements
Status: **NEW**
Doc source `docs/src/algebra.md:1360-1381` (verbatim):
````
For the null-basis, complement operations are different:
```math
\star v_\infty = \star(v_++v_-) = (v_- + v_+)v_{1...n} = v_{\infty1...n}
```
```math
 \star 2v_\emptyset = \star(v_--v_+) = (v_+ - v_-)v_{1...n} = -2v_{\emptyset1...n}
```
The Hodge complement satisfies ``\langle\omega\ast\omega\rangle I=\omega\wedge\star\omega``. This property is naturally a result of using the geometric product in the definition.
An additional metric independent version of the complement operation is available with the `!` operator,
```math
!v_\infty = !(v_++v_-) = (v_- - v_+)v_{1...n} = 2v_{\emptyset1...n}
```
```math
!2v_\emptyset = !(v_--v_+) = (v_+ + v_-)v_{1...n} = -v_{\infty1...n}
```
For that variation of complement, ``||\omega||^2 I = \omega\,\wedge\,!\omega`` holds.
```@repl ga
⋆v∞, !v∞, ⋆v∅, !v∅
!v∞ * v12 == -2v∅, !v∅ * v12 == v∞/2
⋆v∞ * v12 == -v∞, ⋆v∅ * v12 == v∅
v∞ * !v∞, v∅ * !v∅
```
````
Oracle transcript (Grassmann 0.8.46, label `algebra.md:1377`):
````
julia> ⋆v∞, !v∞, ⋆v∅, !v∅
(1v∞₁₂, 2v∅₁₂, -1v∅₁₂, -0.5v∞₁₂)

julia> !v∞ * v12 == -2v∅, !v∅ * v12 == v∞/2
(true, true)

julia> ⋆v∞ * v12 == -v∞, ⋆v∅ * v12 == v∅
(true, true)

julia> v∞ * !v∞, v∅ * !v∅
(0 + 0v∞∅ + 0v∞₁ + 0v∞₂ + 0v∅₁ + 0v∅₂ - 2v₁₂ + 2v∞∅₁₂, -0.0 - 0.0v∞∅ - 0.0v∞₁ - 0.0v∞₂ - 0.0v∅₁ - 0.0v∅₂ + 0.5v₁₂ + 0.5v∞∅₁₂)
````

#### dual numbers with Reduce
Status: **NOT-RUNNABLE + DIFF** — needs Reduce; the `@mixedbasis tangent(ℝ^1)` display changed from doc `(⟨+-₁¹⟩*, v, v₁, w¹, ϵ₁, ∂¹, …)` to oracle `(T¹⟨+-₁²⟩*, v, v₁, w¹, ∂₁, ϵ₁, …)`. Intended golden (symbolic): `a*b = x*y + (dy*x + dx*y)v₁ϵ₁` (product rule / dual numbers).
Doc source `docs/src/algebra.md:1392-1405` (verbatim):
````
The product rule is encoded into `Grassmann` algebra when a `tangent` bundle is used, demonstrated here symbolically with `Reduce` by using the dual number definition:
```julia
julia> using Grassmann, Reduce
Reduce (Free CSL version, revision 4590), 11-May-18 ...

julia> @mixedbasis tangent(ℝ^1)
(⟨+-₁¹⟩*, v, v₁, w¹, ϵ₁, ∂¹, v₁w¹, v₁ϵ₁, v₁∂¹, w¹ϵ₁, w¹∂¹, ϵ₁∂¹, v₁w¹ϵ₁, v₁w¹∂¹, v₁ϵ₁∂¹, w¹ϵ₁∂¹, v₁w¹ϵ₁∂¹)

julia> a,b = :x*v1 + :dx*ϵ1, :y*v1 + :dy*ϵ1
(xv₁ + dxϵ₁, yv₁ + dyϵ₁)

julia> a * b
x * y + (dy * x + dx * y)v₁ϵ₁
```
````
Oracle transcript (Grassmann 0.8.46, label `algebra.md:1397 (Reduce-free variant)`):
````
julia> @mixedbasis tangent(ℝ^1)
(T¹⟨+-₁²⟩*, v, v₁, w¹, ∂₁, ϵ₁, v₁w¹, ∂₁v₁, ϵ¹v₁, ∂₁w¹, ϵ₁w₁, ∂₁ϵ¹, ∂₁v₁w¹, ϵ¹v₁w¹, ∂₁ϵ¹v₁, ∂₁ϵ¹w¹, ∂₁ϵ¹v₁w¹)
````

#### higher-order Taylor numbers
Status: **NEW** — repeated derivation prints with `⊗` (`∂₁⊗∂₁v₁`); third order vanishes (`𝟎`, and `ans*∂1` → `0.0v⃖`).
Doc source `docs/src/algebra.md:1406-1417` (verbatim):
````
Higher order and multivariable Taylor numbers are also supported.
```@repl ga
@basis tangent(ℝ,2,2) # 1D Grade, 2nd Order, 2 Variables
∂1 * ∂1v1
∂1 * ∂2
v1*∂12
∂12*∂2 # 3rd order is zero
@mixedbasis tangent(ℝ^2,2,2); # 2D Grade, 2nd Order, 2 Variables
V(∇) # vector field
V(∇) ⋅ V(∇) # Laplacian
ans*∂1 # 3rd order is zero
```
````
Oracle transcript (Grassmann 0.8.46, label `algebra.md:1408`):
````
julia> @basis tangent(ℝ,2,2)
(T²⟨+₁₂⟩, v, v₁, ∂₁, ∂₂, ∂₁v₁, ∂₂v₁, ∂₁₂, ∂₁₂v₁)

julia> ∂1 * ∂1v1
∂₁⊗∂₁v₁

julia> ∂1 * ∂2
∂₁₂

julia> v1*∂12
∂₁₂v₁

julia> ∂12*∂2
𝟎

julia> @mixedbasis tangent(ℝ^2,2,2);

julia> V(∇)
0v₁₂ + 1∂₁v₁ + 0∂₂v₁ + 0∂₁v₂ + 1∂₂v₂ + 0∂₁₂

julia> V(∇) ⋅ V(∇)
0 + 1∂₁⊗∂₁ + 1∂₂⊗∂₂

julia> ans*∂1
0.0v⃖
````

#### tensor-field product with Reduce
Status: **NOT-RUNNABLE** — symbolic golden kept verbatim.
Doc source `docs/src/algebra.md:1418-1425` (verbatim):
````
Multiplication with an ``\epsilon_i`` element is used help signify tensor fields so that differential operators are automatically applied in the `Submanifold` algebra as ∂ⱼ⊖(ω⊗ϵᵢ) = ∂ⱼ(ωϵᵢ) ≠ (∂ⱼ⊗ω)⊖ϵᵢ.
```julia
julia> using Reduce, Grassmann; @mixedbasis tangent(ℝ^2,3,2);

julia> (∂1+∂12) * (:(x1^2*x2^2)*ϵ1 + :(sin(x1))*ϵ2)
0.0 + (2 * x1 * x2 ^ 2)∂₁ϵ¹ + (cos(x1))∂₁ϵ² + (4 * x1 * x2)∂₁₂ϵ¹
```
Although fully generalized, the implementation in this release is still experimental.
````

#### GaloisFields coefficients
Status: **NOT-RUNNABLE + DIFF** — GaloisFields not installed; doc golden: `F(3)*v1 = 3v₁`, `inv(3v₁) = 5v₁` in 𝔽₇ (inverse of a vector v with v²=1 is v/(v²) coefficientwise inverse: 3⁻¹=5 mod 7). `basis"2"` now displays `⟨11⟩` (doc: `⟨++⟩`). Int oracle: `inv(3*v1) = 0.3333333333333333v₁`.
Doc source `docs/src/algebra.md:1427-1449` (verbatim):
````
## Symbolic coefficients by declaring algebra

Due to the abstract generality of the code generation of the `Grassmann` product algebra, it is easily possible to extend the entire set of operations to other kinds of scalar coefficient types.
```julia
julia> using GaloisFields, Grassmann

julia> const F = GaloisField(7)
𝔽₇

julia> basis"2"
(⟨++⟩, v, v₁, v₂, v₁₂)

julia> F(3)*v1
3v₁

julia> inv(ans)
5v₁
```
By default, the coefficients are required to be `<:Number`. However, if this does not suit your needs, alternative scalar product algebras can be specified with
```julia
Grassmann.generate_algebra(:AbstractAlgebra,:SetElem)
```
where `:SetElem` is the desired scalar field and `:AbstractAlgebra` is the scope which contains the scalar field.
````
Oracle transcript (Grassmann 0.8.46, label `algebra.md:1436 (Int field variant)`):
````
julia> basis"2"
(⟨11⟩, v, v₁, v₂, v₁₂)

julia> 3*v1
3v₁

julia> inv(3*v1)
0.3333333333333333v₁
````

#### Reduce symbolic products
Status: **NOT-RUNNABLE** — numeric instance a,b,c,d = 1,2,3,4 checked instead: `11v`, `-2v₁₂`, `11 - 2v₁₂` (symbolic doc output has a spurious `0.0 +` Reduce artifact).
Doc source `docs/src/algebra.md:1450-1467` (verbatim):
````

With the usage of `Requires`, symbolic scalar computation with [Reduce.jl](https://github.com/chakravala/Reduce.jl) and other packages is automatically enabled,
```julia
julia> using Reduce, Grassmann
Reduce (Free CSL version, revision 4590), 11-May-18 ...

julia> basis"2"
(⟨++⟩, v, v₁, v₂, v₁₂)

julia> (:a*v1 + :b*v2) ⋅ (:c*v1 + :d*v2)
(a * c + b * d)v

julia> (:a*v1 + :b*v2) ∧ (:c*v1 + :d*v2)
0.0 + (a * d - b * c)v₁₂

julia> (:a*v1 + :b*v2) * (:c*v1 + :d*v2)
a * c + b * d + (a * d - b * c)v₁₂
```
````
Oracle transcript (Grassmann 0.8.46, label `algebra.md:1459 (numeric variant)`):
````
julia> basis"2"
(⟨11⟩, v, v₁, v₂, v₁₂)

julia> (1*v1 + 2*v2) ⋅ (3*v1 + 4*v2)
11v

julia> (1*v1 + 2*v2) ∧ (3*v1 + 4*v2)
-2v₁₂

julia> (1*v1 + 2*v2) * (3*v1 + 4*v2)
11 - 2v₁₂
````

#### Reduce 4D wedge
Status: **NOT-RUNNABLE** — symbolic golden verbatim: P∧Q coefficients `px*qy-py*qx` (v₁₂) … `pz-qz` (v₃₄); P∧Q∧R trivector coefficients as shown.
Doc source `docs/src/algebra.md:1469-1488` (verbatim):
````

```julia
julia> using Reduce,Grassmann; basis"4"
Reduce (Free CSL version, revision 4590), 11-May-18 ...
(⟨++++⟩, v, v₁, v₂, v₃, v₄, v₁₂, v₁₃, v₁₄, v₂₃, v₂₄, v₃₄, v₁₂₃, v₁₂₄, v₁₃₄, v₂₃₄, v₁₂₃₄)

julia> P,Q = :px*v1 + :py*v2 + :pz* v3 + v4, :qx*v1 + :qy*v2 + :qz*v3 + v4
(pxv₁ + pyv₂ + pzv₃ + 1.0v₄, qxv₁ + qyv₂ + qzv₃ + 1.0v₄)

julia> P∧Q
0.0 + (px * qy - py * qx)v₁₂ + (px * qz - pz * qx)v₁₃ + (px - qx)v₁₄ + (py * qz - pz * qy)v₂₃ + (py - qy)v₂₄ + (pz - qz)v₃₄

julia> R = :rx*v1 + :ry*v2 + :rz*v3 + v4
rxv₁ + ryv₂ + rzv₃ + 1.0v₄

julia> P∧Q∧R
0.0 + ((px * qy - py * qx) * rz - ((px * qz - pz * qx) * ry - (py * qz - pz * qy) * rx))v₁₂₃ + (((px * qy - py * qx) + (py - qy) * rx) - (px - qx) * ry)v₁₂₄ + (((px * qz - pz * qx) + (pz - qz) * rx) - (px - qx) * rz)v₁₃₄ + (((py * qz - pz * qy) + (pz - qz) * ry) - (py - qy) * rz)v₂₃₄
```

It should be straight-forward to easily substitute any other extended algebraic operations and fields; issues with questions or pull-requests to that end are welcome.
````

#### Makie examples (algebra.md copy)
Status: **PLOT** — same as README §6.1; the text says GeometryTypes (old name of GeometryBasics).
Doc source `docs/src/algebra.md:1265-1316` (verbatim):
````
Due to [GeometryTypes.jl](https://github.com/JuliaGeometry/GeometryTypes.jl) `Point` interoperability, plotting and visualizing with [Makie.jl](https://github.com/JuliaPlots/Makie.jl) is easily possible. For example, the `vectorfield` method creates an anonymous `Point` function that applies a versor outermorphism:
```julia
using Grassmann, Makie
basis"2" # Euclidean
streamplot(vectorfield(exp(π*v12/2)),-1.5..1.5,-1.5..1.5)
streamplot(vectorfield(exp((π/2)*v12/2)),-1.5..1.5,-1.5..1.5)
streamplot(vectorfield(exp((π/4)*v12/2)),-1.5..1.5,-1.5..1.5)
streamplot(vectorfield(v1*exp((π/4)*v12/2)),-1.5..1.5,-1.5..1.5)
@basis S"+-" # Hyperbolic
streamplot(vectorfield(exp((π/8)*v12/2)),-1.5..1.5,-1.5..1.5)
streamplot(vectorfield(v1*exp((π/4)*v12/2)),-1.5..1.5,-1.5..1.5)
```
![paper/img/plane-1.png](https://raw.githubusercontent.com/chakravala/Grassmann.jl/master/paper/img/plane-1.png) ![paper/img/plane-2.png](https://raw.githubusercontent.com/chakravala/Grassmann.jl/master/paper/img/plane-2.png)
![paper/img/plane-3.png](https://raw.githubusercontent.com/chakravala/Grassmann.jl/master/paper/img/plane-3.png) ![paper/img/plane-4.png](https://raw.githubusercontent.com/chakravala/Grassmann.jl/master/paper/img/plane-4.png)
![paper/img/plane-3.png](https://raw.githubusercontent.com/chakravala/Grassmann.jl/master/paper/img/plane-5.png) ![paper/img/plane-4.png](https://raw.githubusercontent.com/chakravala/Grassmann.jl/master/paper/img/plane-6.png)

```julia
using Grassmann, Makie
@basis S"∞+++"
f(t) = (↓(exp(π*t*((3/7)*v12+v∞3))>>>↑(v1+v2+v3)))
lines(V(2,3,4).(points(f)))
@basis S"∞∅+++"
f(t) = (↓(exp(π*t*((3/7)*v12+v∞3))>>>↑(v1+v2+v3)))
lines(V(3,4,5).(points(f)))
```
![paper/img/torus.png](https://raw.githubusercontent.com/chakravala/Grassmann.jl/master/paper/img/torus.png) ![paper/img/helix.png](https://raw.githubusercontent.com/chakravala/Grassmann.jl/master/paper/img/helix.png)

```julia
using Grassmann, Makie; @basis S"∞+++"
streamplot(vectorfield(exp((π/4)*(v12+v∞3)),V(2,3,4)),-1.5..1.5,-1.5..1.5,-1.5..1.5,gridsize=(10,10))
```
![paper/img/orb.png](https://raw.githubusercontent.com/chakravala/Grassmann.jl/master/paper/img/orb.png)

```julia
using Grassmann, Makie; @basis S"∞+++"
streamplot(vectorfield(exp((π/4)*(v12+v∞3)),V(2,3,4),V(1,2,3)),-1.5..1.5,-1.5..1.5,-1.5..1.5,gridsize=(10,10))
```
![paper/img/wave.png](https://raw.githubusercontent.com/chakravala/Grassmann.jl/master/paper/img/wave.png)

```julia
using Grassmann, Makie; @basis S"∞+++"
f(t) = ↓(exp(t*v∞*(sin(3t)*3v1+cos(2t)*7v2-sin(5t)*4v3)/2)>>>↑(v1+v2-v3))
lines(V(2,3,4).(points(f)))
```
![paper/img/orb.png](https://raw.githubusercontent.com/chakravala/Grassmann.jl/master/paper/img/orbit-2.png)

```julia
using Grassmann, Makie; @basis S"∞+++"
f(t) = ↓(exp(t*(v12+0.07v∞*(sin(3t)*3v1+cos(2t)*7v2-sin(5t)*4v3)/2))>>>↑(v1+v2-v3))
lines(V(2,3,4).(points(f)))
```
![paper/img/orb.png](https://raw.githubusercontent.com/chakravala/Grassmann.jl/master/paper/img/orbit-4.png)
````

### 6.4 Cayley tables (`algebra.md:623-1004`)

The doc renders these as LaTeX `array`s (row = left operand, column = right operand, header row/column list the basis `v, v₁, …`). I compared every doc table entry-by-entry against the oracle below: **all agree** (the doc uses `v`/`-v_1`, the oracle `1v`/`-1v₁`, and 𝟎 for 0). The oracle `text/plain` form is the display golden: first line `n×n Endomorphism{V, Multiplex{V, Multivector{V, T, 2^n} where T, 2^n}}:`, then the header row whose first cell is the pseudoscalar label, then one row per left operand. Doc snippets: `cayley(Submanifold(1),wedge)` … `cayley(Submanifold(3),>>)` at `algebra.md:625-1004`.

#### all Cayley tables for n=1,2,3, S"-", S"+-"
Status: **MATCH**
Doc source `docs/src/algebra.md:623-628` (verbatim):
````
When `using Grassmann` in a session, the `cayley` table can be used to recall geometric algebra information, e.g. to compare ``>`` and ``>>`` contractions:

```julia
cayley(Submanifold(1),wedge)
cayley(Submanifold(1),vee)
```
````
Oracle transcript (Grassmann 0.8.46, label `algebra.md:626 cayley`):
````
julia> cayley(Submanifold(1),wedge)
2×2 Endomorphism{⟨1⟩, Multiplex{⟨1⟩, Multivector{⟨1⟩, T, 2} where T, 2}}:
 v₁   v  v₁
  v   v  v₁
 v₁  v₁   𝟎

julia> cayley(Submanifold(1),vee)
2×2 Endomorphism{⟨1⟩, Multiplex{⟨1⟩, Multivector{⟨1⟩, T, 2} where T, 2}}:
 v₁  v  v₁
  v  𝟎   v
 v₁  v  v₁

julia> cayley(Submanifold(1),<)
2×2 Endomorphism{⟨1⟩, Multiplex{⟨1⟩, Multivector{⟨1⟩, T, 2} where T, 2}}:
 v₁  v  v₁
  v  v  v₁
 v₁  𝟎   v

julia> cayley(Submanifold(1),>)
2×2 Endomorphism{⟨1⟩, Multiplex{⟨1⟩, Multivector{⟨1⟩, T, 2} where T, 2}}:
 v₁   v  v₁
  v   v   𝟎
 v₁  v₁   v

julia> cayley(Submanifold(1),<<)
2×2 Endomorphism{⟨1⟩, Multiplex{⟨1⟩, Multivector{⟨1⟩, T, 2} where T, 2}}:
 v₁  v  v₁
  v  v  v₁
 v₁  𝟎   v

julia> cayley(Submanifold(1),>>)
2×2 Endomorphism{⟨1⟩, Multiplex{⟨1⟩, Multivector{⟨1⟩, T, 2} where T, 2}}:
 v₁   v  v₁
  v   v   𝟎
 v₁  v₁   v

julia> cayley(Submanifold(S"-"),wedge)
2×2 Endomorphism{⟨-⟩, Multiplex{⟨-⟩, Multivector{⟨-⟩, T, 2} where T, 2}}:
 v₁   v  v₁
  v   v  v₁
 v₁  v₁   𝟎

julia> cayley(Submanifold(S"-"),vee)
2×2 Endomorphism{⟨-⟩, Multiplex{⟨-⟩, Multivector{⟨-⟩, T, 2} where T, 2}}:
 v₁  v  v₁
  v  𝟎   v
 v₁  v  v₁

julia> cayley(Submanifold(S"-"),<)
2×2 Endomorphism{⟨-⟩, Multiplex{⟨-⟩, Multivector{⟨-⟩, T, 2} where T, 2}}:
 v₁  v   v₁
  v  v   v₁
 v₁  𝟎  -1v

julia> cayley(Submanifold(S"-"),>)
2×2 Endomorphism{⟨-⟩, Multiplex{⟨-⟩, Multivector{⟨-⟩, T, 2} where T, 2}}:
 v₁   v   v₁
  v   v    𝟎
 v₁  v₁  -1v

julia> cayley(Submanifold(S"-"),<<)
2×2 Endomorphism{⟨-⟩, Multiplex{⟨-⟩, Multivector{⟨-⟩, T, 2} where T, 2}}:
 v₁  v   v₁
  v  v   v₁
 v₁  𝟎  -1v

julia> cayley(Submanifold(S"-"),>>)
2×2 Endomorphism{⟨-⟩, Multiplex{⟨-⟩, Multivector{⟨-⟩, T, 2} where T, 2}}:
 v₁   v   v₁
  v   v    𝟎
 v₁  v₁  -1v

julia> cayley(Submanifold(2),wedge)
4×4 Endomorphism{⟨11⟩, Multiplex{⟨11⟩, Multivector{⟨11⟩, T, 4} where T, 4}}:
 v₁₂    v     v₁   v₂  v₁₂
   v    v     v₁   v₂  v₁₂
  v₁   v₁      𝟎  v₁₂    𝟎
  v₂   v₂  -1v₁₂    𝟎    𝟎
 v₁₂  v₁₂      𝟎    𝟎    𝟎

julia> cayley(Submanifold(2),vee)
4×4 Endomorphism{⟨11⟩, Multiplex{⟨11⟩, Multivector{⟨11⟩, T, 4} where T, 4}}:
 v₁₂  v   v₁  v₂  v₁₂
   v  𝟎    𝟎   𝟎    v
  v₁  𝟎    𝟎   v   v₁
  v₂  𝟎  -1v   𝟎   v₂
 v₁₂  v   v₁  v₂  v₁₂

julia> cayley(Submanifold(2),<)
4×4 Endomorphism{⟨11⟩, Multiplex{⟨11⟩, Multivector{⟨11⟩, T, 4} where T, 4}}:
 v₁₂  v  v₁  v₂   v₁₂
   v  v  v₁  v₂   v₁₂
  v₁  𝟎   v   𝟎    v₂
  v₂  𝟎   𝟎   v  -1v₁
 v₁₂  𝟎   𝟎   𝟎     v

julia> cayley(Submanifold(2),>)
4×4 Endomorphism{⟨11⟩, Multiplex{⟨11⟩, Multivector{⟨11⟩, T, 4} where T, 4}}:
 v₁₂    v  v₁    v₂  v₁₂
   v    v   𝟎     𝟎    𝟎
  v₁   v₁   v     𝟎    𝟎
  v₂   v₂   𝟎     v    𝟎
 v₁₂  v₁₂  v₂  -1v₁    v

julia> cayley(Submanifold(2),<<)
4×4 Endomorphism{⟨11⟩, Multiplex{⟨11⟩, Multivector{⟨11⟩, T, 4} where T, 4}}:
 v₁₂  v  v₁  v₂   v₁₂
   v  v  v₁  v₂   v₁₂
  v₁  𝟎   v   𝟎    v₂
  v₂  𝟎   𝟎   v  -1v₁
 v₁₂  𝟎   𝟎   𝟎   -1v

julia> cayley(Submanifold(2),>>)
4×4 Endomorphism{⟨11⟩, Multiplex{⟨11⟩, Multivector{⟨11⟩, T, 4} where T, 4}}:
 v₁₂      v    v₁   v₂  v₁₂
   v      v     𝟎    𝟎    𝟎
  v₁     v₁     v    𝟎    𝟎
  v₂     v₂     𝟎    v    𝟎
 v₁₂  -1v₁₂  -1v₂  1v₁  -1v

julia> cayley(Submanifold(S"+-"),wedge)
4×4 Endomorphism{⟨+-⟩, Multiplex{⟨+-⟩, Multivector{⟨+-⟩, T, 4} where T, 4}}:
 v₁₂    v     v₁   v₂  v₁₂
   v    v     v₁   v₂  v₁₂
  v₁   v₁      𝟎  v₁₂    𝟎
  v₂   v₂  -1v₁₂    𝟎    𝟎
 v₁₂  v₁₂      𝟎    𝟎    𝟎

julia> cayley(Submanifold(S"+-"),vee)
4×4 Endomorphism{⟨+-⟩, Multiplex{⟨+-⟩, Multivector{⟨+-⟩, T, 4} where T, 4}}:
 v₁₂  v   v₁  v₂  v₁₂
   v  𝟎    𝟎   𝟎    v
  v₁  𝟎    𝟎   v   v₁
  v₂  𝟎  -1v   𝟎   v₂
 v₁₂  v   v₁  v₂  v₁₂

julia> cayley(Submanifold(S"+-"),<)
4×4 Endomorphism{⟨+-⟩, Multiplex{⟨+-⟩, Multivector{⟨+-⟩, T, 4} where T, 4}}:
 v₁₂  v  v₁   v₂  v₁₂
   v  v  v₁   v₂  v₁₂
  v₁  𝟎   v    𝟎   v₂
  v₂  𝟎   𝟎  -1v   v₁
 v₁₂  𝟎   𝟎    𝟎  -1v

julia> cayley(Submanifold(S"+-"),>)
4×4 Endomorphism{⟨+-⟩, Multiplex{⟨+-⟩, Multivector{⟨+-⟩, T, 4} where T, 4}}:
 v₁₂    v  v₁   v₂  v₁₂
   v    v   𝟎    𝟎    𝟎
  v₁   v₁   v    𝟎    𝟎
  v₂   v₂   𝟎  -1v    𝟎
 v₁₂  v₁₂  v₂   v₁  -1v

julia> cayley(Submanifold(S"+-"),<<)
4×4 Endomorphism{⟨+-⟩, Multiplex{⟨+-⟩, Multivector{⟨+-⟩, T, 4} where T, 4}}:
 v₁₂  v  v₁   v₂  v₁₂
   v  v  v₁   v₂  v₁₂
  v₁  𝟎   v    𝟎   v₂
  v₂  𝟎   𝟎  -1v   v₁
 v₁₂  𝟎   𝟎    𝟎   1v

julia> cayley(Submanifold(S"+-"),>>)
4×4 Endomorphism{⟨+-⟩, Multiplex{⟨+-⟩, Multivector{⟨+-⟩, T, 4} where T, 4}}:
 v₁₂      v    v₁    v₂  v₁₂
   v      v     𝟎     𝟎    𝟎
  v₁     v₁     v     𝟎    𝟎
  v₂     v₂     𝟎   -1v    𝟎
 v₁₂  -1v₁₂  -1v₂  -1v₁   1v

julia> cayley(Submanifold(3),wedge)
8×8 Endomorphism{⟨111⟩, Multiplex{⟨111⟩, Multivector{⟨111⟩, T, 8} where T, 8}}:
 v₁₂₃     v     v₁      v₂    v₃   v₁₂     v₁₃   v₂₃  v₁₂₃
    v     v     v₁      v₂    v₃   v₁₂     v₁₃   v₂₃  v₁₂₃
   v₁    v₁      𝟎     v₁₂   v₁₃     𝟎       𝟎  v₁₂₃     𝟎
   v₂    v₂  -1v₁₂       𝟎   v₂₃     𝟎  -1v₁₂₃     𝟎     𝟎
   v₃    v₃  -1v₁₃   -1v₂₃     𝟎  v₁₂₃       𝟎     𝟎     𝟎
  v₁₂   v₁₂      𝟎       𝟎  v₁₂₃     𝟎       𝟎     𝟎     𝟎
  v₁₃   v₁₃      𝟎  -1v₁₂₃     𝟎     𝟎       𝟎     𝟎     𝟎
  v₂₃   v₂₃   v₁₂₃       𝟎     𝟎     𝟎       𝟎     𝟎     𝟎
 v₁₂₃  v₁₂₃      𝟎       𝟎     𝟎     𝟎       𝟎     𝟎     𝟎

julia> cayley(Submanifold(3),vee)
8×8 Endomorphism{⟨111⟩, Multiplex{⟨111⟩, Multivector{⟨111⟩, T, 8} where T, 8}}:
 v₁₂₃  v  v₁   v₂  v₃   v₁₂   v₁₃  v₂₃  v₁₂₃
    v  𝟎   𝟎    𝟎   𝟎     𝟎     𝟎    𝟎     v
   v₁  𝟎   𝟎    𝟎   𝟎     𝟎     𝟎    v    v₁
   v₂  𝟎   𝟎    𝟎   𝟎     𝟎   -1v    𝟎    v₂
   v₃  𝟎   𝟎    𝟎   𝟎     v     𝟎    𝟎    v₃
  v₁₂  𝟎   𝟎    𝟎   v     𝟎    v₁   v₂   v₁₂
  v₁₃  𝟎   𝟎  -1v   𝟎  -1v₁     𝟎   v₃   v₁₃
  v₂₃  𝟎   v    𝟎   𝟎  -1v₂  -1v₃    𝟎   v₂₃
 v₁₂₃  v  v₁   v₂  v₃   v₁₂   v₁₃  v₂₃  v₁₂₃

julia> cayley(Submanifold(3),*)
8×8 Endomorphism{⟨111⟩, Multiplex{⟨111⟩, Multivector{⟨111⟩, T, 8} where T, 8}}:
 v₁₂₃     v     v₁      v₂    v₃    v₁₂     v₁₃    v₂₃   v₁₂₃
    v     v     v₁      v₂    v₃    v₁₂     v₁₃    v₂₃   v₁₂₃
   v₁    v₁     1v     v₁₂   v₁₃    1v₂     1v₃   v₁₂₃   1v₂₃
   v₂    v₂  -1v₁₂      1v   v₂₃   -1v₁  -1v₁₂₃    1v₃  -1v₁₃
   v₃    v₃  -1v₁₃   -1v₂₃    1v   v₁₂₃    -1v₁   -1v₂   1v₁₂
  v₁₂   v₁₂   -1v₂     1v₁  v₁₂₃    -1v   -1v₂₃   1v₁₃   -1v₃
  v₁₃   v₁₃   -1v₃  -1v₁₂₃   1v₁   1v₂₃     -1v  -1v₁₂    1v₂
  v₂₃   v₂₃   v₁₂₃    -1v₃   1v₂  -1v₁₃    1v₁₂    -1v   -1v₁
 v₁₂₃  v₁₂₃   1v₂₃   -1v₁₃  1v₁₂   -1v₃     1v₂   -1v₁    -1v

julia> cayley(Submanifold(3),<)
8×8 Endomorphism{⟨111⟩, Multiplex{⟨111⟩, Multivector{⟨111⟩, T, 8} where T, 8}}:
 v₁₂₃  v  v₁  v₂  v₃   v₁₂   v₁₃   v₂₃   v₁₂₃
    v  v  v₁  v₂  v₃   v₁₂   v₁₃   v₂₃   v₁₂₃
   v₁  𝟎   v   𝟎   𝟎    v₂    v₃     𝟎    v₂₃
   v₂  𝟎   𝟎   v   𝟎  -1v₁     𝟎    v₃  -1v₁₃
   v₃  𝟎   𝟎   𝟎   v     𝟎  -1v₁  -1v₂    v₁₂
  v₁₂  𝟎   𝟎   𝟎   𝟎     v     𝟎     𝟎     v₃
  v₁₃  𝟎   𝟎   𝟎   𝟎     𝟎     v     𝟎   -1v₂
  v₂₃  𝟎   𝟎   𝟎   𝟎     𝟎     𝟎     v     v₁
 v₁₂₃  𝟎   𝟎   𝟎   𝟎     𝟎     𝟎     𝟎      v

julia> cayley(Submanifold(3),>)
8×8 Endomorphism{⟨111⟩, Multiplex{⟨111⟩, Multivector{⟨111⟩, T, 8} where T, 8}}:
 v₁₂₃     v   v₁     v₂    v₃  v₁₂   v₁₃  v₂₃  v₁₂₃
    v     v    𝟎      𝟎     𝟎    𝟎     𝟎    𝟎     𝟎
   v₁    v₁    v      𝟎     𝟎    𝟎     𝟎    𝟎     𝟎
   v₂    v₂    𝟎      v     𝟎    𝟎     𝟎    𝟎     𝟎
   v₃    v₃    𝟎      𝟎     v    𝟎     𝟎    𝟎     𝟎
  v₁₂   v₁₂   v₂   -1v₁     𝟎    v     𝟎    𝟎     𝟎
  v₁₃   v₁₃   v₃      𝟎  -1v₁    𝟎     v    𝟎     𝟎
  v₂₃   v₂₃    𝟎     v₃  -1v₂    𝟎     𝟎    v     𝟎
 v₁₂₃  v₁₂₃  v₂₃  -1v₁₃   v₁₂   v₃  -1v₂   v₁     v

julia> cayley(Submanifold(3),<<)
8×8 Endomorphism{⟨111⟩, Multiplex{⟨111⟩, Multivector{⟨111⟩, T, 8} where T, 8}}:
 v₁₂₃  v  v₁  v₂  v₃   v₁₂   v₁₃   v₂₃   v₁₂₃
    v  v  v₁  v₂  v₃   v₁₂   v₁₃   v₂₃   v₁₂₃
   v₁  𝟎   v   𝟎   𝟎    v₂    v₃     𝟎    v₂₃
   v₂  𝟎   𝟎   v   𝟎  -1v₁     𝟎    v₃  -1v₁₃
   v₃  𝟎   𝟎   𝟎   v     𝟎  -1v₁  -1v₂    v₁₂
  v₁₂  𝟎   𝟎   𝟎   𝟎   -1v     𝟎     𝟎   -1v₃
  v₁₃  𝟎   𝟎   𝟎   𝟎     𝟎   -1v     𝟎    1v₂
  v₂₃  𝟎   𝟎   𝟎   𝟎     𝟎     𝟎   -1v   -1v₁
 v₁₂₃  𝟎   𝟎   𝟎   𝟎     𝟎     𝟎     𝟎    -1v

julia> cayley(Submanifold(3),>>)
8×8 Endomorphism{⟨111⟩, Multiplex{⟨111⟩, Multivector{⟨111⟩, T, 8} where T, 8}}:
 v₁₂₃       v     v₁    v₂     v₃   v₁₂  v₁₃   v₂₃  v₁₂₃
    v       v      𝟎     𝟎      𝟎     𝟎    𝟎     𝟎     𝟎
   v₁      v₁      v     𝟎      𝟎     𝟎    𝟎     𝟎     𝟎
   v₂      v₂      𝟎     v      𝟎     𝟎    𝟎     𝟎     𝟎
   v₃      v₃      𝟎     𝟎      v     𝟎    𝟎     𝟎     𝟎
  v₁₂   -1v₁₂   -1v₂   1v₁      𝟎   -1v    𝟎     𝟎     𝟎
  v₁₃   -1v₁₃   -1v₃     𝟎    1v₁     𝟎  -1v     𝟎     𝟎
  v₂₃   -1v₂₃      𝟎  -1v₃    1v₂     𝟎    𝟎   -1v     𝟎
 v₁₂₃  -1v₁₂₃  -1v₂₃  1v₁₃  -1v₁₂  -1v₃  1v₂  -1v₁   -1v
````

### 6.5 docs/src/tutorials/quick-start.md

#### G2 products
Status: **NEW** — `v1|v2` is `𝟎` (Zero), `v1*v2` is the bare blade `v₁₂`.
Doc source `docs/src/tutorials/quick-start.md:5-11` (verbatim):
````
```@repl ga
using Grassmann
@basis ℝ^2
v1*v2 # geometric product
v1|v2 # inner product
v1∧v2 # exterior product
```
````
Oracle transcript (Grassmann 0.8.46, label `quick-start.md:5`):
````
julia> @basis ℝ^2
(⟨++⟩, v, v₁, v₂, v₁₂)

julia> v1*v2
v₁₂

julia> v1|v2
𝟎

julia> v1∧v2
v₁₂
````

#### reflection
Status: **NEW**
Doc source `docs/src/tutorials/quick-start.md:13-19` (verbatim):
````
## Reflection

```@example ga
a = v1+v2
n = v1
-n*a/n # reflect a in hyperplane normal to n
```
````
Oracle transcript (Grassmann 0.8.46, label `quick-start.md:15`):
````
julia> a = v1+v2
1v₁ + 1v₂

julia> n = v1
v₁

julia> -n*a/n
-1.0v₁ + 1.0v₂
````

#### rotation
Status: **NEW**
Doc source `docs/src/tutorials/quick-start.md:21-26` (verbatim):
````
## Rotation

```@repl ga
R = exp(π/4*v12)
~R*v1*R
```
````
Oracle transcript (Grassmann 0.8.46, label `quick-start.md:23`):
````
julia> R = exp(π/4*v12)
0.7071067811865476 + 0.7071067811865475v₁₂

julia> ~R*v1*R
2.22045e-16v₁ + 1.0v₂
````

### 6.6 docs/src/tutorials/algebra-of-space.md

#### basis"3"
Status: **NEW**
Doc source `docs/src/tutorials/algebra-of-space.md:5-10` (verbatim):
````
Import `Grassmann` and instantiate a three dimensional geometric algebra

```@repl ga
using Grassmann
basis"3"
```
````
Oracle transcript (Grassmann 0.8.46, label `algebra-of-space.md:7`):
````
julia> basis"3"
(⟨111⟩, v, v₁, v₂, v₃, v₁₂, v₁₃, v₂₃, v₁₂₃)
````

#### G3 = Λ(3)
Status: **NEW**
Doc source `docs/src/tutorials/algebra-of-space.md:16-25` (verbatim):
````
The `@basis` macro declares the algebra and assigns the `Submanifold` elements to local variables. The `Basis` can also be assigned to `G3` as
```@repl ga
G3 = Λ(3)
```
You may wish to explicitly assign the blades to variables like so,
```julia
e1 = G3.v1
e2 = G3.v2
# etc ...
```
````
Oracle transcript (Grassmann 0.8.46, label `algebra-of-space.md:17`):
````
julia> G3 = Λ(3)
DirectSum.Basis{⟨111⟩,8}(v, v₁, v₂, v₃, v₁₂, v₁₃, v₂₃, v₁₂₃)
````

#### @basis with custom names
Status: **NEW**
Doc source `docs/src/tutorials/algebra-of-space.md:26-30` (verbatim):
````
Or, if you're lazy you can use the macro with different local names
```@repl ga
@basis ℝ^3 E e
e3, e123
```
````
Oracle transcript (Grassmann 0.8.46, label `algebra-of-space.md:27`):
````
julia> @basis ℝ^3 E e
(⟨+++⟩, v, v₁, v₂, v₃, v₁₂, v₁₃, v₂₃, v₁₂₃)

julia> e3, e123
(v₃, v₁₂₃)
````

#### basic products
Status: **NEW**
Doc source `docs/src/tutorials/algebra-of-space.md:32-41` (verbatim):
````
## Basics

The basic products are available

```@repl ga
v1 * v2 # geometric product
v1 | v2 # inner product
v1 ∧ v2 # exterior product
v1 ∧ v2 ∧ v3 # even more exterior products
```
````
Oracle transcript (Grassmann 0.8.46, label `algebra-of-space.md:36`):
````
julia> v1 * v2
v₁₂

julia> v1 | v2
𝟎

julia> v1 ∧ v2
v₁₂

julia> v1 ∧ v2 ∧ v3
v₁₂₃
````

#### rotor construction
Status: **NEW**
Doc source `docs/src/tutorials/algebra-of-space.md:43-48` (verbatim):
````
Multivectors can be defined in terms of the basis blades. For example, you can construct a rotor as a sum of a scalar and a bivector, like so
```@repl ga
θ = π/4
R = cos(θ) + sin(θ)*v23
R = exp(θ*v23)
```
````
Oracle transcript (Grassmann 0.8.46, label `algebra-of-space.md:44`):
````
julia> θ = π/4
0.7853981633974483

julia> R = cos(θ) + sin(θ)*v23
0.7071067811865476 + 0.7071067811865475v₂₃

julia> R = exp(θ*v23)
0.7071067811865476 + 0.7071067811865475v₂₃
````

#### mixed grades, reversion, grade projection, magnitude
Status: **NEW** — `abs2(A)` returns the whole `~A*A`, contrary to the tutorial prose.
Doc source `docs/src/tutorials/algebra-of-space.md:49-72` (verbatim):
````
You can also mix grades without any reason
```@repl ga
A = 1 + 2v1 + 3v12 + 4v123
```
The reversion operator is accomplished with the tilde `~` in front of the `Multivector` on which it acts
```@repl ga
~A
```
Taking a projection into a specific `grade` of a `Multivector` is usually written ``\langle A\rangle_n`` and can be done using the soft brackets, like so
```@repl ga
A(0)
A(1)
A(2)
```
Using the reversion and grade projection operators, we can define the magnitude of `A` as ``|A|^2 = \langle\tilde A A\rangle``
```@repl ga
~A*A
scalar(ans)
```
This is done in the `abs` and `abs2` operators
```@repl ga
abs2(A)
scalar(ans)
```
````
Oracle transcript (Grassmann 0.8.46, label `algebra-of-space.md:50`):
````
julia> A = 1 + 2v1 + 3v12 + 4v123
1 + 2v₁ + 3v₁₂ + 4v₁₂₃

julia> ~A
1 + 2v₁ - 3v₁₂ - 4v₁₂₃

julia> A(0)
1v

julia> A(1)
2v₁ + 0v₂ + 0v₃

julia> A(2)
3v₁₂ + 0v₁₃ + 0v₂₃

julia> ~A*A
30 + 4v₁ + 12v₂ + 24v₃

julia> scalar(ans)
30v

julia> abs2(A)
30 + 4v₁ + 12v₂ + 24v₃

julia> scalar(ans)
30v
````

#### dual of a vector
Status: **NEW**
Doc source `docs/src/tutorials/algebra-of-space.md:73-77` (verbatim):
````
The dual of a multivector `A` can be defined as ``\tilde AI``, where `I` is the pseudoscalar for the geometric algebra. In `G3`, the dual of a vector is a bivector:
```@repl ga
a = 1v1 + 2v2 + 3v3
⋆a
```
````
Oracle transcript (Grassmann 0.8.46, label `algebra-of-space.md:74`):
````
julia> a = 1v1 + 2v2 + 3v3
1v₁ + 2v₂ + 3v₃

julia> ⋆a
3v₁₂ - 2v₁₃ + 1v₂₃
````

#### reflections
Status: **NEW** — `-n*c*n` is a CoSpinor (prints `+ 0v₁₂₃`).
Doc source `docs/src/tutorials/algebra-of-space.md:79-93` (verbatim):
````
## Reflections

Reflecting a vector ``c`` about a normalized vector ``n`` is pretty simple, ``c\mapsto -ncn``
```@repl ga
c = v1+v2+v3 # a vector
n = v1 # the reflector
-n*c*n # reflect a in hyperplane normal to n
```
Because we have the `inv` available, we can equally well reflect in un-normalized vectors using ``a\mapsto n^{-1}an``
```@repl ga
a = v1+v2+v3 # the vector
n = 3v1 # the reflector
inv(n)*a*n
n\a*n
```
````
Oracle transcript (Grassmann 0.8.46, label `algebra-of-space.md:82`):
````
julia> c = v1+v2+v3
1v₁ + 1v₂ + 1v₃

julia> n = v1
v₁

julia> -n*c*n
-1v₁ + 1v₂ + 1v₃ + 0v₁₂₃
````
Oracle transcript (Grassmann 0.8.46, label `algebra-of-space.md:88`):
````
julia> a = v1+v2+v3
1v₁ + 1v₂ + 1v₃

julia> n = 3v1
3v₁

julia> inv(n)*a*n
1.0v₁ - 1.0v₂ - 1.0v₃ + 0.0v₁₂₃

julia> n\a*n
1.0v₁ - 1.0v₂ - 1.0v₃ + 0.0v₁₂₃
````

#### rotations
Status: **NEW**
Doc source `docs/src/tutorials/algebra-of-space.md:96-114` (verbatim):
````
## Rotations

A vector can be rotated using the formula ``a\mapsto \tilde R aR``, where `R` is a rotor. A rotor can be defined by multiple reflections, ``R = mn`` or by a plane and an angle ``R = e^{\theta B/2}``.
For example,
```@repl ga
R = exp(π/4*v12)
~R*v1*R
```
Maybe we want to define a function which can return rotor of some angle ``\theta`` in the ``v_{12}``-plane, ``R_{12} = e^{\theta v_{12}/2}``
```@example ga
R12(θ) = exp(θ/2*v12)
nothing # hide
```
And use it like this
```@repl ga
R = R12(π/2)
a = v1+v2+v3
~R*a*R
```
````
Oracle transcript (Grassmann 0.8.46, label `algebra-of-space.md:100`):
````
julia> R = exp(π/4*v12)
0.7071067811865476 + 0.7071067811865475v₁₂

julia> ~R*v1*R
2.22045e-16v₁ + 1.0v₂ + 0.0v₃ + 0.0v₁₂₃
````
Oracle transcript (Grassmann 0.8.46, label `algebra-of-space.md:105`):
````
julia> R12(θ) = exp(θ/2*v12)
R12 (generic function with 1 method)

julia> R = R12(π/2)
0.7071067811865476 + 0.7071067811865475v₁₂

julia> a = v1+v2+v3
1v₁ + 1v₂ + 1v₃

julia> ~R*a*R
-1.0v₁ + 1.0v₂ + 1.0v₃ + 0.0v₁₂₃
````

#### rotors from bivectors
Status: **NEW**
Doc source `docs/src/tutorials/algebra-of-space.md:115-128` (verbatim):
````
You might as well make the angle argument a bivector, so that you can control the plane of rotation as well as the angle
```@example ga
R_B(B) = exp(B/2)
nothing # hide
```
Then you could do
```@repl ga
Rxy = R_B(π/4*v12)
Ryz = R_B(π/5*v23)
```
or
```@repl ga
R_B(π/6*(v23+v12))
```
````
Oracle transcript (Grassmann 0.8.46, label `algebra-of-space.md:116`):
````
julia> R_B(B) = exp(B/2)
R_B (generic function with 1 method)

julia> Rxy = R_B(π/4*v12)
0.9238795325112867 + 0.3826834323650898v₁₂

julia> Ryz = R_B(π/5*v23)
0.9510565162951535 + 0.3090169943749474v₂₃

julia> R_B(π/6*(v23+v12))
0.93224 + 0.255859v₁₂ + 0.0v₁₃ + 0.255859v₂₃
````

#### rotor factories
Status: **NEW** — `R(a)` uses `a = v1+v2+v3` from the previous block. Closure names (`#R_factory##0`) are Julia-specific, not goldens.
Doc source `docs/src/tutorials/algebra-of-space.md:129-149` (verbatim):
````
Maybe you want to define a function which returns a *function* that enacts a specified rotation, ``f(B) = a\mapsto e^{B/2}\\ae^{B/2}``.
This just saves you having to write out the sandwich product, which is nice if you are cascading a bunch of rotors, like so
```@example ga
R_factory(B) = (R = exp(B/2); a -> ~R*a*R)
Rxy = R_factory(π/3*v12)
Ryz = R_factory(π/3*v23)
Rxz = R_factory(π/3*v13)
nothing # hide
```
Then you can do things like
```@repl ga
R = R_factory(π/6*(v23+v12)) # this returns a function
R(a) # which acts on a vector
Rxy(Ryz(Rxz(a)))
```
To make cascading a sequence of rotations as concise as possible, we could define a function which takes a list of bivectors ``A,B,C,...``, and enacts the sequence of rotations which they represent on some vector ``x``.
```@repl ga
R_seq(args...) = (R = prod(exp.(args./2)); a -> ~R*a*R)
R = R_seq(π/2*v23, π/2*v12, v1)
R(v1)
```
````
Oracle transcript (Grassmann 0.8.46, label `algebra-of-space.md:131`):
````
julia> R_factory(B) = (R = exp(B/2); a -> ~R*a*R)
R_factory (generic function with 1 method)

julia> Rxy = R_factory(π/3*v12)
#R_factory##0 (generic function with 1 method)

julia> Ryz = R_factory(π/3*v23)
#R_factory##0 (generic function with 1 method)

julia> Rxz = R_factory(π/3*v13)
#R_factory##0 (generic function with 1 method)

julia> R = R_factory(π/6*(v23+v12))
#R_factory##0 (generic function with 1 method)

julia> R(a)
0.522956v₁ + 0.738144v₂ + 1.47704v₃ + 0.0v₁₂₃

julia> Rxy(Ryz(Rxz(a)))
0.408494v₁ - 0.658494v₂ + 1.54904v₃ + 0.0v₁₂₃
````
Oracle transcript (Grassmann 0.8.46, label `algebra-of-space.md:145`):
````
julia> R_seq(args...) = (R = prod(exp.(args./2)); a -> ~R*a*R)
R_seq (generic function with 1 method)

julia> R = R_seq(π/2*v23, π/2*v12, v1)
#R_seq##0 (generic function with 1 method)

julia> R(v1)
2.22045e-16 + 3.33067e-16v₁ + 1.0v₂ + 5.55112e-17v₂₃
````

#### barycentric coordinates
Status: **NEW** — division of bivectors yields Spinors with `- 0.0v₂₃` (signed zero) terms.
Doc source `docs/src/tutorials/algebra-of-space.md:151-163` (verbatim):
````
## Barycentric Coordinates

We can find the barycentric coordinates of a point in a triangle using area ratios.
```@repl ga
function barycoords(p, a, b, c)
  ab = b-a
  ca = a-c
  bc = c-b
  A = -ab∧ca
  (bc∧(p-b)/A, ca∧(p-c)/A, ab∧(p-a)/A)
end
barycoords(0.25v1+0.25v2, 0v1, 1v1, 1v2)
```
````
Oracle transcript (Grassmann 0.8.46, label `algebra-of-space.md:154`):
````
julia> function barycoords(p, a, b, c)
         ab = b-a
         ca = a-c
         bc = c-b
         A = -ab∧ca
         (bc∧(p-b)/A, ca∧(p-c)/A, ab∧(p-a)/A)
       end
barycoords (generic function with 1 method)

julia> barycoords(0.25v1+0.25v2, 0v1, 1v1, 1v2)
(0.5 + 0.0v₁₂ + 0.0v₁₃ - 0.0v₂₃, 0.25 + 0.0v₁₂ + 0.0v₁₃ - 0.0v₂₃, 0.25 + 0.0v₁₂ + 0.0v₁₃ - 0.0v₂₃)
````

### 6.7 docs/src/tutorials/dyadic-tensors.md (orphan page, not in make.jl)

#### random nested dyadic (non-deterministic)
Status: **NOT-RUNNABLE (random) → deterministic variant** — tridiagonal 5×5 in ⟨+-+++⟩ solved with `\` as golden.
Doc source `docs/src/tutorials/dyadic-tensors.md:11-15` (verbatim):
````
```@repl ga5
using Grassmann, StaticArrays; basis"+-+++"
value(rand(Chain{V,1,Chain{V,1}}))
A = Chain{V,1}(rand(SMatrix{5,5}))
```
````
Oracle transcript (Grassmann 0.8.46, label `dyadic-tensors.md:12 (deterministic variant)`):
````
julia> basis"+-+++"
(⟨+-+++⟩, v, v₁, v₂, v₃, v₄, v₅, v₁₂, v₁₃, v₁₄, v₁₅, v₂₃, v₂₄, v₂₅, v₃₄, v₃₅, v₄₅, v₁₂₃, v₁₂₄, v₁₂₅, v₁₃₄, v₁₃₅, v₁₄₅, v₂₃₄, v₂₃₅, v₂₄₅, v₃₄₅, v₁₂₃₄, v₁₂₃₅, v₁₂₄₅, v₁₃₄₅, v₂₃₄₅, v₁₂₃₄₅)

julia> M = Chain{V,1}(Chain{V,1}(2.0,1,0,0,0),Chain{V,1}(1.0,3,1,0,0),Chain{V,1}(0.0,1,4,1,0),Chain{V,1}(0.0,0,1,5,1),Chain{V,1}(0.0,0,0,1,6))
(2.0v₁+1.0v₂+0.0v₃+0.0v₄+0.0v₅)v₁ + (1.0v₁+3.0v₂+1.0v₃+0.0v₄+0.0v₅)v₂ + (0.0v₁+1.0v₂+4.0v₃+1.0v₄+0.0v₅)v₃ + (0.0v₁+0.0v₂+1.0v₃+5.0v₄+1.0v₅)v₄ + (0.0v₁+0.0v₂+0.0v₃+1.0v₄+6.0v₅)v₅

julia> M\(v1+2v2+3v3+4v4+5v5)
0.302846v₁ + 0.394309v₂ + 0.514228v₃ + 0.54878v₄ + 0.74187v₅
````

#### Cramer generator + generated A\b
Status: **SPEC** — metaprogramming recipe; the generated code (lines 44-50) is the algorithm spec of §4.12.
Doc source `docs/src/tutorials/dyadic-tensors.md:19-52` (verbatim):
````
Programming the `A\b` method is straight forward with some Julia language metaprogramming and Grassmann.jl by first instantiating some Cramer symbols

```@repl ga5
Base.@pure function Grassmann.Cramer(N::Int)
    x,y = SVector{N}([Symbol(:x,i) for i ∈ 1:N]),SVector{N}([Symbol(:y,i) for i ∈ 1:N])
    xy = [:(($(x[1+i]),$(y[1+i])) = ($(x[i])∧t[$(1+i)],t[end-$i]∧$(y[i]))) for i ∈ 1:N-1]
    return x,y,xy
end
```

These are exterior product variants of the Cramer determinant symbols ($N!$ times $N$-simplex hypervolumes), which can be combined to directly solve a linear system:

```@repl ga5
@generated function Base.:\(t::Chain{V,1,<:Chain{V,1}},v::Chain{V,1}) where V
    N = ndims(V)-1 # paste this into the REPL for faster eval
    x,y,xy = Grassmann.Cramer(N)
    mid = [:($(x[i])∧v∧$(y[end-i])) for i ∈ 1:N-1]
    out = Expr(:call,:SVector,:(v∧$(y[end])),mid...,:($(x[end])∧v))
    return Expr(:block,:((x1,y1)=(t[1],t[end])),xy...,
        :(Chain{V,1}(getindex.($(Expr(:call,:./,out,:(t[1]∧$(y[end])))),1))))
end
```

Which results in the following highly efficient `@generated` code for solving the linear system,

```Julia
(x1, y1) = (t[1], t[end])
(x2, y2) = (x1 ∧ t[2], t[end - 1] ∧ y1)
(x3, y3) = (x2 ∧ t[3], t[end - 2] ∧ y2)
(x4, y4) = (x3 ∧ t[4], t[end - 3] ∧ y3)
Chain{V, 1}(getindex.(SVector(v ∧ y4, (x1 ∧ v) ∧ y3, (x2 ∧ v) ∧ y2, (x3 ∧ v) ∧ y1, x4 ∧ v) ./ (t[1] ∧ y4), 1))
```

Benchmarks with that algebra indicate a $3\times$ faster performance than `SMatrix` for applying `A\b` to bundles of dyadic elements.
````

#### benchmarks
Status: **NOT-RUNNABLE (random + timing)** — use as perf target only: Grassmann `A\b` 72 ns vs SMatrix 151 ns for 5×5; bundle of 10k: 0.81 ms vs 2.59 ms.
Doc source `docs/src/tutorials/dyadic-tensors.md:54-75` (verbatim):
````
```Julia
julia> @btime $(rand(SMatrix{5,5},10000)).\Ref($(SVector(1,2,3,4,5)));
  2.588 ms (29496 allocations: 1.44 MiB)

julia> @btime $(Chain{V,1}.(rand(SMatrix{5,5},10000))).\$(v1+2v2+3v3+4v4+5v5);
  808.631 μs (2 allocations: 390.70 KiB)

julia> @btime $(SMatrix(A))\$(SVector(1,2,3,4,5))
  150.663 ns (0 allocations: 0 bytes)
5-element SArray{Tuple{5},Float64,1,5} with indices SOneTo(5):
 -4.783720495603508
  6.034887114999602
  1.017847212237964
  6.379374861538397
 -4.158116538111051

julia> @btime $A\$(v1+2v2+3v3+4v4+5v5)
  72.405 ns (0 allocations: 0 bytes)
-4.783720495603519v₁ + 6.034887114999605v₂ + 1.017847212237964v₃ + 6.379374861538393v₄ - 4.1581165381110505v₅
```

Such a solution is not only more efficient than Julia's [StaticArrays.jl](https://github.com/JuliaArrays/StaticArrays.jl) method for `SMatrix`, but is also useful to minimize allocations in Grassmann.jl finite element assembly.
````

#### simplex membership / inverse / Frobenius
Status: **NEW** — `sqrt(T:T) == norm(SMatrix(T))` needs StaticArrays; oracle shows `T:T = 5v`, `sqrt(T:T) = 2.23606797749979v`.
Doc source `docs/src/tutorials/dyadic-tensors.md:83-94` (verbatim):
````
```@repl ga3
using Grassmann; @basis ℝ3
T = Chain{V,1}(Chain(v1),v1+v2,v1+v3)
barycenter(T) ∈ T, (v1+v2+v3) ∈ T
```

Of course, there are multiple equivalent ways of computing the same results using the `⋅` and `:` dyadic products.

```@repl ga3
T\barycenter(T) == inv(T)⋅barycenter(T)
sqrt(T:T) == norm(SMatrix(T))
```
````
Oracle transcript (Grassmann 0.8.46, label `dyadic-tensors.md:83`):
````
julia> @basis ℝ3
(⟨111⟩, v, v₁, v₂, v₃, v₁₂, v₁₃, v₂₃, v₁₂₃)

julia> T = Chain{V,1}(Chain(v1),v1+v2,v1+v3)
(1v₁+0v₂+0v₃)v₁ + (1v₁+1v₂+0v₃)v₂ + (1v₁+0v₂+1v₃)v₃

julia> barycenter(T) ∈ T, (v1+v2+v3) ∈ T
(true, false)

julia> barycenter(T)
3v₁ + 1v₂ + 1v₃

julia> T\barycenter(T) == inv(T)⋅barycenter(T)
true

julia> T\barycenter(T)
1.0v₁ + 1.0v₂ + 1.0v₃

julia> inv(T)
(1.0v₁+0.0v₂+0.0v₃)v₁ + (-1.0v₁+1.0v₂-0.0v₃)v₂ + (-1.0v₁+0.0v₂+1.0v₃)v₃

julia> T:T
5v

julia> sqrt(T:T)
2.23606797749979v
````

#### Λ(ℝ3) and its dual
Status: **NEW** — note `Λ(ℝ3)'` = `⟨---⟩'` (dual of the Int-based space still flips to `-`).
Doc source `docs/src/tutorials/dyadic-tensors.md:100-107` (verbatim):
````
Note that `Λ(ℝ3)` gives the vector basis, and `Λ(ℝ3)'` gives the covector basis:
```@setup ga
using Grassmann
```
```@repl ga
Λ(ℝ3)
Λ(ℝ3)'
```
````
Oracle transcript (Grassmann 0.8.46, label `dyadic-tensors.md:104`):
````
julia> Λ(ℝ3)
DirectSum.Basis{⟨111⟩,8}(v, v₁, v₂, v₃, v₁₂, v₁₃, v₂₃, v₁₂₃)

julia> Λ(ℝ3)'
DirectSum.Basis{⟨---⟩',8}(w, w¹, w², w³, w¹², w¹³, w²³, w¹²³)
````

#### mother algebra forms
Status: **BROKEN/DIFF** — intended: `(w1+2w2)(v1+v2) = 3v`, `ℒ(v1+v2) = 7v₁ + 14v₂` (runtests.jl:6, commented out; matrix check `[1,2]*[3,4]'*[1,1] = [7,14]`). Oracle: `0v` and `0v₁ + 0v₂ + 9w¹ + 12w²`. Cause: `@mixedbasis` (DirectSum basis.jl:122-126) re-binds `v…` to the base space V and `w…` to V', so `v1*w1` errors `cannot convert from ⟨11⟩ to ⟨++--⟩*` (probe `dual basis products`). The port should implement the intended evaluation semantics.
Doc source `docs/src/tutorials/dyadic-tensors.md:108-125` (verbatim):
````
The following command yields a local 2D vector and covector basis,
```@repl ga
@mixedbasis ℝ2
w1+2w2
ans(v1+v2)
```
The sum `w1+2w2` is interpreted as a covector element of the dual vector space, which can be evaluated as a linear functional when a vector argument is input.
Using these in the workspace, it is possible to use the Grassmann exterior ``\wedge``-tensor product operation to construct elements `ℒ` of the dyadic (1,1)-bivector subspace of linear transformations from the mother algebra.
```@repl ga
ℒ = (v1+2v2)∧(3w1+4w2)
```
The element `ℒ` is a linear form which can be evaluated,
```@repl ga
ℒ(v1+v2)
L = [1,2] * [3,4]'; L * [1,1]
```
which is a computation equivalent to a matrix computation.

````
Oracle transcript (Grassmann 0.8.46, label `dyadic-tensors.md:109`):
````
julia> @mixedbasis ℝ2
(⟨++--⟩*, v, v₁, v₂, w¹, w², v₁₂, v₁w¹, v₁w², v₂w¹, v₂w², w¹², v₁₂w¹, v₁₂w², v₁w¹², v₂w¹², v₁₂w¹²)

julia> w1+2w2
1w¹ + 2w²

julia> ans(v1+v2)
0v

julia> ℒ = (v1+2v2)∧(3w1+4w2)
0v₁₂ + 3v₁w¹ + 4v₁w² + 6v₂w¹ + 8v₂w² + 0w¹²

julia> ℒ(v1+v2)
0v₁ + 0v₂ + 9w¹ + 12w²

julia> L = [1,2] * [3,4]'; L * [1,1]
2-element Vector{Int64}:
  7
 14
````

#### Leech lattice
Status: **BROKEN** — `Chain{Submanifold(W24),Float64}(matrix)` has no method on 0.8.46 (`binomial(::Int, ::Type{Float64})`). Doc outputs are the intended goldens: `typeof(Leech) = Chain{⟨+×24 -×24⟩*,2,Float64,1128}`, `ndims(Manifold(Leech)) = 48`, `Leech(E24.v1) = 2.82842712474619v₁ + …`, `ans⋅ans = 39.99999999999999v`, `Leech(E24.v2+E24.v5)⋅itself = 7.499999999999998v`. Also demonstrates labels past 9: `v₀ va … vn`, `w⁰ wA … wN`.
Doc source `docs/src/tutorials/dyadic-tensors.md:128-198` (verbatim):
````
### Importing the Leech lattice generator

In the example below, we define a constant `Leech` which can be used to obtain linear combinations of the Leech lattice,
```julia
julia> using Grassmann

julia> generator = [8 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0;
       4 4 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0;
       4 0 4 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0;
       4 0 0 4 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0;
       4 0 0 0 4 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0;
       4 0 0 0 0 4 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0;
       4 0 0 0 0 0 4 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0;
       2 2 2 2 2 2 2 2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0;
       4 0 0 0 0 0 0 0 4 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0;
       4 0 0 0 0 0 0 0 0 4 0 0 0 0 0 0 0 0 0 0 0 0 0 0;
       4 0 0 0 0 0 0 0 0 0 4 0 0 0 0 0 0 0 0 0 0 0 0 0;
       2 2 2 2 0 0 0 0 2 2 2 2 0 0 0 0 0 0 0 0 0 0 0 0;
       4 0 0 0 0 0 0 0 0 0 0 0 4 0 0 0 0 0 0 0 0 0 0 0;
       2 2 0 0 2 2 0 0 2 2 0 0 2 2 0 0 0 0 0 0 0 0 0 0;
       2 0 2 0 2 0 2 0 2 0 2 0 2 0 2 0 0 0 0 0 0 0 0 0;
       2 0 0 2 2 0 0 2 2 0 0 2 2 0 0 2 0 0 0 0 0 0 0 0;
       4 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 4 0 0 0 0 0 0 0;
       2 0 2 0 2 0 0 2 2 2 0 0 0 0 0 0 2 2 0 0 0 0 0 0;
       2 0 0 2 2 2 0 0 2 0 2 0 0 0 0 0 2 0 2 0 0 0 0 0;
       2 2 0 0 2 0 2 0 2 0 0 2 0 0 0 0 2 0 0 2 0 0 0 0;
       0 2 2 2 2 0 0 0 2 0 0 0 2 0 0 0 2 0 0 0 2 0 0 0;
       0 0 0 0 0 0 0 0 2 2 0 0 2 2 0 0 2 2 0 0 2 2 0 0;
       0 0 0 0 0 0 0 0 2 0 2 0 2 0 2 0 2 0 2 0 2 0 2 0;
       -3 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1]

julia> const E24,W24 = Λ(24), ℝ^24⊕(ℝ^24)';

julia> const Leech = Chain{Submanifold(W24),Float64}(generator./sqrt(8));

julia> typeof(Leech)
Chain{⟨++++++++++++++++++++++++------------------------⟩*,2,Float64,1128}

julia> ndims(Manifold(Leech))
48
```
The `Leech` generator matrix is contained in the 1128-dimensional bivector subalgebra of the space with 48 indices.
```julia
julia> Leech(E24.v1)
2.82842712474619v₁ + 0.0v₂ + 0.0v₃ + 0.0v₄ + 0.0v₅ + 0.0v₆ + 0.0v₇ + 0.0v₈ + 0.0v₉ + 0.0v₀ + 0.0va + 0.0vb + 0.0vc + 0.0vd + 0.0ve + 0.0vf + 0.0vg + 0.0vh + 0.0vi + 0.0vj + 0.0vk + 0.0vl + 0.0vm + 0.0vn + 0.0w¹ + 0.0w² + 0.0w³ + 0.0w⁴ + 0.0w⁵ + 0.0w⁶ + 0.0w⁷ + 0.0w⁸ + 0.0w⁹ + 0.0w⁰ + 0.0wA + 0.0wB + 0.0wC + 0.0wD + 0.0wE + 0.0wF + 0.0wG + 0.0wH + 0.0wI + 0.0wJ + 0.0wK + 0.0wL + 0.0wM + 0.0wN

julia> Leech(E24.v2)
1.414213562373095v₁ + 1.414213562373095v₂ + 0.0v₃ + 0.0v₄ + 0.0v₅ + 0.0v₆ + 0.0v₇ + 0.0v₈ + 0.0v₉ + 0.0v₀ + 0.0va + 0.0vb + 0.0vc + 0.0vd + 0.0ve + 0.0vf + 0.0vg + 0.0vh + 0.0vi + 0.0vj + 0.0vk + 0.0vl + 0.0vm + 0.0vn + 0.0w¹ + 0.0w² + 0.0w³ + 0.0w⁴ + 0.0w⁵ + 0.0w⁶ + 0.0w⁷ + 0.0w⁸ + 0.0w⁹ + 0.0w⁰ + 0.0wA + 0.0wB + 0.0wC + 0.0wD + 0.0wE + 0.0wF + 0.0wG + 0.0wH + 0.0wI + 0.0wJ + 0.0wK + 0.0wL + 0.0wM + 0.0wN

julia> Leech(E24.v3)
1.414213562373095v₁ + 0.0v₂ + 1.414213562373095v₃ + 0.0v₄ + 0.0v₅ + 0.0v₆ + 0.0v₇ + 0.0v₈ + 0.0v₉ + 0.0v₀ + 0.0va + 0.0vb + 0.0vc + 0.0vd + 0.0ve + 0.0vf + 0.0vg + 0.0vh + 0.0vi + 0.0vj + 0.0vk + 0.0vl + 0.0vm + 0.0vn + 0.0w¹ + 0.0w² + 0.0w³ + 0.0w⁴ + 0.0w⁵ + 0.0w⁶ + 0.0w⁷ + 0.0w⁸ + 0.0w⁹ + 0.0w⁰ + 0.0wA + 0.0wB + 0.0wC + 0.0wD + 0.0wE + 0.0wF + 0.0wG + 0.0wH + 0.0wI + 0.0wJ + 0.0wK + 0.0wL + 0.0wM + 0.0wN

...
```
Then a `TensorAlgebra` evaluation of `Leech` at an `Integer` linear combination would be
```julia
julia> Leech(E24.v1 + 2*E24.v2)
5.65685424949238v₁ + 2.82842712474619v₂ + 0.0v₃ + 0.0v₄ + 0.0v₅ + 0.0v₆ + 0.0v₇ + 0.0v₈ + 0.0v₉ + 0.0v₀ + 0.0va + 0.0vb + 0.0vc + 0.0vd + 0.0ve + 0.0vf + 0.0vg + 0.0vh + 0.0vi + 0.0vj + 0.0vk + 0.0vl + 0.0vm + 0.0vn + 0.0w¹ + 0.0w² + 0.0w³ + 0.0w⁴ + 0.0w⁵ + 0.0w⁶ + 0.0w⁷ + 0.0w⁸ + 0.0w⁹ + 0.0w⁰ + 0.0wA + 0.0wB + 0.0wC + 0.0wD + 0.0wE + 0.0wF + 0.0wG + 0.0wH + 0.0wI + 0.0wJ + 0.0wK + 0.0wL + 0.0wM + 0.0wN

julia> ans⋅ans
39.99999999999999v

julia> Leech(E24.v2 + E24.v5)
2.82842712474619v₁ + 1.414213562373095v₂ + 0.0v₃ + 0.0v₄ + 0.0v₅ + 0.0v₆ + 0.0v₇ + 0.0v₈ + 0.0v₉ + 0.0v₀ + 1.414213562373095va + 0.0vb + 0.0vc + 0.0vd + 0.0ve + 0.0vf + 0.0vg + 0.0vh + 0.0vi + 0.0vj + 0.0vk + 0.0vl + 0.0vm + 0.0vn + 0.0w¹ + 0.7071067811865475w² + 1.414213562373095w³ + 1.414213562373095w⁴ + 0.0w⁵ + 0.0w⁶ + 0.0w⁷ + 0.0w⁸ + 0.0w⁹ + 0.0w⁰ + 0.0wA + 0.0wB + 0.0wC + 0.0wD + 0.0wE + 0.0wF + 0.0wG + 0.0wH + 0.0wI + 0.0wJ + 0.0wK + 0.0wL + 0.0wM + 0.0wN

julia> ans⋅ans
7.499999999999998v
```
The `Grassmann` package is designed to smoothly handle high-dimensional bivector algebras with headroom to spare. Although some of these calculations may have an initial delay, repeated calls are fast due to built-in caching and pre-compilation.

In future updates, more emphasis will be placed on increased type-stability with more robust sparse output allocation in the computational graph and minimal footprint but maximal type-stability for intermediate results and output.
````
Oracle transcript (Grassmann 0.8.46, label `dyadic-tensors.md:132 Leech`):
````
julia> generator = [8 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0; 4 4 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0; 4 0 4 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0; 4 0 0 4 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0; 4 0 0 0 4 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0; 4 0 0 0 0 4 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0; 4 0 0 0 0 0 4 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0; 2 2 2 2 2 2 2 2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0; 4 0 0 0 0 0 0 0 4 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0; 4 0 0 0 0 0 0 0 0 4 0 0 0 0 0 0 0 0 0 0 0 0 0 0; 4 0 0 0 0 0 0 0 0 0 4 0 0 0 0 0 0 0 0 0 0 0 0 0; 2 2 2 2 0 0 0 0 2 2 2 2 0 0 0 0 0 0 0 0 0 0 0 0; 4 0 0 0 0 0 0 0 0 0 0 0 4 0 0 0 0 0 0 0 0 0 0 0; 2 2 0 0 2 2 0 0 2 2 0 0 2 2 0 0 0 0 0 0 0 0 0 0; 2 0 2 0 2 0 2 0 2 0 2 0 2 0 2 0 0 0 0 0 0 0 0 0; 2 0 0 2 2 0 0 2 2 0 0 2 2 0 0 2 0 0 0 0 0 0 0 0; 4 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 4 0 0 0 0 0 0 0; 2 0 2 0 2 0 0 2 2 2 0 0 0 0 0 0 2 2 0 0 0 0 0 0; 2 0 0 2 2 2 0 0 2 0 2 0 0 0 0 0 2 0 2 0 0 0 0 0; 2 2 0 0 2 0 2 0 2 0 0 2 0 0 0 0 2 0 0 2 0 0 0 0; 0 2 2 2 2 0 0 0 2 0 0 0 2 0 0 0 2 0 0 0 2 0 0 0; 0 0 0 0 0 0 0 0 2 2 0 0 2 2 0 0 2 2 0 0 2 2 0 0; 0 0 0 0 0 0 0 0 2 0 2 0 2 0 2 0 2 0 2 0 2 0 2 0; -3 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1];

julia> E24,W24 = Λ(24), ℝ^24⊕(ℝ^24)';

julia> Leech = Chain{Submanifold(W24),Float64}(generator./sqrt(8));
ERROR: MethodError: no method matching binomial(::Int64, ::Type{Float64})
The function `binomial` exists, but no method is defined for this combination of argument types.

Closest candidates are:
  binomial(::T, !Matched::T) where T<:Integer
   @ Base intfuncs.jl:1317
  binomial(::Integer, !Matched::Integer)
   @ Base intfuncs.jl:1315
  binomial(::Number, !Matched::Integer)
   @ Base intfuncs.jl:1370
  .

julia> typeof(Leech)
ERROR: UndefVarError: `Leech` not defined in `Main.Sandbox6`
Suggestion: add an appropriate import or assignment. This global was declared but not assigned.

julia> ndims(Manifold(Leech))
ERROR: UndefVarError: `Leech` not defined in `Main.Sandbox6`
Suggestion: add an appropriate import or assignment. This global was declared but not assigned.

julia> Leech(E24.v1)
ERROR: UndefVarError: `Leech` not defined in `Main.Sandbox6`
Suggestion: add an appropriate import or assignment. This global was declared but not assigned.

julia> Leech(E24.v1 + 2*E24.v2)
ERROR: UndefVarError: `Leech` not defined in `Main.Sandbox6`
Suggestion: add an appropriate import or assignment. This global was declared but not assigned.

julia> ans⋅ans
ERROR: StackOverflowError:

julia> Leech(E24.v2 + E24.v5)
ERROR: UndefVarError: `Leech` not defined in `Main.Sandbox6`
Suggestion: add an appropriate import or assignment. This global was declared but not assigned.

julia> ans⋅ans
ERROR: StackOverflowError:
````

### 6.8 Additional oracle probes (not in docs; golden for display & semantics)

#### display edge cases
Multivector zero hiding and `v⃖`, Rational/Complex parens, `π*v₁`, `Inf*v₁ + NaN*v₂ - 0.0v₃`, compact floats, result-type table.
Oracle transcript (Grassmann 0.8.46, label `display edge cases`):
````
julia> basis"3"
(⟨111⟩, v, v₁, v₂, v₃, v₁₂, v₁₃, v₂₃, v₁₂₃)

julia> Multivector{V}(1,0,0,0,0,0,0,0)
1v⃖

julia> Multivector{V}(0,0,0,0,0,0,0,0)
0v⃖

julia> Multivector{V}(1.5,0,0,0,0,0,0,2.25)
1.5 + 2.25v₁₂₃

julia> Multivector{V}(1,2,3,4,5,6,7,8)
1 + 2v₁ + 3v₂ + 4v₃ + 5v₁₂ + 6v₁₃ + 7v₂₃ + 8v₁₂₃

julia> Multivector{V}(1.0,-2,3,-4,5,-6,7,-8)
1.0 - 2.0v₁ + 3.0v₂ - 4.0v₃ + 5.0v₁₂ - 6.0v₁₃ + 7.0v₂₃ - 8.0v₁₂₃

julia> Chain{V,2}(0,0,0)
0v₁₂ + 0v₁₃ + 0v₂₃

julia> Chain{V,1}(-1,-2,-3)
-1v₁ - 2v₂ - 3v₃

julia> Chain{V,1}(1//2,1//3,1//4)
(1//2)v₁ + (1//3)v₂ + (1//4)v₃

julia> Chain{V,1}(1.0e10,1.0e-10,π)
1.0e10v₁ + 1.0e-10v₂ + 3.14159v₃

julia> Chain{V,1}(1+2im,3im,0)
(1+2im)v₁ + (0+3im)v₂ + (0+0im)v₃

julia> Spinor{V}(0,0,0,0)
0 + 0v₁₂ + 0v₁₃ + 0v₂₃

julia> CoSpinor{V}(1,2,3,4)
1v₁ + 2v₂ + 3v₃ + 4v₁₂₃

julia> 2v1
2v₁

julia> -2v1
-2v₁

julia> 2.5v12
2.5v₁₂

julia> (1+2im)*v1
(1 + 2im)v₁

julia> v
v

julia> -v
-1v

julia> 0v
0v

julia> Zero(V)
𝟎

julia> v1+v
1 + 1v₁

julia> v12+1.5
1.5 + 1.0v₁₂

julia> v123+3
3 + 1v₁₂₃

julia> 3v123+2v1
2v₁ + 3v₁₂₃

julia> typeof(3v123+2v1)
PseudoCouple{⟨111⟩, v₁, Int64}

julia> typeof(2v1+3v2)
Chain{⟨111⟩, 1, Int64, 3}

julia> typeof(1+v12)
GaussianInteger{⟨111⟩, v₁₂, Int64} (alias for Couple{⟨111⟩, v₁₂, Int64})

julia> typeof(1+v123)
GaussianInteger{⟨111⟩, v₁₂₃, Int64} (alias for Couple{⟨111⟩, v₁₂₃, Int64})

julia> typeof(v1+v123)
PseudoCouple{⟨111⟩, v₁, Int64}

julia> typeof(v1+v12)
Multivector{⟨111⟩, Int64, 8}

julia> typeof(v+v1+v12+v123)
Multivector{⟨111⟩, Int64, 8}

julia> π*v1
π*v₁

julia> Chain{V,1}(Inf,NaN,-0.0)
Inf*v₁ + NaN*v₂ - 0.0v₃
````

#### grade/ops probes
all involutions/parts/products on `Multivector(1..8)` in ⟨111⟩ (norm/metric/abs errors in this sandbox came from name clashes with LinearAlgebra/Leibniz imports; see `norms/metrics`).
Oracle transcript (Grassmann 0.8.46, label `grade/ops probes`):
````
julia> A = Multivector{V}(1,2,3,4,5,6,7,8)
1 + 2v₁ + 3v₂ + 4v₃ + 5v₁₂ + 6v₁₃ + 7v₂₃ + 8v₁₂₃

julia> grade(v12), grade(2v12), grade(A,2)
(2, 2, 5v₁₂ + 6v₁₃ + 7v₂₃)

julia> A(0), A(1), A(2), A(3)
(1v, 2v₁ + 3v₂ + 4v₃, 5v₁₂ + 6v₁₃ + 7v₂₃, 8v₁₂₃)

julia> scalar(A), vector(A), bivector(A), trivector(A), pseudoscalar(A)
(1v, 2v₁ + 3v₂ + 4v₃, 5v₁₂ + 6v₁₃ + 7v₂₃, 8v₁₂₃, 8v₁₂₃)

julia> ~A
1 + 2v₁ + 3v₂ + 4v₃ - 5v₁₂ - 6v₁₃ - 7v₂₃ - 8v₁₂₃

julia> reverse(A)
1 + 2v₁ + 3v₂ + 4v₃ - 5v₁₂ - 6v₁₃ - 7v₂₃ - 8v₁₂₃

julia> involute(A)
1 - 2v₁ - 3v₂ - 4v₃ + 5v₁₂ + 6v₁₃ + 7v₂₃ - 8v₁₂₃

julia> clifford(A)
1 - 2v₁ - 3v₂ - 4v₃ - 5v₁₂ - 6v₁₃ - 7v₂₃ + 8v₁₂₃

julia> conj(A)
1 + 2v₁ + 3v₂ + 4v₃ - 5v₁₂ - 6v₁₃ - 7v₂₃ - 8v₁₂₃

julia> even(A)
1 + 5v₁₂ + 6v₁₃ + 7v₂₃

julia> odd(A)
2v₁ + 3v₂ + 4v₃ + 8v₁₂₃

julia> real(A)
1 + 2v₁ + 3v₂ + 4v₃

julia> imag(A)
0 + 5v₁₂ + 6v₁₃ + 7v₂₃ + 8v₁₂₃

julia> abs2(A)
204 + 38v₁ - 126v₂ + 154v₃

julia> norm(A)
ERROR: UndefVarError: `norm` not defined in `Main.Sandbox1`
Hint: It looks like two or more modules export different bindings with this name, resulting in ambiguity. Try explicitly importing it from a particular module, or qualifying the name with the module it should come from.
Hint: a global variable of this name also exists in LinearAlgebra.
    - Also exported by Grassmann.
Hint: a global variable of

julia> abs(A)
ERROR: inv(205 + 38v₁ - 126v₂ + 154v₃) is undefined

julia> !A
8 + 7v₁ - 6v₂ + 5v₃ + 4v₁₂ - 3v₁₃ + 2v₂₃ + 1v₁₂₃

julia> ⋆A
8 + 7v₁ - 6v₂ + 5v₃ + 4v₁₂ - 3v₁₃ + 2v₂₃ + 1v₁₂₃

julia> A∧A
1 + 4v₁ + 6v₂ + 8v₃ + 10v₁₂ + 12v₁₃ + 14v₂₃ + 48v₁₂₃

julia> A∨A
48 + 32v₁ + 48v₂ + 64v₃ + 80v₁₂ + 96v₁₃ + 112v₂₃ + 64v₁₂₃

julia> A*A
-144 - 108v₁ + 102v₂ - 72v₃ + 74v₁₂ - 36v₁₃ + 46v₂₃ + 48v₁₂₃

julia> A⋅A
204 + 19v₁ - 63v₂ + 77v₃ + 37v₁₂ - 18v₁₃ + 23v₂₃ + 8v₁₂₃

julia> A|A
204 + 19v₁ - 63v₂ + 77v₃ + 37v₁₂ - 18v₁₃ + 23v₂₃ + 8v₁₂₃

julia> A>A
204 + 19v₁ - 63v₂ + 77v₃ + 37v₁₂ - 18v₁₃ + 23v₂₃ + 8v₁₂₃

julia> A<A
204 + 19v₁ - 63v₂ + 77v₃ + 37v₁₂ - 18v₁₃ + 23v₂₃ + 8v₁₂₃

julia> A>>A
-144 - 15v₁ + 69v₂ - 69v₃ - 37v₁₂ + 18v₁₃ - 23v₂₃ - 8v₁₂₃

julia> A<<A
-144 - 93v₁ + 33v₂ - 3v₃ + 37v₁₂ - 18v₁₃ + 23v₂₃ + 8v₁₂₃

julia> inv(A)
ERROR: inv(1 + 2v₁ + 3v₂ + 4v₃ + 5v₁₂ + 6v₁₃ + 7v₂₃ + 8v₁₂₃) is undefined

julia> A/A
ERROR: inv(1 + 2v₁ + 3v₂ + 4v₃ + 5v₁₂ + 6v₁₃ + 7v₂₃ + 8v₁₂₃) is undefined

julia> A*inv(A)
ERROR: inv(1 + 2v₁ + 3v₂ + 4v₃ + 5v₁₂ + 6v₁₃ + 7v₂₃ + 8v₁₂₃) is undefined

julia> exp(v12)
0.5403023058681398 + 0.8414709848078965v₁₂

julia> exp(2v12+v13)
-0.617273 + 0.70369v₁₂ + 0.351845v₁₃ + 0.0v₂₃

julia> log(exp(0.5v12))
4.163336342344337e-17 + 0.5v₁₂

julia> sqrt(4+v12)
2.015329455153383 + 0.24809839340235612v₁₂

julia> metric(A)
ERROR: UndefVarError: `metric` not defined in `Main.Sandbox1`
Hint: It looks like two or more modules export different bindings with this name, resulting in ambiguity. Try explicitly importing it from a particular module, or qualifying the name with the module it should come from.
Hint: a global variable of this name also exists in AbstractTensors.
Hint: a global variable of this name also exists in Leib

julia> cometric(A)
1 + 2v₁ + 3v₂ + 4v₃ + 5v₁₂ + 6v₁₃ + 7v₂₃ + 8v₁₂₃

julia> mdims(A), gdims(A), tdims(A)
ERROR: MethodError: no method matching gdims(::Multivector{⟨111⟩, Int64, 8})
The function `gdims` exists, but no method is defined for this combination of argument types.

Closest candidates are:
  gdims(::Any, !Matched::Any)
   @ AbstractTensors ~/.julia/packages/AbstractTensors/2D9Ks/src/AbstractTensors.jl:181
  gdims(!Matched::DirectSum.Grade{N, N}, !Matched::DirectSum.Grade{N, G}) where {N, G}
  
````

#### norms/metrics
Oracle transcript (Grassmann 0.8.46, label `norms/metrics`):
````
julia> basis"3"
(⟨111⟩, v, v₁, v₂, v₃, v₁₂, v₁₃, v₂₃, v₁₂₃)

julia> A = Multivector{V}(1,2,3,4,5,6,7,8)
1 + 2v₁ + 3v₂ + 4v₃ + 5v₁₂ + 6v₁₃ + 7v₂₃ + 8v₁₂₃

julia> norm(A)
14.2828568570857

julia> metric(A)
1 + 2v₁ + 3v₂ + 4v₃ + 5v₁₂ + 6v₁₃ + 7v₂₃ + 8v₁₂₃

julia> mdims(A), gdims(A,2), tdims(A)
ERROR: MethodError: Multivector{⟨111⟩, Int64, 8}(::Multivector{⟨111⟩, Int64, 8}) is ambiguous.

Candidates:
  (::Type{T})(x...) where T<:Multivector
    @ Grassmann ~/.julia/packages/Grassmann/x3Md4/src/multivectors.jl:275
  (::Type{T})(x::T) where T<:Number
    @ Core boot.jl:1018

Possible fix, define
  (::Type{T})(::Multivector) where T<:Multivector


julia> a = 1v1+2v2+3v3
1v₁ + 2v₂ + 3v₃

julia> abs(a), abs2(a), norm(a), unit(a)
(3.7416573867739413v, 14v, 3.7416573867739413, 0.267261v₁ + 0.534522v₂ + 0.801784v₃)

julia> inv(a)
0.0714286v₁ + 0.142857v₂ + 0.214286v₃

julia> a/a
1.0 + 0.0v₁₂ + 0.0v₁₃ + 0.0v₂₃

julia> inv(1+v12)
0.5 - 0.5v₁₂

julia> abs(1+v12)
1.4142135623730951v

julia> inv(2+v1)
0.4 - 0.2v₁

julia> B = 1+2v1+3v12
1 + 2v₁ + 3v₁₂

julia> ~B*B
14 + 4v₁ + 12v₂

julia> inv(B)
ERROR: inv(1 + 2v₁ + 3v₁₂) is undefined

julia> B*inv(B)
ERROR: inv(1 + 2v₁ + 3v₁₂) is undefined
````

#### dims
Oracle transcript (Grassmann 0.8.46, label `dims`):
````
julia> basis"3"
(⟨111⟩, v, v₁, v₂, v₃, v₁₂, v₁₃, v₂₃, v₁₂₃)

julia> A = Multivector{V}(1,2,3,4,5,6,7,8)
1 + 2v₁ + 3v₂ + 4v₃ + 5v₁₂ + 6v₁₃ + 7v₂₃ + 8v₁₂₃

julia> mdims(A)
3

julia> gdims(A,2)
ERROR: MethodError: Multivector{⟨111⟩, Int64, 8}(::Multivector{⟨111⟩, Int64, 8}) is ambiguous.

Candidates:
  (::Type{T})(x...) where T<:Multivector
    @ Grassmann ~/.julia/packages/Grassmann/x3Md4/src/multivectors.jl:275
  (::Type{T})(x::T) where T<:Number
    @ Core boot.jl:1018

Possible fix, define
  (::Type{T})(::Multivector) where T<:Multivector


julia> tdims(A)
8

julia> gdims(3,2)
3

julia> tdims(V)
8

julia> Phasor(2.0, π/3)
2.0 ∠ 1.0471975511965976

julia> ∠(1.0,v12)
1.0 ∠ v₁₂

julia> complexify(Phasor(2.0,π/3))
5.699307816452722
````

#### quaternion probes
Oracle transcript (Grassmann 0.8.46, label `quaternion probes`):
````
julia> 𝕚,𝕛,𝕜
(1v₂₃, -1v₁₃, 1v₁₂)

julia> 𝕚*𝕛, 𝕛*𝕜, 𝕜*𝕚
(-1v₁₂, -1v₂₃, 1v₁₃)

julia> q = quaternion(1,2,3,4)
1 + 2v₁₂ - 3v₁₃ + 4v₂₃

julia> quatvalues(q)
4-element Values{4, Int64} with indices SOneTo(4):
 1
 2
 3
 4

julia> R = exp(π/4*𝕜)
0.7071067811865476 + 0.7071067811865475v₁₂

julia> R>>>v1
2.22045e-16v₁ - 1.0v₂ + 0.0v₃

julia> v1⊘R
2.22045e-16v₁ + 1.0v₂ + 0.0v₃

julia> Matrix(operator(R))
3×3 Matrix{Float64}:
 2.22045e-16  -1.0          0.0
 1.0           2.22045e-16  0.0
 0.0           0.0          1.0
````

#### sandwich conventions
Oracle transcript (Grassmann 0.8.46, label `sandwich conventions`):
````
julia> R = exp(π/8*v12)
0.9238795325112867 + 0.3826834323650898v₁₂

julia> R>>>v1
0.707107v₁ - 0.707107v₂ + 0.0v₃

julia> v1⊘R
0.707107v₁ + 0.707107v₂ + 0.0v₃

julia> sandwich(v1,R)
0.707107v₁ + 0.707107v₂ + 0.0v₃

julia> ~R*v1*R
0.707107v₁ + 0.707107v₂ + 0.0v₃ + 0.0v₁₂₃

julia> R*v1*~R
0.707107v₁ - 0.707107v₂ + 0.0v₃ + 0.0v₁₂₃
````

#### sandwich scaling
⊘ / >>> do not normalise (§4.6).
Oracle transcript (Grassmann 0.8.46, label `sandwich scaling`):
````
julia> basis"3"
(⟨111⟩, v, v₁, v₂, v₃, v₁₂, v₁₃, v₂₃, v₁₂₃)

julia> v1⊘(3v1)
-9v₁

julia> (3v1)>>>v1
-9v₁

julia> v2⊘(3v1)
9v₂

julia> v2⊘v1
1v₂

julia> v1>>>v2
1v₂

julia> inv(3v1)*v2*(3v1)
-1.0v₂

julia> exp(π/8*v12)
0.9238795325112867 + 0.3826834323650898v₁₂

julia> exp(π/8*v12)^2
0.7071067811865475 + 0.7071067811865476v₁₂

julia> 2^v12
0.7692389013639721 + 0.6389612763136348v₁₂

julia> v12^2
-1v

julia> (v1+v2)^3
2v₁ + 2v₂ + 0v₃

julia> v12^-1
-1.0v₁₂
````

#### ops wiring
`⊙`/`⊠` broken; prefix `|a` is not parseable.
Oracle transcript (Grassmann 0.8.46, label `ops wiring`):
````
julia> basis"3"
(⟨111⟩, v, v₁, v₂, v₃, v₁₂, v₁₃, v₂₃, v₁₂₃)

julia> a = 1v1+2v2+3v3; b = 4v12+5v13+6v23
4v₁₂ + 5v₁₃ + 6v₂₃

julia> a ⨼ b, a ⨽ b, a < b, a > b
(-23v₁ - 14v₂ + 17v₃, 𝟎, -23v₁ - 14v₂ + 17v₃, 𝟎)

julia> b ⨼ a, b ⨽ a, b < a, b > a
(𝟎, -23v₁ - 14v₂ + 17v₃, 𝟎, -23v₁ - 14v₂ + 17v₃)

julia> a ⊛ a, a ∗ a
(14v, 14 + 0v₁₂ + 0v₁₃ + 0v₂₃)

julia> b ∗ b
77 + 0v₁₂ + 0v₁₃ + 0v₂₃

julia> |a
ERROR: ParseError:
# Error @ none:1:1
|a
╙ ── not a unary operator

julia> a ⟑ b
-23v₁ - 14v₂ + 17v₃ + 8v₁₂₃

julia> a ⊖ b
-23v₁ - 14v₂ + 17v₃ + 8v₁₂₃

julia> a ⊙ b
ERROR: UndefVarError: `permutations` not defined in `Grassmann`
Suggestion: check for spelling errors or missing imports.
Hint: a global variable of this name also exists in Combinatorics.

julia> a ⊠ b
ERROR: UndefVarError: `permutations` not defined in `Grassmann`
Suggestion: check for spelling errors or missing imports.
Hint: a global variable of this name also exists in Combinatorics.

julia> a × (4v1+5v2+6v3)
-3v₁ + 6v₂ - 3v₃

julia> a ∥ 2a
true
````

#### grade selection call syntax
Oracle transcript (Grassmann 0.8.46, label `grade selection call syntax`):
````
julia> basis"3"
(⟨111⟩, v, v₁, v₂, v₃, v₁₂, v₁₃, v₂₃, v₁₂₃)

julia> A = 1 + 2v1 + 3v12 + 4v123
1 + 2v₁ + 3v₁₂ + 4v₁₂₃

julia> A(0), A(1), A(2), A(3)
(1v, 2v₁ + 0v₂ + 0v₃, 3v₁₂ + 0v₁₃ + 0v₂₃, 4v₁₂₃)

julia> grade(A,1)
2v₁ + 0v₂ + 0v₃

julia> A[1], A[2]
([2, 0, 0], [3, 0, 0])

julia> value(A)
8-element Values{8, Int64} with indices SOneTo(8):
 1
 2
 0
 0
 3
 0
 0
 4
````

#### Λ index access
Oracle transcript (Grassmann 0.8.46, label `Λ index access`):
````
julia> Λ(3).v21, Λ(3).v32, Λ(3).v13, Λ(3).v321
(-1v₁₂, -1v₂₃, v₁₃, -1v₁₂₃)

julia> Λ(4).v4321
v₁₂₃₄

julia> Λ(3).b
8-element Values{8, Submanifold{⟨111⟩}} with indices SOneTo(8):
    v
   v₁
   v₂
   v₃
  v₁₂
  v₁₃
  v₂₃
 v₁₂₃

julia> Λ(3)[3]
v₂
````

#### hyperplanes 2D/4D
Oracle transcript (Grassmann 0.8.46, label `hyperplanes 2D/4D`):
````
julia> hyperplanes(ℝ^2)
2-element Vector{Single{⟨++⟩, 1, B, Int64} where B}:
 -1v₂
  1v₁

julia> hyperplanes(ℝ^4)
4-element Vector{Single{⟨++++⟩, 3, B, Int64} where B}:
 -1v₂₃₄
  1v₁₃₄
 -1v₁₂₄
  1v₁₂₃
````

#### signature displays
Oracle transcript (Grassmann 0.8.46, label `signature displays`):
````
julia> S"∞∅+++"
⟨∞∅+++⟩

julia> Submanifold(S"∞∅+++")
⟨∞∅111⟩

julia> S"∞+++"
⟨∞+++⟩

julia> Submanifold(S"∞+++")
⟨∞+++⟩

julia> S"+++"
⟨+++⟩

julia> Submanifold(S"+++")
⟨+++⟩

julia> V"+++"
⟨+++⟩

julia> Submanifold(3)
⟨111⟩

julia> ℝ^3
⟨+++⟩

julia> ℝ3
⟨111⟩

julia> D"1,1,1,0"
⟨1,1,1,0⟩

julia> D"0.3,2.4,1"
⟨0.3,2.4,1.0⟩

julia> S"∅+++"
⟨∅+++⟩

julia> S"-+++"
⟨-+++⟩

julia> tangent(ℝ^3)
T¹⟨+++₁⟩

julia> tangent(ℝ^3,2,3)
T²⟨+++₁₂₃⟩

julia> (ℝ^3)'
⟨---⟩'

julia> ℝ^3⊕(ℝ^3)'
⟨+++---⟩*

julia> Submanifold(ℝ^3⊕(ℝ^3)')
⟨+++---⟩*
````

#### metric-weighted products
Oracle transcript (Grassmann 0.8.46, label `metric-weighted products`):
````
julia> @basis D"2,3,5"
(⟨2,3,5⟩, v, v₁, v₂, v₃, v₁₂, v₁₃, v₂₃, v₁₂₃)

julia> v1*v1, v2*v2, v3*v3
(2v, 3v, 5v)

julia> v12*v12
-6v

julia> v1⋅v1
2v

julia> ⋆v1
2v₂₃

julia> !v1
1v₂₃

julia> hodge(v1)
2v₂₃
````

#### dual basis products
Oracle transcript (Grassmann 0.8.46, label `dual basis products`):
````
julia> @mixedbasis ℝ2
(⟨++--⟩*, v, v₁, v₂, w¹, w², v₁₂, v₁w¹, v₁w², v₂w¹, v₂w², w¹², v₁₂w¹, v₁₂w², v₁w¹², v₂w¹², v₁₂w¹²)

julia> v1*w1
ERROR: cannot convert from ⟨11⟩ to ⟨++--⟩*

julia> w1*v1
ERROR: cannot convert from ⟨11⟩ to ⟨++--⟩*

julia> v1∧w1
ERROR: cannot convert from ⟨11⟩ to ⟨++--⟩*

julia> w1(v1)
ERROR: cannot convert from ⟨11⟩ to ⟨++--⟩*

julia> w1(v2)
ERROR: cannot convert from ⟨11⟩ to ⟨++--⟩*
````

#### dualbasis
Oracle transcript (Grassmann 0.8.46, label `dualbasis`):
````
julia> @dualbasis ℝ^3
(⟨---⟩', w, w¹, w², w³, w¹², w¹³, w²³, w¹²³)

julia> w1*w1
-1w

julia> w12
w¹²
````

#### Grassmann complements n=4
Oracle transcript (Grassmann 0.8.46, label `Grassmann complements n=4`):
````
julia> basis"4"
(⟨1111⟩, v, v₁, v₂, v₃, v₄, v₁₂, v₁₃, v₁₄, v₂₃, v₂₄, v₃₄, v₁₂₃, v₁₂₄, v₁₃₄, v₂₃₄, v₁₂₃₄)

julia> [!b for b in Λ(4).b]
16-element StaticVectors.FixedVector{16, Single{⟨1111⟩, _A, _B, Int64} where {_A, _B}, Vector{Single{⟨1111⟩, _A, _B, Int64} where {_A, _B}}} with indices SOneTo(16):
 1v₁₂₃₄
  1v₂₃₄
 -1v₁₃₄
  1v₁₂₄
 -1v₁₂₃
   1v₃₄
  -1v₂₄
   1v₂₃
   1v₁₄
  -1v₁₃
   1v₁₂
    1v₄
   -1v₃
    1v₂
   -1v₁
     1v

julia> [⋆b for b in Λ(4).b]
16-element StaticVectors.FixedVector{16, Single{⟨1111⟩, _A, _B, Int64} where {_A, _B}, Vector{Single{⟨1111⟩, _A, _B, Int64} where {_A, _B}}} with indices SOneTo(16):
 1v₁₂₃₄
  1v₂₃₄
 -1v₁₃₄
  1v₁₂₄
 -1v₁₂₃
   1v₃₄
  -1v₂₄
   1v₂₃
   1v₁₄
  -1v₁₃
   1v₁₂
    1v₄
   -1v₃
    1v₂
   -1v₁
     1v

julia> [complementleft(b) for b in Λ(4).b]
16-element StaticVectors.FixedVector{16, Single{⟨1111⟩, _A, _B, Int64} where {_A, _B}, Vector{Single{⟨1111⟩, _A, _B, Int64} where {_A, _B}}} with indices SOneTo(16):
 1v₁₂₃₄
 -1v₂₃₄
  1v₁₃₄
 -1v₁₂₄
  1v₁₂₃
   1v₃₄
  -1v₂₄
   1v₂₃
   1v₁₄
  -1v₁₃
   1v₁₂
   -1v₄
    1v₃
   -1v₂
    1v₁
     1v
````

#### Minkowski
Oracle transcript (Grassmann 0.8.46, label `Minkowski`):
````
julia> @basis S"+---"
(⟨+---⟩, v, v₁, v₂, v₃, v₄, v₁₂, v₁₃, v₁₄, v₂₃, v₂₄, v₃₄, v₁₂₃, v₁₂₄, v₁₃₄, v₂₃₄, v₁₂₃₄)

julia> [⋆b for b in Λ(V).b]
16-element StaticVectors.FixedVector{16, Single{⟨+---⟩, _A, _B, Int64} where {_A, _B}, Vector{Single{⟨+---⟩, _A, _B, Int64} where {_A, _B}}} with indices SOneTo(16):
 1v₁₂₃₄
  1v₂₃₄
  1v₁₃₄
 -1v₁₂₄
  1v₁₂₃
  -1v₃₄
   1v₂₄
  -1v₂₃
   1v₁₄
  -1v₁₃
   1v₁₂
    1v₄
   -1v₃
    1v₂
    1v₁
    -1v

julia> [!b for b in Λ(V).b]
16-element StaticVectors.FixedVector{16, Single{⟨+---⟩, _A, _B, Int64} where {_A, _B}, Vector{Single{⟨+---⟩, _A, _B, Int64} where {_A, _B}}} with indices SOneTo(16):
 1v₁₂₃₄
  1v₂₃₄
 -1v₁₃₄
  1v₁₂₄
 -1v₁₂₃
   1v₃₄
  -1v₂₄
   1v₂₃
   1v₁₄
  -1v₁₃
   1v₁₂
    1v₄
   -1v₃
    1v₂
   -1v₁
     1v

julia> [b*b for b in Λ(V).b]
16-element StaticVectors.FixedVector{16, TensorTerm{⟨+---⟩, 0, Int64}, Vector{TensorTerm{⟨+---⟩, 0, Int64}}} with indices SOneTo(16):
   v
  1v
 -1v
 -1v
 -1v
  1v
  1v
  1v
 -1v
 -1v
 -1v
 -1v
 -1v
 -1v
  1v
 -1v

julia> v1234*v1234
-1v
````

#### exp special cases
Oracle transcript (Grassmann 0.8.46, label `exp special cases`):
````
julia> basis"3"
(⟨111⟩, v, v₁, v₂, v₃, v₁₂, v₁₃, v₂₃, v₁₂₃)

julia> exp(0.5v1)
1.1276259652063807 + 0.5210953054937474v₁

julia> exp(0.5v12)
0.8775825618903728 + 0.479425538604203v₁₂

julia> @basis S"-++"
(⟨-++⟩, v, v₁, v₂, v₃, v₁₂, v₁₃, v₂₃, v₁₂₃)

julia> exp(0.5v1)
0.8775825618903728 + 0.479425538604203v₁

julia> exp(0.5v12)
1.1276259652063807 + 0.5210953054937474v₁₂

julia> @basis S"∞∅+"
(⟨∞∅1⟩, v, v∞, v∅, v₁, v∞∅, v∞₁, v∅₁, v∞∅₁)

julia> exp(0.5v∞1)
1.0 + 0.0v∞∅ + 0.5v∞₁ + 0.0v∅₁

julia> exp(0.5v∞∅)
1.12763 + 0.521095v∞∅ + 0.0v∞₁ + 0.0v∅₁
````

#### products of ints
Oracle transcript (Grassmann 0.8.46, label `products of ints`):
````
julia> basis"3"
(⟨111⟩, v, v₁, v₂, v₃, v₁₂, v₁₃, v₂₃, v₁₂₃)

julia> (1v1+2v2+3v3) * (4v1+5v2+6v3)
32 - 3v₁₂ - 6v₁₃ - 3v₂₃

julia> (1v1+2v2+3v3) ∧ (4v1+5v2+6v3)
-3v₁₂ - 6v₁₃ - 3v₂₃

julia> (1v1+2v2+3v3) ⋅ (4v1+5v2+6v3)
32v

julia> (1v1+2v2+3v3) × (4v1+5v2+6v3)
-3v₁ + 6v₂ - 3v₃

julia> (1v1+2v2+3v3) ∨ (4v12+5v13+6v23)
8v

julia> v1 ∨ v23
v

julia> v23 ∨ v1
v

julia> v12 ∨ v13
v₁

julia> v12 > v1
v₂

julia> v1 < v12
v₂

julia> v12 >> v1
-1v₂

julia> v1 << v12
v₂

julia> v1 > v12
𝟎

julia> v12 < v1
𝟎

julia> (v1+v2) > v12
𝟎

julia> v12 < (v1+v2)
𝟎
````

#### projective/conformal up-down
Oracle transcript (Grassmann 0.8.46, label `projective/conformal up-down`):
````
julia> @basis S"∞+++"
(⟨∞+++⟩, v, v∞, v₁, v₂, v₃, v∞₁, v∞₂, v∞₃, v₁₂, v₁₃, v₂₃, v∞₁₂, v∞₁₃, v∞₂₃, v₁₂₃, v∞₁₂₃)

julia> ↑(v1+v2+v3)
0.5v∞ + 0.5v₁ + 0.5v₂ + 0.5v₃

julia> ↓(↑(v1+v2+v3))
0.0v∞ + 1.0v₁ + 1.0v₂ + 1.0v₃

julia> f(t) = ↓(exp(π*t*((3/7)*v12+v∞3))>>>↑(v1+v2+v3))
f (generic function with 1 method)

julia> f(0.0)
0.0v∞ + 1.0v₁ + 1.0v₂ + 1.0v₃

julia> f(0.25)
0.0v∞ + 1.40532v₁ + 0.158342v₂ - 1.0v₃

julia> f(0.5)
0.0v∞ + 0.39915v₁ - 0.250802v₂ - 0.333333v₃

julia> V(2,3,4)(f(0.25))
1.40532v₁ + 0.158342v₂ - 1.0v₃

julia> @basis S"∞∅+++"
(⟨∞∅111⟩, v, v∞, v∅, v₁, v₂, v₃, v∞∅, v∞₁, v∞₂, v∞₃, v∅₁, v∅₂, v∅₃, v₁₂, v₁₃, v₂₃, v∞∅₁, v∞∅₂, v∞∅₃, v∞₁₂, v∞₁₃, v∞₂₃, v∅₁₂, v∅₁₃, v∅₂₃, v₁₂₃, v∞∅₁₂, v∞∅₁₃, v∞∅₂₃, v∞₁₂₃, v∅₁₂₃, v∞∅₁₂₃)

julia> ↑(v1+v2+v3)
0.0 + 1.5v∞ + 1.0v∅ + 1.0v₁ + 1.0v₂ + 1.0v₃

julia> ↓(↑(v1+v2+v3))
0.0 + 1.0v₁ + 1.0v₂ + 1.0v₃

julia> g(t) = ↓(exp(π*t*((3/7)*v12+v∞3))>>>↑(v1+v2+v3))
g (generic function with 1 method)

julia> g(0.25)
0.0 + 1.40532v₁ + 0.158342v₂ + 2.5708v₃ + 5.82587e-10v∞₁₂ - 3.5883e-11v∞₁₃ + 3.1847e-10v∞₂₃

julia> V(3,4,5)(g(0.25))
0.0 + 2.5708v₁
````

#### chainfield (vectorfield without GeometryBasics)
Oracle transcript (Grassmann 0.8.46, label `chainfield (vectorfield without GeometryBasics)`):
````
julia> basis"2"
(⟨11⟩, v, v₁, v₂, v₁₂)

julia> F = chainfield(exp(π*v12/2))
#chainfield##0 (generic function with 1 method)

julia> F(Chain{V,1}(1.0,0.0))
-1.0v₁ + 1.22465e-16v₂

julia> F(Chain{V,1}(0.5,-0.25))
-0.5v₁ + 0.25v₂

julia> G = chainfield(exp((π/4)*v12/2))
#chainfield##0 (generic function with 1 method)

julia> G(Chain{V,1}(1.0,0.0))
0.707107v₁ + 0.707107v₂

julia> @basis S"+-"
(⟨+-⟩, v, v₁, v₂, v₁₂)

julia> H = chainfield(exp((π/8)*v12/2))
#chainfield##0 (generic function with 1 method)

julia> H(Chain{V,1}(1.0,0.5))
1.27954v₁ + 0.941922v₂
````

#### orb
Oracle transcript (Grassmann 0.8.46, label `orb`):
````
julia> @basis S"∞+++"
(⟨∞+++⟩, v, v∞, v₁, v₂, v₃, v∞₁, v∞₂, v∞₃, v₁₂, v₁₃, v₂₃, v∞₁₂, v∞₁₃, v∞₂₃, v₁₂₃, v∞₁₂₃)

julia> t = exp((π/4)*(v12+v∞3))
0.5 + 0.0v∞₁ + 0.0v∞₂ + 0.5v∞₃ + 0.5v₁₂ + 0.0v₁₃ + 0.0v₂₃ + 0.5v∞₁₂₃

julia> K = chainfield(t, V(2,3,4))
#chainfield##0 (generic function with 1 method)

julia> K(Chain{V(2,3,4),1}(0.5,0.5,0.5))
-0.363636v₁ + 0.363636v₂ - 0.0909091v₃
````

#### Leech variant
shows the failing Chain-from-matrix constructor.
Oracle transcript (Grassmann 0.8.46, label `Leech variant`):
````
julia> generator = [8 0 0 0; 4 4 0 0; 4 0 4 0; 2 2 2 2];

julia> W4 = ℝ^4⊕(ℝ^4)'
⟨++++----⟩*

julia> L = Chain{Submanifold(W4),2}(generator./sqrt(8))
ERROR: MethodError: Cannot `convert` an object of type Matrix{Float64} to an object of type Values{28, Chain{⟨1111⟩, 2}}
The function `convert` exists, but no method is defined for this combination of argument types.

Closest candidates are:
  (::Type{SA})(::Any...) where SA<:StaticVectors.TupleVector
   @ StaticVectors ~/.julia/packages/StaticVectors/fpkZ5/src/convert.jl:8
  convert(::Type{SA}, !Mat
````

#### generictests basis
`Λ(G).b` as used by generictests.jl:81.
Oracle transcript (Grassmann 0.8.46, label `generictests basis`):
````
julia> Λ(S"∞+").b
4-element Values{4, Submanifold{⟨∞+⟩}} with indices SOneTo(4):
   v
  v∞
  v₁
 v∞₁

julia> Λ(S"∞∅+").b
8-element Values{8, Submanifold{⟨∞∅1⟩}} with indices SOneTo(8):
    v
   v∞
   v∅
   v₁
  v∞∅
  v∞₁
  v∅₁
 v∞∅₁

julia> mdims(S"∞∅+")
3
````


### 6.9 Test suite goldens (`test/*.jl`) — all pass on the oracle

`test/runtests.jl` (includes `issuestests.jl`, `generictests.jl`; `symbolictests.jl` is **not** included and needs SymEngine/SymPy):

| file:line | assertion (golden) |
|---|---|
| `runtests.jl:4` | `@basis "++++" s e; e124 * e23 == e134` (custom sig name `s`, vector prefix `e`) |
| `runtests.jl:5` | `[Λ(3).v32^2, Λ(3).v13^2, Λ(3).v21^2] == [-1Λ(3).v for j∈1:3]` (reversed index names parse with sign; bivectors square to −1) |
| `runtests.jl:6` | (commented) `((Λ(ℝ2).v1+2Λ(ℝ2).v2)∧(3Λ(ℝ2').w1+4Λ(ℝ2').w2))(Λ(ℝ2).v1+Λ(ℝ2).v2) == 7Λ(ℝ2).v1+14Λ(ℝ2).v2` — intended mother-algebra evaluation (currently broken, §6.7) |
| `runtests.jl:7` | `@basis "++++"; (v1*v1, v1⋅v1, v1∧v1) == (1,1,0) && (v2*v2, v2⋅v2, v2∧v2) == (1,1,0)` (blade results compare `==` to plain numbers; `v1∧v1` is `Zero`) |
| `runtests.jl:8` | `@basis "-+++"; (v1*v1, v1⋅v1, v1∧v1) == (-1,-1,0) && (v2*v2,…) == (1,1,0)` |
| `runtests.jl:9` | `basis"-+++"; h = 1v1+2v2; h⋅h == 3v` (−1 + 4) |
| `runtests.jl:10` | `Λ(62).v32a87Ng == -1Λ(62).v2378agN` (skipped on Windows) |
| `runtests.jl:11` | (commented) `Λ.V3 == Λ.C3'` |
| `runtests.jl:12` | `Λ(Manifold(14)) + Λ(Manifold(14))' == Λ(Manifold(14)+Manifold(14)')` (basis container union ≡ basis of direct sum; 28-dim ExtendedBasis) |
| `runtests.jl:14-16` | (commented, Reduce) `a∧b + a⋅b == a*b` symbolic |
| `issuestests.jl:9-16` (#19 conformal split, `@basis S"∞∅++"`) | `(v∞^2, v∅^2, v1^2, v2^2) == (0v, 0v, v, v)`; `v∞ ⋅ v∅ == -1v`; `v∞∅^2 == v`; `(v∞∅ * v∞, v∞∅ * v∅) == (-1v∞, v∅)`; `(v∞ * v∅, v∅ * v∞) == (-1 + 1v∞∅, -1 - 1v∞∅)` |
| `issuestests.jl:18-31` (#17, `basis"2"`) | `a = v + v1 - v1`; `a == v`; `typeof(a) <: Couple`; `a == 1`; `b = a - 1`; `b == 0` (twice); `a - 1 == 0` (cancellation keeps a `Couple` with zero imaginary part; `==` with numbers compares scalar part and requires other parts zero) |
| `issuestests.jl:33-45` (#16, `basis"2"`) | `A = 2v1 + v2; B = v1 + v2`; `A + B == 3v1 + 2v2`; `A == 2v1 + v2`; `B == v1 + v2`; `v1 + A == 3v1 + 1v2`; `A == 2v1 + v2` (no mutation/aliasing) |
| `issuestests.jl:47-50` (#14, `basis"+++"`) | `(v1+v2) + (v1+v2)*(v1+v2) == 2 + 1v1 + 1v2` (Chain + Spinor → mixed, equality across container types) |
| `issuestests.jl:52-61` (#15, `basis"3"`; `i,j,k = hyperplanes(ℝ^3)`; `alpha = 0.5π`) | `exp(alpha/2*(i)) ≈ sqrt(2)*(1+i)/2`; with `a,b,c = 1/sqrt(2)*[1,1,0]`: `exp(alpha/2*(a*i + b*j + c*k)) ≈ (sqrt(2)+j+i)/2` |
| `issuestests.jl:63-72` (#20, `@basis S"∞∅+"`) | `v∅*v∞ == -1 - v∞∅`; `v∅*(-v∞) == 1 + v∞∅`; `a = v∅*basis(-v∞)`; `a == -1 - v∞∅`; `Single{V}(-1, a) == -a` (Single constructor with a non-scalar value multiplies) |
| `issuestests.jl:74-82` (#22, `basis"++"`) | `a = v1 + v2`; `typeof(a) <: Chain`; `Multivector(a) == v1 + v2`; `Chain(v) == v` |
| `generictests.jl:13-59` (`basis"2"`) | `≈` reflexive on `v, v1, v2, v12, 2v, 2v1, v1+v2, v+v2, v+v12, v+v2+v12`; `≈` false between any two of {scalar, vector, bivector, mixed} kinds listed at lines 32-58 (e.g. `!(v ≈ v1)`, `!(2v ≈ v1+v)`, `!(v1+v2 ≈ v1+v12)`, `!(v+v1+v12 ≈ v1+v12)`) — i.e. `≈` must compare full multivectors including missing grades, not just stored parts |
| `generictests.jl:61-69` | `scalar(v) == 1v`, `scalar(2v) == 2v`, `scalar(v1) == 0v`, `scalar(-v+v1) == -1v`, `scalar(v-v) == 0v`, `scalar(v1+v2) == 0v` |
| `generictests.jl:71-161` | for 𝔽=Float64, for G ∈ `[3, V"+++", S"∞+", S"∅+", V"-+++", S"∞∅+"]`: `basis = Λ(G).b`, `basisvecs = basis[2:dims+1]`, `B = Σ i·basisvecs[i]`, `A = Σ rand·basis`. Assertions: `e*A == A == A*e` (e = 1.0) for all multivectors; `a^2 ≈ scalar(a^2)*basis[1]` for vectors; `A*(B*C) ≈ (A*B)*C` and `A*(B+C) ≈ A*B + A*C` for all triples of (all blades ∪ {A, B}); for vector pairs: `a⋅b == 0.5*(a*b + b*a)`, `a∧b == 0.5*(a*b - b*a)`, `a*b == a⋅b + a∧b`, `a*b == 2*a⋅b - b*a`, `a*a == a⋅a` (**exact `==`**, mixing Int and Float coefficients) — 18998 assertions |
| `symbolictests.jl:1-51` | smoke tests only (`@show` of `expand`, `N(subs(...))`, `factor`, `map(typeof, numeric_mv.v)` on SymEngine/SymPy coefficients); no goldens. Porting relevance: coefficient-wise `map` over any TensorAlgebra (`generate_symbolic_methods`, `src/Grassmann.jl:390-409`). |

## 7. Dependencies (chakravala ecosystem and others) and symbols used

`Project.toml:6-15` deps: `AbstractTensors`, `ComputedFieldTypes` (vtjnash; `@computed struct` for `Values{binomial(n,G),T}` field sizes), `DirectSum`, `Leibniz`, `LinearAlgebra`, `Requires` (pre-1.9 extension loading), `SparseArrays`, `Random`, `AbstractFFTs`. Transitive chakravala deps: `StaticVectors` (`Values`, `Variables`, `FixedVector`, `TupleVector`), `AbstractLattices` (`∧`, `∨`, `wedge`, `vee`). Compat: `Leibniz = "0.2,0.3"`, `DirectSum = "0.8.12"`, `AbstractTensors = "0.8"` (`Project.toml:53-60`). Test extras: `GeometryBasics`, `LightGraphs`, `Adapode` (listed but unused; `Project.toml:62-69`). Docs build (`docs/make.jl:4`): `Documenter, AbstractTensors, DirectSum, Leibniz, Grassmann, StaticArrays`.

Imported symbols (all files), grouped by package:

* **AbstractTensors** — types `TensorAlgebra, TensorGraded, TensorTerm, TensorMixed, Manifold, Scalar, GradedVector, Bivector, Trivector`; storage `Values, Variables, FixedVector` (re-exported from StaticVectors); ops `∧, ∨, ⟑, ⊖, ⊘, ⊗, ⊛, ⊙, ⊠, ⨼, ⨽, ⋆, ∗, rem, div, plus, minus, times, contraction, equal, wedgedot, veedot, pseudosandwich, antisandwich, cosandwich, antidot, codot, clifford, hodge, wedge, vee, complement, wedgedot_metric, contraction_metric, log_metric`; accessors `value, valuetype, scalar, isscalar, vector, isvector, bivector, isbivector, trivector, istrivector, volume, isvolume, pseudoscalar, involute, even, odd, antiabs, antiabs2, geomabs, unit, unitize, unitnorm`; constants `TAG, SUB`; math `AbstractTensors.{exp, expm, sin, cos, sinh, cosh, sqrt, abs, norm, dot, inv, mdims, similar_type, _diff}` (`src/Grassmann.jl:23-41`, `multivectors.jl:21-22,962-964`, `algebra.jl:16-18`).
* **DirectSum** — `V0, ⊕, generate, basis, getalgebra, getbasis, dual, Zero, One, Basis, Single, Signature, metrichash, antimetric, cometric, signbool, antireverse, antiinvolute, anticlifford, paritymetric, parityanti, complementleftanti, complementrightanti`, qualified `DirectSum.{submanifold, supermanifold, getbasis, orand, getalgebra, eval_shift, diagonalform, options, indexparity, diagsig, basis, TensorBundle, printindices, indices}`; macros/strings `@basis…`, `S"…"`, `D"…"`, `V"…"`, `Λ`, `tangent` (`src/Grassmann.jl:33-37`, `parity.jl:17-18`).
* **Leibniz** — bit/index machinery `hasinf, hasorigin, dyadmode, value, pre, vsn, metric, mdims, gdims, bit2int, indexbits, indices, diffvars, diffmask, hasconformal, symmetricmask, indexstring, indexsymbol, combo, digits_fast, algebra_limit, sparse_limit, cache_limit, fill_limit, gdimsall, spincumsum, binomial, binomial_set, binomsum, binomsum_set, lowerbits, expandbits, bladeindex, basisindex, indexbasis, indexbasis_set, loworder, intlog, antisum, antisum_set, anticumsum, antiindex, spinindex, binomcumsum, promote_type, mvec, svec, insert_expr, supermanifold, Fields, parval, mixed, mvecs, svecs, spinsum, spinsum_set, grade, antigrade, showvalue, basis, order, diffcheck, diffmode, symmetricsplit, isnull, Field, ExprField`; parity helpers `parityreverse, parityinvolute, parityconj, parityclifford, parityright, parityleft, parityrighthodge, paritylefthodge, complementleft, complementright, complementlefthodge, complementrighthodge, grade_basis`; calculus `∇, Δ, d, ∂, δ, Derivation, Operator`; printing `showvalue, showstar, check_parnot, extend_parnot, check_field, extend_field`; `indexsplit`, `count_gdims` (`src/Grassmann.jl:34-49,73-74`, `parity.jl:15-16`, `multivectors.jl:23,31`, `algebra.jl:19-20`).
* **AbstractLattices** (via AbstractTensors) — `wedge`, `vee`, `∧`, `∨` generic functions.
* **StaticVectors** — `Values` (immutable SVector-like), `Variables` (mutable MVector-like), `FixedVector`, `TupleVector`, `SOneTo`.
* Base/stdlib: `LinearAlgebra: I, UniformScaling, isdiag, det, tr, dot, ⋅, cross, ×, rank, norm, eigvals, eigvecs, eigen, diag` (`multivectors.jl:25-26`, `forms.jl:12`); `Random: SamplerType, AbstractRNG` (`composite.jl:1060`, `rand(Chain{V,1,…})`); `AbstractFFTs` (fft family over arrays of `TensorGraded`/`Couple`/`Chain`/`Phasor` via `complexify`, `src/Grassmann.jl:350-358`); `SparseArrays`.

### 7.1 Extensions (`ext/*.jl`, `Project.toml:17-51`; each also `@require`d at `src/Grassmann.jl:420-451` pre-1.9)

| extension | adds | notes / bugs |
|---|---|---|
| `ReduceExt` | `RExpr * Submanifold/Multivector`, `∧` with RExpr, `extend_field`/`extend_parsym` so symbolic coefficients print in parens, `generate_inverses`, `generate_derivation(:(Reduce.Algebra),T,:df,:RExpr)` for `Symbol`, `Expr`, `RExpr` | symbolic CAS coefficients; skip in Lean (use a generic `K`) |
| `SymbolicsExt` | `generate_algebra(:Symbolics,:Num,…)`; `expand`, `simplify`, `substitute` mapped over coefficients; `isfixed(Num)=true` | skip |
| `SymPyExt` | `generate_algebra(:SymPy,:Sym,…,:diff,:symbols)`; `expand, factor, together, apart, cancel, N, subs` coefficientwise; `SymPy.collect` on Chain/Multivector/Single | skip |
| `SymEngineExt` | `generate_algebra(:SymEngine,:Basic,…)`, `expand, N, subs, evalf` | skip |
| `AbstractAlgebraExt` | `generate_algebra(:AbstractAlgebra,:SetElem,…)`; `isfixed` | shows the "any ring as K" story (docs `algebra.md:1445-1449`) |
| `GaloisFieldsExt` | `generate_algebra(:GaloisFields,:AbstractGaloisField,…)` | finite-field coefficients (docs `algebra.md:1430-1444`) → Lean `ZMod p` |
| `LightGraphsExt` | `SimpleDiGraph(x)` for `TensorTerm`, `Chain`, `Multivector`: edges from grade-2 blades (reversed if coefficient negative), recurse through `∂` for higher grades | simplicial-complex → digraph; optional |
| `StaticArraysExt` | `SMatrix(::Chain{V,G,Chain{W,G}})`, `Chain(::SMatrix{N,N})`, `Chain{V,G}(::SMatrix)` conversions | matrix interop; Lean: `Matrix`/`Array` conversions |
| `MeshesExt` | `Meshes.Point` conversions, `pointpair`, `ptype`, `pointfield(t,V,W)`, `pointfield(t,ϕ)` FE interpolation | **PLOTTING**; bug: `Meshes(0.0,0.0)` (`MeshesExt.jl:33`, calls module) |
| `GeometryBasicsExt` | `GeometryBasics.Point(::Values/Variables/TensorAlgebra/Couple/Phasor/Chain)`, `pointpair`, `ptype`, **`pointfield`/`vectorfield` methods** (`:30-44`) | **PLOTTING** (Makie point type). Bugs: `GeometryBasis.Point` typo (`:21`), `GeometryBasics(0.0,0.0)` (`:34`) |
| `MakieExt` | `convert_arguments(::PointBased, ::Vector{<:Chain})`, `arrows`/`arrows!` for `Vector{<:Chain}` base points + vectors, `lines`/`lines!` for vectors of TensorAlgebra / TensorTerm / 1-element Chains | **PLOTTING**. Bug: `convert_single_argument` references undefined `P` (`:20`); `arrows` is deprecated in Makie 0.24 (arrows2d/arrows3d) |
| `UnicodePlotsExt` | `vandermonde(x,y,V,grid)`: least-squares polynomial fit via `vandermondeinterp`, draws `scatterplot` + `lineplot!` to the terminal and prints `||ϵ||: <residual>` | **PLOTTING (terminal)**; returns coefficients |
| `SpecialFunctionsExt` | lifts ~40 unary (gamma, erf, airy, bessel…, zeta) and many binary/ternary SpecialFunctions to `TensorTerm` (scalar → `Single`, else via `Couple`→`Complex`), `Couple` (→ Complex and back), `Chain` (via `complexify`/`vectorize`), `Phasor` | pattern: "treat a 2D element as a complex number". Bugs: undefined `k` in several ternary methods (`SpecialFunctionsExt.jl:54,77,82-84`; `besselh` methods at `:133-150` are fine since `k` is an argument there) |
| `EllipticFunctionsExt` | same lifting pattern for `qfromtau, taufromq, etaDedekind, lambda, kleinj, ellipticE/K/F/Z/PI, jtheta*, am, agm, Carlson*, wp, wsigma, wzeta, theta*`, `jellip` | bug: the `Array{<:TensorTerm{V,0}}` `jellip` method calls `jellip(Real.(x))` without `kind` and broadcasts `Single{V}.(kind, …)` (`EllipticFunctionsExt.jl:176`) |
| `FewSpecialFunctionsExt` | same pattern for `η, FresnelC/S/E, Ci_complex, C, F, G, H⁺, H⁻, MarcumQ, dQdb, F_clausen` | same `k` typos (`FewSpecialFunctionsExt.jl:54,59-61`) |

## 8. Lean 4 porting notes

### 8.1 design.md philosophy (summary)
* **K-module as a compile-time value** (`design.md:12-37`): a vector space is `TensorBundle{n,ℙ,g,ν,μ}` — rank n, projective flags ℙ ⊆ {v∞, v∅}, metric g, ν tangent variables, μ Leibniz-Taylor order — "byte-encoded" and available at precompilation so the compiler can pre-allocate and cache. `V = Submanifold(::TensorBundle)` is the canonical handle; all algebra types carry `V`.
* **Dual spaces and mother algebra** (`design.md:35,88-99`): `V'` flips the metric signature and switches vectors `vᵢ` ↔ covectors `wⁱ`; `V⊕V'` is the full "mother space"; dyadic (1,1)-tensors live in its bivector subspace (dyadic-tensors.md:1-5).
* **Optional Leibniz extension** (`design.md:23-37`, `algebra.md:142-176`): ∂ₖ (symmetric derivations) and ϵₖ (their duals) extend the exterior algebra into a mixed-symmetry algebra; "standard geometric algebra is only concerned with vᵢ" — can be ignored for plain GA.
* **Set algebra on spaces** (`design.md:100-107`): `⊕ ∪ ∩ ⊆ ⊇` on manifolds computed at compile time from bit parameters.
* **Staged caching by dimension** (`design.md:111-153`): N ≤ 8 full Basis cache; ≤ 22 SparseBasis; ≤ 62 ExtendedBasis (UInt64 bitmasks, 62 = alphanumeric labels); full Multivectors only to 22; sparse elements (blades/Single) fast at any N.
* **Universal interoperability** (`design.md:155-186`): binary ops on elements of different spaces apply the union morphism `op(VW(a),VW(b))` with `VW = V∪W` (`interop`); `LinearAlgebra.I` (`UniformScaling`) is a universal pseudoscalar whose meaning is taken from the other operand's V.
* **Code generation over a minimal kernel** (`README.md:158`, `algebra.md:238-240`, `1427-1449`): the product algebra is generated for any scalar field (`generate_products`, `generate_algebra`) — coefficient type is a parameter, not hard-wired.

### 8.2 Ecosystem-wide naming / notation conventions (to mirror in Lean notation)
* Vector basis `v` + subscript indices (`v₁₂₃`, ASCII `v123`); covectors `w` + superscript (`w¹²`, ASCII `w12`); tangent derivations `∂` + subscripts (`∂₁₂`, ASCII `∂12`); duals `ϵ` (`ϵ₁`, `ϵ¹` in mixed); scalar blade is the bare prefix `v` (also `v⃖` alias), zero is `𝟎`, `∞`=Infinity. Indices beyond 9: `0`=10, `a…z`=11…36, `A…Z`=37…62 (covectors swap case). Projective basis symbols `v∞`, `v∅` come first (`v∞∅₁₂`).
* Manifold notation `⟨…⟩`, `ℝ^n` (Signature, `+` slots) vs constants `ℝ0…ℝ9` (Int-based, `1` slots); `T^μ⟨…⟩` tangent; `'` dual, `*` mixed.
* String macros: `S"+-++"` (Signature from `+`/`-`, with optional leading `∞`, `∅`), `D"1,1,1,0"` / `D"0.3,2.4,1"` (DiagonalForm), `V"…"` (generic), `basis"…"`, `dualbasis"…"`, `mixedbasis"…"`; `@basis M [VName vecPrefix covPrefix duoPrefix difPrefix]` defaults `V v w ∂ ϵ` (`@dualbasis`: `VV w ϵ`; `@mixedbasis`: `W`, and then re-binds `VV` (dual) and `V` (base) — see §6.7 pitfall). `@basis` also binds `v⃖`, `𝟎`, `∞` and returns the tuple.
* Operators: `∧ ∨ * ⋅ | < > << >> ⊘ >>> ⋆ ! ~ ' × ⊗ ↑ ↓ ∂ d δ ∇`; element call `x(g)` = grade projection; `x(y)` for forms/dyadics = evaluation; `Λ(n).vIJK` property access with sign.

### 8.3 Dependent types vs runtime values (zero-cost recommendations)
* **Signature `V` → index** (`structure Sig` with `n : Nat`, `inf orig : Bool`, `metric : Metric n` (sign bits `BitVec n` or diagonal `Vector ℚ n`/`Float`), `dyad : Int` (0 plain, 1 dual, −1 mixed), `nu mu : Nat`, `sub : BitVec n` subspace mask). Use it as a type parameter of every element type. Its fields are erased at runtime when used only in types/proofs; for runtime table lookups pass tables via typeclass instances (`[GATables V]`) so that each concrete signature's tables are closed terms computed once (Lean extracts closed terms to global constants initialized lazily).
* **Grade `G` → index** on `Chain V G K := { v : Vector K (V.n.choose G) }` — `Vector` erases its length proof, so `Chain V G Float` is an `Array Float` at runtime (or better a `FloatArray` specialization for the hot Float case; keep `Vector K` generic path). Note `Nat.choose n g = 0` for g > n gives a natural zero-size chain for overflowing wedge grades (`Chain V (G+L)`), a free "Zero" encoding. Contractions need grade `G − L` only when `L ≤ G`; use `Int` grades with `gdim n g := if 0 ≤ g ∧ g ≤ n then choose n g.toNat else 0` so negative grades are zero-size (**do not** use truncated `Nat.sub`, which would map to grade 0 = scalar).
* **Blade `B`** → runtime `UInt64` mask with a `B < 2^n` proof field (or `BitVec V.n`); make it a type index only for `Single`/`Couple` if you want `Couple V B K` to be two floats (it is in Julia); otherwise store the mask.
* **Scalar type `K`** → ordinary parameter with typeclasses (`Add, Mul, Neg, OfNat, Inv`); Float/Int/Rat/ZMod all fall out; symbolic CAS extensions become "any `CommRing`".
* **Result-kind computation**: Julia picks `Submanifold/Single/Couple/PseudoCouple/Chain/Spinor/CoSpinor/Multivector/Zero` by type. In Lean do this with a small closed type family: product of `Chain V G` and `Chain V L` → wedge `Chain V (G+L)`, contraction `Chain V (G-L)`, geometric → `Multivector V` (or a grade-set-indexed sparse type), even×even → `Spinor`, odd×even → `CoSpinor`. The *display* goldens depend on the Julia kind (zero-hiding differs: Multivector hides zeros, Spinor/Chain don't), so the Lean port needs either the same kinds or a `kind` tag used by `toString`.
* **Proof obligations that pay for themselves** (development velocity): grade bookkeeping (`Nat.choose` sizes), blade-index bijection `bladeindex ∘ indexbasis = id` (decide for n ≤ 8), sign of reordering `(−1)^Π`, involution laws (`~~x = x`, `involute∘involute = id`, clifford = composition), `!` then `complementleft` = id, `⋆⋆ω = (−1)^{m(n−m)}ω|I|²` for diagonal metrics, associativity of the blade product (`decide`/`bv_decide` on 6-bit masks for n ≤ 6), `a∧a = 0` for vectors, `ab = a⋅b + a∧b`. These mirror the generictests identities and can replace most of that test file.

### 8.4 How Julia gets its speed (hot paths) and the Lean equivalent
* `@generated` functions specialise every binary op on `(V, G, L, T)` and emit fully unrolled straight-line code using precomputed product tables and `@pure` caches (`algebra.jl` product generators, `product_sandwich` `algebra.jl:1567`, `chain_src` `multivectors.jl:247-261` for N < `cache_limit`=12, sparse loop fallback above). Lean: (1) table-driven kernels over `FloatArray`/`Array` with `@[specialize]` on K and `@[inline]` on small helpers — first; (2) optional `elab`/macro that, for a literal signature, generates unrolled `def`s (e.g. `ga_codegen ℝ3`) — only if profiling shows the loop overhead matters. Julia's `A\b` on 5×5 dyadics at 72 ns is the perf target (dyadic-tensors.md:70-72).
* Global lazily-filled caches (`combo_cache`, `binomsum_cache`, `indexbasis_cache`, `bladeindex_cache`, Leibniz `utilities.jl:112-243`) → Lean `initialize`d `IO.Ref (Array …)` or pure memo tables built for n ≤ 12 at first use; above that compute on the fly (`combo` via lexicographic combinations).
* Allocation-free: all element types are immutable fixed-size (`Values`); keep Lean structures unboxed where possible (`Float` fields, `FloatArray` payload) and avoid `Array (Array _)` in inner loops.

### 8.5 Tricky semantics to preserve (all verified)
1. `⊘` and `>>>` are **not normalised** (§4.6); only unit versors give rotations. `x⊘R = ~R x R` is the Euler (CCW) convention.
2. `hyperplanes(ℝ^3) = (v₂₃, −v₁₃, v₁₂)` gives `ijk = +1`; `quaternion(s,i,j,k)` uses `i=v₁₂, j=−v₁₃, k=v₂₃` (Hamilton). `𝕚,𝕛,𝕜` are the hyperplanes version.
3. `abs2(x) = ~x*x` (full product), `norm` = Euclidean coefficient norm (metric-independent), `scalar(x)` is a Single not a number; numbers compare `==` to scalar-only elements.
4. `inv` only when `~x*x` is scalar-like; otherwise throws "inv(...) is undefined".
5. `ℝ^n` (Signature, `+`) ≠ `ℝn`/`Submanifold(n)`/`@basis n` (Int-based, `1`) in display; mixing them in one op may need conversion.
6. `m[g]` on Multivector = grade-g `Values`; `m(g)` = grade projection element; `Λ(3).v21 = -v₁₂`.
7. Display differences by kind (§5) — Chain/Spinor/CoSpinor show zeros, Multivector hides zeros and uses `v⃖`, Couple/Single full precision, containers compact.
8. Curl sign in tangent algebra differs from the doc formula (§6.3 `curl ⋆d`).
9. Conformal: v∞ alone squares to +1, v∅ alone to −1, together null with `v∞⋅v∅ = −1`; `!` vs `⋆` differ on null basis by factors 2, ½.
10. `@mixedbasis` rebinds names; mother-algebra evaluation `ℒ(v)` currently returns wrong results — implement the intended `7v₁+14v₂`.
11. Exported-but-undefined names (§2.1) and broken helpers (`⊙`, `⊠`, `Δ`-based `𝒫`/`subcomplex`, doc `χ(Δ(ω))`, Leech constructor, extension typos) — do not replicate bugs; mark as intentional deviations with tests pinned to the *intended* doc output where the doc gives one.
12. `betti` is combinatorial counting, can go negative — either replicate for parity (flagged) or implement true homology ranks and document.
13. Julia float printing (shortest round-trip and compact 6-significant) is part of every golden string — implement a faithful formatter (Ryu-style shortest digits; compact mode `%.6g`-like with Julia's `e-16` exponent style, `1.0e10`, trailing `.0` kept).

### 8.6 Julia-specific pieces to skip or redesign
`@pure`, `@computed` (ComputedFieldTypes), `Requires`/`__init__` and weak-dep extensions, `generate_products/generate_algebra/generate_symbolic_methods` `eval` metaprogramming (→ typeclasses), `Base.show` MIME plumbing (→ `ToString`/`Repr` + a `showPlain` that mimics REPL), world-age/`invokelatest`, AbstractFFTs overloads (→ optional), Symbolic CAS extensions, LightGraphs digraphs, Meshes/GeometryBasics `Point` conversions (→ LeanPlot point types), UnicodePlots vandermonde side effects. Makie usage in docs → **LeanPlot** equivalents: `streamplot(f, xrange, yrange[, zrange]; gridsize)`, `lines(points)`, `arrows(base, vec)`; cross-test by sampling the same `chainfield`s/curves as `readme_plot_goldens.json` and comparing images qualitatively against `plots/*.png` / `paper/img/*.png`.

### 8.7 Suggested Lean module decomposition (Grassmann layer only; DirectSum/Leibniz/AbstractTensors ports are separate)

| module | content | est. LOC |
|---|---|---|
| `Grassmann/Sig.lean` (or reuse DirectSum port) | `Sig` structure, `S"…"`/`D"…"`/`V"…"` elaborators, `ℝ^n`, `ℝn`, dual `'`, `⊕`, subspace `V(i,…)`, tangent | 400 |
| `Grassmann/Index.lean` | bitmask ↔ index tuples, lexicographic `indexbasis`, `bladeindex`, `binomsum/spinsum/antisum`, reorder sign, caches | 350 |
| `Grassmann/Types.lean` | `Blade`, `Single`, `Zero`, `Chain`, `Multivector`, `Spinor`, `CoSpinor`, `Couple`, `PseudoCouple`, `Phasor`, conversions, `+ - ` scalar mult, `==`, `≈` | 900 |
| `Grassmann/Products.lean` | blade product tables (geometric/wedge/vee/contractions) for diagonal + null (∞∅) metrics + DiagonalForm + tangent multiset rules; element-level kernels; result-kind family | 1300 |
| `Grassmann/Parity.lean` | reverse/involute/clifford, even/odd/real/imag, complements `! ⋆` left/right/anti, metric/cometric | 350 |
| `Grassmann/Composite.lean` | inv, `/ \ ^`, abs/abs2/norm/unit, exp/log/sqrt/trig/hyperbolic (special cases + series), pseudo*/co* variants | 700 |
| `Grassmann/Sandwich.lean` | `⊘`, `>>>`, rotors, quaternion helpers, `hyperplanes`, `𝕚𝕛𝕜` | 150 |
| `Grassmann/Forms.lean` | TensorOperator/Endomorphism/Outermorphism/Projector/Dyadic/DiagonalOperator, `operator`, `outermorphism`, `compound`, det/tr/inv/adjugate/cofactor, Cramer `\` (§4.12), characteristic/eigen*/roots*/companion/vandermonde, `cayley` | 1500 |
| `Grassmann/Calculus.lean` | `∇` construction, `d ∂ δ`, tangent (Leibniz) products | 450 |
| `Grassmann/Conformal.lean` | `↑ ↓` (Riemann sphere, CGA) | 150 |
| `Grassmann/Simplicial.lean` | skeleton, χ, betti (flagged), chain, path, collapse | 250 |
| `Grassmann/Fields.lean` | `points`, `chainfield/vectorfield`, `scalarfield`, FE interpolation, LeanPlot bridge | 250 |
| `Grassmann/Display.lean` | Julia-exact printing (§5) + float formatter | 550 |
| `Grassmann/Notation.lean` | `basis!` command (binds `v₁₂`/`v12`/…), operator notations, `Λ(n).vIJK` accessor macro | 300 |
| `Grassmann/Theorems/*.lean` | §8.3 proofs (small-n `decide`, general sign lemmas) | 600 |
| `Grassmann/Test/Oracle.lean` + goldens | JSON golden loader/comparator, generictests-style property tests, display tests | 600 |
| **total** | | **≈ 8,700** |

## 9. Oracle test plan (Julia → JSON goldens)

Prototype: `scripts/oracle_tables.jl` already produced `blade_tables.json`. Schema: `{ "<sigName>": { "display": "⟨…⟩", "n": n, "basis_order": [mask…] (Multivector order), "basis_names": ["v", "v₁", …], "<binop>": [[maskA, maskB, [[mask, coeff], …]] …], "<unop>": [[mask, [[mask, coeff] …]] …] } }` with binops `wedge vee geom contract_right contract_left rshift lshift dot sandwich tsandwich`, unops `complementright complementleft hodge complementlefthodge reverse involute clifford metric`; a string `"ERROR: …"` records oracle exceptions. Signatures covered: `R1 R2 R3 R4` (Int-based), `S- S+- S-++ S++- S+--- S--`, `Sinf+ Sorig+ Sinforig+ Sinf+++ Sinforig++`, `D235 D1110`.

Recommended full oracle dump (one `oracle_dump.jl`, fixed `Random.seed!`), each record `{sig, op, args:[{kind, grade?, blade?, coeffs:[…] (Multivector order, Float64 as shortest repr string or exact Int)}], out:{kind, coeffs, display_plain, display_repl}}`:
1. **Blade tables** (as prototype) for: Int-based R1–R6; Signatures `+-`, `-++`, `++-`, `+---`, `-+++`, `--`, `---`; conformal `∞+`, `∅+`, `∞∅+`, `∞+++`, `∞∅++`, `∞∅+++`; DiagonalForms `D"2,3,5"`, `D"1,1,1,0"`, `D"0.3,2.4,1"`; duals `(ℝ^3)'`; mixed `ℝ^2⊕(ℝ^2)'`; tangent `tangent(ℝ^2)`, `tangent(ℝ^3,2,3)`, `tangent(ℝ,2,2)`. Ops: all of §2.2 binary (`∧ ∨ * ⋅ > < >> << ⊛ ∗ × ⊘ >>> ⟇ antidot`) and unary (`! ⋆ complementleft complementlefthodge ~ involute clifford metric cometric even odd real imag`).
2. **Random elements** per signature (n ≤ 5): kinds {Single, Chain g=0..n, Spinor, CoSpinor, Couple (random B), PseudoCouple, Multivector}; coefficients (a) Int uniform in [−5,5] (exact compare), (b) Float64 N(0,1) (compare rel 1e−12, abs 1e−14). All ordered kind pairs × all binary ops; record result kind (tests the type-promotion lattice) and coeffs.
3. **Composite functions**: `inv, /, \, abs, abs2, norm, unit, sqrt, exp, log, sin, cos, tan, sinh, cosh, tanh, asin…` on: vectors, bivectors θ·B with θ ∈ {−π, −1, −0.1, 0, 0.1, 1, π} and B unit in each 2-plane (covers ω² = −1, +1, 0 cases incl. null ∞∅), rotors, Couples, Spinors in 3D/4D; include error records (e.g. `inv(1+2v₁+3v₁₂)`).
4. **Display strings**: for every element in (2) and (3) record `sprint(show,x)` and the REPL `text/plain` form with `:limit=>true`; add hand-picked edge cases from §6.8 (`v⃖`, `-0.0`, `Inf/NaN`, `π`, Rational, Complex, 1e10/1e-10, compact vs full precision), manifold/basis container displays (§3.5, design.md examples), `@basis` tuples for all signatures in (1), `Endomorphism` tables (`cayley`, `operator`).
5. **Parsing/indexing**: `Λ(n).<name>` for random permutations/duplicates of indices (n ≤ 8, 62 with alphanumerics) → sign & blade (duplicates → zero or error); `x(g)`, `x[g]`, `grade(x,g)`.
6. **Complement/Hodge identities** as property checks (no oracle needed, but also dump): `⋆⋆ω`, `!complementleft`, DeMorgan, `ω∧⋆ω = (ω⋅ω)I`.
7. **Linear algebra layer**: `TensorOperator` from random well-conditioned n×n (n=2..5; Int and Float) → `\`, `inv`, `det`, `tr`, `adjugate`, `compound(F,g)`, `outermorphism`, `characteristic`, `eigvals/eigvecs` (real spectra), `roots(a...)` for random polynomials of degree 2–4, `companion`, `vandermonde` (fixed x,y), `cayley` tables; `operator(B)` for bivectors and rotors (and `Matrix(operator(R))`).
8. **Conformal**: `↑`, `↓`, round trip, for random points in `S"∞+++"`, `S"∅+++"`, `S"∞∅+++"`; translators `exp(v∞k)`, rotor+translator compositions (README curves), sampled at 41 t-values (as `readme_plot_goldens.json`).
9. **Fields**: `chainfield(t)` / `chainfield(t,V(2,3,4),V(1,2,3))` on grids (as `readme_plot_goldens.json`), `points(f, r)` for coarse r.
10. **Calculus/tangent**: `V(∇)`, `d`, `∂`, `δ`, `⋆d` on `v1+v2+v3` in `tangent(ℝ^3,2,3)`, boundaries `∂(Λ(tangent(ℝ^n,2,n)).v1…n)` for n=2..5, Taylor products in `tangent(ℝ,2,2)` / `tangent(ℝ^2,2,2)`.
11. **Simplicial**: `skeleton, χ, betti, chain, path` on simplices `Λ(ℝ5).v12 … v12345` and their boundaries.
12. **Docs corpus**: every transcript in §6 (already saved as text) → also emitted as JSON `{source: "file:line", input, output}` pairs for the Lean display tests.

Input distributions: Int coefficients in [−5,5] (exact), Float64 standard normal and log-uniform magnitudes 1e−8…1e8 for display tests, special values {0.0, −0.0, 1.0, π, Inf, NaN} for printing only; angles as above; signatures as in (1); n ≤ 5 for exhaustive pair products (32×32 blades × 20 sigs × 14 ops ≈ 290k records, ~15 MB JSON), n = 6–8 sampled.
