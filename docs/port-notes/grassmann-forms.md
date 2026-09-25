# Grassmann.jl `src/forms.jl` — Lean 4 porting spec

Scope: **everything in `Grassmann.jl/src/forms.jl`** (1765 lines): nested Chain-of-Chains as linear maps
(`TensorNested`, `TensorOperator`/`Endomorphism`, `DiagonalOperator`, `Outermorphism`, `Projector`/`SpectralOperator`,
`Dyadic`), function-call ("form") semantics of algebra elements, subspace projection/embedding, spectral tools
(characteristic polynomial, eigen*, discriminant, Sylvester), metric tensors (`MetricTensor`, `metrictensor`,
`metricextensor`), Cayley tables, Lie brackets, TeX printing. Appendix A covers the closely related simplex utilities
that actually live in `composite.jl` (affineframe, detsimplex, volumes, Cramer solve/inverse, point-in-simplex,
barycentric gradient) because the orchestrator listed them; `gradienthat` lives in Cartan.jl (pointer only).

Source of truth: `/Users/alokbeniwal/chakravala/Grassmann.jl` master @ `4f79a7fdb2d569bf6c13751fad3c078b6c135283`
("improved dispatch", 2026-08-09, Project version 0.8.47). All `forms.jl:N` citations are to that file.
Other citations: `composite.jl`, `multivectors.jl`, `algebra.jl`, `products.jl` (same repo `src/`),
`DirectSum.jl/src/*.jl`, `Leibniz.jl/src/*.jl`, `AbstractTensors.jl/src/AbstractTensors.jl`.

Oracle: the Julia env at `scratchpad/juliaenv` has **registered Grassmann 0.8.46**. `diff` against master forms.jl shows
the only difference is that master adds the three `Base.:(==)` methods (`forms.jl:506`, `:658`, `:755`); in 0.8.46
`==` on `TensorOperator`/`DiagonalOperator`/`Outermorphism` hits a `StackOverflowError`. Everything else in this
report was verified against 0.8.46 with the probe scripts in
`/private/tmp/claude-502/-Users-alokbeniwal-Grassmann/c6cc2308-bfca-4b9a-ad33-d89b110132a8/scratchpad/forms_probe/p*.jl`
(raw transcripts in `.../forms_probe/outputs/p*.txt`, ~3100 lines of verbatim golden output). Line numbers in
0.8.46 stack traces are offset by up to -6 from master.

**Dead code (skip entirely):** `forms.jl:144-291` is one `#= ... =#` block (dualform/dualindex caches, dyadic
`Chain{V,2}` evaluation on mixed spaces, `Chain{V,T}(::AbstractMatrix)` for dyadic spaces); `forms.jl:1273-1326`
(`eigprods`, `getprod`, `eigvecs2`, `tryperm`, `checkmult`) is commented out. `eigprods` is still exported
(`forms.jl:6`) but undefined — drop it.

---

## 1. Purpose & scope

`forms.jl` turns Grassmann's graded algebra into a **linear-algebra layer**:

* A linear map `F : Λ^g V → Λ^h W` is stored as a *nested Chain*: `Chain{V,g,Chain{W,h,T}}` — an outer chain
  indexed by the domain basis blades (columns), whose coefficients are inner chains in the codomain (the column images).
  `TensorOperator` is a thin wrapper that gives this nested chain linear-map semantics (matrix display, `det`, `tr`,
  `inv`, eigen, composition). Same trick for even (`Spinor`), odd (`CoSpinor`=`AntiSpinor`) and full (`Multivector`)
  gradings.
* `Outermorphism` stores the tuple of compound matrices `(Λ¹F, Λ²F, …)` = the extension of `F` to the whole exterior
  algebra, `F(v₁∧…∧v_k) = F(v₁)∧…∧F(v_k)`.
* `DiagonalOperator` is the diagonal special case (stores just the diagonal as a Chain or Multivector).
* `Dyadic(x,y) = x⊗y` and `Projector(v,λ) = λ·(v/|v|)⊗(v/|v|)` are unmaterialised rank-one forms;
  `SpectralOperator` = `Projector` whose `v` is a Chain of eigenvectors and `λ` a Chain of eigenvalues (the result of
  `eigen`).
* Elements act as functions: `t(y...) = t ⋅ (y₁∧…∧y_k)` (multilinear-form evaluation), `W(x)` converts `x` into
  subspace/superspace `W`, `x(i)` extracts a component, etc.
* Spectral utilities: characteristic polynomial (closed forms for n≤4, compound traces otherwise), eigenvalues via
  closed-form polynomial roots (n<5, from `composite.jl`) or LAPACK (n≥5), normalized elementary symmetric
  polynomials (`eigpolys`), Sylvester products, multiplicities, Vandermonde/discriminant, Gershgorin radii.
* Metric layer: `metrictensor(V)` as an `Endomorphism`, its outermorphism `metricextensor`, and the non-diagonal
  `MetricTensor` TensorBundle type.

The port target is a Lean 4 library where operators are dense column-major matrices indexed by type-level shape
data; the Julia oracle provides goldens.

---

## 2. Public API inventory

Conventions: `V`,`W` = manifold type params; `N = mdims(V)`, `M = mdims(W)`; "val" = `value(x)` (the coefficient
tuple). `⋅` is `contraction` (`LinearAlgebra.dot` is routed to `contraction` by `AbstractTensors.jl:260`).
ASCII aliases: `⋅`=`contraction`/`dot`, `⟑`=`wedgedot` (geometric product), `∧`=`wedge`, `∨`=`vee`,
`⊘`=`sandwich` (`algebra.jl:24`), `𝓛`=`Lie`=`LieBracket()`, `Proj`=`Projector`, `AntiSpinor`=`CoSpinor`
(`multivectors.jl:456`), `disc`/`discreal`/`disccomplex` = `discriminant*`, `metriceven`=`metricodd`=`metricextensor`.

### 2.1 Exports declared in forms.jl

| line | exported names |
|---|---|
| 4 | `TensorNested, Projector, Dyadic, Proj, outer, operator, gerschgorin, diag` |
| 5 | `DiagonalOperator, TensorOperator, Endomorphism, Outermorphism, outermorphism` |
| 6 | `sylvester, characteristic, eigen, eigvecs, eigvals, eigpolys, eigprods`(dead)`, eigmults` |
| 7 | `eigvalsreal, eigvalscomplex, eigvecsreal, eigvecscomplex, eigenreal, eigencomplex` |
| 8 | `discriminant, disc, discriminantreal, discreal, discriminantcomplex, disccomplex` |
| 9 | `MetricTensor, metrictensor, metricextensor, InducedMetric` |
| 10 | `vandermondereal, vandermondecomplex` |
| 11 | `@TensorOperator, @Endomorphism, @Outermorphism, @SpectralOperator` (728 re-exports `@Outermorphism`) |
| 384 | `SpectralOperator` |
| 483 | `DiagonalMorphism, DiagonalOutermorphism` |
| 1545 | `𝓛, Lie, LieBracket, LieDerivative, bracket` |

Also defined here but exported elsewhere: `cayley` (`Grassmann.jl:60`), `vandermonde, pfaffian, invdet, adjugate,
cofactor, compound, companion` (`composite.jl:20`), `affineframe` (`composite.jl:905`), `mean, barycenter, curl`
(`composite.jl:962-971`), `contraction, det, tr, isdiag` (`multivectors.jl:27`). Name clash: `sylvester` also exists
in `LinearAlgebra` → `using Grassmann, LinearAlgebra` makes it ambiguous (use `Grassmann.sylvester`).

Not exported but semantically important: `vecdot`, `matrix`, `display_matrix`, `show_matrix`, `chainbasis`,
`evenbasis`, `oddbasis`, `fullbasis`, `chaindyad`, `evendyad`, `odddyad`, `fulldyad`, `gradedoperator`,
`characteristic_exact`, `bivector` (on Endomorphism), `scalarcheck`, `printtex`, `alltex`, `isinduced`,
`antimetrictensor`, `metricdyad`, `cayleyeven`, `cayleyodd`, `transpose_row`, `_transpose`, `matmul`, `matwedge`,
`matvee`, `contraction_mat`, `_axes`, `_codomain`, `getpairs`, `nozero`, `getmult`, `getdiff`, `isrealmatrix`,
`_make_real_disc`, `choicevec`, `subscrepl`, `applyf`.

### 2.2 Element function-call ("form") semantics and conversions

| signature | semantics | line |
|---|---|---|
| `choicevec(M,G,T)`, `choicevec(M,T)` | pick immutable `svec` for `T ∈ (Any,BigFloat,BigInt,Complex{BigFloat},Rational{BigInt},Complex{BigInt})`, else mutable `mvec` scratch buffer | 16-17 |
| `(W::Signature)(b::Chain)` | `= Submanifold(W)(b)` | 22 |
| `(w::Submanifold{Q,M})(b::Chain{V,G,T})` @generated | see §4.1: basis blade → contraction/dyadic eval; `W==V` → relabel; `W⊆V` → projection; `V⊆W` → embedding; `V==V''` → retry with `V''`; else error `"cannot convert from $V to $w"` | 23-90 |
| `(W::Signature)(b::Multivector)` | `= Submanifold(W)(b)` | 92 |
| `(W::Submanifold{Q,M,S})(m::Multivector{V,T})` | same case analysis for multivectors; dyadic basis → error `"Multivector forms not yet supported"` | 93-142 |
| `(t::TensorGraded)(y::TensorGraded...)` | `contraction(t, ∧(y...))`: k-vector evaluated on k vectors | 293 |
| `(t::TensorMixed)(y::TensorGraded...)` | same for Multivector/Spinor/Couple | 294 |
| `(P::Projector)(x)`, `(D::Dyadic)(x)`, `(T::DiagonalOperator{V})(x)`, `(T::TensorOperator{V})(x)`, `(T::Outermorphism{V})(x)` | `contraction(P,x)` (apply) | 396, 451, 496, 572, 723 |
| `(T::…{V})(x,y)` (same 5 types) | bilinear form `vecdot(contraction(T,x), y)` (coefficient dot, metric-free) | 397-399, 452-454, 497-499, 573-575, 724-726 |
| `(M::MetricTensor)(b::Int...)`, `(M)(b::AbstractVector{Int})`, `(M)(b::AbstractRange{Int})` | `Submanifold{M}(b)` = subspace spanned by those indices | 1668-1670 |

Related element-call/getindex semantics defined outside forms.jl (listed because they are in the requested scope
"function-call semantics of elements, getindex with basis"):

| signature | semantics | file:line |
|---|---|---|
| `m::Chain[i::Int]`, `[i::UnitRange]`, `[i::AbstractVector]` | raw coefficient(s) `m.v[i]` (1-based, blade order §3.1) | `multivectors.jl:96-98` |
| `m::Chain{V,G,<:Chain}[i,j]` | `m[j][i]` (row i, column j) | `multivectors.jl:99` |
| `m::Chain[i::AbstractVector{<:Submanifold}]` | `getindex.(m,i)` | `multivectors.jl:161` |
| `m::Chain{V,G}[b::Submanifold{V,G}]` | coefficient at `bladeindex(N,UInt(b))` | `multivectors.jl:162` |
| `m::Chain{V,G,T}[b::Submanifold{V}]` (other grade) | `zero(T)` | `multivectors.jl:163` |
| `(m::Chain{V,G,T})(i::Integer)` / `(Val(i))` | `Single{V,G,basis_i,T}(m[i])` (i-th blade term) | `multivectors.jl:165-170` |
| `m.v12` (`getproperty`) | `m.v[bladeindex]*B` if grade matches else `zero(T)*B` (a `Single`) | `multivectors.jl:172-179` |
| `(t::Multivector)(G::Int)` / `(Val(G))` | grade-G part as `Chain{V,G}` (BoundsError outside `0:N`) | `multivectors.jl:300-304, 325` |
| `t::Multivector[G::Int]`, `[Val(G)]` | grade-G coefficient `Values` (NOT a flat index) | `multivectors.jl:305-314` |
| `(m::Multivector)(g,i)` | `Single` for the i-th blade of grade g | `multivectors.jl:326-329` |
| `m::Multivector[b::Submanifold]` | intends coefficient of blade `b`, but calls `m[basisindex(...)]` which is the *grade* getindex → BoundsError / wrong (Julia bug; port as `m.v[basisindex]`) | `multivectors.jl:405` |
| `(W::Submanifold)(b::Submanifold)` | basis-level projection/embedding/evaluation (`evaluate1`, `evaluate2`) | `DirectSum.jl/src/operations.jl:199-234` |
| `(a::Single)(b)` | `interform(a,b)` → `a(b)` on common manifold `V∪W` | `DirectSum.jl/src/operations.jl:242`, `AbstractTensors.jl:247-256` |

### 2.3 `TensorNested` abstract type and generic nested-chain methods

| signature | semantics | line |
|---|---|---|
| `abstract type TensorNested{V,T} <: Manifold{V,T}` | supertype of all operator types | 298 |
| `Manifold(::TensorNested{V})`, `Manifold(::Type{…})` | `V` | 299-300 |
| `transpose_row(t::Values{N,<:Chain{V}}, i, W=V)` (+`FixedVector`, `Chain{V,1,<:Chain}`) | `Chain{W,1}(t[1][i],…,t[N][i])` = row i | 302-304 |
| `_transpose(t::Values{N,<:Chain{V,1}}, W=V)` @generated | `Chain{V,1}(transpose_row(t,i,W) for i=1:mdims(V))` | 305-306 |
| `transpose(t::Chain{V,1,<:Chain{V,1}})`, `transpose(t::Chain{V,1,<:Chain{W,1}})` | matrix transpose (only grade-1 outer & inner) | 307-308 |
| `inv(t::TensorNested,g)`, `exp(t,g)`, `log(t,g)` | drop metric arg | 309-311 |
| `tr(::TensorNested)`, `tr(::Chain{V,G,<:Chain{W}})` (V≠W) | `throw("LinearAlgebra.tr undefined for …")` | 312-313 |
| `tr(m::Chain{V,G,<:Chain{V,G,T,M},N})` @generated | `Σ_{i=1}^{min(N,M)} m[i][i]` | 314-316 |
| `tr(m::Spinor/AntiSpinor/Multivector{V,<:same{V,T,M},N})` | `Σ value(value(m)[i])[i]`; mismatched inner manifold throws | 317-322 |
| `Matrix(t::TensorAlgebra)` | `matrix(t)` | 324 |
| `matrix(m)` (8 methods) | Julia `Matrix` via `hcat` of column coefficient vectors; inner Zero/TensorGraded entries are first converted with `Chain`, inner mixed with `Multivector`/`Spinor`/`AntiSpinor` | 326-334, 353-355 |
| `Chain(m::Matrix)` | `DyadicChain{…}(m)` — **undefined name, broken** | 336 |
| `Chain{V}(m::Matrix)`, `Chain{V,G}(m::Matrix)`, `Chain{V,G,<:Chain{W,L}}(m)` | intended: columns of `m` become `Chain{W,L}`; in practice dispatch fails (MethodError converting Matrix to Values) | 337-342 |
| `Multivector(m::Matrix)`, `Multivector{V}(m)`, `Multivector{V,<:Chain{W}}(m)`; same for `Spinor`, `AntiSpinor` | intended column-wise nested construction; broken in 0.8.46 (conversion MethodError) | 344-349, 356-361 |
| `display_matrix(m)` (6 methods) | header row `[Submanifold(V), domain basis…]`, then rows `[codomain basis blade, entries…]` (§5) | 365-372 |

### 2.4 `Projector` / `Proj` / `SpectralOperator`

| signature | semantics | line |
|---|---|---|
| `struct Projector{V,T,Λ} <: TensorNested{V,T}; v::T; λ::Λ` | inner ctor normalizes `V` via `DirectSum.submanifold(V)`; default `λ=1` | 374-380 |
| `const Proj = Projector` | alias | 382 |
| `const SpectralOperator{V,T<:Simplex{V},Λ} = Projector{V,T,Λ}` | Proj whose `v` is a Chain of vectors (eigenvectors) | 383 |
| `Proj(v::TensorGraded{V}, λ=1)` | `Proj{V}(v/abs(v), λ)` (normalizes) | 386 |
| `Proj(v::Chain{W,1,<:Chain{V}}, λ=1)` | normalizes each inner vector: `Proj{V}(Chain(value(v)./abs.(value(v))), λ)` | 387 |
| `SpectralOperator(t::AbstractMatrix)`, `SpectralOperator{V}(t)` | `SpectralOperator(Endomorphism(t))` → `eigen` | 389-390 |
| `SpectralOperator(t::Endomorphism)` | `eigen(t)` | 635 |
| `@SpectralOperator ex` | `SpectralOperator(eval(ex))` at macro-expansion time | 392-394 |
| `exp(P::Proj)`, `log(P::Proj)` | `out = exp(Chain(P))[1]` (first column of matrix exp); `Proj{V}(out/sqrt(out[1]))` — heuristic, see §4.6 | 401-408 |
| `det(P::Proj)` | `Chain{V,0}(N≠1 ? 0 : P.λ[1])` | 409 |
| `∧(P::Proj)` | `!det(P)` (complement → pseudoscalar chain) | 410 |
| `exp/log/inv(P::SpectralOperator)` | map over eigenvalues `Proj{V}(P.v, map(f,P.λ))` | 411-413 |
| `invdet(P::SpectralOperator)` | `(inv(P), det(P))` | 414 |
| `tr(P::Proj)` | `sum(value(P.λ))` | 415 |
| `det(P::SpectralOperator)` | `Chain{V,0}(prod(P.λ))` — bug: `prod` of a Chain returns the Chain itself (§8.4) | 416 |
| `∧(P::SpectralOperator)` | `!det(P)` | 417 |
| `P[i,j]` | `P.v[i]*P.v[j]` (ignores λ, no conj) | 419 |
| `P[i]` (SpectralOperator) | `Proj{V}(P.v[i], P.λ[i])` (i-th rank-one term) | 420 |
| `P[i,j]` (SpectralOperator) | `sum(column(P.v,i).*column(P.v,j))` = `Σ_k v_k[i] v_k[j]` (ignores λ) | 421 |
| `Leibniz.check_parnot(::Type{<:Projector}) = true`; `extend_parnot(Projector)` | Projector coefficients print without parentheses | 424-425 |
| `show(io,P)` | §5.3 | 427-428 |
| `Chain{V}(P::SpectralOperator)` | `Σ_k outer(v_k*λ_k, v_k)` | 431 |
| `Chain{V}(P::Proj)`, `Chain(P)` | `outer(P.v*P.λ, P.v)` | 432-433 |
| `x::Real/Complex * P`, `P * x` | `Proj(P.v, x*P.λ)` (λ scaled, v untouched) | 435-438 |
| `Endomorphism(P)`, `TensorOperator(P)` | via `Chain(P)` | 618, 626 |
| `Dyadic(P)` | `Dyadic(P.v*P.λ, P.v)` | 448 |

### 2.5 `Dyadic`

| signature | semantics | line |
|---|---|---|
| `struct Dyadic{V,X,Y} <: TensorNested{V,X}; x::X; y::Y` | `x⊗y`; `V` taken from `y`'s manifold | 440-445 |
| `Dyadic(x::TensorGraded, y::TensorGraded{V})` | ctor | 447 |
| `x ⊗ y` for two `TensorGraded` | `Dyadic(x,y)`; if either side has grade 0 → `x*y` | `algebra.jl:150-152` |
| `Dyadic(D::Dyadic)` | identity | 449 |
| `expm1/exp/log(D)` | via `Endomorphism(D)` | 456-458 |
| `tr(D)` | `value(D.x)⋅value(D.y)` (coefficient dot) | 459 |
| `D[i,j]` | `D.x[i]*D.y[j]` | 461 |
| `transpose(D)` | `Dyadic(D.y, D.x)` | 462 |
| `show` | `"(" x ")⊗(" y ")"` | 464 |
| `Chain{V}(D)`, `Chain(D)` | `outer(D.x, D.y)` | 466-467 |
| `x::Real/Complex * D`, `D * x` | scale `D.x` | 469-472 |
| `Endomorphism(D)`, `TensorOperator(D)` | via `Chain(D)` | 619, 627 |

### 2.6 `DiagonalOperator` / `DiagonalMorphism` / `DiagonalOutermorphism`

| signature | semantics | line |
|---|---|---|
| `struct DiagonalOperator{V,T<:TensorAlgebra{V}} <: TensorNested{V,T}; v::T` | diagonal stored as a Chain (any grade) or Multivector (or Spinor/AntiSpinor) | 476-480 |
| `DiagonalMorphism{V,T<:Chain{V,1}}`, `DiagonalOutermorphism{V,T<:Multivector{V}}` | aliases | 481-482 |
| `DiagonalMorphism(t::TensorGraded{V,1})` | `DiagonalOperator(Chain(t))` | 484 |
| `DiagonalMorphism(t::DiagonalOutermorphism)` | grade-1 part: `DiagonalOperator(value(t)(Val(1)))` | 485 |
| `DiagonalOutermorphism(t::Multivector)` | `DiagonalOperator(Multivector(t))` | 486 |
| `DiagonalOutermorphism(t::Chain{V,1})`, `(t::DiagonalMorphism)`, `(t::AbstractMatrix)`, `{V}(t::AbstractMatrix)` | `outermorphism(DiagonalOperator(...))` | 487-489, 492 |
| `DiagonalMorphism(t::AbstractMatrix)`, `DiagonalOperator(t::AbstractMatrix)`, `{V}(m)` | diagonal of the matrix: `Chain{V}(m[i,i] for i=1:N)`; `V = Submanifold(size(m,1))` default | 490-494 |
| `DiagonalOperator(t::Endomorphism)` | `DiagonalOperator(diag(t))` | 636 |
| `DiagonalOperator(t::Outermorphism)` | `outermorphism(DiagonalOperator(TensorOperator(t.v[1])))` | 737 |
| `value(t)` | `t.v` | 501 |
| `matrix(m)` | `matrix(TensorOperator(m))` | 502 |
| `t[i,j]` | `i≠j ? zero(valuetype(value(t))) : value(value(t))[i]` | 503 |
| `t[i]` | `value(t)(i)` → `Single` (i-th diagonal entry times its basis blade) | 504 |
| `a==b` | `value(a)==value(b)` (master only) | 506 |
| `zero(t)`, `zero(::Type)` | zero diagonal | 508-509 |
| `scalar(m)` | `tr(m)/length(value(m))` (Float) | 511 |
| `tr(m)` | `sum(value(value(m)))` | 512 |
| `det(m)` | `!∧(m)` → `Chain{V,0}` | 513-514 |
| `∧(m::DiagonalMorphism{V})` | `Chain{V,N}(prod(diagonal))` | 515 |
| `∧(m::DiagonalOutermorphism{V})` | `value(m)(Val(N))` (top-grade part) | 516 |
| `compound(m::DiagonalMorphism{V},Val(0))` | `DiagonalOperator(Chain{V,0}(1))` | 517 |
| `compound(m::DiagonalMorphism{V},Val(G))` @generated | `DiagonalOperator(Chain{V,G}(Π_{i∈I} d_i for I in indexbasis(N,G)))` | 518-520 |
| `outermorphism(m::DiagonalMorphism{V})` @generated | `DiagonalOperator(Multivector{V}(1, Π_{i∈I} d_i for every blade I≠∅ in full basis order))` | 521-523 |
| `cofactor(t)` | `adjugate(t)` | 525 |
| `adjugate(t::DiagonalMorphism{V})` | `DiagonalOperator(Chain{V}(reverse(values of compound(t,N-1))))` = `(Π_{j≠i} d_j)_i` | 526-528 |
| `adjugate(t::DiagonalOutermorphism)` | `outermorphism(adjugate(grade-1 part))` | 529 |
| `invdet(t)` | `(inv(t), det(t))` | 530-531 |
| `inv/exp/expm1/log(t::DiagonalMorphism)` | elementwise `map(f, value(t))` | 532-537 |
| `inv/exp/expm1/log(t::DiagonalOutermorphism)` | `outermorphism(DiagonalOperator(map(f, grade-1 part)))` | 532-537 |
| `_axes(t)` | `(1:gdims(T), 1:gdims(T))` for Chain, else `(1:length(t.v))²` | 539-540 |
| `summary`, `show`, `show(::MIME"text/plain")` | via `TensorOperator(X)` display | 543-553 |
| `Endomorphism(t)`, `TensorOperator(t)` for Chain/Spinor/AntiSpinor/Multivector diagonals @generated | materialize: columns `d_i * basis_i` | 620-623, 628-631 |
| `eigvecs(X)`, `eigvecsreal(X)`, `eigvecscomplex(X)` | `DiagonalOperator(map(unit, diag))` (unit = sign; `Complex` for the complex variant) | 1336-1346 |
| `characteristic(X)`, `characteristic(X,m)` | `characteristic_exact` | 1441, 1465 |
| `gerschgorin(x::DiagonalOperator{V})` | `zero(Chain{V,1,Int})` | 1519 |
| `map(fn,x)` | `DiagonalOperator(map(fn,value(x)))` | 1125 |

### 2.7 `TensorOperator` / `Endomorphism`

| signature | semantics | line |
|---|---|---|
| `struct TensorOperator{V,W,T<:TensorAlgebra{V,<:TensorAlgebra{W}}} <: TensorNested{V,T}; v::T` | `V` = domain (outer), `W` = codomain (inner) | 555-561 |
| `Endomorphism{V,T} = TensorOperator{V,V,T}` | alias | 563 |
| `Endomorphism(t::TensorAlgebra{V,<:TensorAlgebra{V}})` | wrap | 564 |
| `TensorOperator(t::Chain{V,G,T,N}...)` / `Endomorphism(...)` (exactly N args of length N) | `op(Chain{V,G}(t...))` columns | 565-566 |
| `TensorOperator(t::Spinor/CoSpinor/Multivector...)` (N args) | nested mixed operator | 567-569 |
| `@TensorOperator ex`, `@Endomorphism ex` | eval at expansion time | 577-582 |
| `value(t)` | `t.v` | 584 |
| `matrix(m)` | `matrix(value(m))` | 585 |
| `compound(m,g)` | `TensorOperator(compound(value(m),g))` (compound in `composite.jl:715-720`) | 586-587 |
| `t[i,j]` | `value(value(t.v)[j])[i]` (row i, column j) | 588 |
| `t[i]` | `value(t.v)[i]` (column i as Chain) | 589 |
| `lastindex(t)` | `lastindex(value(t))` | 590 |
| `transpose(t)` | `TensorOperator(transpose(value(t)))` — correct only for grade-1/grade-1; other gradings hit `transpose(::Number)=identity` (bug) | 591 |
| `pfaffian(A::Endomorphism)` | `pfaffian(bivector(A))` (`composite.jl:888-895`) | 592 |
| `scalar(m::Endomorphism)` | `tr(m)/length(value(m))` | 593 |
| `tr(m)` | `tr(value(m))` | 594 |
| `det(t)` | `!∧(value(t))` → `Chain{V,0}` (non-square: complement of the column wedge) | 595 |
| `∧(t)` | `∧(value(t))` = wedge of all columns (`algebra.jl:115`) | 596 |
| `⊕(t::Chain{V,G}...)` | `TensorOperator(t...)` (only works as an N-ary call, not chained binary) | 597 |
| `zero(t)`, `zero(::Type)` | zero operator | 599-600 |
| `invdet(t::TensorOperator{…,<:Chain})` | `(TensorOperator(i), d)` from `invdet(value(t))` (`composite.jl:774`) | 602-605 |
| `log(t::Endomorphism{V,<:Chain})` | `Endomorphism{V}(log(Matrix(t)))` (LinearAlgebra matrix log) | 606 |
| `inv/adjugate/cofactor(t::TensorOperator{…,<:Chain})` | wrap the nested-chain result (`composite.jl:761-812`, Cramer/wedge based) | 607-609 |
| `exp/expm1(t::Endomorphism{V,<:Chain})` | wrap (`composite.jl:196-300`, 2×2 closed form, else Higham Padé scaling-squaring) | 610-612 |
| `bivector(A::Endomorphism{V,<:Simplex})` @generated | `Chain{V,2}(A[j,i] for (i<j) in indexbasis(N,2) order)` (lower triangle) | 614-616 |
| `Endomorphism(m::AbstractMatrix)` | `Endomorphism{Submanifold(size(m,1))}(m)` | 624 |
| `TensorOperator(m::AbstractMatrix)` | `TensorOperator{Submanifold.(size(m))...}(m)` — non-square broken (DimensionMismatch) | 632 |
| `TensorOperator{V,W}(m::AbstractMatrix)` | `TensorOperator(Chain{V}(Chain{W,1}(m[:,j]) for j=1:mdims(V)))` | 633 |
| `diag(t::TensorOperator{V,W,<:Simplex{V}})` | `Chain{X,1}(t[i,i] for i=1:mdims(X))`, `X` = smaller of V,W | 638-641 |
| `diag(t::Endomorphism{V,<:Simplex{V}})` | `Chain{V,1}(t[i,i])` | 642-644 |
| `diag(t::Endomorphism{V,<:Chain{V,G}})` | `Chain{V,G}(t[i,i] for i=1:binomial(N,G))` | 645-647 |
| `diag(t::Endomorphism{V,<:Spinor})` | `Spinor{V}(t[i,i] for i=1:2^(N-1))` | 648-650 |
| `diag(t::Endomorphism{V,<:CoSpinor})` | returns a **Spinor** (bug; should be CoSpinor) | 651-653 |
| `diag(t::Endomorphism{V,<:Multivector})` | `Multivector{V}(t[i,i] for i=1:2^N)` | 654-656 |
| `a==b` | `value(a)==value(b)` (master only) | 658 |
| `_axes`, `summary`, `show`, `show(::MIME"text/plain")`, `show_matrix` | §5 | 660-710 |
| `Endomorphism/TensorOperator(t::Outermorphism)` | full `2^M×2^N` Multivector-of-Multivector matrix | 765-774 |
| `eigvecs(X::Endomorphism{V,<:Simplex})` | `Endomorphism{V}(eigvecs(Matrix(X)))` (LAPACK) | 1338 |
| `eigvecsreal`, `eigvecscomplex` | `map(Float64,…)`, `map(Complex,…)` of the above | 1342, 1347 |
| `map(fn,x::TensorOperator)` | apply `fn` to every scalar entry (Chain/Spinor/AntiSpinor/Multivector nestings) | 1126-1129 |
| `complementright/complementleft/complementrighthodge/complementlefthodge/metric/cometric(a::Endomorphism{V,<:Chain})` | `map(op, a)` — elementwise on entries (meaningless for scalar entries; yields `UniformScaling`/`UInt` junk in Julia) | 1025-1027 |
| `a ⊘ b` for `TensorOperator{V,W,<:Chain/Spinor/AntiSpinor/Multivector}`, `b::TensorAlgebra{W}` | sandwich every column by `b` | 1157-1162 |

### 2.8 `Outermorphism`

| signature | semantics | line |
|---|---|---|
| `struct Outermorphism{V,T<:Tuple} <: TensorNested{V,T}; v::T` | tuple of compounds `(Λ¹F,…,Λ^{min(N,M)}F)`, each `Chain{V,g,Chain{W,g}}`; grade 0 implicit (=1) | 714-717 |
| `outermorphism(t::Chain{V,1,<:TensorGraded{W,1}})` @generated | `Outermorphism{V}((compound(t,Val(g)) for g=1:min(N,M)))` | 719-721 |
| `Outermorphism(t::AbstractMatrix)` | `Outermorphism(Endomorphism(t))` | 733 |
| `Outermorphism(t::Simplex)`, `Outermorphism(t::TensorOperator{…,<:Simplex})`, `outermorphism(t::TensorOperator{…,<:Simplex})` | `outermorphism(value(t))` | 734-736 |
| `@Outermorphism ex` | `Outermorphism(Endomorphism(eval(ex)))` | 729-731 |
| `value(t)` | `t.v` | 738 |
| `matrix(m)` | `matrix(TensorOperator(m))` | 739 |
| `t[i]` | `i==0 ? Chain{V,0}((Chain(One(V)),)) : t.v[i]` | 740 |
| `pfaffian(A)` | `pfaffian(compound(A,Val(1)))` | 741 |
| `transpose(m)` | `Outermorphism(map(transpose,value(m)))` — **MethodError** (no `Outermorphism(::Tuple)` ctor); intended `Outermorphism{V}(…)` | 742 |
| `scalar(m)` | `tr(m)/2^N` | 743 |
| `tr(m)` | `1 + Σ_g tr(Λ^gF)` | 744 |
| `det(m)` | `!∧(m)` | 745 |
| `∧(m)` | top compound's column(s): if one column return it (a `Chain{W,N}`), else `Chain{V,length(v)}(Real.(cols))` | 746-753 |
| `a==b` | value equality (master) | 755 |
| `zero(t)`, `zero(::Type)` @generated | zero each compound | 757-760 |
| `compound(m,g)` | `TensorOperator(value(m)[g])` | 762-763 |
| `invdet(t)` | `(Outermorphism(inv F), det)` from `invdet(t.v[1])` | 776-779 |
| `adjugate/cofactor/inv/exp/expm1/log(t)` | `Outermorphism(op(t.v[1]))` (recompute compounds from the grade-1 result) | 780-782 |
| `_codomain(t)`, `__axes` | codomain `W` from `T.parameters[1]` | 784-786 |
| `_axes(t)` | `(1:2^M, 1:2^N)` | 787 |
| `summary`, `show` (→ `TensorOperator(X)`), `show(::MIME"text/plain")` | §5 | 790-800 |
| `DiagonalOperator(t::Outermorphism)` | diagonal outermorphism of the grade-1 diagonal | 737 |
| `eigvecs(X)`, `eigvecsreal`, `eigvecscomplex`, `characteristic(X)` (N<5 via grade 1), `gerschgorin(X)` | delegate to grade-1 compound | 1339, 1343, 1348, 1442-1444, 1466-1468, 1520 |
| `eigpolys(X::Outermorphism, Val(1))` | `scalar(TensorOperator(value(x)[1]))` — references undefined `x` (should be `X`) → UndefVarError | 1264 |

### 2.9 Cayley tables, companion, bases, operator constructors

| signature | semantics | line |
|---|---|---|
| `cayley(V, op=*)` | `TensorOperator(Multivector{V}([Multivector{V}(op.(bas,b)) for b∈bas]))`, `bas=Λ(V).b`; entry `(i,j) = op(bas_i, bas_j)` | 807-810 |
| `cayley(V, G::Int, op=*)`, `cayley(V, Val(G), op=*)` | grade-G sub-table, `Chain{V,G}` nesting | 811-815 |
| `cayleyeven(V,op=*)`, `cayleyodd(V,op=*)` | even (Spinor) / odd (AntiSpinor) sub-tables | 816-823 |
| `cayley(b::AbstractVector)`, `cayley(b,op)`, `cayley(a,b)`, `cayley(a,b,op)` | Julia matrices: `a*transpose(b)` or `[op(x,y) for x∈a, y∈b]` | 824-827 |
| `companion(x...)`, `companion(x::Chain)`, `companion(x::Values{N})` @generated | `N×N` companion of monic `z^N + x_N z^{N-1} + … + x_1`: column i (<N) = basis vector `e_{i+1}`, column N = `-x` | 829-835 |
| `chainbasis(V, G=1)` | `Values` of the grade-G basis blades (`Λ(V).b[binomsum(N,G)+1 : +binomial(N,G)]`) | 1175-1180 |
| `chaindyad(V,G)` | `Chain.(chainbasis(V,G))` | 1174 |
| `fullbasis(V)`, `fulldyad(V)` | all `2^N` blades in grade order; `Multivector.(…)` | 1171-1172 |
| `evenbasis(V, even=true)`, `oddbasis(V)`, `evendyad`, `odddyad` | even/odd blades in grade order (grades 0,2,4… / 1,3,5…) | 1205-1213 |
| `Chain{V}(I)` | `Chain{V,1}(I)` | 1164 |
| `Chain{V,G}(t::UniformScaling)` | `t.λ * Chain{V,G}(I)` | 1165 |
| `Chain{V,G}(I::UniformScaling{Bool})` | identity `TensorOperator(Chain{V,G}(chaindyad(V,G)))` | 1166 |
| `Spinor{V}(I)`, `AntiSpinor{V}(I)`, `Multivector{V}(I)` (+ λ·I variants) | identity operators on even/odd/full algebra | 1161, 1167-1169 |
| `operator(t::TensorAlgebra, G::Int)` / `operator(t, Val(G)=Val(1))` | matrix of `x ↦ x ⊘ t` on the grade-G basis: `TensorOperator(Chain{V,G}(chainbasis(V,G) .⊘ Ref(t)))` | 1182, 1186-1188 |
| `operator(t::TensorTerm{V}, G)` | if `isdiag(V)`: `DiagonalOperator(operator(Chain(t),G))` (diag extracted) else general | 1183-1185 |
| `operator(fun, V, Val(G)=Val(1))`, `operator(fun,V,G::Int)` | `TensorOperator(Chain{V,G}(fun.(chainbasis(V,G))))` (matrix of an arbitrary linear function) | 1198-1201 |
| `outermorphism(t::TensorAlgebra)` | `gradedoperator(t)` | 1190 |
| `gradedoperator(t::TensorTerm{V})` | `isdiag(V) ? outermorphism(operator(t)) : gradedoperator(Chain(t))` | 1191-1193 |
| `gradedoperator(t::TensorAlgebra{V})` @generated | `Outermorphism{V}((value(operator(t,Val(G))) for G=1:N))` — each grade's sandwich matrix independently | 1194-1196 |

### 2.10 Spectral functions

| signature | semantics | line |
|---|---|---|
| `getpairs(n,i)` (codegen) | `Values(x[j]-x[i] for j in indices(complement of e_i))` (all j≠i ascending) | 1217-1220 |
| `nozero(x)` | `iszero(x) ? one(x) : x` | 1221 |
| `getmult(n,i)` / `getdiff(n,i)` (codegen) | `1 + #{j≠i: x_j==x_i}` / `Π_{j≠i} nozero(x_j-x_i)` | 1222-1223 |
| `sylvester(X::TensorNested)` | `sylvester(eigvals(X))` | 1224 |
| `sylvester(x::Chain{V,1})` @generated | `Chain{V}(Π_{j≠i} nozero(x_j - x_i))_i` | 1225-1227 |
| `eigmults(X::TensorNested)`, `eigmults(x::Chain{V,1})` | multiplicities `Chain{V}(1+#{j≠i: x_j = x_i})_i` | 1228-1231 |
| `eigpolys(X::TensorNested{V})` | `N≠2`: `Chain{V}(reverse(characteristic(X)) ./ binomial.(N,1:N) .* (-1).^(1:N))`; `N==2`: `Chain{V}(eigpolys(X,1), eigpolys(X,2))` | 1233-1240 |
| `eigpolys(x::Chain{V,1})`, `eigpolys(x::Multivector{V})` @generated | `Chain{V}(eigpolys(x,Val(i)) for i=1:N)` | 1241-1246 |
| `eigpolys(X, G::Int)` | `eigpolys(X,Val(G))` | 1247 |
| `eigpolys(::TensorAlgebra, Val(0))` | `1` | 1248 |
| `eigpolys(X::TensorNested{V}, Val(G))` | `N≠G`: `c = characteristic(X,Val(N-G+1))/binomial(N,G)`, return `isodd(G) ? -c : c`; `N==G`: `Real(det(X))` | 1249-1257 |
| `eigpolys(x::Chain{V,1}, Val(G))` | `N≠G ? scalar(compound(DiagonalOperator(x),Val(G))) : prod(value(x))` = `e_G(x)/C(N,G)` | 1258-1260 |
| `eigpolys(x::Multivector{V}, Val(G))` | `N≠G ? scalar(DiagonalOperator(x(Val(G)))) : eigpolys(x(Val(1)),Val(G))` | 1261-1263 |
| `eigpolys(X::Endomorphism{V,<:Simplex}, Val(1))`, `(X::DiagonalMorphism, Val(1))` | `scalar(X)` = `tr/N` | 1265-1266 |
| `eigpolys(X::DiagonalMorphism[,G])`, `eigpolys(X::DiagonalOutermorphism[,G])` | via stored diagonal (`Val(1)` for outermorphism: `scalar(DiagonalOperator(value(X)(G)))`) | 1267-1271 |
| `f(X,i::Int)`, `f(X,Val(i))` for `f ∈ {eigvecs,eigvecsreal,eigvecscomplex,eigvals,eigvalsreal,eigvalscomplex,eigen,eigenreal,eigencomplex}` | `f(X)[i]` | 1328-1333 |
| `eigvecs(X::TensorAlgebra)` | `eigvecs(operator(X))` | 1334 |
| `eigvecs(X::SpectralOperator)` | `TensorOperator(X.v)` | 1335 |
| `eigvecscomplex(X::TensorAlgebra)` | `eigvecscomplex(operator(X))` | 1344 |
| `eigvals(X::SpectralOperator)` | `X.λ` | 1349 |
| `eigvals(X::TensorAlgebra)` | `eigvals(operator(X))` | 1350 |
| `eigvals(X::Scalar{V})` | `Chain{V}(abs2(X)*ones(N))` (sandwich by a scalar = `|s|²I`) | 1351 |
| `eigvals(X::TensorGraded{V,G})` | if supermanifold is 2D or 3D Euclidean (`S==2 \|\| S===S"2" \|\| S===3 \|\| S===S"3"`) and G even: `eigvals(T<:Chain ? Spinor(X) : Couple(X))`; else `eigvals(operator(X))` | 1352-1359 |
| `eigvals(X::Union{Couple,Spinor})` | 2D: `X2=X*X; re=scalar(X2); sq=sqrt(abs2(imaginary(X2)))` → `Chain{V}(re-i·sq, re+i·sq)`; 3D: same plus third `Real(abs2(X))`; else via `operator` | 1360-1373 |
| `eigvals(X::TensorNested{V})` | `N==1`: `X[1]` (a column Chain!); `N<5`: `Chain{V}(monicroots(characteristic(X)))`; else `Chain{V}(Values{N}(eigvals(eigen(Matrix(X)))))` | 1374-1383 |
| `eigvalsreal(X::TensorNested{V})` | same with `monicrootsreal` / `Values{N,Float64}` | 1384-1393 |
| `eigvalscomplex(...)` (TensorAlgebra, Scalar, TensorGraded, Couple/Spinor, TensorNested) | complex-typed analogues | 1394-1427 |
| `eigen(X::TensorNested{V})` | `eig=eigen(Matrix(X))`; `Proj(value(Endomorphism{V}(eigvecs(eig))), Chain{V}(Values{N}(eigvals(eig))))` → SpectralOperator | 1428-1431 |
| `eigenreal`, `eigencomplex` | with `Float64`/`Complex` maps | 1432-1439 |
| `characteristic(X::Endomorphism{V,<:Simplex})` | closed forms N=1..4 (§4.9), else `characteristic_exact` | 1445-1462 |
| `characteristic(X, m::Int/Val)` | single coefficient `c_{m-1}` (1-based m) | 1464-1498 |
| `characteristic_exact(X)` | via traces of all compounds (§4.9); exact over ℤ | 1500-1512 |
| `characteristic_exact(X::TensorNested{V}, Val(M))` | `c = tr(compound(X,Val(N-M+1)))`; `isodd(N-M) ? c : -c` | 1513-1517 |
| `gerschgorin(x::Endomorphism)` | `Values` of row sums of `|off-diagonal|`: `sum.(abs.(rows of X - diag(X)))` | 1521-1523 |
| `gerschgorin(x::Outermorphism)` | grade-1 | 1520 |
| `isrealmatrix(x)`, `_make_real_disc(x,Δ)` | real part if entries Real | 1525-1526 |
| `vandermonde(x::Chain{V})`, `vandermonde(x::Values{N})` | `TensorOperator` with `V[i,j] = x_i^{j-1}` | 1528-1529 |
| `vandermonde(x::Endomorphism)`, `vandermondereal`, `vandermondecomplex` | of eigvals / eigvalsreal / eigvalscomplex | 1530-1532 |
| `discriminant(x)` | `value(Single(det(vandermonde(x))))^2` = `Π_{i<j}(x_j-x_i)²` | 1533 |
| `discriminant(x::Endomorphism)`, `discriminantreal`, `discriminantcomplex` | N=2: `tr²-4det`; else `_make_real_disc(x, det(vandermonde(eig*))²)` | 1534-1542 |
| `disc, discreal, disccomplex` | aliases | 1543 |

### 2.11 Contraction / product rules (all `⋅` unless stated)

| lhs, rhs | result | line |
|---|---|---|
| `vecdot(x::Chain{V,G}, y::Chain{V,G})` | `value(x)⋅value(y)` coefficient dot (no metric, no conj beyond `LinearAlgebra.dot`) | 839 |
| `vecdot` cross-type table (36 methods) | same-grade coefficient dot; parity/grade mismatch → 0; Multivector extracts matching grade/parity; Couple/PseudoCouple via `multispin` | 840-881 |
| `outer(a::Chain{W}, b::Chain{V,1})` | `Chain{V,1}(a .* conj.(value(b)))` = matrix `a bᴴ` (columns `a·conj(b_j)`) | 885 |
| `outer(a::Derivation, b)`, `outer(a, b::Derivation)` | convert derivation with `V(a)` | 883-884 |
| `contraction_metric(a,b,g)`, `wedgedot_metric(a,b,g)` with a TensorNested side | drop `g` | 887-892 |
| `Proj/Dyadic/Spectral × TensorOperator/Outermorphism/Diagonal*` (26 methods) | delegate by converting to nested chain/`Endomorphism` | 894-919 |
| `Proj ⋅ x::TensorGraded` | `P.v ⊗ (P.λ*(P.v⋅x))` | 921 |
| `Dyadic ⋅ x` | `D.x ⊗ (D.y⋅x)` | 922 |
| `x ⋅ Dyadic` | `(x⋅D.x) ⊗ D.y` | 923 |
| `x ⋅ Proj` | `((x⋅P.v)*P.λ) ⊗ P.v` | 924 |
| `Dyadic ⋅ Dyadic` | `(a.x*(a.y⋅b.x)) ⊗ b.y` | 925 |
| `Dyadic ⋅ Proj`, `Proj ⋅ Dyadic`, `Proj ⋅ Proj` | analogous; results are `Dyadic` | 926-928 |
| `Dyadic ⋅ scalar`, `Proj ⋅ scalar term/Chain{V,0}` | scale (`Dyadic(x*b,y)`, `Proj(v, λ*b)`) | 929-931 |
| `Proj{V,<:Chain{V,1,<:TensorNested}} ⋅ scalar` | `Proj(Chain(contraction.(value(a.v),b)))` | 932 |
| `Chain{W,1,<:Dyadic} ⋅ Chain{V,1}` | `Chain{W,1}(D_k⋅b)_k` | 934 |
| `Proj{W,<:Chain{W,1,<:TensorNested}} ⋅ b` | `a.v : b` | 935 |
| `a::Chain{V,1,<:Chain} : b::Chain{V,1,<:Chain}` | `Σ_k a_k⋅b_k` (Frobenius-type double contraction) | 936 |
| `a::Chain{W,1,<:Dyadic} : b::Chain{V,1}` | `Σ_k D_k⋅b` | 937 |
| `a::Chain{W} ⋅ b::Chain{V,G,<:Chain}` | row-vector × matrix: `Chain{V,G}(value(a)⋅value(col_j))_j` | 940 |
| `a::Chain{W,L,<:Chain{U,H},N} ⋅ b::Chain{V,G,<:Chain{W,L},M}` | composition `A∘B`: columns `a⋅b_j` | 941 |
| `a::Multivector{W,<:Multivector} ⋅ b::Multivector{V,<:Multivector{W}}` | composition (full algebra) | 942 |
| `a::TensorTerm{W} ⋅ b::Chain{V,G,<:Chain}` | `contraction(Chain(a),b)` | 944 |
| `x::Chain{V,G,<:Chain} ⋅ y::Single{V,G}` / `y::Submanifold{V,G}` | `value(y) * x[bladeindex(y)]` / `x[bladeindex(y)]` (pick column) | 945-946 |
| `x::Chain{V,L,<:Chain{V,G},N} ⋅ y::Chain{V,G,<:Chain{V,L},N}` | `Chain{V,G}(contraction_mat(x, y_j))` (square composition, grades swap) | 948-949 |
| `x::Chain{W,L,<:Chain{V,G},N} ⋅ y::Chain{V,G,T,N}` | matrix·vector `Chain{V,G}(matmul(x,y))` (metric-free) | 950 |
| `x::Chain{W,L,<:Multivector{V},N} ⋅ y::Chain{V,G,T,N}` | `Multivector{V}(matmul)` | 951 |
| `x::Multivector{W,<:Chain{V,G},N} ⋅ y::Multivector{V,T,N}` / `<:Multivector{V}` | matmul | 952-953 |
| `matmul(x::Values{N,<:Single}, y)` | `Values(y[i]*value(x[i]))` (diagonal-ish) | 954-956 |
| `matmul(x::Values{N,<:Chain{V,G}/Multivector/Spinor/AntiSpinor}, y::Values{N})` @generated | `out_j = Σ_i x[i][j]*y[i]` | 957-968 |
| `matwedge`, `matvee` | same with `∧`/`∨` instead of `*` | 969-974 |
| `Spinor{W,<:Spinor{V},N} ⋅ Spinor{V,T,N}`, AntiSpinor analogue | matmul | 976-977 |
| `Dyadic{V,<:Chain{V,1,<:Chain},<:Chain{V,1,<:Chain}} ⋅ b` | `Σ_k x_k⊗(y_k⋅b)` (sum of dyads) | 979 |
| `Dyadic{V,<:Chain{V,1,<:Chain}} ⋅ b` / `Dyadic{V,T,<:Chain{V,1,<:Chain}} ⋅ b` | `Σ_k x_k⊗(y⋅b)` / `Σ_k x⊗(y_k⋅b)` | 980-981 |
| `SpectralOperator ⋅ b::TensorGraded` | `Σ_k v_k ⊗ (λ_k*(v_k⋅b))` | 982 |
| `SpectralOperator{V,<:Chain{W,1,<:Chain{V,1}}} ⋅ b::TensorGraded{V,1}` | `Σ_k v_k ⊗ (λ_k * (v_k⋅b)[1])` | 983 |
| `+(a::Proj{V}...)` | `Proj{V}(Chain(eigvec.(a)), Chain(eigval.(a)))` — `eigvec`/`eigval` undefined → UndefVarError | 985 |
| `+(a::Dyadic{V}...)`, `+(a::TensorNested{V}...)` | `Proj(Chain(a...))` / `Proj(Chain(Dyadic.(a)...))` — broken (MethodError `Dyadic(::Int)` or `conj(::Dyadic)`) | 986-987 |
| `plus(Proj-of-nested, nested)`, reverse, `+(Proj-of-nested, Proj-of-nested)` | concatenate term lists | 988-990 |
| `+(SpectralOperator, SpectralOperator)` | `Chain(Values(v_a..., v_b...))` — returns a bare Chain of all eigenvectors, drops λ | 991 |
| `+(a,b,c...)` on TensorNested | left fold | 995 |
| `+(a::TensorNested)` / `-(a)` / `minus(a,b)` | `a` / `-1a` / `a+(-b)` | 996-998 |
| `a::Number * b::TensorNested{V}`, `b * a` | `(a*One(V))*b` (falls into more specific scalar rules) | 999-1000 |
| `scalar ⟑ nested`, `nested ⟑ scalar`, `scalar ⟑ Proj-of-nested` | `b⋅a`, `a⋅b`, `Proj{V}(a*b.v)` | 1001-1004 |
| `⟑` between Chain and Chain-of-Chains (7 methods) | `contraction` (geometric product of operators = composition) | 1006-1012 |
| `DiagonalOperator{V,<:Chain{V,G}} ∧/∨ Chain{V,G}` | elementwise `.∧`/`.∨` of values | 1016 |
| `Diag ∧/∨ Diag` | elementwise, `DiagonalOperator` | 1017 |
| `Endomorphism{W,<:TensorGraded} ∧/∨ Endomorphism{V,<:Chain{V,G}}` | `TensorOperator(Chain{V,G}(a ∧ b_j))` | 1019 |
| `Endomorphism{W,<:Chain} ∧ Chain{V,G}` / `∨` | `matwedge` / `matvee` (entries combined with ∧/∨ instead of *) | 1023-1024 |
| `Diag{Chain{V,G}} ⋅ Chain{V,G}`, `Chain ⋅ Diag`, `Diag ⋅ Diag` | elementwise product | 1029-1031 |
| `DiagonalOutermorphism ⋅ Chain{V,G}` (and reverse) | elementwise with grade-G part | 1033-1034 |
| `DiagonalOutermorphism ⋅ Spinor` (and reverse) | elementwise with `even(value(a))` | 1035-1036 |
| `DiagonalOutermorphism ⋅ AntiSpinor` (and reverse) | **uses `even`** (bug; correct is `odd`) | 1037-1038 |
| `DiagonalOutermorphism ⋅ Multivector`, `⋅ DiagonalOutermorphism` | elementwise | 1039-1041 |
| `Outermorphism ⋅ Endomorphism{V,<:Chain{V,G}}` / reverse | via `TensorOperator(a[G])` | 1043-1044 |
| `DiagonalOutermorphism ⋅ Endomorphism{…G}` / reverse | via `DiagonalOperator(grade G)` | 1045-1046 |
| `Diag{Chain{V,G}} ⋅ Endomorphism{V,<:Chain{V,G}}` | `TensorOperator(a) ⋅ b` (= D·A, correct) | 1047 |
| `Endomorphism{V,<:Chain{V,G}} ⋅ Diag{Chain{V,G}}` | `TensorOperator(transpose(Chain{V,G}(cols .* d)))` = **(A·D)ᵀ** (bug; correct A·D) | 1048 |
| `Outermorphism ⋅ TensorGraded{V,G}` / reverse | `a[G] ⋅ b` / `a ⋅ b[G]` | 1050-1051 |
| `Outermorphism ⋅ Outermorphism` | `Outermorphism(TensorOperator(a.v[1]⋅b.v[1]))` (compose grade 1, recompute compounds) | 1052 |
| `Outermorphism ⋅ Couple` / `⋅ PseudoCouple` | sum of parts | 1054-1055 |
| `Outermorphism ⋅ Spinor/AntiSpinor/Multivector` @generated | per-grade apply, codomain padding (§4.5) | 1056-1073 |
| `scalarcheck(x)` | `isscalar(x) ? value(scalar(x)) : x` | 1075 |
| `contraction[_metric](x::Endomorphism{V,<:Chain{V,G,<:Chain{V,G,<:TensorGraded{W,L}}}}, y::TensorGraded{W,L}[,g])` @generated | operator with algebra-valued entries: contract every entry with `y`, collapse scalars | 1076-1081 |
| `Endomorphism + DiagonalOperator` (both orders) | via `TensorOperator(diag)` | 1083-1084 |
| `plus/minus/+/-(Outermorphism{V}, Outermorphism{V})` @generated | per-grade op (grade 0 stays implicit 1) | 1085-1089 |
| `plus/minus/+/-(TensorOperator,TensorOperator)`, `(Diag,Diag)` | op on values | 1090-1092 |
| `⟑`/`*` with DiagonalOperator or Outermorphism on either side | `contraction` | 1094-1102 |
| `*`/`⟑`/`contraction`/`/` with TensorOperator | unwrap; `Op op Op` rewraps | 1103-1109 |
| `F * Outermorphism`, `Outermorphism * F`, `Outermorphism / F` (`F ∈ Fields=(Real,Complex)`) | scale every compound block by `a` (not `a^g`) | 1110-1115 |
| `F * TensorOperator/DiagonalOperator`, `…*F`, `…/F` | scale values | 1116-1122 |
| `Projector/Dyadic ± TensorAlgebra` (both orders), `± UniformScaling` | via `Chain(P)` | 1133-1142 |
| `Endomorphism ± UniformScaling` (4 methods) | `TensorOperator(value ± I)` | 1143-1146 |
| `Chain{V,1,<:Chain{V,1}} ± UniformScaling` (6 methods) | add/subtract `λ·e_i` to column i (`UniformScaling{Bool}` uses the basis directly) | 1147-1153 |

### 2.12 Lie brackets

| signature | semantics | line |
|---|---|---|
| `struct LieBracket end`; `const 𝓛 = LieBracket()`, `const Lie = LieBracket()` | singleton | 1547, 1551-1552 |
| `struct LieDerivative{X}; v::X` | wrapped operator | 1548-1550 |
| `show(io,::LieBracket)` | `"LieBracket[...]"` | 1554 |
| `𝓛[X...]` | `bracket(X...)` | 1555 |
| `𝓛(X,Y...)` / `𝓛(X)` | `LieDerivative(bracket(X,Y...))` / `LieDerivative(X)` | 1556-1557 |
| `(X::LieDerivative)(Y...)` / `(X)(Y::LieDerivative)` | `bracket(X.v,Y...)` / `LieDerivative(X.v(Y.v))` | 1558-1559 |
| `LieBracket(X...)` | `bracket(X...)` | 1560 |
| `bracket(X)`, `bracket(X,Y)`, `bracket(X,Y,Z)`, 4-, 5-ary | explicit recursion formulas (§4.12) | 1561-1565 |
| `bracket(X::Vararg{T,N})` @generated | general alternating recursion | 1566-1568 |
| `±`, `*n`, `/n` on LieDerivative | act on `.v` | 1570-1576 |

### 2.13 Metric tensors

| signature | semantics | line |
|---|---|---|
| `antimetrictensor(V,G)`, `antimetrictensor(V,Val(G)=Val(1))` | `compound(metrictensor(V), grade(V)-G)` | 1580-1581 |
| `metrictensor(V::TensorBundle)`, `metrictensor(V::Int)` | `TensorOperator(map(Chain, value(metricdyad(V))))` | 1582-1583 |
| `metricdyad(V::TensorBundle/Int)` | `metricdyad(Submanifold(V))` | 1584-1585 |
| `metricdyad(V)` | conformal (`hasconformal`, ∞ & ∅): columns `(-e₂, -e₁, e₃, …, e_N)`; else `cayley(V,1,(x,y)->value(contraction(x,y)))` (Gram matrix `g_ij = e_i⋅e_j`) | 1586-1593 |
| `applyf(f,mat)` | `f.(value(value(mat)))` | 1595 |
| `metricextensor(V)` | `Outermorphism(metrictensor(V))` | 1597 |
| `metriceven, metricodd` | `= metricextensor` | 1598 |
| `struct MetricTensor{n,ℙ,g,Vars,Diff,Name} <: TensorBundle` | singleton type; `g` = 1-based index into global `metrictensor_cache` | 1603-1605 |
| ctors `MetricTensor{N,M,S,F,D}()`, `{N,M,S}()`, `{N,M}(b::Values{N,<:Tuple/Values/Chain/AbstractVector})`, `{N,M}(b::Vector)`, `(b::Tuple)`, `(b::Values{N})`, `(b::Values{N,<:Real})→DiagonalForm`, `(b::AbstractVector{<:Real})→DiagonalForm`, `(b::AbstractVector)`, `(b::AbstractMatrix)` (columns), `(b::Chain-of-Chains)`, `(b::Chain)→DiagonalForm`, `(b::TensorOperator)`, `(b...)` | registry-backed construction | 1607-1623 |
| `Manifold(::Type{<:MetricTensor})` | instance | 1625 |
| `construct_cache(:MetricTensor)` | DirectSum algebra-cache codegen for the new bundle type | 1627 |
| `metrictensor(b::Submanifold{V})` | basis blade → `metrictensor(V)`; subspace → restricted Gram matrix `TensorOperator(map(b, b(value(metrictensor(V)))))` | 1628 |
| `metrictensor(V,G)` | `compound(metrictensor(V),G)` | 1629 |
| `metrictensor(V::MetricTensor{N,M,S})` | `TensorOperator(Chain{Submanifold(V)}(isdual(V) ? SUB(out) : out))`, `out = Chain{Submanifold(V)}.(metrictensor_cache[S])` | 1630-1633 |
| `const metrictensor_cache = Values[]`; `metricsig(M,b)` | intern `b` (or `SUB(b)` when `dyadmode(M)>0`), return 1-based index | 1634-1643 |
| `getalgebra(V::MetricTensor)` | via `Submanifold(V)` | 1645 |
| `s::MetricTensor[i]` (Any/Integer), `[i::Vector]`, `[i::UnitRange]`, `[:]` | i-th Gram column `Values`; list; `[:]` broken (`Vector(::Chain)` MethodError) | 1647-1652 |
| `Signature(V::MetricTensor{N,M,S,F,D})` | `Signature{N,M,0,F,D}()` (all `+`) | 1654 |
| `summary`, `show` (2-arg `show(Submanifold(M))`), `show(::MIME"text/plain")` | §5 | 1657-1666 |
| `isdiag(::MetricTensor)` | `false` | 1672 |
| `DirectSum.TensorBundle(b::Submanifold{V})` | subspace → bundle: basis→`TensorBundle(V)`; Int→`Signature(mdims(b))`; Signature→`Signature(b)`; DiagonalForm→restricted diagonal; MetricTensor→restricted Gram matrix (new cache entry) | 1674-1688 |
| `struct InducedMetric end`; `isinduced(x)` (8 methods) | marker; `true` for `InducedMetric`, non-basis `Submanifold`, `TensorBundle` (value and type) | 1692-1704 |
| `log(t::Real/Complex, g::InducedMetric)` | `log(t)` | 1706-1707 |

### 2.14 Misc / TeX

| signature | semantics | line |
|---|---|---|
| `affineframe(x::TensorOperator, y=x[1])` | `affineframe(value(value(x)), y)` (§A) | 1711 |
| `mean(m::TensorOperator)`, `barycenter(m)`, `curl(m)` | delegate to column Values / nested chain | 1712-1714 |
| `findall(P, t::AbstractVector{<:TensorOperator})` | `findall(P .∈ t)` | 1715 |
| `findfirst(P, t)`, `findlast(P, t)` | first/last simplex index containing point `P` (via `∈`), `0` if none | 1716-1727 |
| `const subscrepl` | char → TeX map (`'∞'→"_{\\infty}"`, `'∅'→"_{\\emptyset}"`, `'𝟎'→"0"`, `'₀'…'₉'→"_{0}"…"_{9}"`) | 1731-1744 |
| `printtex(io,data)`, `printtex(data)`, `printtex(data::Endomorphism)` | TeX array body (§5.6) | 1745-1760 |
| `alltex(V, ops=[∧,∨,<,>,<<,>>])` | `printtex.(cayley.(Ref(V),ops))` | 1762-1764 |

---

## 3. Data representations

### 3.1 Blade ordering (inherited; restated because every operator layout depends on it)

* Basis blades of `V` (dim N) are bitmasks `B ∈ [0,2^N)`, bit `k-1` ↔ generator `v_k`.
* Grade-G blades are ordered **lexicographically by index tuple** (`indexbasis(N,G)`): N=3 G=2 → `v₁₂, v₁₃, v₂₃`;
  N=4 G=2 → `v₁₂, v₁₃, v₁₄, v₂₃, v₂₄, v₃₄` (verified: `ℝ^4(B)` printed `1v₁₂ + 2v₁₃ + 0v₁₄ + 3v₂₃ + 0v₂₄ + 0v₃₄`).
  This is NOT numeric bitmask order (which would give 12,13,23,14,…).
* `bladeindex(N,B)` = 1-based position of `B` within its grade; `basisindex(N,B)` = 1-based position in the full
  `Multivector` layout = `binomsum(N,grade)+bladeindex`, where `binomsum(N,g) = Σ_{k<g} C(N,k)`.
* Full basis order (`Λ(V).b`, `fullbasis`): grade 0, then grade 1 blades, grade 2, …: N=3 →
  `v, v₁, v₂, v₃, v₁₂, v₁₃, v₂₃, v₁₂₃`.
* Even basis (`evenbasis`, Spinor layout, length `2^(N-1)`): grades 0,2,4,… concatenated in that order
  (N=3: `v, v₁₂, v₁₃, v₂₃`). Odd basis (CoSpinor): grades 1,3,… (N=3: `v₁, v₂, v₃, v₁₂₃`) (`forms.jl:1209-1213`).
* `lowerbits(N,S,B)` = parallel bit extract (`pext(B,S)`): compress the bits of `B` that lie in subspace mask `S`
  to the low bits. `expandbits(N,S,B)` = parallel bit deposit (`pdep(B,S)`). (`Leibniz.jl/src/utilities.jl:254-289`.)
  **The Julia `lowerbits` is buggy** (`lowerbits_calc` returns positions within `B` instead of within `S`, and the
  cache is filled with the wrong `k` for `s<S`): `lowerbits(3,0b011,0b010)=1` (should be 2),
  `lowerbits(3,0b110,0b100)=1` (should be 2). Port the mathematical definition (pext); `expandbits` is correct.
* `mixed(V,B)` (`Leibniz.jl/src/generic.jl:109-117`): embed a vector-space mask into a dyadic (V⊕V′) space: without
  diff vars, `isdual(V) ? B<<N : B`.

### 3.2 Nested chain = matrix (column-major)

`Chain{V,G,Chain{W,L,T,M},N}` with `N = C(mdims(V),G)`, `M = C(mdims(W),L)`:

* storage: `Values{N, Chain{W,L,T,M}}` — N columns, each an `M`-vector. In Julia it is an isbits flat tuple-of-tuples
  (stack allocated, zero indirection).
* `A[i,j] = A.v[j].v[i]`: **outer index = column = domain basis blade j (in V, grade G); inner index = row =
  codomain component i (in W, grade L)** (`multivectors.jl:99`, `forms.jl:588`).
* `A ⋅ x` for `x::Chain{V,G}`: `Σ_j x_j · col_j` (`matmul`, `forms.jl:957-959`).
* Julia `Matrix(A)` = `hcat(columns...)` → rows are codomain components; `Endomorphism([1 2;3 4])` keeps the Julia
  matrix layout (`TensorOperator{V,W}(m)` takes columns `m[:,j]`).
* `TensorOperator{V,W,T}`: `V` = outer = domain manifold, `W` = inner = codomain manifold. `_axes` =
  `(1:rows, 1:cols) = (1:gdims(inner), 1:gdims(outer))` (`forms.jl:661`). Example: 2 columns in ℝ³ →
  `TensorOperator{⟨11⟩, ⟨111⟩, …}` printed as `3×2`.
* Same scheme for `Spinor{V,<:Spinor{W}}` (length `2^(N-1)` both ways), `AntiSpinor`, `Multivector{V,<:Multivector{W}}`
  (`2^M × 2^N`), and mixed nestings (`Chain{V,G,<:Multivector{W}}`, `Multivector{V,<:Chain{W,G}}`).
* Entries may themselves be algebra elements (not scalars): `cayley` tables store `Single`/`Submanifold`/`Zero`
  entries; `operator(fun,V)` may produce `Single` entries (`Simplex{⟨+++⟩, Single{⟨+++⟩,1,B,Int64} where B, 3}`).
  Contraction rules at `forms.jl:1076-1081` handle such algebra-valued operators.
* `Simplex{V,T<:GradedVector,N} = Chain{V,1,T,N}` (`multivectors.jl:94`) — any Chain of vectors: used both for
  grade-1 endomorphisms and simplices (list of N points in homogeneous coordinates).

### 3.3 Per-type fields and invariants

| type | type params (compile time) | runtime fields | invariants |
|---|---|---|---|
| `TensorOperator{V,W,T}` | V domain, W codomain, T nested storage type | `v::T` | `T <: TensorAlgebra{V,<:TensorAlgebra{W}}` |
| `Endomorphism{V,T}` | V=W | same | square |
| `DiagonalOperator{V,T}` | V, T (Chain{V,G} / Spinor / AntiSpinor / Multivector) | `v::T` diagonal | implicitly square on that grading |
| `Outermorphism{V,T<:Tuple}` | V domain; codomain W recovered from `T.parameters[1]` | `v::Tuple` of `min(N,M)` compounds; compound g is `Chain{V,g,Chain{W,g}}` | `v[g] == compound(v[1], g)` for *constructed* values (not re-checked; `+`, scalar `*` break it) |
| `Projector{V,T,Λ}` | V normalized by `DirectSum.submanifold`, T, Λ | `v::T`, `λ::Λ` (default Int 1) | `v` unit (constructor `Proj(...)` normalizes; inner ctor `Projector{V}(v,λ)` does not) |
| `SpectralOperator{V,T<:Simplex{V},Λ}` | alias | `v` = Chain of eigenvectors, `λ` = Chain of eigenvalues or scalar | columns unit |
| `Dyadic{V,X,Y}` | V from `y` | `x::X`, `y::Y` | x,y TensorGraded; when x/y are Chains-of-vectors, represents Σ of dyads |
| `MetricTensor{n,ℙ,g,Vars,Diff,Name}` | all compile time; `g` = registry index (1-based, into a *global mutable* cache) | none (singleton) | registry entry is a `Values` of N `Values{N}` Gram columns |
| `LieDerivative{X}` | X | `v::X` | — |
| `InducedMetric`, `LieBracket` | — | — | singleton markers |

### 3.4 Result-type conventions (observed)

* `det(T)` → `Chain{V,0}` (prints `-3v`), not a raw number; `∧(T)` → `Chain{V,N}` pseudoscalar (`-3v₁₂₃`);
  `tr(T)` → raw scalar; `scalar(T)` → Float (`tr/N`).
* `det/∧/compound/adjugate/cofactor/characteristic_exact` on Int input stay Int (exact, wedge-based).
  `inv`, `invdet`'s inverse, `characteristic` for N=3,4 (contains `/2`, `/-6`) → Float.
  `characteristic` N=2 and N≥5 → Int for Int input.
* `eigvals` element type depends on runtime values (Float for real roots, ComplexF64 otherwise) — Julia type
  instability. `eigvalsreal` throws `DomainError` for complex roots; `eigvalscomplex` always Complex.
* `gerschgorin(::Endomorphism)` → `Values` (not Chain); `gerschgorin(::DiagonalOperator)` → `Chain{V,1,Int}` zero.
* N=1: `eigvals(X) = X[1]`, `characteristic(X) = -X[1]`, both are the *column Chain* (e.g. `3v₁`, `-3v₁`).

### 3.5 Compile-time vs runtime in Julia

All manifolds (`V`, `W`), grades, dimensions, blade index tables, compound index sets, generated unrolled
loops (`matmul`, `compound`, `outermorphism`, `sylvester`, `bivector`, `diag`, Outermorphism application padding)
are compile-time. Runtime: coefficients, `λ`, eigen-decomposition values, the `MetricTensor` registry contents
(global cache populated at type-construction time, **order dependent**).

---

## 4. Algorithms

### 4.1 `(w::Submanifold{Q,M})(b::Chain{V,G,T})` — `forms.jl:23-90`

Let `W = Manifold(w)`; `isbasis(w)` is true when `w` is a basis blade of some algebra (its param is a Manifold),
false when it denotes a (sub)space.

```
if isbasis(w):
    if Q == V:                                 # same parent algebra
        if isdyadic(V):                         # mixed V⊕V' space — BROKEN in Julia (undefined Y, N)
            G==M==1: x=UInt(w); X = x >> (mdims(V)/2); Y = X≠0 ? X : x
                     return Single{V}( (V[intlog(Y)+1] ? -1 : 1) * b.v[bladeindex(mdims(V),Y)], One)
            G==1,M==2: (m1,m2) = eval_shift(w); return ±b.v[m2] * getbasis(V, indexbasis(N,1)[m1])
            else error("not yet possible")
        else return contraction(w, b)            # basis blade acts by contraction
    else return interform(w, b)                   # promote both to V∪W then call
elif V == W:  return V===W ? b : Chain{w,G,T}(value(b))       # relabel
elif W ⊆ V:                                        # projection onto subspace
    G == 1: ind = indices(UInt(W), mdims(V)); return Chain{w,1,T}(b.v[ind])
    else:   out = zeros(C(M,G)); S = UInt(w)
            for k, B in enumerate(indexbasis(N,G)):
                if b[k]≠0 and popcount(B & S) == G:     # blade fully inside the subspace
                    out[bladeindex(M, pext(B,S))] = b[k]
            # Julia calls lowerbits(M,S,B) here (M instead of N) → BoundsError; also lowerbits itself is buggy
            return Chain{w,G}(out)
elif V ⊆ W:                                        # embedding into superspace
    for k, B in enumerate(indexbasis(N,G)) with b[k]≠0:
        B' = (V is a Submanifold) ? pdep(B, UInt(V)) : B
        if isdyadic(W) && !isdyadic(V): B' = mixed(V,B')
        elif !isdyadic(W) && !isdyadic(V): (keep)
        else error("arbitrary Manifold intersection not yet implemented.")
        out[bladeindex(M, B')] = b[k]
    return Chain{w,G}(out)
elif V == V'': return w(Chain{V'',G}(value(b)))
else error("cannot convert from $V to $w")
```
Multivector version (`forms.jl:93-142`) is identical per grade using `setmulti!`/`basisindex`, uses the correct
`lowerbits(N,S,B)` but inherits the Leibniz `lowerbits` bug; dyadic basis blades error. Verified outputs:
`V(1,2)(x) = 1v₁ + 2v₂`, `V(2,3)(x) = 2v₂ + 3v₃`, `ℝ^4(x) = 1v₁ + 2v₂ + 3v₃ + 0v₄`,
`ℝ^4(B) = 1v₁₂ + 2v₁₃ + 0v₁₄ + 3v₂₃ + 0v₂₄ + 0v₃₄`, `(V⊕V')(x) = 1v₁ + 2v₂ + 3v₃ + 0w¹ + 0w² + 0w³`,
`V(Multivector{V(1,3)}(1,2,3,4)) = 1 + 2v₁ + 3v₃ + 4v₁₃`. Julia outputs for multivector/higher-grade projection are
wrong/nondeterministic (`V(1,2)(M) = 1 + 3v₁ + 5v₁₂`; `V(1,3)(M)` gave `1 + 4v₁ + 6v₁₃` in one session and
`2 + 4v₁ + 6v₃` in another) — do **not** use as goldens; correct result for `M = 1+2v₁+3v₂+4v₃+5v₁₂+6v₁₃+7v₂₃+8v₁₂₃`:
`V(1,2)(M) = 1 + 2v₁ + 3v₂ + 5v₁₂`, `V(1,3)(M) = 1 + 2v₁ + 4v₃ + 6v₁₃`, `V(2,3)(M) = 1 + 3v₂ + 4v₃ + 7v₂₃`.
Also `ℝ4(x)` where `x` lives in `S"+++"` (a `Signature` vs `Submanifold(4)`) recurses forever (`V == V''` branch) —
port must return an error instead.

### 4.2 Multilinear-form evaluation — `forms.jl:293-294`

`t(y₁,…,y_k) = t ⋅ (y₁ ∧ … ∧ y_k)`. With one argument it is just `t ⋅ y`. Grassmann's `⋅` (right contraction,
`products.jl`) uses reversion so that `v₁₂ ⋅ v₁₂ = +1` (`Λ(G).v12⋅Λ(G).v12 = 1v`). Goldens (basis `S"+++"`,
`x=1v₁+2v₂+3v₃`, `y=4v₁+5v₂+6v₃`, `B=1v₁₂+2v₁₃+3v₂₃`):
`x(y) = 32v` (Chain{V,0}), `B(x) = -8v₁ - 8v₂ + 8v₃`, `x(B) = 𝟎`, `B(x,y) = -24v`, `B(v1,v2) = 1v`,
`v12(v1,v2) = v`, `v123(v1,v2,v3) = v`, `v12(x) = -2v₁ + 1v₂ + 0v₃`, `x(v1) = 1v`, `v1(x) = 1v`,
`M(x) = 20 - 28v₁ - 16v₂ + 20v₃ + 24v₁₂ - 16v₁₃ + 8v₂₃` (`M = Multivector{V}(1..8)`),
`M(Chain{V,1}(1,0,0), Chain{V,1}(0,1,0)) = 5 + 8v₃` (= `M ⋅ v₁₂`).

### 4.3 Transpose — `forms.jl:302-308`

`transpose(A::Chain{V,1,<:Chain{W,1}})` → `Chain{W,1}(row_i)` where `row_i = Chain{V,1}(A[1][i],…,A[n][i])`, i.e.
new outer manifold = old inner (W), new inner = old outer (V). Other nestings fall through to
`Base.transpose(::Number) = identity` — **Julia returns the operator unchanged** for `compound(T,2)`, Spinor or
Multivector operators. Port: implement true transpose for all nestings; flag divergence in tests.

### 4.4 Compound matrices, determinant, outermorphism

* `compound(x::Chain{V,1,<:Chain{W,1}}, Val(G))` (`composite.jl:715-720`): error if `G > N`; else
  `Chain{V,G}( ∧(x[i] for i ∈ I) for I in indexbasis(N,G) )` — column I of `Λ^G A` is the wedge of the columns
  indexed by I; its entry at codomain blade J is the minor `det A[J,I]`. `G=0` → `Chain{V,0}(Values(Chain{V,0}(1)))`.
  Exact (only ± and *), metric-free (wedge is metric independent; verified identical on `S"+++"`, `S"-++"`,
  `S"---"`, `D"2,3,5"`).
* `∧(t::Chain{V,1,<:Chain{W}})` (`algebra.jl:115`) = `t[1]∧…∧t[n]`; `det(t) = !∧(t)` (`composite.jl:952`), where
  `!` = `complementright` maps the pseudoscalar `d·I` to scalar `d` (metric-independent).
* `outermorphism(t)` (`forms.jl:719-721`) = tuple `(compound(t,1),…,compound(t,min(N,M)))`.
* `TensorOperator(O::Outermorphism{V})` (`forms.jl:766-774`):
  ```
  out = concat over g of [Multivector{W}(col) for col in O.v[g]]   # each column embedded in the full algebra
  val = [Multivector 1] ++ out ++ zeros(Multivector) padded to total length 2^N
  return TensorOperator(Multivector{V}(val))                          # 2^M × 2^N block-diagonal
  ```
  Grade-0 block is always the scalar 1 (even after `2O`, `O+O`: those only scale/add the stored compounds).
* `∧(O)` (`forms.jl:746-753`) = the single column of the top compound (a pseudoscalar chain) when square.
* DiagonalOperator versions (`forms.jl:515-523`): products of diagonal entries over each blade's index set.
* `tr(O) = 1 + Σ_g tr(Λ^g F)`; for an N×N F this equals `det(I+F)` = Σ_k e_k(λ).

### 4.5 Outermorphism application (`forms.jl:1050-1073`)

Let `N = dim V` (domain), `M = dim W` (codomain), `K = min(N,M)`.
* `O ⋅ x` for `x::TensorGraded{V,G}`: `O.v[G] ⋅ x` (for G=0 `O[0]` is the 1×1 identity).
* Multivector `m`: `Multivector{W}(m[0], (O.v[g] ⋅ m(g)).values for g=1..K, zeros(C(M,g)) for g=K+1..M)`.
* Spinor (even): `Spinor{W}(m[0], (O.v[g]⋅m(g)) for even g in 2..K, zeros for g = K+2, K+4, …)` — Julia pads with
  `binomial(M, g+K)` for `g ∈ 2:2:M-N`, which is wrong when `K` is odd (padding grades become odd). Correct rule:
  for each even grade k≤M of W: k≤K → apply, else zeros(C(M,k)).
* AntiSpinor (odd): analogous with odd grades; Julia pads `g ∈ 1:2:M-N` → grade `g+K` (wrong parity when K odd).
* Couple = scalar + imaginary blade: `O⋅scalar + O⋅imag`; PseudoCouple: `O⋅imag + O⋅volume`.
* Verified (`T` = [1 4 7;2 5 8;3 6 10] as columns (1,2,3),(4,5,6),(7,8,10)):
  `O(1v₁+1v₂+1v₃) = 12v₁ + 15v₂ + 19v₃`, `O(Chain{V,2}(1,1,1)) = -12v₁₂ - 19v₁₃ - 5v₂₃`,
  `O(Chain{V,3}(1)) = -3v₁₂₃`, `O(Multivector ones) = 1 + 12v₁ + 15v₂ + 19v₃ - 12v₁₂ - 19v₁₃ - 5v₂₃ - 3v₁₂₃`,
  `O(Spinor ones) = 1 - 12v₁₂ - 19v₁₃ - 5v₂₃`, `O(CoSpinor ones) = 12v₁ + 15v₂ + 19v₃ - 3v₁₂₃`.
  Non-square (2 columns in ℝ³, A=[1 4;2 5;3 6]): `O(Multivector{⟨11⟩}(1,1,1,1)) = 1 + 5v₁ + 7v₂ + 9v₃ - 3v₁₂ - 6v₁₃ - 3v₂₃`,
  `O(Spinor{⟨11⟩}(1,1)) = 1 - 3v₁₂ - 6v₁₃ - 3v₂₃`, `O(CoSpinor{⟨11⟩}(1,1)) = 5v₁ + 7v₂ + 9v₃ + 0v₁₂₃`.

### 4.6 Projector / Dyadic / SpectralOperator

```
Proj(v, λ=1)                 = Projector(v/|v|, λ)            # |v| = abs(v) = sqrt(~v*v) (metric!)
Proj(chain of vectors vs, λ) = Projector(Chain(v_k/|v_k|), λ)  # λ scalar or Chain
P ⋅ x   = v ⊗ (λ (v⋅x))            # rank one; ⊗ with a scalar is multiplication, else a Dyadic
x ⋅ P   = ((x⋅v) λ) ⊗ v
D ⋅ x   = D.x ⊗ (D.y ⋅ x);   x ⋅ D = (x ⋅ D.x) ⊗ D.y
Spectral ⋅ x = Σ_k v_k ⊗ (λ_k (v_k⋅x))      # λ broadcast if scalar
Chain(P) = outer(λ v, v)  (M[i,j] = λ v_i conj(v_j));   Chain(Spectral) = Σ_k outer(λ_k v_k, v_k)
tr(P) = Σ value(λ);  det(P) = N==1 ? λ : 0 (as Chain{V,0});  tr(D) = x·y (coefficient dot)
exp/log/inv(Spectral) = same v, f(λ)  (functional calculus)
exp(P::Proj) (rank one): out = first column of exp(matrix(P)); Proj(out/sqrt(out[1]))   # heuristic, not a projector identity
log(P::Proj): out = first column of log(Endomorphism(P)); Proj(out/sqrt(out[1]))       # complex for singular P
```
Goldens (`x=1v₁+2v₂+3v₃`, `y=4v₁+5v₂+6v₃`, `P=Proj(x)`, `D=Dyadic(x,y)`): `P(y) = 2.28571v₁ + 4.57143v₂ + 6.85714v₃`
(= `x·32/14`), `P(y,y) = 73.14285714285715`, `P⋅P` = `Dyadic(v̂,v̂)`, `D(x) = 32v₁ + 64v₂ + 96v₃`,
`x⋅D = 56v₁ + 70v₂ + 84v₃`, `D⋅D = (32v₁ + 64v₂ + 96v₃)⊗(4v₁ + 5v₂ + 6v₃)`, `D(x,y) = 1024`, `tr(D) = 32`,
`D[1,2] = 5`, `P[1,2] = 0.14285714285714288`, `P⋅D = (1.0v₁ + 2.0v₂ + 3.0v₃)⊗(4v₁ + 5v₂ + 6v₃)`.
2D (`x=(1,2)`, `y=(3,4)` Float): `Dyadic(Chain(x,y),Chain(y,x))⋅x = 26.0v₁ + 42.0v₂`,
`Dyadic(Chain(x,y),y)⋅x = 44.0v₁ + 66.0v₂`, `Proj(Chain(x,y))⋅x = 2.32v₁ + 3.76v₂`,
`Proj(Chain(x,y),Chain(2.0,3.0))⋅x = 5.96v₁ + 9.28v₂`, `Chain(Proj(Chain(x,y),Chain(2.0,3.0))) = (1.48v₁+2.24v₂)v₁ + (2.24v₁+3.52v₂)v₂`.
`S = eigen(Endomorphism([2.0 1.0;1.0 2.0]))`: `S.λ = 1.0v₁ + 3.0v₂`, `S[2] = 3.0Proj(0.707107v₁ + 0.707107v₂)`,
`Chain(S) = (2.0v₁+1.0v₂)v₁ + (1.0v₁+2.0v₂)v₂`, `tr(S) = 4.0`, `S(1v₁) = 2.0v₁ + 1.0v₂`,
`inv(S) = (1.0v₁ + 0.333333v₂)Proj(…)`, `exp(S) = (2.71828v₁ + 20.0855v₂)Proj(…)`, `log(S) = (0.0v₁ + 1.09861v₂)Proj(…)`.

### 4.7 Operator products (metric-free kernels)

```
apply(A: cod×dom, x: dom)  : out[i] = Σ_j A[i,j] x[j]              (matmul, forms.jl:957-959)
rowapply(x: cod, A)        : out[j] = Σ_i x[i] A[i,j] = x·col_j     (forms.jl:940)
compose(A: c×m, B: m×d)    : col_j(A∘B) = apply(A, col_j(B))       (forms.jl:941, 948-950)
matwedge/matvee            : out[j] = Σ_i x[i][j] ∧ y[i]            (entries combined by ∧/∨)
```
* For scalar entries `∧` is multiplication, so `T∧U == T*U` numerically; `∨` of two scalars is 0 (verified:
  `T∨U` = zero matrix, `d∨x` = `0v₁ + 0v₂ + 0v₃`).
* Quirk: the square path (`forms.jl:950`) requires `y` to be typed over the *codomain* manifold with length =
  #columns; non-square `A⋅x` instead dispatches to generic `contraction(::TensorGraded{V,L}, ::Chain{V,G})`
  (`products.jl:1165`) which contracts using the *domain metric*. Identical for Euclidean domains. Port: always use
  metric-free `apply`; note divergence only for non-Euclidean non-square cases.
* `A/B = A * inv(B)` (verified `T/U`).
* `A:B` (`forms.jl:936`) = `Σ_k A_k ⋅ B_k` (column-wise inner products summed; with Grassmann's `⋅` on grade-1
  columns this is `Σ_{ij} A_ij B_ij` → `Chain{V,0}`; `T:T = 5v` for T = columns (1,0,0),(1,1,0),(1,0,1)).
* `T + I` / `I - T` etc. only for grade-1 endomorphisms (`forms.jl:1143-1153`): column i gets `± λ e_i`.
* `A ⊘ b` (`forms.jl:1157-1162`) sandwiches each column; `operator(t)` builds `[e_j ⊘ t]_j` (`forms.jl:1186-1188`).
  Goldens: `operator(v12)` = diag(-1,-1,1) (DiagonalMorphism), `operator(v12,2)` = diag(1,-1,-1) on (v₁₂,v₁₃,v₂₃),
  `operator(v1+v2)` = `[0 -2 0;-2 0 0;0 0 2]`, `operator(1+v12)` = `[0 -2 0;2 0 0;0 0 2]`, `operator(2v1)` = diag(-4,4,4),
  `operator(v12+2v13-3v23)` = `[4 12 -6;12 -6 -4;-6 -4 -12]`, `inv` of that =
  `[0.0204082 0.0612245 -0.0306122; 0.0612245 -0.0306122 -0.0204082; -0.0306122 -0.0204082 -0.0612245]`
  (= `operator(inv(B))`). Metric dependence: `operator(Λ(S"-++").v1)` = diag(1,-1,-1), `operator(Λ(D"2,3,5").v1)`
  = diag(-2,2,2).

### 4.8 Inverse, adjugate, cofactor (composite.jl, used by forms)

`inv/adjugate/cofactor/invdet` of `Values{M,<:Chain{V,1}}` via exterior-product Cramer symbols
(`composite.jl:707-812`): prefix wedges `x_k = t₁∧…∧t_k`, suffix wedges `y_k = t_{n-k+1}∧…∧t_n`; row i of the
adjugate is `⋆(x_{i-1} ∧ y_{n-i})` with sign pattern; `inv = adjugateᵀ / det`. Exact integer adjugate/cofactor;
`adjugate(T)` is the classical adjugate as an operator (`adjugate(T)·T = det·I`); `cofactor(T) = adjugate(T)ᵀ`.
Goldens: `adjugate(T)` = `[2 2 -3; 4 -11 6; -3 6 -3]`, `cofactor(T)` = `[2 4 -3; 2 -11 6; -3 6 -3]`,
`inv(T)` = `[-0.6666666666666666 -0.6666666666666666 1.0; -1.3333333333333333 3.6666666666666665 -2.0; 1.0 -2.0 1.0]`
(first 3×3 block of `inv(O)` matrix), `invdet(T) = (inv(T), -3v)`.
Non-square (`M > N` columns in fewer dims, or `M < N`): pseudo-inverse `tt ⋅ inv(t ⋅ tt)` (`composite.jl:764`);
golden: `inv(A)` for A=[1 4;2 5;3 6] = `(-0.944444v₁+0.444444v₂)v₁ + (-0.111111v₁+0.111111v₂)v₂ + (0.722222v₁-0.222222v₂)v₃`.

### 4.9 Characteristic polynomial (`forms.jl:1441-1517`)

Returns `c = (c₀,…,c_{N-1})` as `Chain{V,1}` such that `χ(z) = z^N + c_{N-1} z^{N-1} + … + c₀ = det(zI − X)`.
General identity used: `c_{k-1} = (-1)^{N-k+1} e_{N-k+1}` where `e_j = tr(Λ^j X)` (sum of principal j-minors).
```
characteristic(X) N=1: -X[1]                       # column chain, not scalar
                  N=2: (Real(det X), -tr X)
                  N=3: a0=-Real(det X); a2=tr X; (a0, (a2^2 - tr(X⋅X))/2, -a2)
                  N=4: a3=tr X; a0=Real(det X); X2=X⋅X; a32=a3^2; t2=tr X2
                       a2=(a32-t2)/2; a1=(a3*(a32-3*t2) + 2*tr(X2⋅X))/-6
                       (a0, a1, a2, -a3)
                  N≥5: characteristic_exact(X)
characteristic_exact(X::Endomorphism) = characteristic_exact(outermorphism(X))
characteristic_exact(O::Outermorphism{V}): out = (tr Λ¹,…,tr Λ^N)
      c_k (k=1..N, 1-based) = isodd(N-k) ? out[N-k+1] : -out[N-k+1]
characteristic_exact(D::DiagonalOutermorphism): out_g = Σ(grade-g diagonal) = e_g ; same sign rule
characteristic(X, Val(m)) = the m-th coefficient (1-based); characteristic_exact(X,Val(m)) = ±tr(compound(X,N-m+1))
```
Goldens: `T` (N=3) → `3.0v₁ - 12.0v₂ - 16.0v₃`, exact → `3v₁ - 12v₂ - 16v₃`; diag(1,2,3) → `-6v₁ + 11v₂ - 6v₃`;
rotation `[0 -1;1 0]` → `1v₁ + 0v₂`; `A4=[4 1 0 0;1 3 1 0;0 1 2 1;0 0 1 1]` → `7.0v₁ - 35.0v₂ + 32.0v₃ - 10.0v₄`
(exact `7v₁ - 35v₂ + 32v₃ - 10v₄`), `characteristic(A4,2) = -35.0`;
`A5` = tridiag(1,2,1) 5×5 → `-6v₁ + 35v₂ - 56v₃ + 36v₄ - 10v₅`; 1×1 [3] → `-3v₁`.

### 4.10 Eigen-related

```
eigpolys(X) (N≠2) = Chain( (-1)^k * c_{N-k} / C(N,k) for k=1..N )   = normalized elementary symmetric E_k = e_k/C(N,k)
eigpolys(X,Val(G)) = G==N ? det : (-1)^G * characteristic(X,Val(N-G+1)) / C(N,G)
eigpolys(x::Chain eigenvalues, Val(G)) = G==N ? Π x : mean over G-subsets of products
sylvester(x)_i  = Π_{j≠i} nozero(x_j - x_i)          (j ascending; zero differences replaced by 1)
eigmults(x)_i   = 1 + #{ j≠i : x_j == x_i }            (exact equality)
eigvals(X) : N==1 → X[1]; N<5 → monicroots(characteristic X) (composite.jl:1112-1190 closed forms
             quadratic/cubic/quartic); N≥5 → LAPACK eigvals of Matrix(X) (Julia sorts by (real, imag))
eigen(X)   : LAPACK eigen(Matrix(X)) → SpectralOperator(columns = eigvecs (unit 2-norm), λ = eigvals)
gerschgorin(X)_i = Σ_{j≠i} |X[i,j]|   (row radii, returned as Values)
vandermonde(x)[i,j] = x_i^(j-1);  discriminant(x) = det(vandermonde x)^2 = Π_{i<j}(x_j-x_i)^2
discriminant(X::Endomorphism) = N==2 ? tr^2 - 4 det : Re?( det(vandermonde(eigvals X))^2 )
```
Special multivector eigvals (`forms.jl:1352-1373`): for even elements in 2D/3D Euclidean,
`X² = re + imag`, eigenvalues `re ∓ i·|imag|` (+ `|X|²` in 3D) — these are eigenvalues of the sandwich operator
`x ↦ x⊘X`. Goldens: `eigvals(2+3w12)` (2D) = `(-5.0-12.0im)v₁ + (-5.0+12.0im)v₂`; `eigvals(2+3v12)` (3D) =
`(-5.0-12.0im)v₁ + (-5.0+12.0im)v₂ + (13.0+0.0im)v₃`; `eigvals(Spinor{V}(1,2,3,4))` =
`(-28.0-10.7703im)v₁ + (-28.0+10.7703im)v₂ + (30.0+0.0im)v₃`; `eigvals(Chain{V,2}(1,2,3))` =
`(-14.0-0.0im)v₁ + (-14.0+0.0im)v₂ + (14.0+0.0im)v₃`; `eigvals(Chain{V,0}(2)) = 4.0v₁ + 4.0v₂ + 4.0v₃`;
`eigvals(Chain{V,1}(1,2,3)) = -14.0v₁ + 14.0v₂ + 14.0v₃`; `eigvals(v12)` = `(-1.0-0.0im)v₁ + (-1.0+0.0im)v₂ + (1.0+0.0im)v₃`.

### 4.11 Metric tensor

* `metricdyad(V)` for non-conformal = Gram matrix `g_ij = value(e_i ⋅ e_j)` (via `cayley(V,1,…)`); conformal
  `S"∞∅++"`: `[0 -1 0 0;-1 0 0 0;0 0 1 0;0 0 0 1]`. `S"∅++"` (origin only, not conformal) → diag(-1,1,1).
* `MetricTensor([1 2 0;2 5 0;0 0 1])`: registry interning; `Λ(G).v1⋅Λ(G).v2 = 2v`, `Λ(G).v1*Λ(G).v2 = 2 + 1v₁₂`,
  `G(1,3)` restricted → `MetricTensor{2,0,3,0,0,1}` with Gram `[1 0;0 1]`.
* Port: the registry index in the *type* is Julia's workaround for non-isbits type params. In Lean make the Gram
  matrix an ordinary value (`Matrix n n α`) stored in the algebra/space structure; equality of spaces becomes a
  decidable/propositional check where needed.

### 4.12 Lie bracket (`forms.jl:1561-1568`)

```
bracket(X) = X
bracket(X,Y) = X(Y) - Y(X)
bracket(X,Y,Z) = X([Y,Z]) + Y([Z,X]) + Z([X,Y])
bracket(W,X,Y,Z) = W([X,Y,Z]) + X([W,Z,Y]) + Y([W,X,Z]) + Z([W,Y,X])
bracket(V,W,X,Y,Z) = V([W,X,Y,Z]) + W([V,X,Z,Y]) + X([V,W,Y,Z]) + Y([V,W,Z,X]) + Z([V,W,X,Y])
bracket(X₁..X_N) (generic @generated, N>5) = Σ_i (-1)^{i+1} X_i( bracket(X₁..X̂_i..X_N) )
```
`X(Y)` is function application; for operators it is composition (`T(U) = T⋅U`), so
`𝓛[T,U] = T⋅U − U⋅T` (golden `[4 -10 -2; 10 0 18; 6 -16 -4]`) and `𝓛[T,U,T] = 0`. The explicit 3–5-ary formulas
use specific argument orders (reference: Reed, "Multilinear Lie bracket recursion formula", viXra 2412.0034);
port them verbatim — the generic formula differs in argument order from the 4/5-ary special cases.

### 4.13 Gershgorin, diag, bivector, pfaffian

* `bivector(A)` coefficient of `e_i∧e_j` (i<j) = `A[j,i]` (lower triangle). `T` → `2v₁₂ + 3v₁₃ + 6v₂₃`.
* `pfaffian(ω)` (`composite.jl:888-895`) = `!(ω∧…∧ω)` (n=⌊N/2⌋ factors) / n! (no division when n=1): in odd N this
  is a *vector* (`pfaffian(T) = 6v₁ - 3v₂ + 2v₃`); 4D `Chain{⟨1111⟩,2}(1..6)` → `8.0v` (= a₁₂a₃₄ − a₁₃a₂₄ + a₁₄a₂₃).

---

## 5. Display / printing

### 5.1 2-arg `show` of nested chains (inherits `multivectors.jl:109-116`, `Leibniz.jl/src/indices.jl:187-203`)

* Outer chain prints `term₁ + term₂ …` with `" + "`/`" - "` separators on a non-compact io; each coefficient uses a
  compact io (`compactio`, `multivectors.jl:39-44`: Grassmann's global `compact()` flag defaults to true).
* `showvalue(io,V,B,i)`: if the coefficient type needs parentheses (`showparens(T) = !check_parnot(T) &&
  check_parval(T)`; parval = `Expr, Complex, Rational, TensorAlgebra`; `Projector` and TensorTerms are parnot) print
  `"(" i ")"` then the blade label; otherwise `show(i)` then `showstar(i)` (`"⊗"` if `i isa TensorAlgebra`,
  `"*"` if not an Integer/finite float) then the label.
* A negative sign is pulled out only for `Real` coefficients (`showterm`), so nested chains always print
  `" + (…)v₂"`.
* Results: `T` → `(1v₁+2v₂+3v₃)v₁ + (4v₁+5v₂+6v₃)v₂ + (7v₁+8v₂+10v₃)v₃`; inner chains print without spaces.
  Single-entry operators: `2v₁⊗v₁ + 2v₂⊗v₂ + 2v₃⊗v₃`; Zero entries `𝟎⊗v₁ + 𝟎⊗v₂ + 𝟎⊗v₃`.
* Multivector-of-Multivector (Outermorphism/TensorOperator(O)): first coefficient printed raw, and a Multivector
  whose only nonzero term is the scalar prints `1v⃖` (scalar then `pre[1]*'⃖'`, `multivectors.jl:355`), giving
  `1v⃖ + (0+1v₁+2v₂+3v₃)v₁ + … + (0-3v₁₂₃)v₁₂₃` (zero-coefficient outer terms are skipped via `isnull`, inner zero
  scalars shown as `0`).
* `show(io, X::TensorOperator) = show(io, X.v)` (`forms.jl:667`); `DiagonalOperator` and `Outermorphism` 2-arg
  show go through `TensorOperator(X)` (`forms.jl:545, 792`).

### 5.2 3-arg `show(io, MIME"text/plain", t)` (`forms.jl:669-710`, 547-553, 794-800, 1660-1666)

```
X = display_matrix(t.v)                          # Matrix{Any}, (rows+1) × (cols+1)
X[1,1]   = Submanifold(V)   (pseudoscalar label of the OUTER/domain manifold, e.g. "v₁₂₃", "v∞∅₁₂", "v₁₂")
X[1,2:]  = domain basis labels (chainbasis(V,G) | evenbasis | oddbasis | fullbasis)
X[2:,1]  = codomain basis labels (chainbasis(W,L) | …)
X[2:,2:] = matrix(t.v)
print(summary(t))  →  "R×C <julia type>"  using _axes (R = codomain dim, C = domain dim)
if X empty: return
print(":"); newline
print_matrix(IOContext(io, :compact=>true, :typeinfo=>eltype(X)), X)   # Julia Base printer
```
Julia `print_matrix` rules needed for byte-exact output (Julia 1.13 `base/arrayshow.jl:81-163`,
`base/show.jl:3009-3048`):
* every row starts with `pre = " "`; columns separated by `sep = "  "`; rows joined by `"\n"`; no trailing newline.
* per cell alignment pair `(l,r)`: Real → split `show(x)` at the first char in `[.eEfF]` (`l` = prefix width,
  `r` = rest); Integer and other `Number` (incl. `Submanifold`, `Single`, `Zero`, all TensorAlgebra since
  `TensorAlgebra <: Number`) → `(textwidth, 0)`; Complex → split after the last `+`/`-` not preceded by `e`/`f`;
  non-Number → `(0, width)`.
* column alignment `(L,R)` = max over the column; cell printed as `" "^(L-l) * s * " "^(R-r)`, except the last
  column gets no right padding.
* widths are `textwidth` (subscript digits, `⊗`, `𝟎`, `⃖` combining char → width 0!).
* compact float formatting: Julia `:compact=>true` Float64 show = shortest round-trip repr limited to 6 significant
  digits (`0.0714286`, `3.66667`, `8.88178e-16`, `279.14`, `-0.0`, `20.0855`, `1.0`); Complex compact
  `0.707107-0.0im`, `0.0+0.707107im`.
* `:limit` truncation (`" …"`) only when displaysize is tiny — ignore.
* Summary type strings are Julia type names with aliases (`Endomorphism{⟨+++⟩, Simplex{⟨+++⟩, Chain{⟨+++⟩, 1, Int64, 3}, 3}}`,
  `DiagonalMorphism{…}`, `Multiplex{…}`, `Quaternion{…}`, `SpectralOperator{…}`, `MetricTensor{3, 0, 1, 0, 0, 1}`).
  Recommendation: Lean goldens compare the dims prefix `R×C` and the matrix body byte-exactly, and use a Lean-native
  type description.

### 5.3 Projector (`forms.jl:427-428`)

* `λ::Real`: `(isone(λ) ? "" : string(λ)) * "Proj(" * string(v) * ")"` → `Proj(0.267261v₁ + 0.534522v₂ + 0.801784v₃)`,
  `2Proj(…)`, `2.5Proj(…)`, `-1Proj(…)`, `3.0Proj(0.707107v₁ + 0.707107v₂)`.
* otherwise: `"(" λ ")Proj(" v ")"` → `(1 + 2im)Proj(…)`, `(1.0v₁ + 3.0v₂)Proj((-0.707107v₁+0.707107v₂)v₁ + (0.707107v₁+0.707107v₂)v₂)`.
* 3-arg show falls back to 2-arg.

### 5.4 Dyadic (`forms.jl:464`)

`"(" x ")⊗(" y ")"` → `(1v₁ + 2v₂ + 3v₃)⊗(4v₁ + 5v₂ + 6v₃)`; nested: `((1.0v₁+2.0v₂)v₁ + (3.0v₁+4.0v₂)v₂)⊗((3.0v₁+4.0v₂)v₁ + (1.0v₁+2.0v₂)v₂)`.
Proj of a chain of dyadics: `Proj(((1.0v₁+2.0v₂)⊗(3.0v₁+4.0v₂))v₁ + ((3.0v₁+4.0v₂)⊗(1.0v₁+2.0v₂))v₂)`.

### 5.5 Others

* `LieBracket` → `LieBracket[...]` (`forms.jl:1554`).
* `MetricTensor` 2-arg → `show(Submanifold(M))` → `⟨[1, 2, 0],[2, 5, 0],[0, 0, 1]⟩`; subspace `G(1,2)` →
  `⟨[1, 2],[2, 5],_⟩` (DirectSum printing).
* `summary` strings: `"3×3 DiagonalMorphism{⟨+++⟩, Chain{⟨+++⟩, 1, Int64, 3}}"`,
  `"3×3 Endomorphism{⟨+++⟩, Simplex{⟨+++⟩, Chain{⟨+++⟩, 1, Int64, 3}, 3}}"`, `"3×3 MetricTensor{3, 0, 1, 0, 0, 1}"`.

### 5.6 `printtex` / `alltex` (`forms.jl:1745-1764`)

```
printtex(io, data):  n,m = size(data)
   for j in 1:n: for i in 1:m: print(data[j,i]); if i≠n print(" & ")     # (compares with n — bug for non-square)
                 if j≠m print(" \\\\\n")
printtex(data) = replace(replace(String, subscrepl...), "}_{" => "")   # merges consecutive subscripts
printtex(E::Endomorphism) = printtex(display_matrix(E.v))
alltex(V, ops=[∧,∨,<,>,<<,>>]) = printtex.(cayley.(Ref(V),ops))
```
Golden `Grassmann.alltex(ℝ2)[1]` (∧) =
`"v_{12} & v & v_{1} & v_{2} & v_{12} \\\\\nv & v & v_{1} & v_{2} & v_{12} \\\\\nv_{1} & v_{1} & 0 & v_{12} & 0 \\\\\nv_{2} & v_{2} & -1v_{12} & 0 & 0 \\\\\nv_{12} & v_{12} & 0 & 0 & 0"`
(Julia string literal; `\\\\\n` = two backslashes + newline). All six are in `outputs/p8.txt`.

---

## 6. Golden examples (verbatim; copy into Lean tests)

Setup for §6.1-6.5: `@basis S"+++"` (so `V = ⟨+++⟩`), `T = TensorOperator(Chain{V}(Chain{V}(1,2,3),Chain{V}(4,5,6),Chain{V}(7,8,10)))`,
`U = TensorOperator(Chain{V}(Chain{V}(2,0,1),Chain{V}(0,1,0),Chain{V}(1,0,3)))`, `O = outermorphism(T)`,
`x = Chain{V,1}(1,1,1)`. Matrices written row-wise (Julia literal).

### 6.1 TensorOperator display (3-arg), from `outputs/p1.txt`

```
3×3 Endomorphism{⟨111⟩, Simplex{⟨111⟩, Chain{⟨111⟩, 1, Int64, 3}, 3}}:
 v₁₂₃  v₁  v₂  v₃
   v₁   1   4   7
   v₂   2   5   8
   v₃   3   6  10
```
(for `TensorOperator(Chain(Chain(1,2,3),Chain(4,5,6),Chain(7,8,10)))`; with `S"+++"` the header is identical, type
params print `⟨+++⟩`.)
```
3×3 Endomorphism{⟨111⟩, Simplex{⟨111⟩, Chain{⟨111⟩, 1, Float64, 3}, 3}}:
 v₁₂₃  v₁         v₂         v₃
   v₁  -0.666667  -0.666667   1.0
   v₂  -1.33333    3.66667   -2.0
   v₃   1.0       -2.0        1.0
```
```
3×3 Endomorphism{⟨111⟩, Chain{⟨111⟩, 2, Chain{⟨111⟩, 2, Int64, 3}, 3}}:
 v₁₂₃  v₁₂  v₁₃  v₂₃
  v₁₂   -3   -6   -3
  v₁₃   -6  -11   -2
  v₂₃   -3   -4    2
```
```
8×8 Outermorphism{⟨111⟩, Tuple{Simplex{⟨111⟩, Chain{⟨111⟩, 1, Int64, 3}, 3}, Chain{⟨111⟩, 2, Chain{⟨111⟩, 2, Int64, 3}, 3}, Chain{⟨111⟩, 3, Chain{⟨111⟩, 3, Int64, 1}, 1}}}:
 v₁₂₃  v  v₁  v₂  v₃  v₁₂  v₁₃  v₂₃  v₁₂₃
    v  1   0   0   0    0    0    0     0
   v₁  0   1   4   7    0    0    0     0
   v₂  0   2   5   8    0    0    0     0
   v₃  0   3   6  10    0    0    0     0
  v₁₂  0   0   0   0   -3   -6   -3     0
  v₁₃  0   0   0   0   -6  -11   -2     0
  v₂₃  0   0   0   0   -3   -4    2     0
 v₁₂₃  0   0   0   0    0    0    0    -3
```
2-arg: `1v⃖ + (0+1v₁+2v₂+3v₃)v₁ + (0+4v₁+5v₂+6v₃)v₂ + (0+7v₁+8v₂+10v₃)v₃ + (0-3v₁₂-6v₁₃-3v₂₃)v₁₂ + (0-6v₁₂-11v₁₃-4v₂₃)v₁₃ + (0-3v₁₂-2v₁₃+2v₂₃)v₂₃ + (0-3v₁₂₃)v₁₂₃`

Non-square (`outputs/p13.txt`):
```
3×2 TensorOperator{⟨11⟩, ⟨111⟩, Simplex{⟨11⟩, Chain{⟨111⟩, 1, Int64, 3}, 2}}:
 v₁₂  v₁  v₂
  v₁   1   4
  v₂   2   5
  v₃   3   6
```
Complex (`eigvecs(Endomorphism([0 -1;1 0]))`):
```
2×2 Endomorphism{⟨11⟩, Simplex{⟨11⟩, Chain{⟨11⟩, 1, ComplexF64, 2}, 2}}:
 v₁₂         v₁                   v₂
  v₁  0.707107-0.0im       0.707107+0.0im
  v₂       0.0+0.707107im       0.0-0.707107im
```
Algebra-valued entries (`cayley(V,1)`):
```
3×3 Endomorphism{⟨+++⟩, Simplex{⟨+++⟩, Chain{⟨+++⟩, 1, T, 3} where T, 3}}:
 v₁₂₃     v₁     v₂   v₃
   v₁     1v    v₁₂  v₁₃
   v₂  -1v₁₂     1v  v₂₃
   v₃  -1v₁₃  -1v₂₃   1v
```
2-arg: `(1v⊗v₁+-1v₁₂⊗v₂+-1v₁₃⊗v₃)v₁ + (v₁₂⊗v₁+1v⊗v₂+-1v₂₃⊗v₃)v₂ + (v₁₃⊗v₁+v₂₃⊗v₂+1v⊗v₃)v₃`.
Conformal metric (`metrictensor(S"∞∅++")`):
```
4×4 Endomorphism{⟨∞∅11⟩, Simplex{⟨∞∅11⟩, Chain{⟨∞∅11⟩, 1, Int64, 4}, 4}}:
 v∞∅₁₂  v∞  v∅  v₁  v₂
    v∞   0  -1   0   0
    v∅  -1   0   0   0
    v₁   0   0   1   0
    v₂   0   0   0   1
```
MetricTensor:
```
3×3 MetricTensor{3, 0, 1, 0, 0, 1}:
 v₁₂₃  v₁  v₂  v₃
   v₁   1   2   0
   v₂   2   5   0
   v₃   0   0   1
```

### 6.2 Operator arithmetic (`outputs/p1.txt`, `p6.txt`, `p7.txt`)

| expression | result |
|---|---|
| `T[1,2]`, `T[2]`, `T[3,3]`, `T[end]` | `4`, `4v₁ + 5v₂ + 6v₃`, `10`, `7v₁ + 8v₂ + 10v₃` |
| `Matrix(T)` | `[1 4 7; 2 5 8; 3 6 10]` |
| `det(T)`, `∧(T)`, `tr(T)`, `scalar(T)` | `-3v`, `-3v₁₂₃`, `16`, `5.333333333333333` |
| `transpose(T)` | matrix `[1 2 3; 4 5 6; 7 8 10]` |
| `T(x)`, `T⋅x`, `T*x` | `12v₁ + 15v₂ + 19v₃` |
| `x⋅T` (row) | `6v₁ + 15v₂ + 25v₃`; `Chain{V,1}(1,0,0)⋅T = 1v₁ + 4v₂ + 7v₃` |
| `T(x,x)` | `46`; `T(e₁,e₂) = 2` |
| `T(v1)`, `T(2v2)` | `1v₁ + 2v₂ + 3v₃`, `8v₁ + 10v₂ + 12v₃` |
| `T+U`, `T*U`, `T/U` | `[3 4 8; 2 6 8; 4 6 13]`, `[9 4 22; 12 5 26; 16 6 33]`, `[-0.8 4.0 2.6; -0.3999999999999999 5.0 2.8000000000000003; -0.19999999999999973 6.0 3.4]` |
| `T+I`, `T-2I`, `I-T`, `2I-T` | `[2 4 7; 2 6 8; 3 6 11]`, `[-1 4 7; 2 3 8; 3 6 8]`, `[0 -4 -7; -2 -4 -8; -3 -6 -9]`, `[1 -4 -7; -2 -3 -8; -3 -6 -8]` |
| `T∧U`, `T∨U` | `[9 4 22; 12 5 26; 16 6 33]`, zeros |
| `T∧x`, `T∨x` | `12v₁ + 15v₂ + 19v₃`, `0v₁ + 0v₂ + 0v₃` |
| `exp(T/10)` | `[1.381098686987805 1.0258224828474027 1.7347950479557805; 0.54078553235932 2.267549715157114 2.0702278263185505; 0.7275554257321238 1.566608015206723 3.6009306854316674]` |
| `expm1(T/10)` | same minus I |
| `log(U)` | `[0.5895144857350482 -0.0 0.43040894096400373; -0.0 0.0 0.0; 0.43040894096400373 0.0 1.0199234266990527]` |
| `compound(T,2)` | `[-3 -6 -3; -6 -11 -2; -3 -4 2]` |
| `compound(T,3)` | `(-3v₁₂₃)v₁₂₃` |
| `compound(T,2)⋅compound(U,2)` | `[-3 -30 -6; -10 -55 0; -8 -20 9]` |
| `bivector(T)`, `pfaffian(T)` | `2v₁₂ + 3v₁₃ + 6v₂₃`, `6v₁ - 3v₂ + 2v₃` |
| `diag(T)`, `diag(compound(T,2))`, `DiagonalOperator(T)` | `1v₁ + 5v₂ + 10v₃`, `-3v₁₂ - 11v₁₃ + 2v₂₃`, diag(1,5,10) |
| `gerschgorin(T)`, `gerschgorin(U)` | `[11, 10, 9]`, `[1, 0, 1]` |
| `mean(T)`, `barycenter(T)`, `affineframe(T)` | `4.0v₁ + 5.0v₂ + 6.33333v₃`, `12v₁ + 15v₂ + 19v₃`, 2×2 `[3 6; 3 7]` on `⟨_++⟩` |
| `tr(O)`, `scalar(O)`, `det(O)`, `∧(O)` | `2`, `0.25`, `-3v`, `-3v₁₂₃` |
| `O[0]`, `O[2]` | `(1v)v`, compound 2 |
| `O⋅O` | block-diag `1`, `[30 66 109; 36 81 134; 45 102 169]`, `[54 96 15; 90 165 36; 27 54 21]`, `9` |
| `O⋅T`, `T⋅O` | `[30 66 109; 36 81 134; 45 102 169]` |
| `inv(O)` | block-diag `1.0`, `inv(T)`, `[-3.333333333333333 2.6666666666666665 -2.333333333333333; 2.0 -1.6666666666666665 1.3333333333333335; -1.0 0.6666666666666667 -0.3333333333333335]`, `-0.33333333333333304` |
| `adjugate(O)` | block-diag `1`, adj(T), `[-30 24 -21; 18 -15 12; -9 6 -3]`, `9` |
| `invdet(O)` | `(…, -3v)` |
| `characteristic(O)`, `eigvals(O)` | `3.0v₁ - 12.0v₂ - 16.0v₃`, `-0.90574v₁ + 0.198247v₂ + 16.7075v₃` |
| `eigvals(T)` / `eigvalsreal` / `eigvalscomplex` | `-0.90574v₁ + 0.198247v₂ + 16.7075v₃` / same / `(-0.90574+0.0im)v₁ + (0.198247+0.0im)v₂ + (16.7075+0.0im)v₃` |
| `eigpolys(T)` | `5.33333v₁ - 4.0v₂ - 3.0v₃` |
| `eigmults(T)` | `1v₁ + 1v₂ + 1v₃` |
| `discriminant(T)` | `103052.99999999785` |
| `vandermonde(T)` | rows `(1, λ_i, λ_i²)`: `[1.0 -0.90574 0.820365; 1.0 0.198247 0.0393018; 1.0 16.7075 279.14]` (compact print) |
| `eigvals(U)` | `1.0v₁ + 1.38197v₂ + 3.61803v₃` |
| `companion(1,2,3)` | `[0 0 -1; 1 0 -2; 0 1 -3]`; `companion(Chain(1,2,3,4))` = `[0 0 0 -1; 1 0 0 -2; 0 1 0 -3; 0 0 1 -4]` |
| `𝓛[T,U]` | `[4 -10 -2; 10 0 18; 6 -16 -4]` |
| `@TensorOperator([1 2; 3 4])\Chain(5,6)` | `-4.0v₁ + 4.5v₂` (docs: "exact") |

### 6.3 DiagonalOperator (`d = DiagonalOperator(Chain{V,1}(1,2,3))`, `outputs/p4.txt`)

| expression | result |
|---|---|
| `d[2,2]`, `d[1,2]`, `d[2]` | `2`, `0`, `2v₂` |
| `tr(d)`, `det(d)`, `∧(d)`, `scalar(d)` | `6`, `6v`, `6v₁₂₃`, `2.0` |
| `compound(d,2)` | diag `(2,3,6)` on `v₁₂,v₁₃,v₂₃` |
| `compound(d,0)` | `(1v)v` |
| `outermorphism(d)` 2-arg | `1v⃖ + (0+1v₁)v₁ + (0+2v₂)v₂ + (0+3v₃)v₃ + (0+2v₁₂)v₁₂ + (0+3v₁₃)v₁₃ + (0+6v₂₃)v₂₃ + (0+6v₁₂₃)v₁₂₃` |
| `adjugate(d)`, `adjugate(od)` | diag `(6,3,2)`; diag `1,6,3,2,18,12,6,36` |
| `inv(d)`, `exp(d)`, `log(d)` | diag `(1.0,0.5,0.333333)`, `(2.71828,7.38906,20.0855)`, `(0.0,0.693147,1.09861)` |
| `inv(od)` | diag `1.0,1.0,0.5,0.333333,0.5,0.333333,0.166667,0.166667` |
| `d(x=1v₁+2v₂+3v₃)`, `x⋅d`, `d*x`, `d∧x`, `d∨x` | `1v₁ + 4v₂ + 9v₃` ×4, `0v₁ + 0v₂ + 0v₃` |
| `d(x,x)` | `36` |
| `od(Chain{V,2}(1,1,1))`, `od(Multivector ones)` | `2v₁₂ + 3v₁₃ + 6v₂₃`, `1 + 1v₁ + 2v₂ + 3v₃ + 2v₁₂ + 3v₁₃ + 6v₂₃ + 6v₁₂₃` |
| `d+d`, `d-d`, `2d`, `d/2` | diag `(2,4,6)`, zeros, `(2,4,6)`, `(0.5,1.0,1.5)` |
| `eigvals(d)`, `eigvecs(d)`, `eigpolys(d)`, `eigpolys(d,2)` | `1.0v₁ + 2.0v₂ + 3.0v₃`, identity (Float), `2.0v₁ + 3.66667v₂ + 6.0v₃`, `3.6666666666666665` |
| `characteristic(d)`, `gerschgorin(d)` | `-6v₁ + 11v₂ - 6v₃`, `0v₁ + 0v₂ + 0v₃` |
| `Grassmann.sylvester(d)` | `2.0v₁ - 1.0v₂ + 2.0v₃` |
| `sylvester(Chain(1,1,2))`, `eigmults(Chain(1,1,2))`, `eigmults(Chain(2,2,2))` | `1v₁ + 1v₂ + 1v₃`, `2v₁ + 2v₂ + 1v₃`, `3v₁ + 3v₂ + 3v₃` |
| `DiagonalOperator([1 2;3 4])` | diag `(1,4)` on `⟨11⟩` |
| `DiagonalOutermorphism([1 2;3 4])` 2-arg | `1v⃖ + (0+1v₁)v₁ + (0+4v₂)v₂ + (0+4v₁₂)v₁₂` |
| `d⋅T`, `T⋅d` (Julia) | `[1 4 7; 4 10 16; 9 18 30]` (correct D·T), `[1 2 3; 8 10 12; 21 24 30]` (**buggy** = (T·D)ᵀ; correct `[1 8 21; 2 10 24; 3 12 30]`) |
| `DiagonalOperator(Chain(2,3,5))` outer on `CoSpinor ones` (Julia) | `1v₁ + 6v₂ + 10v₃ + 15v₁₂₃` (**buggy**; correct `2v₁ + 3v₂ + 5v₃ + 30v₁₂₃`) |

### 6.4 Rotation / 2×2 / 4×4 / 5×5 (`outputs/p7.txt`)

`R = Endomorphism([0 -1; 1 0])`: `eigvals(R) = (0.0-1.0im)v₁ + (0.0+1.0im)v₂`; `eigvalsreal(R)` →
`DomainError with -4.0`; `characteristic(R) = 1v₁ + 0v₂`; `discriminant(R) = -4`; `eigpolys(R) = 0.0v₁ + 1.0v₂`;
`eigen(R) = ((0.0-1.0im)v₁ + (0.0+1.0im)v₂)Proj(((0.707107-0.0im)v₁+(0.0+0.707107im)v₂)v₁ + ((0.707107+0.0im)v₁+(0.0-0.707107im)v₂)v₂)`.
`A4 = Endomorphism([4 1 0 0;1 3 1 0;0 1 2 1;0 0 1 1])`: `eigvals = 0.254719v₁ + 1.82272v₂ + 3.17728v₃ + 4.74528v₄`,
`eigpolys = 2.5v₁ + 5.33333v₂ + 8.75v₃ + 7.0v₄`, `discriminant = 16317.000000000002`, `gerschgorin = [1, 2, 2, 1]`,
`sylvester = 20.5783v₁ - 6.2074v₂ + 6.2074v₃ - 20.5783v₄`.
`A5 = Endomorphism(tridiag 2/1)`: `eigvals = 0.267949v₁ + 1.0v₂ + 2.0v₃ + 3.0v₄ + 3.73205v₅`, `det = 6v`.
`vandermonde(Chain(1,2,3))` = `[1 1 1; 1 2 4; 1 3 9]`, `discriminant(Chain(1,2,3)) = 4`.

### 6.5 Metric (`outputs/p8.txt`)

`metrictensor(ℝ3)` = I (on `⟨111⟩`); `metrictensor(S"-++")` = diag(-1,1,1); `metrictensor(D"1,2,3")` = diag(1,2,3);
`metrictensor(S"∅++")` = diag(-1,1,1); `metrictensor(S"-++",2)` = diag(-1,-1,1) on `(v₁₂,v₁₃,v₂₃)`;
`antimetrictensor(S"-++")` = same; `metricextensor(S"-++")` = block diag `1,-1,1,1,-1,-1,1,-1`;
`MetricTensor(Values(1,2,3))`, `MetricTensor([1,2,3])`, `MetricTensor(Chain(1,2,3))` → `DiagonalForm` `⟨1,2,3⟩`;
`MetricTensor((1,2),(2,5))` → `⟨[1, 2],[2, 5]⟩`; `G[1] = [1, 2, 0]`; `Signature(G) = ⟨+++⟩`; `isdiag(G) = false`.

### 6.6 Cayley tables (docs `docs/src/algebra.md:623-1000`, reproduced by `alltex`)

`cayley(Submanifold(3),*)` rows/cols `v, v₁, v₂, v₃, v₁₂, v₁₃, v₂₃, v₁₂₃` (entry = row * col):
```
v     | v  v₁  v₂  v₃  v₁₂  v₁₃  v₂₃  v₁₂₃
v₁    | v₁  v  v₁₂  v₁₃  v₂  v₃  v₁₂₃  v₂₃
v₂    | v₂  -v₁₂  v  v₂₃  -v₁  -v₁₂₃  v₃  -v₁₃
v₃    | v₃  -v₁₃  -v₂₃  v  v₁₂₃  -v₁  -v₂  v₁₂
v₁₂   | v₁₂  -v₂  v₁  v₁₂₃  -v  -v₂₃  v₁₃  -v₃
v₁₃   | v₁₃  -v₃  -v₁₂₃  v₁  v₂₃  -v  -v₁₂  v₂
v₂₃   | v₂₃  v₁₂₃  -v₃  v₂  -v₁₃  v₁₂  -v  -v₁
v₁₂₃  | v₁₂₃  v₂₃  -v₁₃  v₁₂  -v₃  v₂  -v₁  -v
```
The docs also give `∧, ∨, <, >, <<, >>` tables for `Submanifold(1)`, `S"-"`, `Submanifold(2)`, `S"+-"`,
`Submanifold(3)` (`algebra.md:626-1000`) — reuse them as goldens for the `cayley`/`printtex` pipeline (they are
products.jl semantics, but the table layout is forms.jl).

### 6.7 Docs examples that are NOT reproducible (do not use as goldens)

`docs/src/tutorials/dyadic-tensors.md`: `@mixedbasis ℝ2; (w1+2w2)(v1+v2)` expected a covector evaluation `3`, current
Julia returns `0v`; `ℒ = (v1+2v2)∧(3w1+4w2); ℒ(v1+v2)` expected `[7,14]`, returns `0v₁ + 0v₂ + 9w¹ + 12w²` (the
dyadic form evaluation lived in the commented-out block). Also `Chain(m::Matrix)` examples (`DyadicChain` undefined).

---

## 7. Dependencies on other chakravala packages

| package | symbols used by forms.jl |
|---|---|
| **Leibniz.jl** | `mdims, gdims, tdims, indices, indexbasis, bladeindex, basisindex, binomsum, binomsum_set, gdimsall, lowerbits, expandbits, mixed, intlog, mvec, svec, insert_expr, Fields=(Real,Complex), check_parnot, extend_parnot, parval, showvalue, showstar, supermanifold, dyadmode, hasconformal, Derivation` |
| **DirectSum.jl** | `Submanifold, Signature, DiagonalForm, TensorBundle, Manifold, Single, Zero, One, getbasis, isbasis, isdyadic, isdual, issubmanifold, submanifold, eval_shift, evaluate1/2, interform, Λ (basis cache, .b), diffvars, diffmode, options, diagsig, diagonalform, construct_cache, getalgebra, SUB, grade(V), ⊕, ⊆, ∪` |
| **AbstractTensors.jl** | `TensorAlgebra, TensorGraded, TensorMixed, TensorTerm, Manifold, Values, FixedVector, Variables, value, valuetype, scalar, isscalar, vector, bivector, volume, contraction, wedgedot (⟑), contraction_metric, wedgedot_metric, ⊗, interop/interform, isnull, unit, multispin` |
| **StaticVectors.jl** (via AbstractTensors) | `Values{N,T}` (immutable SVector), `Variables` (mutable), `SOneTo` |
| Grassmann internals | `Chain, Multivector, Spinor, CoSpinor/AntiSpinor, Couple, PseudoCouple, Simplex, compound, invdet, adjugate, cofactor, inv, exp, pfaffian, monicroots*, companion (self), affineframe, mean, barycenter, curl, even, odd, imaginary, multispin, complementright/…, metric, cometric, ⊘ sandwich, ∧/∨, column, list, evens, setblade!, setmulti!` |
| Base/stdlib | `LinearAlgebra: eigen, eigvals, eigvecs, diag, det, tr, I/UniformScaling, log (matrix)`, Julia `print_matrix` |

Downstream users: Cartan.jl (`gradienthat`, `affineframe(FaceBundle)`, `volumes`, `detsimplex` for meshes),
Adapode.jl (FEM assembly uses `TensorOperator` gradients), Grassmann plotting exts.

---

## 8. Lean 4 porting notes

### 8.1 Type design (dependent indices only where free)

Recommended core (all shape data are `Nat`/small inductive indices; storage is a flat column-major array):
```lean
/-- A graded component of Λ(ℝⁿ): which blades a vector-like object spans. -/
inductive Shape (n : Nat) | grade (g : Nat) | even | odd | full
def Shape.dim : Shape n → Nat
  | .grade g => n.choose g | .even => 2^(n-1) | .odd => 2^(n-1) | .full => 2^n   -- n ≥ 1 for even/odd

/-- Dense column-major matrix; rows = codomain components, cols = domain blades. -/
structure Mat (r c : Nat) (α : Type) where
  data : Array α          -- FloatArray specialization for α = Float
  hsize : data.size = r * c   -- erased proof

/-- TensorOperator: Λ^{sd} ℝ^n → Λ^{sc} ℝ^m. -/
structure Op (n m : Nat) (sd : Shape n) (sc : Shape m) (α) where
  mat : Mat sc.dim sd.dim α
abbrev Endo (n) (s : Shape n) α := Op n n s s α
structure Diag (n) (s : Shape n) α where d : Vec s.dim α
structure Outer (n m : Nat) α where blocks : (g : Fin (min n m)) → Op n m (.grade (g+1)) (.grade (g+1)) α
structure Proj (n) (s) α (Λ) where v : Vec s.dim α; λ : Λ          -- rank one
structure Spectral (n) α where vecs : Endo n (.grade 1) α; vals : Vec n α
structure Dyadic (n m) (sx sy) α where x : Vec sx.dim α; y : Vec sy.dim α  -- + a "sum" variant: Array of pairs
```
* `n, m, g` as type indices: they're `Nat` so the compiler passes them at runtime (cheap scalars) but all sizes are
  checked statically → no bounds checks with `Fin`-indexed access (`data[i]'h`).
* **Metric/signature does not appear in operator types.** All operator linear algebra (apply, compose, compound,
  det, inv, adjugate, trace, characteristic, eigen) is metric-free (verified on 4 signatures). Only `operator(t)`
  (sandwich), `metrictensor`, `Proj(v)` normalisation (`abs` uses the metric), multivector-level `⋅` in
  Proj/Dyadic contraction, and display labels need the algebra's `Space`. Pass the space explicitly to those.
* `Outermorphism` stores `min(n,m)` blocks; represent with an `Array` of per-grade `Mat`s plus a proof of sizes,
  or a heterogeneous `(g : Fin k) → Mat …` (functions are not cached — prefer `Array (Σ …)` or a flat block-diagonal
  buffer with offset table `binomsum`). The grade-0 block is implicit 1 (keep that quirk as a separate field
  `scalarBlock := 1` only if you want Julia `2O` fidelity; recommended: make scalar mult act on grade 0 too and
  record the divergence).
* Julia's nested `Chain{V,G,Chain{W,L}}` values also occur *outside* TensorOperator (e.g. `compound` returns a raw
  nested Chain; `transpose` of a raw Simplex; simplices as point lists). Provide `Op.ofColumns : Vec c (Chain m sc) → Op`
  and `Op.cols` so the core `Chain` type from the multivector port can interoperate without copying (share the flat
  array layout: a Chain is a column).
* Algebra-valued entries (cayley tables, `operator(fun,V)` with `Single` results) → generic `α` (any type with the
  needed ops); `Op n m sd sc (Multivector …)` works since `Op` is polymorphic in `α`.

### 8.2 Hot paths and how Julia gets its speed

| Julia mechanism | where | Lean equivalent |
|---|---|---|
| `@generated matmul` fully unrolled `Σ_i x[i][j]*y[i]` over isbits `Values` | `forms.jl:954-974` | tight `for` loops over `Fin` on a flat `FloatArray`; `@[specialize, inline]`; for n≤4 optionally hand-unrolled `Mat3`/`Mat4` structs with unboxed Float fields |
| `@generated compound` = tuple of wedge products of column subsets | `composite.jl:717-720` | precomputed per-(n,g) combination tables (`Array (Array (Fin n))`, built once via `initialize` or compile-time `#eval`/`decide`-reduced constants); compute minors by iterated wedge of columns reusing the core wedge kernel (sign via inversion count), or Bareiss for large g |
| Cramer via wedge chains (`Grassmann.Cramer`) for `\`, `inv`, `∈` | `composite.jl:707-840` | same algorithm (prefix/suffix wedges) — exact for Int/Rat; for Float n≥5 consider LU |
| `@generated outermorphism`/`sylvester`/`bivector`/`diag` | forms.jl | ordinary loops; index tables cached |
| global caches (`indexbasis_cache`, `lowerbits_cache`, `metrictensor_cache`) | Leibniz, forms.jl:1634 | pure functions + optional memo `IO.Ref`/`initialize` tables; the metric registry disappears (metric is a value) |
| `choicevec` mutable scratch `mvec` + `setblade!` | forms.jl:16-17, 53-62 | build output with `Array.mkArray` + `set!` in `Id.run do` (unique ownership → in-place) |
| type-level dims → LLVM constant folding | everywhere | `Nat` indices + `@[specialize]`; avoid `Array (Array α)` double indirection |
| LAPACK eigen for n≥5, matrix `log` | forms.jl:1381, 1429, 606 | implement Hessenberg+Francis QR (real), Jacobi (symmetric) in Lean; matrix log via inverse scaling & squaring + Padé (or eigen for diagonalizable); document tolerance-based goldens |
| Padé scaling-squaring `exp` (Higham) | composite.jl:246+ | port directly (pure arithmetic) |

### 8.3 Proof opportunities that speed development (cheap, high value)

* `Mat` size invariant as an erased field; `Fin`-indexed get/set without bounds checks.
* `Shape.dim` lemmas: `(Shape.grade g).dim = n.choose g`, `Σ_g choose = 2^n` (`Nat.sum_range_choose`) → proves
  Outermorphism→full-matrix block offsets are in range (`binomsum`), and `even.dim + odd.dim = full.dim`.
* `transpose (transpose A) = A`, `(A*B)ᵀ = BᵀAᵀ` on the spec model (`List`/`Function`-based) with a
  `@[csimp]`-style refinement to the array implementation, or `decide`/`native_decide` spot checks on small ℤ matrices.
* `det (diag d) = Π d`, `compound_g (diag d) = diag (Π over subsets)`, `adjugate (diag d)_i = Π_{j≠i} d_j`,
  `characteristic_exact (diag d) = (−1)^… e_k(d)` — all by `simp`/`decide` for fixed n ≤ 4, or general induction.
* Characteristic closed forms (n≤4) vs `characteristic_exact` equality over ℚ: `ring`-checkable identities
  (Newton's identities) — a nice "standout" theorem that also guards the port.
* Cauchy–Binet: `compound_g (A*B) = compound_g A * compound_g B` — state as a spec (`sorry`-able theorem) and
  property-test it; it is exactly why `Outermorphism ⋅ Outermorphism` may recompute from grade 1.
* `tr (outermorphism A) = det (1 + A)` spec.

### 8.4 Julia bugs / quirks — decide per item (default: port the *intended* math, record divergence in tests)

1. `Endomorphism ⋅ DiagonalOperator` returns `(A·D)ᵀ` (`forms.jl:1048`) → port `A·D`.
2. `DiagonalOutermorphism ⋅ AntiSpinor` uses the even part (`forms.jl:1037-1038`) → use odd part.
3. `diag(::Endomorphism{V,<:CoSpinor})` returns `Spinor` (`forms.jl:651-653`) → CoSpinor.
4. `transpose` is identity for non-grade-1 nestings (Base fallback) → implement real transpose.
5. `transpose(::Outermorphism)` MethodError (`forms.jl:742`) → `Outermorphism{V}(map transpose)`.
6. `Outermorphism ⋅ Spinor/AntiSpinor` padding wrong for odd `min(N,M)` < M (`forms.jl:1056-1067`).
7. `eigpolys(::Outermorphism, Val(1))` references undefined `x` (`forms.jl:1264`).
8. `+` on `Projector`s (`eigvec` undefined, `forms.jl:985`), on `Dyadic`s / TensorNested (`forms.jl:986-987`)
   broken; `+(Spectral,Spectral)` returns a bare Chain (drops λ, `forms.jl:991`). Intended: formal sums of rank-one
   terms (`Spectral` with concatenated vectors and eigenvalues; `Dyadic` with Chain-of-vectors x,y) — which the
   `contraction` rules at `forms.jl:979-983` already evaluate correctly.
9. `det(::SpectralOperator)` = `Chain{V,0}(prod(λ))` where `prod(::Chain)` is the Chain itself → prints
   `(1.0v₁+3.0v₂)v` (`forms.jl:416`) → port `Π λ_k`.
10. `P[i,j]` for Proj and SpectralOperator ignore λ (and conj) (`forms.jl:419, 421`) → port `Σ_k λ_k v_k[i] conj(v_k[j])`
    (fidelity mode: keep Julia behaviour behind a flag if exact golden parity is required).
11. `exp/log(::Proj)` (rank one) are heuristics (first column of matrix exp normalised by `sqrt(out[1])`,
    `forms.jl:401-408`) — no algebraic meaning; recommend porting `exp(P) = Endomorphism(exp(matrix P))` instead and
    mark divergence; `log` of a singular projector yields complex garbage in Julia.
12. `==` StackOverflow in 0.8.46 for operator types (fixed in master: value equality).
13. Subspace projection (`W⊆V`, grade ≥2 / Multivector) uses `lowerbits(M,…)` and a buggy/cache-order-dependent
    `lowerbits` (§3.1, §4.1) → implement pext.
14. Dyadic (mixed V⊕V′) Chain evaluation branch references undefined `Y`/`N` (`forms.jl:32, 35`) → either
    implement covector pairing (`wⁱ(x) = x_i`, `(vᵢ∧wʲ)(x) = x_j vᵢ` as the docs intend) or leave unsupported;
    current Julia falls back to contraction for those calls.
15. `TensorOperator(::AbstractMatrix)` non-square → DimensionMismatch (`forms.jl:632-633`, V/W mislabelled);
    `Chain(::Matrix)` → `DyadicChain` undefined (`forms.jl:336`); `Chain{V}(::Matrix)`, `Multivector(::Matrix)`,
    `Spinor(::Matrix)` → MethodError. Port: `Op.ofMatrix (m : Array (Array α))` with rows/cols explicit.
16. `eigen(X)` MethodError when `V` is a `Signature` (e.g. `S"+++"`) because `Endomorphism{V}(eigvecs matrix)` builds
    inner chains over `Submanifold(n)`; works for `Endomorphism(matrix)` (`forms.jl:1430`).
17. `eigvals(::Spinor)` in 2D fails (`imaginary(::Spinor)` missing, `forms.jl:1364`).
18. `vecdot(::CoSpinor, ::Multivector)` uses `even(y)` → always 0 (`forms.jl:874`) → use `odd(y)`.
19. `MetricTensor[:]` MethodError (`forms.jl:1652`); `Signature(::MetricTensor)` returns all-plus signature.
20. `ℝ4(x)` with `x` over `S"+++"` → infinite recursion (V == V'' branch).
21. `LinearAlgebra.sylvester` name clash.
22. Type instability of `eigvals` (Real vs Complex by runtime discriminant): Lean API should be
    `eigvals : … → Vec n Complex`, `eigvalsReal : … → Except String (Vec n Float)`, `eigvalsComplex` = `eigvals`.
23. `printtex` compares column index with the row count (`i≠n`) — only correct for square data.
24. `Outermorphism` scalar multiplication / addition do not touch the implicit grade-0 block (quirk; decide).
25. Julia-specific and to be **skipped/redesigned**: `@pure`, `@generated`, `choicevec`/`mvec`/`svec` storage choice,
    `construct_cache`, `metrictensor_cache` type-level interning, `Leibniz.check_parnot/extend_parnot` printing
    registries (replace with a `ShowCoeff` typeclass flag), macros `@TensorOperator/@Endomorphism/@Outermorphism/@SpectralOperator`
    (just functions in Lean), `IOContext` machinery (replace with explicit `compact : Bool`), `Base.summary` type names.

### 8.5 Suggested module decomposition (Lean, rough LOC)

| module | contents | LOC |
|---|---|---|
| `Grassmann/Forms/Shape.lean` | `Shape`, dims, blade index tables for grade/even/odd/full, pext/pdep, combination tables | 200 |
| `Grassmann/Forms/Mat.lean` | flat column-major `Mat`, get/set, map, zipWith, transpose, matmul/matvec/vecmat, identity, `±λI`, trace, diag, gerschgorin, `ofRows`/`toRows` | 350 |
| `Grassmann/Forms/Operator.lean` | `Op`/`Endo` over shapes, apply to Chain/Spinor/CoSpinor/Multivector, compose, `/`, scalar ops, `ofFun` (operator(fun,V)), `ofColumns`, bilinear `T(x,y)` via `vecdot`, `A:B` | 350 |
| `Grassmann/Forms/Compound.lean` | compound via column wedges / minors, det (exact, Bareiss for large n), adjugate/cofactor/inv/invdet (Cramer wedge chains, pseudo-inverse), `∧(T)`, bivector, pfaffian | 450 |
| `Grassmann/Forms/Outermorphism.lean` | `Outer`, construction, apply (all shapes with correct padding), to full `Op` (block-diag), tr/det/scalar/inv/adjugate/transpose/±/scalar mult | 300 |
| `Grassmann/Forms/Diagonal.lean` | `Diag` for all shapes, compound/outermorphism/adjugate/inv/exp/log, contraction rules incl. Diag·Op and Op·Diag (fixed) | 250 |
| `Grassmann/Forms/Dyadic.lean` | `Dyadic` (single + sums), `Proj`, `Spectral`, contraction rules, materialisation (`outer`), functional calculus on Spectral | 300 |
| `Grassmann/Forms/Spectral.lean` | characteristic (closed n≤4 + exact), eigpolys, sylvester, eigmults, companion, vandermonde, discriminant(s), eigvals (monicroots from composite port + QR), eigvecs/eigen (QR + inverse iteration or Jacobi) | 600 |
| `Grassmann/Forms/Metric.lean` | metricdyad/metrictensor/antimetrictensor/metricextensor, non-diagonal metric spaces & restriction to subspaces, InducedMetric | 200 |
| `Grassmann/Forms/Eval.lean` | element call semantics: subspace projection/embedding (Chain/Multivector), multilinear `t(y…)`, component/grade accessors, `vecdot` table | 300 |
| `Grassmann/Forms/Cayley.lean` | cayley/cayleyeven/cayleyodd tables, sandwich `operator(t)`, `gradedoperator`, `⊘` on Op | 150 |
| `Grassmann/Forms/Lie.lean` | LieBracket/LieDerivative, n-ary bracket recursion | 100 |
| `Grassmann/Forms/Show.lean` | 2-arg nested show, Julia `print_matrix` alignment clone, compact float/complex formatting (shared with core show), Proj/Dyadic show, printtex/alltex | 400 |
| `Grassmann/Forms/Simplex.lean` (Appendix A) | affineframe, mean/barycenter/centroid, detsimplex, volumes, point-in-simplex, Cramer solve, barycentric gradient | 250 |
| `Grassmann/Forms/Spec.lean` + tests | spec model lemmas (§8.3), golden tests, property tests | 400 |
| **total** | | **~4600** |

(Core `Chain`/`Multivector`/wedge/contraction kernels are assumed to come from the multivector/products port.)

---

## 9. Oracle test plan

Driver: a Julia script in the juliaenv (`--startup-file=no`) writing JSON Lines `{fn, args, out, meta}`; Lean reads
and compares. Encode matrices as row-major nested arrays (from `Matrix(T)`), Chains as `{"V": "S\"+++\"", "G": g,
"v": [...]}`, Floats as both decimal and `reinterpret(UInt64,x)` hex, Complex as `[re,im]`. Strings (show output) as
raw UTF-8. Seeded RNG (`Random.seed!(k)`), record seed.

### 9.1 Input distributions

* Dimensions n ∈ {1,2,3,4,5,6} (Julia closed forms switch at n=5; n≤8 for compounds/outermorphisms).
* Integer matrices entries uniform in −5..5 (exactness: det, compound, adjugate, cofactor, characteristic_exact).
* Float matrices entries N(0,1); plus special families: symmetric positive definite (`B'B+I`), skew-symmetric,
  rotations (Givens products), diagonal with repeated entries (eigmults/sylvester), nilpotent (Jordan blocks),
  singular (rank-deficient), companion matrices of random monic polynomials with known roots, near-degenerate
  (eigenvalue gaps 1e-8).
* Non-square shapes (m,n) ∈ {(3,2),(2,3),(4,2),(4,3)} as `Chain{Submanifold(n),1}(Chain{Submanifold(m),1}(...)...)`
  (NOT via `TensorOperator(::Matrix)`, which is broken).
* Signatures: `ℝ^n`, `S"-++"`, `S"---"`, `D"2,3,5"`, `S"∞∅++"`, `S"∅++"`, `MetricTensor([...])` SPD 3×3.
* Algebra elements for `operator`/`outermorphism`/`eigvals`: random vectors, bivectors, rotors (`exp(θ B)`),
  `Couple`s, full Multivectors, in n=2,3,4.

### 9.2 Functions to dump (grouped; ✔ = Julia output trustworthy, ✘ = known-buggy → hand-written or skip)

| group | functions | trust |
|---|---|---|
| layout | `Matrix(T)`, `T[i,j]`, `T[i]`, `summary(T)`, `size` | ✔ |
| apply | `T(x)`, `T⋅x`, `x⋅T`, `T(x,y)`, `T(basis blade)`, `T*U`, `T⋅U`, `T+U`, `T-U`, `T/U`, `2T`, `T/2`, `T±I`, `I±T`, `λI` ctors, `map(f,T)` | ✔ (square); non-square `A⋅x` ✔ for Euclidean |
| transpose | grade-1 nestings ✔; other nestings ✘ (identity in Julia) |
| exact det family | `det`, `∧`, `compound(T,g)` all g, `adjugate`, `cofactor`, `invdet` second component | ✔ |
| float inverse | `inv`, `invdet`, `\` (Cramer) incl. pseudo-inverse non-square | ✔ (rtol 1e-12) |
| outermorphism | `Matrix(outermorphism(T))`, `O(x)` for Chain of each grade, Multivector, Spinor/CoSpinor (N==M or even min), `O⋅O`, `inv(O)`, `adjugate(O)`, `tr/scalar/det/∧(O)` | ✔ (except transpose ✘, odd-min padding ✘) |
| diagonal | all of §6.3; `Op⋅Diag` ✘; `DiagOuter⋅CoSpinor` ✘ | mixed |
| spectral | `characteristic` (n=1..6), `characteristic_exact`, `characteristic(X,m)`, `eigpolys`, `eigpolys(X,g)`, `sylvester`, `eigmults`, `vandermonde*`, `discriminant*`, `gerschgorin`, `companion` | ✔ |
| eigen | `eigvals*` (n≤4 closed forms, n≥5 LAPACK), `eigen` (only on `Submanifold(n)` spaces ✘ on Signature), `eigvecs` | ✔ values (sort then compare, rtol 1e-9); vectors compare by residual `‖Av−λv‖` and up to phase |
| element eigvals | `eigvals(Couple/Spinor/Chain/Scalar)` in 2D/3D | ✔ (2D Spinor ✘) |
| operator(t) | `operator(t, g)`, `outermorphism(t)` (gradedoperator), `eigvals(operator(t))` | ✔ |
| dyadic/proj | `Proj(v,λ)⋅x`, `x⋅Proj`, `Dyadic⋅x`, `x⋅Dyadic`, `Dyadic⋅Dyadic`, `Proj⋅Dyadic`, `Chain(P)`, `tr`, `D[i,j]`, `transpose(D)`, sums via Chain-of-vectors | ✔; `P[i,j]` with λ≠1 ✘; `+` ✘; `det(Spectral)` ✘; `exp/log(Proj)` ✘ |
| spectral op | `eigen(Endomorphism(matrix))`: `S.λ`, `S[i]`, `Chain(S)`, `S⋅x`, `inv/exp/log(S)`, `tr(S)` | ✔ |
| metric | `Matrix(metrictensor(V))`, `metrictensor(V,g)`, `antimetrictensor`, `Matrix(metricextensor(V))`, `MetricTensor` Gram columns, restriction `TensorBundle(G(i,j))` | ✔ |
| eval/forms | `W(x)` embeddings ✔, `W(x)` grade-1 projections ✔, higher-grade/Multivector projections ✘, `t(y…)` multilinear ✔, `vecdot` table ✔ (except CoSpinor·Multivector ✘) | mixed |
| cayley/TeX | `cayley(V,op)` for n≤3 and ops `[*,∧,∨,<,>,<<,>>]` as entry strings; `Grassmann.alltex(V)`; `printtex(Endomorphism)` | ✔ |
| show | 2-arg `repr(T)`, 3-arg `repr(MIME"text/plain"(),T)` body lines (drop summary), Proj/Dyadic show | ✔ |
| Lie | `𝓛[T,U]`, `𝓛[T,U,W]`, 4/5-ary on random endomorphisms (compare matrices) | ✔ |
| simplex (App. A) | `affineframe`, `mean`, `barycenter`, `centroid`, `∈`, `\`, `inv`, `gradient`, `detsimplex`, `volumes` on random simplices in homogeneous coords (first coordinate 1) | ✔ |

Tolerances: exact (Int/Rational) for the det family and characteristic_exact; `rtol=1e-12` for inverse/Cramer;
`rtol=1e-9, atol=1e-12` for closed-form roots and LAPACK; `exp`/`log` `rtol=1e-12`. For display goldens require
byte equality of matrix bodies generated with the same values (use integer-valued or dyadic-rational Floats to avoid
last-digit issues).

### 9.3 Suggested dump skeleton (Julia)

```julia
using Grassmann, LinearAlgebra, JSON, Random
out = open("forms_golden.jsonl","w")
emit(fn, args, val) = println(out, JSON.json(Dict("fn"=>fn,"args"=>args,"out"=>val)))
for n in 1:6, trial in 1:50
    Random.seed!(1000n+trial)
    A = rand(-5:5, n, n); T = Endomorphism(A)
    emit("det", A, Int(value(det(T))[1]))
    for g in 0:n; emit("compound", (A,g), Matrix(compound(T,g))); end
    emit("adjugate", A, Matrix(adjugate(T))); emit("cofactor", A, Matrix(cofactor(T)))
    emit("characteristic_exact", A, collect(value(Grassmann.characteristic_exact(T))))
    emit("outermorphism", A, Matrix(outermorphism(T)))
    x = rand(-5:5, n); emit("apply", (A,x), collect(value(T(Chain{Submanifold(n),1}(x...)))))
    n ≤ 4 && emit("characteristic", A, collect(value(characteristic(T))))
    # … floats, eigen (sorted), show strings, etc.
end
close(out)
```
(`JSON` is in the env; do not `Pkg.add`.)

---

## Appendix A — simplex utilities (composite.jl; requested in scope)

All operate on a simplex given as `Values{N,Chain{V,1}}` / `Chain{V,1,<:Chain}` of N points in **homogeneous
coordinates** (first coordinate = 1, e.g. 2D points in `Submanifold(3)` as `(1,x,y)`).

| function | definition | file:line |
|---|---|---|
| `list(a,b)`, `evens(a,b)` | `Values(a:b)`, `Values(a:2:b)` | `composite.jl:897-898` |
| `affineframe(x::Values{1,…})` | empty `Values{0}` | `composite.jl:899` |
| `affineframe(x::Values{N,<:Chain{V}}, y=x[1])` @generated | `TensorOperator(Chain{V(2:N),1}(↓(V).(x[2:N] .- y)))`: edge vectors from the first point, homogeneous coordinate dropped (`↓(V)` on a Euclidean space = `V(2:mdims(V))`) | `composite.jl:900-903` |
| `affineframe(x::Chain{V,1}, y)` / `(x::TensorOperator, y)` | delegate | `composite.jl:904`, `forms.jl:1711` |
| `vectors` | alias of affineframe | `composite.jl:906` |
| `signscalar(x)` | true iff scalar and nonnegative (Submanifold grade 0 → true; Single/Chain grade 0 → `!signbit`) | `composite.jl:909-914` |
| `Cramer(N, j=0)` | builds prefix/suffix wedge symbol assignments `(x_{i+1},y_{i+1}) = (x_i∧t[1+i-j], t[end-i]∧y_i)` | `composite.jl:707-712` |
| `t \ v` (`Values{M,<:Chain{V,1}}`, square) | Cramer: `c_i = (x_{i-1} ∧ v ∧ y_{n-i}) / (t₁∧y_{n-1})`, returned as `Chain{W,1}(Real.(…))` | `composite.jl:722-732` |
| `t \ v` (M > dims) | least squares `tt⋅(inv(t⋅tt)⋅v)` | `composite.jl:725` |
| `v ∈ t` (N == dims) | all Cramer numerators have the same sign as the determinant (barycentric coords ≥ 0) | `composite.jl:734-739` |
| `v ∈ t` (N < dims, embedded simplex) | same test in the affine frame with `signscalar` | `composite.jl:740-746` |
| `inv(t)` / `invdet` / `adjugate` / `cofactor` | §4.8 | `composite.jl:749-812` |
| `gradient(T::Values{M,<:Chain{V,1}})` | barycentric-coordinate gradients ("hat function" gradients): for a full simplex, rows of `inv(T)` minus the homogeneous component → `Simplex{V,Chain{↓V}}`; for M < dims: `map(↓(V), ct⋅inv(tᵀ⋅ct))` | `composite.jl:814-831` |
| `findfirst/findlast/findall(P, t::AbstractVector{<:Chain{V,1,<:Chain}})` | simplex search by `∈` | `composite.jl:917-929` |
| `edgelength(e)` | `|p₂−p₁|` of an edge | `composite.jl:931` |
| `volumes(m, dets)`, `volumes(m)` | `Real.(abs.(dets))`; for 2-point elements edge lengths else `abs.(detsimplex(m))` | `composite.jl:932-933` |
| `detsimplex(m::Vector{<:Chain{V}})` | `det(m)/(mdims(V)-1)!` (signed simplex volume) | `composite.jl:934` |
| `mean(m)`, `barycenter(m)`, `centroid(m)` | `Σ/N`; `Σ`; `s = Σ; s/s[1]` (homogeneous normalisation) | `composite.jl:935-941` |
| `means/centroids/barycenters/curls(m,p)` | map over index lists `m` into point set `p` | `composite.jl:962-971` |
| `curl(m)`, `divergence(m)`, `gradient(m::TensorAlgebra)` | `V(∇)×m`, `∂(m)`, `d(m)` | `composite.jl:942-951` |
| `det(t::Chain{V,1,<:Chain})` | `!∧(t)` | `composite.jl:952` |
| `det(m::Vector{<:Chain})`, `∧(m::DenseVector{<:Chain})` | per-element wedge over point-index chains (mesh) | `composite.jl:953-961` |
| `area(m::Vector{<:Chain})` | shoelace via `Σ m_i∧m_{i+1}`, `abs(⋆S)/2` | `composite.jl:974-980` |
| `gradienthat` | **Cartan.jl** `src/element.jl:456-472` (FaceBundle/TensorField level: 1D `±1/length`, 2D `revrot` of `curls/2vol`, else `TensorOperator.(grad.(affinehull(t)))`); belongs in the Cartan port | — |

Goldens (`outputs/p17.txt`; `t` = points `(1,0,0),(1,1,0),(1,0,1)` in `Submanifold(3)`, Float):
`affineframe(t)` = identity 2×2 on `⟨_11⟩`; `∧(t) = 1.0v₁₂₃`; `det(t) = 1.0v`;
`inv(t) = (1.0v₁+0.0v₂+0.0v₃)v₁ + (-1.0v₁+1.0v₂-0.0v₃)v₂ + (-1.0v₁+0.0v₂+1.0v₃)v₃`;
`t\Chain(1.0,0.25,0.25) = 0.5v₁ + 0.25v₂ + 0.25v₃`; `(1,.25,.25) ∈ t = true`, `(1,.75,.75) ∈ t = false`;
`gradient(t) = (-1.0v₂-1.0v₃)v₁ + (1.0v₂-0.0v₃)v₂ + (0.0v₂+1.0v₃)v₃`; `mean(t) = 1.0v₁ + 0.333333v₂ + 0.333333v₃`;
`barycenter(t) = 3.0v₁ + 1.0v₂ + 1.0v₃`; `centroid(t) = 1.0v₁ + 0.333333v₂ + 0.333333v₃`;
`compound(t,2) = (1.0v₁₂+0.0v₁₃+0.0v₂₃)v₁₂ + (0.0v₁₂+1.0v₁₃+0.0v₂₃)v₁₃ + (-1.0v₁₂+1.0v₁₃+1.0v₂₃)v₂₃`;
`cofactor(t) = (1.0v₁-1.0v₂-1.0v₃)v₁ + (0.0v₁+1.0v₂+0.0v₃)v₂ + (0.0v₁-0.0v₂+1.0v₃)v₃`.
Docs (`dyadic-tensors.md`, verified): `T = Chain{V,1}(Chain(v1),v1+v2,v1+v3)` in ℝ3 →
`(barycenter(T) ∈ T, (v1+v2+v3) ∈ T) = (true, false)`, `T\barycenter(T) = inv(T)⋅barycenter(T) = 1.0v₁ + 1.0v₂ + 1.0v₃`,
`T:T = 5v`.
