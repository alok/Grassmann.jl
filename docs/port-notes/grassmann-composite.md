# Grassmann.jl `src/composite.jl` — Lean 4 porting spec

Source of truth: `/Users/alokbeniwal/chakravala/Grassmann.jl` at commit `4f79a7f` (Project version 0.8.47-dev).
`src/composite.jl` (1227 lines) is byte-identical to the registered v0.8.46 installed in the oracle env
(`git diff v0.8.46 HEAD` touches only `Project.toml` and `src/forms.jl`), so the Julia oracle env
`.../scratchpad/juliaenv` (Julia 1.13.0, Grassmann 0.8.46) reproduces this file exactly.
Every behaviour marked **[verified]** below was executed in that env; scripts live in
`.../scratchpad/comp/t*.jl` and the prototype oracle dumper is `.../scratchpad/comp/oracle_composite.jl`.

File references: `C:` = `Grassmann.jl/src/composite.jl`, `A:` = `Grassmann.jl/src/algebra.jl`,
`M:` = `Grassmann.jl/src/multivectors.jl`, `P:` = `Grassmann.jl/src/products.jl`, `F:` = `Grassmann.jl/src/forms.jl`,
`AT:` = `AbstractTensors.jl/src/AbstractTensors.jl`, `LZ:` = `Leibniz.jl/src/utilities.jl`.

---------------------------------------------------------------------------------------------------

## 1. Purpose & scope

`composite.jl` is the "transcendental / composite operations" layer of Grassmann. It sits on top of
the product kernels (`products.jl`, `parity.jl`), the element types (`multivectors.jl`) and `inv`/`^`
(`algebra.jl`), and is included just before `forms.jl` (`src/Grassmann.jl:51-56`). It provides:

1. **Exponential family** — `exp`, `expm1` for every element kind: closed forms when the (non-scalar part
   of the) argument squares to a scalar ("elliptic / parabolic / hyperbolic" by sign of the square),
   a special closed form for bivectors of the 3D PGA `⟨1,1,1,0⟩`, and a power series otherwise
   (`C:24-194`). `exph = cosh + sinh` (`C:572`).
2. **Logarithm family** — `log`, `log1p` via closed forms for `Couple` / Euclidean `Quaternion` /
   `Phasor`, otherwise the atanh series `log t = 2·atanh((t−1)/(t+1))` (`qlog`, `C:299-399`);
   Newton/Halley alternatives `log_fast`, `logh_fast` (`C:574-587`).
3. **Roots** — `sqrt`, `cbrt` via `exp(log(t)/n)` or polar/complex closed forms (`C:436-452`).
4. **Hyperbolic functions** — `cosh`, `sinh` power series (`C:456-570`). All circular/inverse trig
   functions come from identities in `AbstractTensors` (`AT:405-431`) that call these.
5. **Angles** — `angle`/`radius` for `Couple` and `Quaternion`; a 2-argument hyperbolic
   `atanh(y,x)` modelled on `atan(y,x)` (`C:619-705`).
6. **Matrix functions on Chain-of-Chain operators** — `exp` (1×1, 2×2 real, 2×2 complex closed
   forms; general Higham Padé scaling & squaring), `expm1`, `log` (via `LinearAlgebra.log(Matrix)`)
   (`C:196-297, 361`).
7. **Exterior-algebra linear algebra on lists of vectors** (`Values{M,Chain{V,1}}`, `Chain{V,1,Chain}`):
   Cramer's rule by prefix/suffix wedges (`\`), cone/simplex membership (`in`), `inv`, `invdet`,
   `adjugate`, `cofactor`, barycentric `gradient`, `compound` (k-th exterior power matrix), `det`,
   `pfaffian`, Vandermonde fitting (`C:707-895`).
8. **Mesh / simplex helpers** (`affineframe`, `mean`, `barycenter`, `centroid`, `area`, `volumes`,
   `detsimplex`, `array`, `submesh`, `find*`) — mostly consumed by Cartan.jl (`C:897-986`).
9. **Element-wise utilities** — `div/rem/mod/...`, `round/rad2deg/...`, `isfinite`, `rationalize`,
   `map`, `rand`, sparse-matrix × Chain products, static `_diff` (`C:988-1084`).
10. **Polynomial roots** — closed-form quadratic (stable), cubic (Cardano + Viète), quartic
    (Ferrari via resolvent cubic), companion-matrix eigenvalues for degree ≥ 5 (`C:1086-1226`).

It also *exports* the `pseudo*`/`co*` complement-conjugated function family defined in AbstractTensors
(`C:15-19`, definitions `AT:500-551`).

Cross-file material that composite.jl cannot be ported without (and that the task asked about) is
summarised in §4.17–§4.19: `inv`, `^`, `Couple`/`Phasor` helpers, `companion`, `characteristic`,
`eigvals*`, `eigen`, `cayley`, the trig identities and the pseudo/co family.

---------------------------------------------------------------------------------------------------

## 2. Public API inventory

### 2.1 Export statements in composite.jl

| line | names |
|---|---|
| `C:15` | `exph, log_fast, logh_fast, pseudoexp, pseudolog, pseudometric, pseudodot, @pseudo` |
| `C:16` | `pseudoabs, pseudoabs2, pseudosqrt, pseudocbrt, pseudoinv, pseudoscalar` |
| `C:17` | `pseudocos, pseudosin, pseudotan, pseudocosh, pseudosinh, pseudotanh` |
| `C:18` | `coabs, coabs2, cosqrt, cocbrt, coinv, coscalar, coexp, colog, cometric, codot, @co` |
| `C:19` | `cocos, cosin, cotan, cocosh, cosinh, cotanh` |
| `C:20` | `vandermonde, pfaffian, invdet, adjugate, cofactor, volumes, compound, companion` |
| `C:905` | `affineframe` (+ `const vectors = affineframe`, `C:906`, not exported) |
| `C:965` (loop `C:962-971`) | `mean, means, centroid, centroids, barycenter, barycenters, curl, curls` |
| `C:1092` | `roots, rootsreal, rootscomplex, monicroots, monicrootsreal, monicrootscomplex` |

**Dangling exports [verified]**: `coscalar` is defined nowhere in the ecosystem; `pseudodot` is a const
in AbstractTensors (`AT:314`) but never imported into `Grassmann`, so `Grassmann.pseudodot` →
`UndefVarError`. `companion` is defined in `F:829-835`. `pseudoscalar` comes from `AT:203` (only
`pseudoscalar(::Manifold)`); on a `Single` bivector it returns `Zero` [verified `pseudoscalar(v12) = 𝟎`].
In Lean: define `pseudodot := codot` and drop `coscalar` (or alias `coscalar t := complementleft (scalar (complementright t))`, flagged as new).

### 2.2 Methods (all Base/LinearAlgebra extensions and internal helpers)

Every function in `C:24-634` is generated twice by `for (op,field) ∈ ((:⟑,false),(:wedgedot_metric,true))`
(`C:24`, `C:299`): the second copy takes a trailing runtime metric argument `g` and uses
`wedgedot_metric(a,b,g)` / `abs2(t,g)` / `log_metric` instead of `⟑` / `abs2` / `log`. Each metric copy
starts with `indu`: `isinduced(g) && return f(t)` (`C:26`, `C:301`; `isinduced` at `F:1698-1704`:
true for `InducedMetric`, `TensorBundle`, non-basis `Submanifold`, false otherwise), i.e. "g equals the
algebra's own metric → ignore it". Below I list the `field=false` signature; assume a `(…, g)` twin
unless noted.

| Julia signature | semantics (details in §4) | unicode / ASCII | line |
|---|---|---|---|
| `expm1(t::Submanifold{V,0})` | `Single{V}(ℯ-1)` | | `C:27` |
| `expm1(t::TensorGraded{V,0})` | `Single(expm1(scalar value))` | | `C:28` |
| `expm1(t::Chain)` | `expm1(multispin(t))` | | `C:30` |
| `expm1(t::TensorAlgebra)` | generic power series (complex shortcut for elliptic `Couple`) | | `C:31-52` |
| `expm1(b::Multivector)`, `expm1(b::Spinor)` | `@generated` series, unrolled products | | `C:54-81` |
| `exp(t::Multivector)`, `exp(t::Spinor)` | closed form if `(t−⟨t⟩₀)²` scalar, else `1+expm1` | | `C:83-96` |
| `exp(t::Couple{V,B})` | closed form (sign of `B²`) | | `C:99-110` |
| `expm1(t::PseudoCouple)`, `exp(t::PseudoCouple)` | via `Couple{V,I}` if `B` scalar, else `multispin` | | `C:112-128` |
| `expm1(t::Phasor)`, `exp(t::Phasor{V,<:TensorGraded})` | see §4.2.6 (buggy) | | `C:130-134` |
| `exp(t::TensorGraded)` | zero/PGA/closed-form/series dispatch | | `C:136-159` |
| `exp(t::Multivector, ::Val{hint})` | closed form with caller-supplied sign of square | | `C:162-173` (no `g` twin) |
| `exp(t::TensorGraded, ::Val{hint})` | same for graded | | `C:182-194` (no `g` twin) |
| `isR301(V)` | `diagonalform(V) == (1,1,1,0)` for `DiagonalForm`, else false | | `C:175-177` |
| `unabs!(t)` | strip `abs(...)` from symbolic `Expr` (Julia-only) | | `C:179-180` |
| `expm1(A::Chain{V,G,<:Chain{V,G}})` | `exp(A) - I` | | `C:196` |
| `exp(A)` 1×1, 2×2 real, 2×2 complex, N×N | matrix exponential | | `C:197-297` |
| `qlog(w, x::Int=10000)` | `2·Σ_{k odd} w^k/k` (= `2 atanh w`) | | `C:302-322` |
| `qlog_fast(b::Multivector/Spinor, x)` | generated version (broken, dead code) | | `C:324-357` |
| `log(A::Chain-of-Chain)` | `Chain(log(Matrix(A)))` | | `C:361` |
| `log(t::TensorTerm)` | `log(Couple(t))` | | `C:362` |
| `log(t::Phasor)`, `log1p(t::Phasor)` | `log(amplitude)+angle`, `log(1+t)` | | `C:363-364` |
| `log(t::Couple)`, `log1p(t::Couple)` | complex log if `B²=−1`, else `log(radius)+angle` | | `C:365-366` |
| `log(t::Quaternion)`, `log1p(t::Quaternion)` | polar closed form if Euclidean, else `qlog` | | `C:367-368` |
| `log(t::TensorAlgebra)`, `log1p(t::TensorAlgebra)` | `qlog((t−1)/(t+1))`, `qlog(t/(t+2))` | | `C:369-370` |
| `log`, `log1p` on `PseudoCouple` | via `Couple{V,I}` or `multispin` | | `C:373-390` |
| `exp/expm1/log/log1p/log_fast/logh_fast(::CoSpinor)` | convert to `Multivector` | | `C:392-399` |
| `cosh/sinh(::PseudoCouple)`, `(::CoSpinor)` | `multispin` / `Multivector` | | `C:400-405` |
| `log, exp, asin, acos, atan, acot, sinc, cosc` on `TensorGraded{V,0}` | scalar function on the coefficient | | `C:407-409` |
| special values `One/Zero/Infinity` | table §4.20 | | `C:411-434` |
| `sqrt`, `cbrt` (`TensorAlgebra`, `Quaternion`, `Couple`, `Phasor`, scalar) | §4.5 | `√` = `sqrt` (`AT:626`) | `C:436-452` |
| `cosh`, `sinh` (scalar, generic, generated) | power series | | `C:456-570` |
| `exph(t)` | `cosh(t)+sinh(t)` | | `C:572` |
| `log_fast(t)`, `logh_fast(t)` | Halley/Newton iteration on `exp` resp. `exph` | | `C:574-587` |
| `angle(z::Couple)` | `atan(im,re)·B` (B²=−1), `atanh(im,re)·B` (B²=+1), else `error` | | `C:619-627` |
| `radius(z::Quaternion)` | `value(scalar(abs(z)))` | | `C:629` |
| `angle(z::Quaternion, r=radius(z))` | `(acos(⟨z⟩₀/r)/|⟨z⟩₂|)·⟨z⟩₂` | | `C:630-633` |
| `atanh(y::Real,x::Real)` | promote-float then 2-arg atanh | | `C:636-705` |
| `Cramer(N,j=0)` | code generator for prefix/suffix wedges | | `C:707-712` |
| `DirectSum.Λ(x::Chain{V,1,<:Chain{W,1}},G)` | `compound(x,G)` | `Λ` | `C:714` |
| `compound(x,G)` / `compound(x,Val(G))` | G-th compound (exterior power) matrix | | `C:715-720` |
| `\(t::Values{M,Chain{V,1}}, v::Chain{V,1})` | Cramer solve / least squares | `\` (ldiv) | `C:722-732` |
| `in(v::Chain{V,1}, t::Values{N,Chain{V,1}})` | cone / simplex membership | `∈` | `C:734-747` |
| `_inv(M,N)` | generator for inverse numerators | | `C:749-759` |
| `inv(t::Values{M,Chain{V,1}})` | inverse / reciprocal frame / pseudo-inverse | `⁻¹` postfix (`AT:575-578`) | `C:761-772` |
| `invdet(t)` | `(inv(t), det)` | | `C:774-785` |
| `adjugate(t)` | classical adjugate (transposed cofactor) | | `C:796-803` |
| `cofactor(t)` | cofactor matrix | | `C:805-812` |
| `gradient(T::Values{M,Chain{V,1}})` | barycentric gradients of a simplex | `grad` (`C:972`) | `C:814-831` |
| `\(t::Values{N,Chain{M,1}}, v::Chain{V,1})` (mixed spaces) | least squares | | `C:833-840` |
| `inv_approx(t)` | `(tᵀt)⁻¹tᵀ` or `tᵀ(ttᵀ)⁻¹` | | `C:841-844` |
| `\(v::Chain-of-Chain, ::UniformScaling)` = `inv(v)`; `\(I, v)` = `v` | | | `C:846-847` |
| `\(t::Chain-of-Chain, v::Chain-of-Chain)` = `inv(t)*v`; `\(t, v::Chain{V,1})` = `value(t)\v` | | | `C:848-849` |
| `in`, `inv`, `invdet`, `adjugate`, `cofactor`, `gradient` on `Chain{V,1,<:Chain}` | unwrap to `Values` | | `C:850-856` |
| `approx(x, y)` | polynomial evaluation `Σ y_i x^(i-1)` | | `C:858-860` |
| `vandermonde(x::Array,y::Array,N)` / `(x::Array,N)` / `(x,y,V)` / `(x,V)` | Vandermonde matrix / LSQ fit | | `C:862-875` |
| `polynom(x, Val(N))` | `Chain(1, x, …, x^(N−1))` | | `C:875` |
| `vandermondeinterp(x,y,V,grid)` | fit + dense resample | | `C:877-885` |
| `pfaffian(ω::Bivector)`, `pfaffian(A::Quaternion)` | `!(ω^∧n)/n!` | | `C:887-895` |
| `list(a,b)`, `evens(a,b)` | static integer ranges | | `C:897-898` |
| `affineframe(x, y=x[1])` | edge vectors `↓(x_i − y)` as operator | | `C:899-904` |
| `signscalar(x)` | "is a non-negative scalar" predicate | | `C:909-914` |
| `ands(x)` | build `x1 && x2 && …` Expr | | `C:915` |
| `findfirst/findlast/findall(P, t::AbstractVector{<:Chain{V,1,<:Chain}})` | point location in simplex list; returns `0` if none | | `C:917-929` |
| `edgelength`, `volumes`, `detsimplex`, `mean`, `barycenter`, `centroid` | mesh helpers | | `C:931-941` |
| `gradient(m::TensorAlgebra)=d(m)`, `curl`, `divergence`, `Base.div(m)` (1-arg) | differential operators (Leibniz `d`, `∂`, `∇`) | `grad` | `C:942-951` |
| `det(t::Chain{V,1,<:Chain})` | `!∧(t)` | | `C:952` |
| `det(m::Vector{<:Chain})`, `∧(m::DenseVector{<:Chain})` | per-simplex volumes (needs Cartan `points`) | | `C:953-961` |
| `means/centroids/barycenters/curls(m,p)` | `op.(getindex.(Ref(p),m))` | | `C:962-971` |
| `area(m::Vector{<:Chain})` | shoelace area | | `C:974-980` |
| `array(m)`, `submesh(m)`, stubs `array!`, `submesh!` | point list → matrix | | `C:982-986` |
| `div, rem, mod, mod1, fld, fld1, cld, ldexp` (`a, m`) | element-wise | | `C:988-997` |
| `mod2pi, rem2pi, rad2deg, deg2rad, round` (kwargs) | element-wise | | `C:998-1007` |
| `isfinite`, `rationalize` | element-wise | | `C:1008-1020` |
| `*(::SparseMatrixCSC, ::StridedVector{Chain})` etc. | Julia sparse interop (skip) | | `C:1022-1035` |
| `AbstractTensors._diff(Val(N), a::Values{Q,<:Chain}, Val(1))` | forward differences | | `C:1037-1050` |
| `map(fn, x)` | coefficient-wise map | | `C:1052-1058` |
| `rand(::SamplerType{…})` | random elements | | `C:1060-1084` |
| `zero!`, `subzero`, `subsqrt`, `subsqrtcomplex` | numeric guards | | `C:1086-1090` |
| `roots`, `rootsreal`, `rootscomplex` | roots of `a0 + a1 z + … + an z^n` | | `C:1094-1110` |
| `monicroots`, `monicrootsreal`, `monicrootscomplex` | roots of monic `a0 + … + a_{n-1}z^{n-1} + z^n` | | `C:1112-1226` |
| `quadratic(a0,a1,rt)` | stable quadratic formula | | `C:1120-1126` |
| `cubicmax(a0,a1,a2)` | largest real root of monic cubic | | `C:1154-1172` |
| `quartic(a0,a1,a2,a3)` | Ferrari factorisation data | | `C:1173-1181` |

The `pseudo*`/`co*` family and trig identities are in §4.18/§4.19.

---------------------------------------------------------------------------------------------------

## 3. Data representations used by composite.jl

(Full spec of these types belongs to the multivectors/DirectSum reports; here is what composite relies on.)

| type | params (compile-time) | runtime fields | storage order |
|---|---|---|---|
| `Submanifold{V,G,B}` | signature `V`, grade `G`, blade bitmask `B` | none (singleton); `value` = 1 | — |
| `Single{V,G,B,T}` | `V,G,B`, scalar type `T` | `v::T` coefficient | — |
| `Chain{V,G,T,N}` | `V`, grade `G`, `N = binomial(n,G)` | `v::Values{N,T}` | grade-`G` blades in `indexbasis(n,G)` order = lexicographic index tuples: 3D grade 2 = `v12,v13,v23`; 4D grade 2 = `v12,v13,v14,v23,v24,v34` [verified via `Λ(V).b`] |
| `Multivector{V,T,2^n}` | `V` | `v::Values{2^n,T}` | grade blocks 0,1,…,n, each in `indexbasis` order: 3D = `[1,v1,v2,v3,v12,v13,v23,v123]` |
| `Spinor{V,T,2^(n-1)}` (= `Quaternion` when 4 components, `M:972`) | `V` | `v::Values` | even grades 0,2,4,… concatenated: 3D = `[1,v12,v13,v23]` |
| `CoSpinor{V,T,2^(n-1)}` (`AntiSpinor`) | `V` | `v::Values` | odd grades 1,3,…: 3D = `[v1,v2,v3,v123]` |
| `Couple{V,B,T}` (`M:656`) | `V`, blade `B` | `v::Values{2,T}` = `[re, im]` meaning `re + im·B` | — |
| `PseudoCouple{V,B,T}` (`M:677`) | `V`, blade `B` | `[re, im]` meaning `re·B + im·I` (`I` = pseudoscalar) | — |
| `Phasor{V,B,T}` (`M:852`) | `V`, *type* of angle `B` | `v::T` amplitude, `ω::B` angle (usually a `Single` bivector, may be `Real`) | meaning `v·exp(ω)` |
| `Zero{V}`, `One{V}` (=`Submanifold{V,0}`), `Infinity{V}` | `V` | none | printed `𝟎`, `v`, `∞` |
| matrix: `Chain{V,1,Chain{W,1,T,M},N}` (`Simplex`, `M:94`); `TensorOperator{V,W,…}` wraps one (`F:555`) | `V` = column-index space (N = mdims V), `W` = row space | `N` columns, each a `Chain{W,1}` of length M | **column-major**: `A[j][i] = Matrix(A)[i,j]` [verified `Matrix(Chain(Chain(1,3),Chain(2,4))) = [1 2; 3 4]`] |
| point/vector lists: `Values{M,Chain{V,1}}` | `M`, `V` | `M` column vectors | same as a matrix with `M` columns |

Key invariants / conventions:

* **Compile-time**: `V` (dimension n, metric sign bitmask, degenerate/conformal flags, diff vars), `G`, `B`,
  lengths `N`, operator shapes. The sign of `B⟑B` for a blade is therefore a compile-time constant; Julia
  still evaluates it at runtime (`value(B⟑B)`) but it constant-folds.
* **Runtime**: coefficients (Float64 in practice; Int/Rational/Complex/symbolic also flow through), the
  metric argument `g` of the `_metric` twins, series iteration counts, all branch decisions that depend on
  values (`isscalar(sq)`, `hint` for `Chain`/`Multivector`, Padé degree, etc.).
* `norm(t)` is **always the Euclidean 2-norm of the stored coefficient vector** (`AT:444`), not the metric
  norm: `norm(v12)=1`, `norm(2v12)=2`, `norm(Couple(3,4))=5` [verified].
* `isscalar(t) = norm(t) ≈ norm(scalar(t))` (`M:1140`) uses Julia's `≈` (rtol = √eps ≈ 1.49e-8, atol 0):
  an element whose non-scalar part is ≤ ~1.73e-4 of its scalar part **counts as scalar**
  [verified: `1 + 1e-4 v12` → true, `1 + 2e-4 v12` → false].
* Julia `x ≈ y` for Floats: `x == y || (isfinite(x) && isfinite(y) && |x−y| ≤ √eps·max(|x|,|y|))`.
  Consequence: `x ≈ 0` is true **only** when `x == 0` (so `zero!` below is a no-op except `-0.0 → 0.0`).
  `isapprox` on two `TensorAlgebra`s is `norm(a−b) ≤ √eps·max(norm a, norm b)` with finiteness checks (`AT:229-240`).
* `isnull(x) = iszero(x)` for numbers (`AT:592`): exact zero test.
* `a / b` for tensors is **right** division `a ⟑ inv(b)`; `a \ b = inv(a) ⟑ b` (`AT:320-325`).
* `~t` is reversion; `abs2(t) = ~t ⟑ t` (collapsed to its scalar if scalar) for mixed types (`AT:437`),
  `contraction(t,t)` for graded types (`AT:439`); `abs = sqrt ∘ abs2` (`AT:435`).
* `multispin(t)` (`M:999-1014`): `Chain` of even grade → `Spinor`, odd → `CoSpinor`; `Couple` with even
  `B` → `Spinor`, else `Multivector`; `PseudoCouple`: `Spinor` if n and grade(B) both even, `CoSpinor` if
  both odd, else `Multivector`.

---------------------------------------------------------------------------------------------------

## 4. Algorithms

Notation: `⟑` geometric product, `s = ⟨t⟩₀`, `‖·‖` Euclidean coefficient norm, `≈` Julia default,
`I` pseudoscalar (`V(I)` = `Submanifold(V)`), `One(V)` = 1.

### 4.1 Termination heuristics shared by all series (read this first)

Every power series in this file (expm1, cosh, sinh, qlog) uses the same rule with a 3-slot state
`norms = (previous term norm, current term norm, previous partial-sum norm)`:

```
loop while (norms[2] < norms[1] || norms[2] > 1)   [ && k ≤ cap ]
    S += term
    ns = ‖S‖
    if ns ≈ norms[3] then break        # partial-sum NORM stopped changing (rtol √eps)
    term = next(term, k)
    norms = (norms[2], ‖term‖, ns)
    k += step
```

Consequences to replicate exactly (they are observable in the oracle):
* The loop exits **without adding** the current term if the term norm is non-decreasing and ≤ 1.
* The stopping test compares *norms of partial sums*, so accuracy is ~1e-8…1e-12 relative, not 1 ulp
  [verified: `expm1(Spinor(0.3v12+0.2v13+0.4v23))` bivector coefficient `0.28570880412104` vs exact
  `0.2857088041056532`; `exp(x)*exp(−x) − 1` in 6D has norm 4.7e-11; `log1p(One)` = `0.6931471795482411`].
* The generic (non-generated) variants have **no iteration cap**; the `@generated` Multivector/Spinor
  variants cap at `k ≤ 10000`; `qlog` caps at `k ≤ x` (default 10000).
* The generated variants initialise `norms[3] = ‖term‖ = 0` (term buffer is zeros), the generic ones
  initialise `norms[3] = f`. **Bug-compatible edge case [verified]**: `expm1(Spinor(−2.0))` returns `0`
  because `S = −2 + 2 = 0` after the first addition and `0 ≈ 0` breaks the loop.

### 4.2 `exp` / `expm1`

#### 4.2.1 `exp(t::TensorGraded)` — `Single`, `Submanifold`, `Chain` (`C:136-159`)

```
exp(t):
  S = t is Submanifold; B = t is TensorTerm (Single/Submanifold); V = Manifold(t)
  if B and isnull(t):                     # zero single term
      return Couple{V, basis(t)}(1, 0)
  elif (not field) and isR301(V) and grade(t) == 2:      # 3D PGA bivector, see 4.2.5
      ...
  i = B ? basis(t) : t
  sq = i ⟑ i
  if isscalar(sq):                        # approx-scalar test, §3
      hint = value(scalar(sq))
      if isnull(hint): return One(V) + t                 # nilpotent: 1 + t
      if grade(t) == 0: return Single{V}(exp(scalar value))
      θ = sqrt(|value(scalar(abs2(t)))|)                 # abs2 = contraction(t,t) (metric-signed)
      if hint < 0: return cos θ + t ⟑ (S ? sin θ : sin θ / θ)
      else:        return cosh θ + t ⟑ (S ? sinh θ : sinh θ / θ)
  else:
      return One(V) + expm1(t)            # expm1(Chain) = expm1(multispin(t)) → generated series
```
* For a `Single` `c·B`, `sq = B⟑B ∈ {−1,0,+1}` (a compile-time constant), `θ = |c|·sqrt(|B·B|)`; result
  type `Couple{V,B}`: `exp(cB) = cos|c| + sign(c) sin|c|·B` (elliptic) etc. For `Submanifold` `θ = 1` and the
  divisor is skipped (identical value).
* For a `Chain`, `hint` is the (runtime) scalar part of `t⟑t` — e.g. a Euclidean vector has `hint=|v|²>0`
  → `cosh`; a 3D bivector has `hint = −|B|²` → `cos`; a Minkowski null vector has `hint = 0` → `1+t`
  [verified `exp(0.4v1+0.4v2)` in `⟨-+++⟩` = `1.0 + 0.4v₁ + 0.4v₂`]. Output type = scalar + Chain:
  `Spinor` for even grade, `Multivector` for odd grade (e.g. `exp(0.3v1+0.4v2)` → `Multivector` `1.12763 + 0.312657v₁ + 0.416876v₂`).
* **Near-scalar squares are treated as scalar** (`isscalar` tolerance): e.g. a 4D bivector whose `B∧B`
  part is < ~1.7e-4 of `|B|²` uses the closed form and silently drops the `B∧B` contribution.
* Zero `Chain` (not a TensorTerm): goes to `hint=0` branch → `1 + t` (a `Multivector`/`Spinor` equal to 1).

#### 4.2.2 `exp(t::Couple{V,B})` (`C:99-110`)

```
st = scalar(t); mt = imaginary(t)            # mt = Single{V,grade B,B}(im)
if isscalar(B⟑B):                            # always true for diagonal metrics
    hint = value(scalar(B⟑B))                # ∈ {−1,0,+1}
    if isnull(hint): return exp(re)·(One + t)      # BUG: should be exp(re)(1 + mt)
    θ = sqrt(|scalar(abs2(mt))|) = |im|·sqrt(|B·B|)
    return exp(re)·( hint<0 ? cos θ + mt⟑(sin θ/θ) : cosh θ + mt⟑(sinh θ/θ) )
else: return One + expm1(t)
```
* **θ = 0 (im = 0) gives `sin 0/0 = NaN`** [verified `exp(Couple(1.0,0.0,v12)) = 2.718281828459045 + NaN*v₁₂`].
* **Parabolic bug** [verified in `D"1,1,1,0"`: `exp(1.0+0.5v14) = 5.43656365691809 + 1.3591409142295225v₁₄` = `e·(2 + 0.5v14)`; correct is `e·(1+0.5v14)`].
* Elliptic values [verified]: `exp(1.0+2.0v12) = -1.1312043837568135 + 2.4717266720048188v₁₂` (= complex exp).

#### 4.2.3 `exp(t::Multivector)`, `exp(t::Spinor)` (`C:83-96`) and `Val{hint}` variants (`C:162-194`)

```
st = scalar(t); mt = t − st; sq = mt ⟑ mt
if isscalar(sq):
    hint = value(scalar(sq))
    if isnull(hint): return exp(s)·(One + t)          # BUG: uses t, not mt
    θ = sqrt(|value(scalar(abs2(mt)))|)               # abs2 = ~mt⟑mt, scalar part
    return exp(s)·( hint<0 ? cos θ + mt⟑(sin θ/θ) : cosh θ + mt⟑(sinh θ/θ) )
else: return One + expm1(t)                           # series on the FULL t (scalar not factored out)
```
* **Pure-scalar multivector bug [verified]**: `exp(Multivector(2.0)) = 22.1672` (= 3e²) and
  `exp(Spinor(−2.0))` = `−e^{−2}`; `exp(Spinor(0))` = 1 (correct by luck).
* `Val{hint}` variants skip the zero-`Single` and PGA branches and take `hint` from the type parameter but
  still require `isscalar(sq)`; no metric twin.
* Result type equals input type (`Multivector` stays `Multivector` even if the result is even).

#### 4.2.4 Series `expm1` (`C:31-52` generic, `C:54-81` generated)

Generic (`TensorAlgebra` not otherwise covered — `Single` through `expm1`, non-elliptic `Couple`,
`TensorNested` …):
```
if t is Couple and value(B⟑B) == −1: return Couple{V,B}(expm1(Complex(t)))
S = t; term = (t⟑t)/2; f = ‖t‖; norms = (f, ‖term‖, f); k = 3
loop (rule 4.1, no cap):  S += term; …; term = term ⟑ (t/k); …; k += 1
return S
```
Generated for `Multivector`/`Spinor` (identical math, different buffers):
```
B = value(b); sb = scalar(b); nb = ‖B‖
if sb ≈ nb: return Single{V}(expm1(value(sb)))       # only fires for POSITIVE pure scalars
S = B; out = value(b⟑b)/2; term = 0; norms = (nb, ‖out‖, 0); k = 3
loop (rule 4.1, cap k ≤ 10000):
    S += out; ns = ‖S‖; ns ≈ norms[3] && break
    term = out; out = (term / k) ⟑ B      # each LEFT coefficient divided by k before multiplying
    norms = (norms[2], ‖out‖, ns); k += 1
return Multivector{V}(S) / Spinor{V}(S)
```
* The product inside the loop is `generate_loop_multivector`/`generate_loop_spinor`
  (`A:1838-1889`) called with divisor `d = k`: for `mdims(V) < 6` (`cache_limit/2`, `LZ:94`) it is a fully
  unrolled straight-line expression computing every output coefficient as a sum of `(a[i]/d)*b[j]`
  with signs from `derive_pre`; for `n ≥ 6` it loops over nonzero left coefficients and accumulates with
  `geomaddmulti!`/`geomaddspin!`. Output: `Values` of length 2^n (Multivector) or 2^(n−1) (Spinor).
* Rounding noise from the `(a[i]/k)·b[j]` order produces `~1e-19…1e-21` coefficients on blades that cancel
  in exact arithmetic [verified: `exp(v1+2v12)` 3D, `expm1(Chain(0.3v1+0.4v2))` has `1.70068e-21v₁₂`].
* `expm1(t::Chain) = expm1(multispin(t))`; `CoSpinor` → `Multivector` (`C:394`); `PseudoCouple` → see 4.2.6.
* `expm1(Submanifold{V,0}) = Single(ℯ−1)`; `expm1(TensorGraded{V,0}) = Single(expm1(coef))`.

#### 4.2.5 3D PGA bivector closed form (`C:142-147`)

Guard: `!field && isR301(V) && grade(t) == 2`, where `isR301` is true only for a `DiagonalForm` whose
diagonal is exactly `(1,1,1,0)` (`D"1,1,1,0"`); `S"+++0"` is **not** R301 [verified: `isR301(S"+++0")=false`].
```
u = sqrt(|abs2(t)[1]|)                  # Euclidean part norm  (abs2 of a Chain is Chain{V,0}; [1] = its value)
if u < 1e-5: return One + t
v  = (t∧t) ⟑ (−0.5/u)                   # pseudoscalar-valued (grade 4)
cu, su = cos u, sin u
return (cu − v⟑su) + ((su + v⟑cu) ⟑ t) ⟑ (1/u − v/(u·u))
```
Derivation: with `I² = 0`, `t² = −(u + vI)²`, so `exp t = cos(u+vI) + sin(u+vI)·t/(u+vI)` and
`(u+vI)⁻¹ = 1/u − vI/u²`. Works for `Chain` input [verified `exp(0.3v12+0.4v34)` in `⟨1,1,1,0⟩` =
`0.955336 + 0.29552v₁₂ + 0.382135v₃₄ + 0.118208v₁₂₃₄` (Spinor)]. **Bug [verified]**: for a `Single` blade
`abs2(t)[1]` is a `Single` scalar, so `cos/sin(u)` go through the pseudoscalar trig identity with `I²=0` →
`exp(0.3v12) = 1.0 + NaN*v₁₂`. Port the math with `u : Float`.

#### 4.2.6 `PseudoCouple`, `Phasor`, `CoSpinor`

* `exp(t::PseudoCouple{V,B})` (`C:120-128`): if `B` is the scalar blade (`isscalar(B)`, i.e. `t = a + bI`) →
  `out = exp(Couple{V,I}(re,im))`, return `PseudoCouple{V,B}(re(out), im(out))`; otherwise
  `exp(multispin(t))` [verified `exp(1.0v+2.0v₁₂₃)` in 3D = `-1.1312043837568135v + 2.4717266720048188v₁₂₃`;
  `exp(1.0v₃ + 2.0v₁₂₃)` = Multivector `-0.642148 - 0.489056v₃ + 1.06861v₁₂ + 1.40312v₁₂₃`].
  `expm1(PseudoCouple)` = `exp(t) − One` if `B` scalar else `expm1(multispin(t))` (`C:112-119`).
* `exp(t::Phasor{V,<:TensorGraded})` (`C:131-134`): `z = exp(angle(t))` (a Couple);
  `Phasor{V}(exp(amplitude(t) + realvalue(z)), imagvalue(z))`. **This is mathematically wrong**
  (`exp(r e^{Bθ}) = e^{r cos θ} ∠ (r sin θ)B`); Julia returns a Phasor with a *real* angle
  [verified `exp(2.0∠0.5v₁₂) = 17.77126028818127 ∠ 0.479425538604203`]. `expm1(Phasor) = exp(t) − One`
  [verified garbage `27.703185237564256v`].
* `exp/expm1/log/log1p/log_fast/logh_fast(::CoSpinor)` convert to `Multivector` (`C:392-399`).

#### 4.2.7 Matrix exponential on Chain-of-Chain (`C:196-297`)

Indexing (column-major): `a = A[1][1] = M11`, `c = A[1][2] = M21`, `b = A[2][1] = M12`, `d = A[2][2] = M22`.

* 1×1 (`C:197`): `Chain{V,G}(Values(Chain{V,G}(exp(A[1][1]))))`.
* 2×2 real (`C:199-224`, from StaticArrays):
  ```
  v = (a−d)² + 4bc
  v>0: z=√v,  z1=cosh(z/2), z2=sinh(z/2)/z
  v<0: z=√−v, z1=cos(z/2),  z2=sin(z/2)/z
  v=0: z1=1, z2=1/2          # Julia: T(1.0) with T a tensor type → HANGS [verified]; port as 1, 0.5
  r = exp((a+d)/2)
  M11 = r(z1+(a−d)z2); M12 = 2r·b·z2; M21 = 2r·c·z2; M22 = r(z1−(a−d)z2)
  return columns (M11,M21), (M12,M22)
  ```
* 2×2 complex (`C:226-242`):
  ```
  z = sqrt((a−d)² + 4bc)                         # complex sqrt
  e = expm1((a+d−z)/2); f = expm1((a+d+z)/2)
  g = |z|² < eps()² ? exp((a+d)/2)·(1 + z²/24) : (f−e)/z
  M11 = (g(a−d)+f+e)/2 + 1; M12 = g b; M21 = g c; M22 = (−g(a−d)+f+e)/2 + 1
  ```
* N×N general (`C:246-297`), Higham 2008 without balancing; `S` = float type of `T`;
  `nA = max over columns of Σ|entries|` (1-norm).
  * `nA ≤ 2.1`: `A2 = A·A`; choose by `nA`:
    * `> 0.95` (degree 9): `U = A·(8821612800 I + A2(302702400 I + A2(2162160 I + A2(3960 I + A2))))`,
      `V = 17643225600 I + A2(2075673600 I + A2(30270240 I + A2(110880 I + 90 A2)))`
    * `> 0.25` (degree 7): `U = A·(8648640 I + A2(277200 I + A2(1512 I + A2)))`, `V = 17297280 I + A2(1995840 I + A2(25200 I + 56 A2))`
    * `> 0.015` (degree 5): `U = A·(15120 I + A2(420 I + A2))`, `V = 30240 I + A2(3360 I + 30 A2)`
    * else (degree 3): `U = A·(60 I + A2)`, `V = 120 I + 12 A2`
    * `expA = (V − U) \ (V + U)`
  * else: `s = log2(nA/5.4)`; if `s > 0`: `si = ceil(Int, s)`, `A = A / 2^si`. `A2=A·A, A4=A2·A2, A6=A2·A4`;
    `U = A·( A6(A6 + 16380 A4 + 40840800 A2) + (33522128640 A6 + 10559470521600 A4 + 1187353796428800 A2) + 32382376266240000 I )`;
    `V = A6(182 A6 + 960960 A4 + 1323241920 A2) + (670442572800 A6 + 129060195264000 A4 + 7771770303897600 A2) + 64764752532480000 I`;
    `expA = (V−U)\(V+U)`; if `s > 0` square `si` times.
  * `\` here is `inv(V−U)*(V+U)` with the Cramer inverse of §4.11 (`C:848`), `*` is matrix product
    [verified `Matrix(A*A) == Matrix(A)^2`]. Relative error vs `Base.exp` ≈ 1e-16…2e-15 over norms 0.001–20 [verified].
* `expm1(A) = exp(A) − I` (`C:196`). `exp(TensorOperator)` wraps (`F:610-612`); `exp(Proj)`,
  `exp(SpectralOperator)` = `map(exp, λ)` (`F:401-413`); `DiagonalOperator` maps element-wise (`F:532-537`).

### 4.3 `log` / `log1p`

#### 4.3.1 Dispatch (`C:360-399`)

```
log(A::Chain-of-Chain)   = Chain{V,G,Chain{V,G}}(LinearAlgebra.log(Matrix(A)))   # MethodError if the log is complex [verified]
log(t::TensorTerm)       = log(Couple(t))        # Single{V,0}(c) → Couple{V,I}(c,0): scalar log through the PSEUDOSCALAR
log(t::Phasor)           = log(amplitude(t)) + angle(t)
log1p(t::Phasor)         = log(One + t)
log(t::Couple{V,B})      = value(B⟑B) == −1 ? Couple{V,B}(log(Complex(t))) : log(radius(t)) + angle(t)
log1p(t::Couple{V,B})    = value(B⟑B) == −1 ? Couple{V,B}(log1p(Complex(t))) : log(One + t)
log(t::Quaternion{V})    = iszero(metric(V)) ? log(r) + angle(t, r) (r = radius(t)) : qlog((t−1)/(t+1))
log1p(t::Quaternion{V})  = iszero(metric(V)) ? log(One + t) : qlog(t/(t+2))
log(t::TensorAlgebra)    = qlog((t − One)/(t + One))
log1p(t::TensorAlgebra)  = qlog(t/(t + 2))
log(t::PseudoCouple{V,B}) = isscalar(B) ? via Couple{V,I} : log(multispin(t))      (C:373-381)
log1p(t::PseudoCouple)    = same pattern                                           (C:382-390)
log / exp / asin / acos / atan / acot / sinc / cosc on TensorGraded{V,0} = Single{V}(f(coef))   (C:407-409)
```
`metric(V)` is the negative-sign bitmask (DirectSum `generic.jl:20`), so `iszero(metric(V))` ⇔ no
negative basis vectors (degenerate/zero diagonals are *not* negative).

Observed consequences [verified]:
* `log(2.0v)` in 3D = `0.6931471805599453 + 0.0v₁₂₃` (Couple with the pseudoscalar), `log(−2.0v)` =
  `0.6931471805599453 + 3.141592653589793v₁₂₃`; in 4D Euclidean (`I²=+1`) `log(−2.0v)` =
  `0.6931471805599453 + 0.0v₁₂₃₄` (sign lost).
* `log(0.5v12)` 3D = `-0.6931471805599453 + 1.5707963267948966v₁₂`; `log(0.5v1)` 3D → `DomainError`
  (hyperbolic radius `sqrt(0 − 0.25)`).
* Euclidean quaternion with zero bivector → `NaN` bivector (`0/0` in `angle`): `log(Q(2,0,0,0))` =
  `0.693147 + NaN*v₁₂ + NaN*v₁₃ + NaN*v₂₃`; `log(Q(−1,0,0,0))` returns a `Chain` of NaN (log 1 = 0.0 exactly
  and `0.0 + Chain` stays a Chain).
* General `Multivector` / `CoSpinor` / `PseudoCouple` with non-scalar `B`: `(t−1)/(t+1)` needs
  `inv(t+1)` which only exists when `~m⟑m` is scalar or a single grade (`A:486-496`), else
  `error("inv(...) is undefined")` [verified `log(Multivector(1+0.3v1+0.2v12+0.1v123))`, `log(0.3v1+0.4v2)`].
* `log(b::Real, t::TensorAlgebra)` is **shadowed** by `log(t::Real, g::TensorAlgebra) = log(t)` (`AT:401`),
  so `log(2.0, x) == log(2.0)` [verified]; intended `log(t)/log(b)` (`AT:330`).
* `log2(t) = log2(ℯ)·log(t)`, `log10(t) = log10(ℯ)·log(t)`, `exp2(t) = exp(log(2)·t)`,
  `exp10(t) = exp(log(10)·t)` (`AT:381-385`).

#### 4.3.2 `qlog` — atanh series (`C:302-322`)

```
qlog(w, x=10000):                    # returns 2·atanh(w) = 2(w + w³/3 + w⁵/5 + …)
  w2 = w⟑w; f = ‖w‖; prod = w⟑w2
  S = w; term = prod/3; norms = (f, ‖term‖, f); k = 5
  while (norms[2] < norms[1] || norms[2] > 1) && k ≤ x:
      S += term; ns = ‖S‖; ns ≈ norms[3] && break
      prod = prod ⟑ w2               # NOTE: plain ⟑ even in the metric twin
      term = prod / k
      norms = (norms[2], ‖term‖, ns); k += 2
  return 2S
```
`qlog(b::PseudoCouple) = qlog(multispin(b))`, `qlog(b::CoSpinor) = qlog(Multivector(b))`.
Convergence is geometric in ‖w‖; for pure-imaginary `t`, `|(t−1)/(t+1)| = 1` and the series is at the
boundary → poor accuracy [verified `sqrt(Chain(0.3v12+0.4v23))` = `0.499978 + 0.300023v₁₂ + … + 0.400031v₂₃`,
exact `0.5 + 0.3v12 + 0.4v23`, error 4e-5]. For hyperbolic Couples the result is the correct idempotent
decomposition [verified `qlog(Couple{v1}(0.5,0.1)) = 1.1167961042822967 + 0.2694982438951282v₁` =
`(2atanh .6 ± 2atanh .4)/2`].

`qlog_fast` (`C:324-357`): generated twin of `qlog` for `Multivector`/`Spinor` — **broken** (`$pinor`,
`$op` interpolated at the wrong quote level → `UndefVarError: pinor`), unused. Port only if useful.

#### 4.3.3 `log_fast`, `logh_fast` (`C:574-587`)

```
logfast(t) with expf ∈ {exp (log_fast), exph (logh_fast)}:
  term = Zero(V); nrm = (0.0, 0.0)
  loop forever:
      en = expf(term)
      term -= (2(en − t)) / (en + t)            # Halley step for exp(y) = t; right division
      nrm = (nrm[2], ‖term‖)
      if nrm[1] ≈ nrm[2]: break                 # consecutive ITERATE norms agree
  return term
```
No iteration cap: **infinite loop** for hyperbolic `Couple`s with `|im| ≥ |re|` or `re < 0` and other
inputs without a log [verified hangs for `Couple{⟨11⟩,v1}(−0.034,−0.454)` etc.]. The break tests the
*norm* of the iterate, so it can stop on a wrong answer with the right norm. `logh_fast` uses
`exph = cosh + sinh` which is broken for Multivector/Spinor (§4.6). For `t = 1` it returns `Zero`.
Values [verified]: `log_fast(exp(0.5v12)) = -1.3515494402519288e-16 + 0.5v₁₂`,
`logh_fast(...) = -1.11102447327775e-17 + 0.5v₁₂`.

#### 4.3.4 `angle`, `radius`, 2-arg `atanh`

* `angle(z::Couple{V,B})` (`C:619-627`): `B⟑B == −1` → `atan(im, re)·B`; `== +1` → `atanh(im, re)·B`;
  otherwise `error("Unsupported trigonometric angle")` (degenerate blades).
* `radius(z::Couple{V,B}) = sqrt(re² − im²·value(B⟑B))` (`M:912`) → DomainError when negative.
* `radius(z::Quaternion) = value(scalar(abs(z)))` (`C:629`); `angle(z::Quaternion, r)` =
  `(acos(⟨z⟩₀/r) / value(abs(⟨z⟩₂))) · ⟨z⟩₂` (`C:630-633`).
* `atanh(y, x)` (`C:636-705`), adapted from `atan(y,x)` — effectively `sign(y)·atanh(|y/x|)`, sign of `x`
  ignored:
  ```
  promote to float (Float32/Float64 only; other AbstractFloat → no_op_err)
  isnan(x) || isnan(y)          → NaN
  x == ±1                       → atanh(y)
  m = 2·signbit(x) + signbit(y)
  y == 0                        → y                  (keeps signed zero)
  x == 0                        → atanh(copysign(Inf,y))  → DomainError
  isinf(x): isinf(y) → y ; else (m∈{0,2} ? +0 : −0)
  isinf(y)                      → atanh(y) → DomainError
  k = Int32(poshighword(y) − poshighword(x)) >> SHIFT      (SHIFT = 20 F64 / 23 F32)
  if   k >  THR:  z = π/2 + 0.5·PI_LO; m &= 1             (THR = 60 F64 / 26 F32; PI_LO = 1.2246467991473532e-16 F64, -8.742278e-8 F32)
  elif x<0 && k < −THR: z = 0
  else z = atanh(|y/x|)                  → DomainError if |y/x| > 1
  return (m ∈ {0,2}) ? z : −z
  ```
  `poshighword(x)` = high 32 bits of the IEEE bit pattern with the sign cleared. Goldens [verified]:
  `atanh(0.5,1.0)=0.5493061443340549`, `atanh(0.5,−1.0)=0.5493061443340549`, `atanh(−0.5,2.0)=−0.2554128118829953`,
  `atanh(0.5,−2.0)=0.2554128118829953`, `atanh(3.0,1.0)` DomainError, `atanh(0.0,1.0)=0.0`,
  `atanh(1.0,0.0)` DomainError, `atanh(Inf,2.0)` DomainError, `atanh(2.0,Inf)=0.0`, `atanh(−2.0,−Inf)=−0.0`,
  `atanh(Inf,Inf)=Inf`, `atanh(NaN,1.0)=NaN`, `atanh(1f0,2f0)=0.54930615f0`, `atanh(1,2)=0.5493061443340549`.
  The `k > THR` branch returning ~π/2 is an artefact of the atan2 template (atanh is undefined there).

### 4.4 `sqrt`, `cbrt` (`C:436-452`), n = 2 resp. 3

```
qrt(t::TensorAlgebra)  = isscalar(t) ? qrt(scalar(t)) : exp(log(t)/n)
qrt(t::Quaternion{V})  = iszero(metric(V)) ? qrt(radius(t))·exp(angle(t)/n) : exp(log(t)/n)   # no isscalar check
qrt(t::Couple{V,B})    = value(B*B) == −1 ? Couple{V,B}(qrt(Complex(t))) : qrt(radius(t))·exp(angle(t)/n)
qrt(t::Phasor)         = Phasor(qrt(amplitude(t)), angle(t)/n)
qrt(t::Submanifold{V,0}) = t;   qrt(t::TensorGraded{V,0}) = Single{V}(qrt(coef))
```
Notes [verified]: `cbrt` of an elliptic Couple calls `cbrt(::ComplexF64)` → **MethodError** (Julia has
none); port with principal complex cube root and flag. `sqrt(−4.0 + 0.0v12)` = `0.0 + 2.0v₁₂`;
`sqrt(0.3v12)` = `0.3872983346207417 + 0.38729833462074165v₁₂`; `sqrt(Couple(1.0,0.5,v1))` =
`0.9659258262890682 + 0.25881904510252074v₁`; `cbrt(Couple(1.0,0.5,v1))` = `0.9692073842687158 + 0.17550685828461604v₁`;
`sqrt(Q(2,.1,.2,.3))` = `1.42033 + 0.035203v₁₂ + 0.070406v₁₃ + 0.105609v₂₃`; `sqrt(Q(−1,0,0,0))` =
`1.0 + NaN*…` (0/0 angle). The Couple branch tests `B*B` (plain product) even in the metric twin.

### 4.5 `cosh`, `sinh`, `exph` (`C:456-572`)

Scalar shortcut: `cosh/sinh(t::TensorGraded{V,0}) = Single(cosh/sinh(coef))`.

Generic (`C:458-481`, `C:517-539`), no cap:
```
cosh(t): if Couple and B⟑B == −1: return Couple{V,B}(cosh(Complex(t)))
         τ = t⟑t; S = τ/2; term = (τ⟑τ)/24; f = ‖S‖; norms = (f, ‖term‖, f); k = 6
         loop (4.1): S += term; …; term = term ⟑ (τ/(k(k−1))); …; k += 2
         return One + S
sinh(t): if Couple and B⟑B == −1: return Couple{V,B}(sinh(Complex(t)))
         τ = t⟑t; f = ‖t‖; S = t; term = (t⟑τ)/6; norms = (f, ‖term‖, f); k = 5
         loop (4.1): …; term = term ⟑ (τ/(k(k−1))); …; k += 2
         return S
```
Generated `Multivector`/`Spinor` versions (`C:483-513`, `C:541-570`) have the same math plus a
`sb ≈ nb` scalar shortcut and cap 10000, **but are broken**: they interpolate `$op`/`$(args...)` inside
the inner `quote` (should be `$$op`, compare `C:66`), so every call raises
`UndefVarError: op not defined in Grassmann` [verified for `cosh(Multivector)`, `sinh(Spinor)`, and
transitively `exph(Multivector)`, `cos/sin(Couple)` in 3D (via `PseudoCouple → CoSpinor → Multivector`)].
The Lean port should implement them with the generic series (math is unambiguous). Hyperbolic Couples
(`B²=+1`) use the series, not `cosh(a)cosh(b)+…` closed forms [verified
`cosh(1+0.5v1) = 1.7400177902090013 + 0.6123918250026203v₁`].
`exph(t) = cosh(t) + sinh(t)` (`C:572`).

### 4.6 Trigonometric / inverse functions (defined in `AT:405-431`, rely on composite.jl)

With `i = V(I)` (pseudoscalar Submanifold), `op = ⟑`, all divisions right-divisions:

| function | definition |
|---|---|
| `cos t` | `cosh(i⟑t)` |
| `sin t` | `sinh(i⟑t) / i` |
| `tan`, `cot` | `sin/cos`, `cos/sin` |
| `sec`, `csc`, `sech`, `csch` | `inv(cos)`, `inv(sin)`, `inv(cosh)`, `inv(sinh)` |
| `asec`, `acsc`, `asech`, `acsch` | `acos(inv t)`, `asin(inv t)`, `acosh(inv t)`, `asinh(inv t)` |
| `tanh`, `coth` | `sinh/cosh`, `cosh/sinh` |
| `asinh t` | `log(t + sqrt(1 + t⟑t))` |
| `acosh t` | `log(t + sqrt(t⟑t − 1))` |
| `atanh t` | `(log(1+t) − log(1−t))/2` |
| `acoth t` | `(log(t+1) − log(t−1))/2` |
| `asin t` | `(−i) ⟑ log(i⟑t + sqrt(1 − t⟑t))` |
| `acos t` | `(−i) ⟑ log(t + i⟑sqrt(1 − t⟑t))` |
| `atan t` | `(−i/2) ⟑ (log(1 + i⟑t) − log(1 − i⟑t))` |
| `acot t` | `(−i/2) ⟑ (log(t − i) − log(t + i))` |
| `sinc t` | `iszero(t) ? 1 : sin(πt)/(πt)` |
| `cosc t` | `iszero(t) ? 0 : cos(πt)/t − sin(πt)/((πt)⟑t)` |

These are only correct when `i` is central with `i² = −1` (e.g. 3D Euclidean; n ≡ 3 mod 4 Euclidean); in
4D Euclidean `i² = +1` so `cos = cosh`. Because `cos x = cosh(ix)` routes through the series, even
`cos(One)` is ~1e-11 accurate [verified `cos(v) = 0.5403023058795628v`]. `^(b::Number, t) = exp(t⟑log b)`
(`AT:326`). `exp(t::TensorAlgebra) = one(V) + expm1(t)` is the AbstractTensors fallback (`AT:329`).

### 4.7 `inv`, `/`, `^` summary (from `A:403-638`; needed by log/sqrt)

* `inv(Multivector/Spinor/CoSpinor)`: `rm = ~m; d = rm⟑m`; if `‖⟨d⟩₀‖ ≈ ‖d‖` → `rm/⟨d⟩₀`; else for each
  grade k (all k for Multivector, even k ≥ 2 for (Co)Spinor) if `‖⟨d⟩_k‖ ≈ ‖d‖` → `rm / d(k)`; else error.
* `inv(Chain) = ~a / abs2(a)` (scalar), `inv(Single c·B) = ±(1/(c·B²))·B` with reversion sign,
  `inv(Couple) = (re, ±im)/(re² + im²·B²)` (Smith/robust variants for Float64, `A:607-651`),
  `inv(Phasor) = Phasor(inv amplitude, −angle)`, `inv(PseudoCouple) = ~a / abs2(a)`.
* `Couple / Couple` robust complex division generalised by `e = B²` (`A:556-605`).
* `t^n` (Int): `Chain` with n ≤ 3 dims uses `(~v⟑v)^(n÷2)` (× v if odd); elliptic Couple → complex power;
  `n < 8` repeated multiplication, else binary powering (`A:440-469`); `Phasor^n = Phasor(amp^n, n·angle)`.

### 4.8 Cramer machinery (`C:707-856`)

`Cramer(N, j=0)` generates, for input columns `t[1..M]` (or `T` when `j ≠ 0`):
```
x1 = t[1];  y1 = t[end]
for i = 1..N−1−j:  x_{i+1} = x_i ∧ t[1+i−j];   y_{i+1} = t[end−i] ∧ y_i
```
so `x_k = t1∧…∧tk` (prefix wedges) and `y_k = t_{M−k+1}∧…∧t_M` (suffix wedges); `∧` of a list is a left
fold (`A:111`, `wedges` `A:125`).

* **`\(t::Values{M,Chain{V,1}}, v)`** (`C:722-732`), `N = M−1`, `W = M ≠ mdims(V) ? Submanifold(M) : V`:
  * `N < 1` (M=1): `inv(t) ⋅ v`.
  * `M > mdims(V)`: `tt = transpose(t)`; `tt ⋅ (inv(Chain{W,1}(t) ⋅ tt) ⋅ v)` (least-norm).
  * else Cramer: numerators `(v∧y_N, x_1∧v∧y_{N−1}, …, x_{N−1}∧v∧y_1, x_N∧v)`, `detx = (t[1]∧y_N)[1]`,
    result `Chain{W,1}(Real.(num) ./ detx)` — `Real(blade)` takes the top-grade coefficient.
    [verified `B \ (1,2,3) = (0.30920245398773, 0.33128834355828213, 1.7423312883435587)`]
  * `\` with a *mixed* column space `Values{N,Chain{M,1}}` (`C:833-840`): if `mdims(M) > mdims(V)` least
    squares `ct⋅(inv(transpose(t)⋅ct)⋅v)`, else `transpose(t)\v`.
* **`in(v, t)`** (`C:734-747`):
  * `N == mdims(V)`: `s = signbit((t1∧y_{N−1})[1])` (sign of det); true iff `signbit` of every Cramer numerator
    `(v∧y_{N−1}), (x_i∧v∧y_{N−1−i}), (x_{N−1}∧v)` equals `s` — i.e. `v` lies in the closed positive cone of the
    columns (barycentric coords ≥ 0 for homogeneous simplices). Signed zeros matter (`+0.0` vs `-0.0`).
    [verified triangle `(1,0,0),(1,1,0),(1,0,1)`: `(1,.2,.2)` true, `(1,.8,.8)` false, `(1,−.1,.2)` false]
  * `N ≠ mdims(V)` (affine simplex in higher space): uses `affineframe` + `Cramer(N−1,1)` + `signscalar`
    of numerators over `d`; **broken in 0.8.46** [verified `MethodError: objects of type Vector{Number} are not callable`].
* **`_inv(M, N)`** (`C:749-759`): `M1 = M−1`, `(x,y) = Cramer(M1)`; numerator list `val`:
  * `M1` even: `(y_{M1}, y_{M1−1}∧x_1, …, y_1∧x_{M1−1}, x_{M1})`
  * `M1` odd, `M ≠ N`: `(y_{M1}, (i even ? + : −)(y_{M1−i}∧x_i) for i=1..M1−1, −x_{M1})`
  * `M1` odd, `M == N`: `(−y_{M1}, (i odd ? + : −)(y_{M1−i}∧x_i) …, x_{M1})`
  * `dt = t[1] ∧ y_{M1}` (the M-blade `t1∧…∧tM`).
* **`inv(t)`** (`C:761-772`): `M==1` → `transpose(Values(inv(t[1])))` (`v/|v|²` as a row);
  `M > N` → `tt⋅inv(Chain(t)⋅tt)`; `M == N` → rows `!(val_i / dt[1])` (complement of an (M−1)-blade scaled by
  1/det → vector), then `_transpose` (rows → column storage); `M < N` → rows `vector(val_i / dt)`
  (geometric division by the M-blade = **reciprocal frame**) [verified 3 points in 4D].
  `!` = right complement, metric-independent: inverse/det are the plain matrix ones even for `⟨-+++⟩` [verified].
* **`invdet(t)`** (`C:774-785`): `(inverse, !(dt))`; for `M==N` the second is `Chain{V,0}(det)`; for
  `M<N` it is the complement of the M-blade (a vector for M=N−1); `M>N` → `error("pseudo-determinant")`.
* **`adjugate(t)`** (`C:796-803`): `M==N` → `_transpose(.!(val))` (no division); `M<N` → `vector.(val)`
  (**broken**: grade-(M−1) blades have zero vector part → `Values{3,Zero}` MethodError [verified]);
  `M > N` → `tt⋅adjugate(Chain(t)⋅tt)`.
* **`cofactor(t)`** (`C:805-812`): same `val` but packed as `Chain{W}(out)` without `_transpose`, i.e.
  `cofactor = transpose(adjugate)`; `M > N` → `transpose(tt⋅adjugate(Chain(t)⋅tt))`; `M==1` → `Chain(Values(inv(t[1])))`.
  [verified `A=[1 2;3 4]`: adjugate columns `(4,−3),(−2,1)`, cofactor columns `(4,−2),(−3,1)`, inverse
  columns `(−2,1.5),(1,−0.5)`, `det = -2.0v`]
* **`gradient(T)`** (`C:814-831`) — gradients of the barycentric coordinates of a simplex with homogeneous
  vertices: `M < mdims(V)` → `map(↓(V), ct⋅inv(transpose(T)⋅ct))`; else `t = transpose(T)`, Cramer on the
  rows, numerators like `_inv` but **without the first entry**, divided by `(t1∧y_end)[1]`, mapped by `⋆`
  (Hodge, metric-aware) for square, `vector` otherwise, transposed into `↓(V)` (first coordinate dropped).
  Equivalent (Euclidean): column `i` = row `i` of `inv(T)` without its first component [verified triangle:
  `(-1,-1),(1,0),(0,1)`].
* **`compound(x, Val(G))`** (`C:715-720`): `Chain{V,G}(Values(∧(x[i] for i ∈ indices(j)) for j ∈ indexbasis(mdims(V),G)))`
  — column `j` of the G-th compound is the wedge of the columns indexed by the G-subset `j` (lexicographic
  subset order). `G > mdims(V)` → `throw("G = $G > $N")` (a String); `G == 0` → `Chain{V,0}(Values(Chain{V,0}(1)))`
  (Int 1). `Λ(x,G) = compound(x,G)`. [verified `compound(B,2)` 3×3 = columns `(5.9,1.35,−0.8), (0.6,2.9,1.3), (−0.56,0.01,4.22)`]
* **`det(t::Chain{V,1,<:Chain})`** (`C:952`) = `!(t1∧…∧tN)` → `Chain{W,0}`; `∧(t)` for `mdims(V) > mdims(W)`
  returns `map(Real, compound(t, min dims))` (`A:115-121`).
* `inv_approx` (`C:841-844`) not exported; `\`/`in`/`inv`/… on `Chain{V,1,<:Chain}` unwrap `value(t)` (`C:846-856`);
  `A \ I = inv(A)`, `I \ A = A`, `A \ B = inv(A)*B`.

### 4.9 `pfaffian` (`C:887-895`)

`n = floor(mdims(V)/2)`; `ω^∧n = ω∧ω∧…∧ω` (n factors); return `!ω` if n = 1 else `!(ω^∧n)/n!`.
For even dimension this is the Pfaffian as `Chain{V,0}` [verified 4D `(1,2,3,4,5,6)` → `8.0v` =
`ω12ω34 − ω13ω24 + ω14ω23`]; for odd dimension it is a vector (complement of a 2n-blade)
[verified 3D `(1,2,3)` → `3.0v₁ − 2.0v₂ + 1.0v₃`]. `pfaffian(Quaternion) = pfaffian(bivector(A))`;
`pfaffian(Endomorphism) = pfaffian(bivector(A))` with `bivector(A)[ij] = A[j,i]` (`F:592,614-616`).

### 4.10 Vandermonde (`C:858-885`)

* `polynom(x, Val(N)) = Chain{Submanifold(N),1}(x^0, x^1, …, x^(N−1))`.
* `approx(x, y::Chain{V}) = polynom(x, Val(mdims V)) ⋅ y` (→ `Chain{V,0}`); `approx(x, y::Values{N})` → scalar;
  `approx(x, y::AbstractVector) = [x^i for i=0:len−1] ⋅ y`. [verified `approx(2.0, (1,1,1)) = 7.0v`]
* `vandermonde(x::Array, N)` = dense matrix `V[i,d+1] = x_i^d`; `vandermonde(x::Array, y::Array, N) = vandermonde(x,N) \ y` (Julia QR least squares).
* `_vandermonde(x::Values{N}, V) = Chain{Submanifold(N),1}(polynom.(x, Val(mdims V)))` (columns = rows of the
  Vandermonde matrix); `vandermonde(x, V) = transpose(_vandermonde(x, V))` (proper Vandermonde, columns = powers);
  `vandermonde(x, y, V) = (length(x) ≠ mdims(V) ? _vandermonde(x,V) : vandermonde(x,V)) \ y`
  [verified exact fit of `(1,4,9)` at `(1,2,3)` → `0.0v₁ + 0.0v₂ + 1.0v₃`].
* `vandermondeinterp(x,y,V,grid)`: `coef = vandermonde(x,y,V)`; `xp = collect(minx:(maxx−minx)/grid:maxx)`;
  `yp = coef[1]·ones(grid+1)`, then `yp += coef[d+1] .* xp.^d` for `d = 1..len−1`; returns `(coef, xp, yp)`.

### 4.11 Simplex / mesh helpers (`C:897-986`)

* `list(a,b) = Values{max(0,b−a+1),Int}(a:b...)`, `evens(a,b) = Values{(b−a)÷2+1,Int}(a:2:b...)`.
* `affineframe(x::Values{N,Chain{V}}, y=x[1]) = TensorOperator(Chain{V(2..N),1}(↓(V).(x[2:N] .− y)))`;
  one point → empty `Values{0}`. `↓(V)` drops the first (homogeneous) basis vector; the result's manifold
  prints as `⟨_11⟩` [verified].
* `signscalar`: `Submanifold{V,0}` → true; `Single{V,0}` → `!signbit(value)`; other `Single`/`Chain` → false;
  `Chain{V,0}` → `!signbit(x[1])`; `Multivector` → `isscalar(x) && !signbit(scalar value)`.
* `findfirst(P, t)` / `findlast`: first/last `i` with `P ∈ t[i]`, **0** if none; `findall(P,t) = findall(P .∈ t)`.
* `mean(m) = sum(m)/length(m)`; `barycenter(m) = sum(m)` (unnormalised); `centroid(m) = s/s[1]` with `s = sum(m)`
  (homogeneous normalisation) [verified triangle: mean `1.0v₁ + 0.333333v₂ + 0.333333v₃`, barycenter
  `3.0v₁ + 1.0v₂ + 1.0v₃`].
* `area(m) = value(abs(⋆(m[end]∧m[1] + Σ m[i]∧m[i+1]))/2)` (shoelace; unit square → `1.0` [verified]).
* `array(m)[i,j] = m[i][j]`, `submesh(m)` drops column 1; `array!`, `submesh!` are empty generic functions.
* `edgelength`, `volumes`, `detsimplex = det(m)/(mdims V − 1)!`, `det(::Vector{Chain})`, `∧(::DenseVector{Chain})`
  need Cartan's `points`/`isbundle` → `UndefVarError` standalone [verified]; port inside the Cartan layer.
* `gradient(m::TensorAlgebra) = d(m)`, `curl(m) = Manifold(m)(∇) × m`, `divergence(m) = ∂(m)`, `Base.div(m) = divergence(m)`
  (1-arg!) — Leibniz derivations; `grad = gradient`.

### 4.12 Element-wise utilities (`C:988-1084`)

* `op(a, m)` for `op ∈ {div, rem, mod, mod1, fld, fld1, cld, ldexp}`: `Chain`, `Spinor`, `CoSpinor`,
  `Multivector` broadcast over coefficients; `Couple`/`PseudoCouple` call `op(value(a), m)` **without**
  broadcasting → MethodError [verified `rem(Couple,3)`]. Same pattern for `mod2pi, rem2pi, rad2deg, deg2rad, round`
  with kwargs [verified `round(1.26v1+2.71v2; digits=1) = 1.3v₁ + 2.7v₂ + 0.0v₃`].
* `isfinite(a) = prod(isfinite.(value(a)))` (Bool product = all).
* `rationalize(T, a; tol=eps(T))` element-wise; `rationalize(t::TensorAlgebra; kw...) = rationalize(Int, t; kw...)`
  (the Couple/PseudoCouple versions reference an undefined `T` in the default).
* `map(fn, x)`: coefficient-wise for Multivector/Spinor/CoSpinor/Chain (same type); `TensorTerm` →
  `fn(value(x))*basis(x)`; Couple/PseudoCouple → both slots.
* `_diff(Val(N), a::Values{Q,Chain}, Val(1))` = `(a[2]−a[1], …, a[N]−a[N−1])`.
* `rand(Chain{V,G})` = `Chain{V,G}(DirectSum.orand(...))`, `rand(Multivector{V})` etc.; `Couple{V}` picks a random
  nonzero blade `UInt(rand(1:2^n−1))`; `PseudoCouple{V}` picks from `0:(2^n−1)−1`. Not needed for parity (use your own RNG).
* Sparse matrix × `Vector{Chain}`: Julia interop; in Lean provide `SparseMatrix.mulVec` over a module of Chains.

### 4.13 Polynomial roots (`C:1086-1226`)

Helpers: `zero!(x) = x ≈ 0 ? zero(x) : x` (identity except `-0.0 → 0.0`, since `x≈0` ⇔ `x==0`);
`zero!(z::Complex)` component-wise; `subzero(a,b) = a/b ≈ 1 ? 0 : a−b` (catastrophic-cancellation guard,
rtol √eps on the ratio) [verified `subzero(1,1+1e-9) = 0.0`, `subzero(1,1+1e-7) = -1.0000000005838672e-7`];
`subsqrt(a,b) = a/b ≈ 1 ? 0 : sqrt(a−b)` (real sqrt, may DomainError); `subsqrtcomplex` → complex sqrt if negative.

Entry points (`a_i` = coefficient of `z^i`):
```
roots(a)           = roots(value(a)...)
roots(a0::Real/Complex) = 0                   # constant polynomial → zero (sic)
roots(a0,a1)       = monicroots(a0/a1)
roots(a0,a1,a2)    = monicroots(a0/a2, a1/a2)
roots(a::Real...)  = monicroots((a[1:N−1] ./ a[N])...)
rootsreal / rootscomplex: same normalisation into monicrootsreal / monicrootscomplex
monicroots(a...)   (≥5 args)  = value(eigvals(companion(Values(a...))))      # LAPACK, sorted (re,im) lexicographic
monicroots(a0)     = −a0
monicroots(a0,a1)  = quadratic(a0, a1, sqrt(a1²−4a0 < 0 ? Complex(a1²−4a0) : a1²−4a0))
quadratic(a0,a1,rt) = a1 < 0 ? (2a0/(−a1+rt), (−a1+rt)/2) : ((−a1−rt)/2, 2a0/(−a1−rt))
```
Cubic `z³ + a2 z² + a1 z + a0` (`C:1127-1153`), `C = Val(false)` (complex output requested when true):
```
a22 = a2²; a23 = a2/3
q = subzero(a1/3, a22/9); r = a1·a2/6 − a0/2 − a22·a2/27
r2 = r²; q3 = q³
if r2 + q3 > 0:                                   # one real root
    A = cbrt(|r| + sqrt(r2+q3)); qA = q/A
    t = r < 0 ? qA − A : A − qA
    x = zero!(−(t/2 + a23)); y = zero!((√3/2)(A + qA)); z = t − a23
    return z < x ? (z, x−iy, x+iy) : (x−iy, x+iy, z)      # Values promoted to Complex
else:                                             # three real roots (Viète)
    sq = sqrt(−q)
    if q < 0: c = r / (q > −1 ? sqrt(−q3) : sq·sq·sq); ϕ1 = acos(|c| ≈ 1 ? sign(c) : c)/3
    else:     ϕ1 = sq/3                           # q == 0 (then r == 0): ϕ1 = 0
    sq2 = 2sq; ϕ2 = ϕ1 − 2π/3; ϕ3 = ϕ1 + 2π/3
    out = (sq2 cos ϕ3 − a23, sq2 cos ϕ2 − a23, sq2 cos ϕ1 − a23)   # ascending
    return C ? Complex.(out) : out
```
`cubicmax(a0,a1,a2)`: same `q,r`; one-real-root branch returns `(r<0 ? q/A − A : A − q/A) − a23`; Viète branch
returns `2sq·cos(θ/3) − a23` with `θ = acos(clamped c)` if `q<0` else `θ = sq`.

Quartic `z⁴ + a3 z³ + a2 z² + a1 z + a0` (`C:1173-1191`):
```
quartic(a0,a1,a2,a3):
  a04 = 4a0
  u = cubicmax(a04·a2 − a1² − a0·a3², a1·a3 − a04, −a2)     # largest root of resolvent cubic
  a32 = a3/2; u2 = u/2
  z1 = zero!(a32² + u − a2)
  psq = z1 ≤ 0 ? 0 : sqrt(z1);  qsq = subsqrt(u2², a0)
  p1 = a32 − psq; p2 = a32 + psq
  qsqpm = (a1 − a3·u/2 > 0) ? qsq : −qsq
  q1 = u2 + qsqpm; q2 = u2 − qsqpm
  return (q1, q2, p1/−2, p2/−2)            # z⁴+… = (z² + p1 z + q1)(z² + p2 z + q2)
monicroots(a0,a1,a2,a3):
  (q1,q2,p12,p22) = quartic(...)
  sq1 = p12² − q1; sq2 = p22² − q2; rt_i = sqrt(sq_i < 0 ? Complex(sq_i) : sq_i)
  return (p22−rt2, p22+rt2, p12−rt1, p12+rt1)   # Float if both rt real else Complex
monicrootsreal quartic:    rt_i = sqrt(zero!(p_i² − q_i))            (DomainError if negative)
monicrootscomplex quartic: rt_i = sqrt(Complex(subzero(p_i², q_i)))
monicrootsreal(a0,a1,a2): Viète only (DomainError when not all real); monicrootsreal(a0,a1) = quadratic with real sqrt
monicrootscomplex: Complex(−a0); quadratic with sqrt(Complex(·)); cubic = monicroots(...,Val(true)); ≥5 → eigvalscomplex
```
Goldens [verified]: `roots(1,2,3) = [−1/3 − 0.4714045207910317i, −1/3 + 0.4714045207910317i]`;
`roots(6,−5,1) = [2.0, 3.0]`; `roots(−6,11,−6,1) = [1.0, 2.0, 3.0]`; `roots(1,0,1) = [−0.0 − 1.0i, −0.0 + 1.0i]`;
`roots(24,−50,35,−10,1) = [1.0000000000000009, 1.9999999999999885, 3.000000000000025, 3.999999999999986]`;
`roots(1,0,0,0,1) = [−0.7071067811865476 ∓ 0.7071067811865475i, 0.7071067811865476 ∓ 0.7071067811865475i]` (order `−,+,−,+` imag);
`monicroots(2,3,1) = [−0.7152252384350903+0i, −0.14238738078245483 − 1.6661475736120595i, −0.14238738078245483 + 1.6661475736120595i]`;
`cubicmax(2,3,1) = −0.7152252384350903`; `quartic(1,2,3,4) = (0.4598786605959496, 2.1744866324175933, −0.046799431780810474, −1.9532005682191895)`;
`monicroots(1,2,3,4,5)` (companion/LAPACK) `= [−4.192725723692126+0i, −0.5640990957045253 ∓ 0.39090263789747076i, 0.16046195755058748 ∓ 0.6932715588679899i]`.

### 4.14 `companion`, `characteristic`, eigenvalues (forms.jl; used by roots)

* `companion(x::Values{N})` (`F:829-835`): `TensorOperator(Chain(e_2, e_3, …, e_N, −x))` — column i<N is the unit
  vector `e_{i+1}`, last column `−(a0,…,a_{N−1})`: subdiagonal ones, last column negated coefficients
  [verified `Matrix(companion(1,2,3)) = [0 0 −1; 1 0 −2; 0 1 −3]`]. Unit columns are `Int` Chains.
* `characteristic(X::Endomorphism)` (`F:1445-1462`) returns the monic char-poly coefficients **ascending,
  without the leading 1**, i.e. `det(λI − X) = λ^N + c_{N−1}λ^{N−1} + … + c_0`:
  * N=1: `−X[1]`; N=2: `(det X, −tr X)`; N=3: `(−det, (tr² − tr(X²))/2, −tr)`;
  * N=4: `a3 = tr X, X2 = X⋅X`: `(det, (a3(a3² − 3tr X2) + 2tr(X2⋅X))/−6, (a3² − tr X2)/2, −a3)`;
  * N≥5: `characteristic_exact`: coefficient `M` = `±tr(compound(X, N−M+1))`, sign `+` iff `N−M` odd (`F:1513-1517`).
  [verified 3×3 `B`: `(−8.15, 13.02, −6.5)`; 4×4: `(8.6522, −22.114, 20.06, −7.6)`]
* `eigvals(X::TensorNested)` (`F:1374-1383`): N=1 → `X[1]`; N<5 → `Chain(monicroots(characteristic(X)))`
  (closed forms, ascending for real roots); N≥5 → LAPACK `eigen(Matrix(X))`. `eigvalsreal`/`eigvalscomplex`
  analogous with `monicrootsreal`/`monicrootscomplex`. [verified 3×3 `B`: `1.31032, 1.87837, 3.31131`]
* `eigvals` of an even `Couple`/`Spinor` in 2D/3D (`F:1360-1373`): `X2 = X⟑X`, `re = ⟨X2⟩₀`,
  `sq = sqrt(abs2(imaginary(X2)))` → `(re − i sq, re + i sq)` (2D) or `(re − i sq, re + i sq, abs2(X))` (3D);
  otherwise `eigvals(operator(X))` where `operator(t) = TensorOperator(Chain(chainbasis .⊘ t))` (sandwich).
* `eigen/eigenreal/eigencomplex` → LAPACK then `Proj(eigvecs, λ)`; `eigvecs(DiagonalMorphism)` = unit columns.
* `eigpolys(X)` = `reverse(characteristic)./binomial(N,1:N).*(−1)^(1:N)` (normalised elementary symmetric
  polynomials; N=2 special) [verified 3×3: `2.16667, 4.34, 8.15`]; `sylvester(x)` = product of nonzero
  pairwise differences per index; `eigmults(x)` = 1 + number of equal eigenvalues (`F:1217-1271`).
* **Lean note**: N ≥ 5 requires an eigenvalue solver; Lean has no LAPACK. Implement Hessenberg reduction +
  shifted QR (Francis double shift) on `Float`, sort `(re, im)` lexicographically to match Julia's `eigvals`.

### 4.15 `cayley` tables (`F:802-827`)

`cayley(V, op=*) = TensorOperator(Multivector{V}([Multivector{V}(op.(bas, b)) for b ∈ bas]))` with
`bas = Λ(V).b` (all 2^n blades in Multivector order): **column j = `op(bas[i], bas[j])` over rows i**, so
`Matrix(cayley)[i,j] = op(bas[i], bas[j])` [verified 2D:
`[v v₁ v₂ v₁₂; v₁ 1v v₁₂ 1v₂; v₂ −1v₁₂ 1v −1v₁; v₁₂ −1v₂ 1v₁ −1v]`]. `cayley(V, G::Int, op)` restricts to
grade-G blades (`Chain` of Chains); `cayleyeven`/`cayleyodd` to even/odd blades; `cayley(a::AbstractVector, b, op)`
= dense `[op(x,y) for x ∈ a, y ∈ b]`; `cayley(a,b) = a*transpose(b)`. Docs goldens (`docs/src/algebra.md:623-715`)
for `Submanifold(1)` and `S"-"` with `∧, ∨, <, >, <<, >>` are reproduced in §6.

### 4.16 `pseudo*` / `co*` family (`AT:482-570`)

For `fun ∈ (abs, abs2, sqrt, cbrt, exp, log, inv, sin, cos, tan, sinh, cosh, tanh)`:
`pseudo<fun>(t) = co<fun>(t) = complementleft(fun(complementright(t)))` (+ metric twin except `log`;
`colog_metric`, `pseudolog_metric` separately). `const antiabs, antiabs2, antimetric, pseudometric = coabs,
coabs2, cometric, cometric`; `pseudodot = codot = antidot = expansion`; `geomabs(t) = abs(t) + coabs(t)`;
`unit(t) = t/abs(t)`; `counit = unitize: t/value(coabs(t))`; `unitnorm(t) = t/norm(geomabs(t))`;
`cosandwich(x,R) = complementleft(sandwich(!x, !R))`; `antisandwich(R,x) = complementleft(!R >>> !x)`.
Macros: `@co f(x,y)` defines `cof(x,y) = complementleft(f(complementright(x), complementright(y)))`; `@pseudo`
identical with prefix `pseudo`. `complementright` (`!`) is the metric-free right complement
(`!⟨v_{i1}…v_{im}⟩ = (−1)^{m(m+1)/2 + Σ i_j} ⟨∧_{k∉i} v_k⟩`, `docs/src/algebra.md:457-460`),
`complementleft` its inverse. [verified 3D: `pseudoexp(0.5v₃) = 0.479425538604203v₃ + 0.8775825618903728v₁₂₃`,
`pseudoabs(3v₁+4v₂) = 5.0v₁₂₃`, `pseudoinv(2v₁₂) = 0.5v₁₂`, `pseudosin(0.5v₃) = 0.5210953054814953v₃`,
`pseudocosh(0.5v₃) = 0.8775825618898637v₁₂₃`, `codot(v₁₂, 2v₁₂) = 2.0v₁₂₃`, `geomabs(3v₁+4v₁₂₃) = 5.0 + 5.0v₁₂₃`,
`unitize(3v₁+4v₁₂₃) = 0.6000000000000001v₁ + 0.8v₁₂₃`]. `cometric(a,b)` on two Singles is a Julia method
ambiguity error [verified].

### 4.17 `Couple` / `Phasor` helper semantics used above (`M:656-1066`)

* `Couple{V,B}` = `re + im·B`; `scalar`, `imaginary(z) = Single{V,grade B,B}(im)`; `abs2(z) = re² + im²·abs2_inv(B)`;
  `radius = sqrt(re² − im²·(B⟑B))`; `Complex(z) = re + im·i`; `Couple(Single{V,0})` uses `B = I` (pseudoscalar);
  `Couple(Single{V,G,B})` = `(0, c)`.
* `PseudoCouple{V,B}` = `re·B + im·I`; `imaginary(z) = Single(B, re)`, `volume(z) = Single(I, im)`.
* `Phasor{V}(v, ω)` means `v·exp(ω)`: `complexify(z) = amplitude ⟑ exp(angle)` (or sandwich form for nested
  tensor amplitudes); `polarize(Couple) = Phasor(radius, angle)`; `Phasor(z)(t) = Phasor(amp, angle·t)`;
  display `amp ∠ angle`; `Phasor^n = Phasor(amp^n, n·angle)`; `inv(Phasor) = Phasor(1/amp, −angle)`.

### 4.18 Special singleton values (`C:411-434`) [verified table, 3D]

| f | `f(Zero)` | `f(One)` | `f(Infinity)` |
|---|---|---|---|
| exp, exp2, exp10, cosh | One | `Single(e)`, `2.0`, `10.000000000000002`, `1.5430806348152437` | ∞ |
| expm1 | `0.0v` | `1.718281828459045v` | `Inf*v` |
| log, log2, log10 | **hangs** (`log(Zero)` loops) | Zero | ∞ |
| log1p | MethodError (ambiguous `/`) | `0.6931471795482411v` (series!) | MethodError |
| sinh, tanh | Zero | `1.1752…v`, `0.761594155955765v` | ∞, One |
| coth | ∞ | `1.3130352854993312v` | One |
| sqrt, cbrt | Zero | One | ∞ |
| asin | Zero | `1.5707963267948966v` | DomainError |
| atan | Zero | `0.7853981633974483v` | `1.5707963267948966v` |
| asinh | Zero | `0.881373587019543 + 0.0v₁₂₃` (Couple) | ∞ |
| atanh | Zero | ∞ | MethodError |
| acosh | DomainError | Zero | ∞ |
| acos | `1.5707963267948966v` | Zero | DomainError |
| acoth | `-0.0 - 1.5707963267948966v₁₂₃` | ∞ | Zero |
| acot | `1.5707963267948966v` | `0.7853981633974483v` | Zero |
| sinc | One | `0v` (Int) | Zero |
| cosc | Zero | `-1.0v` | Zero |
| asech | ∞ | Zero | DomainError |
| cos, sin | One, Zero | `0.5403023058795628v`, `0.8414709848086585v` (series via `I`) | ∞, ∞ |

(`C:411` contains the typo `:(Basesinc)` which defines a junk function `Grassmann.Basesinc` instead of
`sinc(One)=Zero`.)

---------------------------------------------------------------------------------------------------

## 5. Display / printing of composite results (observed; printing spec belongs to the show report)

* `Couple`: `show(re)` then `showterm` → `"<re> + <im><blade>"` or `"<re> - <|im|><blade>"`, full `repr`
  precision: `0.8775825618903728 + 0.479425538604203v₁₂`, `0.8 - 0.4v₁`, `2.718281828459045 + NaN*v₁₂`
  (non-finite coefficients print as `NaN*`/`Inf*` before the blade).
* `PseudoCouple`: `"<re><B> + <im><I>"`: `1.0v₃ + 2.0v₁₂₃`, `1.0v + 2.0v₁₂₃`, `-0.0 - 1.5707963267948966v₁₂₃`.
* `Phasor`: `"<amp> ∠ <angle>"` (`M:931-934`; compact IO: no spaces): `2.0 ∠ 0.5v₁₂`.
* `Single`: `0.5v₁₂`, scalar `7.38905609893065v`; `One` prints `v`, `Zero` `𝟎`, `Infinity` `∞`.
* `Chain`, `Spinor`, `CoSpinor`, `Multivector`: 6 significant digits (`%g`-like: `0.85847`, `3.51291e-19`);
  Chain/Spinor/CoSpinor print zero coefficients (`+ 0.0v₁₃`), Multivector omits zeros except it prints a
  lone scalar as `22.1672v⃖` / `1.0v⃖`; negative terms join with `" - "`.
* Chain-of-Chain: `(1.0v₁+3.0v₂)v₁ + (2.0v₁+4.0v₂)v₂` — each column in parentheses without inner spaces
  followed by the outer basis label. `Values`: `[2.0, 3.0]`; complex: `ComplexF64[-0.3333333333333333 - 0.4714045207910317im, …]`.
* `det`: `8.15v` (a `Chain{V,0}`), `invdet` prints a tuple `(…, 8.15v)`.

---------------------------------------------------------------------------------------------------

## 6. Golden examples (verbatim `repr` output from the oracle env)

3D Euclidean `@basis S"+++"` unless stated.
```
exp(0.5v12)                      = 0.8775825618903728 + 0.479425538604203v₁₂          :: Couple
exp(v1+2v12)                     = -0.617273 + 0.351845v₁ + 0.70369v₁₂                :: Multivector
exp(Multivector(1+0.3v1+0.2v12+0.1v123)) = 2.7726 + 0.818189v₁ + 3.51291e-19v₂ - 0.0547285v₃ + 0.545459v₁₂ + 1.11893e-18v₁₃ + 0.0820927v₂₃ + 0.278188v₁₂₃
q = 1.0 + 0.3v12 + 0.2v13 + 0.4v23                                                      :: Quaternion
exp(q)   = 2.33356 + 0.776637v₁₂ + 0.517758v₁₃ + 1.03552v₂₃
log(q)   = 0.127321 + 0.275192v₁₂ + 0.183461v₁₃ + 0.366922v₂₃
sqrt(q)  = 1.03339 + 0.145154v₁₂ + 0.0967691v₁₃ + 0.193538v₂₃
cbrt(q)  = 1.02924 + 0.0952755v₁₂ + 0.063517v₁₃ + 0.127034v₂₃
q^3      = 0.13 + 0.813v₁₂ + 0.542v₁₃ + 1.084v₂₃
inv(q)   = 0.775194 - 0.232558v₁₂ - 0.155039v₁₃ - 0.310078v₂₃
c = 1.0 + 2.0v12
exp(c)   = -1.1312043837568135 + 2.4717266720048188v₁₂
log(c)   = 0.8047189562170501 + 1.1071487177940904v₁₂
sqrt(c)  = 1.272019649514069 + 0.7861513777574233v₁₂
cosh(c)  = -0.64214812471552 + 1.0686074213827783v₁₂
sinh(c)  = -0.4890562590412937 + 1.4031192506220405v₁₂
angle(c) = 1.1071487177940904v₁₂ ; radius(c) = 2.23606797749979
log1p(c) = 1.0397207708399179 + 0.7853981633974483v₁₂
expm1(c) = -2.131204383756814 + 2.471726672004819v₁₂
b = 0.3v12 + 0.2v13 + 0.4v23 (Chain)
exp(b)   = 0.85847 + 0.285709v₁₂ + 0.190473v₁₃ + 0.380945v₂₃          :: Quaternion
expm1(b) = -0.14153 + 0.285709v₁₂ + 0.190473v₁₃ + 0.380945v₂₃
cosh(b)  = 0.85847 + 0.0v₁₂ + 0.0v₁₃ + 0.0v₂₃ ; sinh(b) = 0.0 + 0.285709v₁₂ + 0.190473v₁₃ + 0.380945v₂₃
cos(b)   = 1.14854 + 0.0v₁₂ + 0.0v₁₃ + 0.0v₂₃ ; sin(b) = 0.0 + 0.314712v₁₂ + 0.209808v₁₃ + 0.419616v₂₃
v = 0.3v1+0.4v2
exp(v)   = 1.12763 + 0.312657v₁ + 0.416876v₂                         :: Multivector
cosh(v)  = 1.12763 + 0.0v₁₂ + 0.0v₁₃ + 0.0v₂₃                       :: Quaternion
sinh(v)  = 0.312657v₁ + 0.416876v₂ + 0.0v₃ + 0.0v₁₂₃                :: CoSpinor
cos(v)   = 0.877583 + 0.0v₁₂ + 0.0v₁₃ + 0.0v₂₃ ; sin(v) = 0.287655v₁ + 0.38354v₂ + 0.0v₃ - 0.0v₁₂₃
exp(2.0v1) = 3.7621956910836314 + 3.6268604078470186v₁
exp(v1)    = 1.5430806348152437 + 1.1752011936438014v₁
exp(v12)   = 0.5403023058681398 + 0.8414709848078965v₁₂
exp(v123)  = 0.5403023058681398 + 0.8414709848078965v₁₂₃
exp(0.7v123) = 0.7648421872844885 + 0.644217687237691v₁₂₃
exp(Single(2.0)) = 7.38905609893065v
exp(1.0v1+1.0v2+1.0v3) = 2.91458 + 1.58059v₁ + 1.58059v₂ + 1.58059v₃
c2 = 1.0 + 0.5v1 (hyperbolic)
exp(c2) = 3.065205170519096 + 1.4164838998189684v₁ ; log(c2) = -0.14384103622589053 + 0.5493061443340549v₁
angle(c2) = 0.5493061443340549v₁ ; radius(c2) = 0.8660254037844386
sqrt(c2) = 0.9659258262890682 + 0.25881904510252074v₁ ; cosh(c2) = 1.7400177902090013 + 0.6123918250026203v₁
sinh(c2) = 1.3251873801254557 + 0.8040920746317085v₁ ; log1p(c2) = 0.6608779199911597 + 0.2554128118829953v₁
c2^3 = 1.75 + 1.625v₁ ; inv(c2) = 0.8 - 0.4v₁
expm1(c2) (series) = 2.065205168660134 + 1.4164838979600063v₁     # vs exp(c2)-1 = 2.065205170519096 + 1.4164838998189684v₁
p = Phasor(2.0, 0.5v12) = 2.0 ∠ 0.5v₁₂
log(p) = 0.6931471805599453 + 0.5v₁₂ ; sqrt(p) = 1.4142135623730951 ∠ 0.25v₁₂ ; p^2 = 4.0 ∠ 1.0v₁₂
inv(p) = 0.5 ∠ -0.5v₁₂ ; complexify(p) = 1.7551651237807455 + 0.958851077208406v₁₂
Phasor(1.0+1.0v12) = 1.4142135623730951 ∠ 0.7853981633974483v₁₂
log1p(p) = 1.0706403744156554 + 0.3349093296212582v₁₂
exp(p) = 17.77126028818127 ∠ 0.479425538604203      # BUG-compatible
pc2 = PseudoCouple{S"+++",v}(1.0,2.0) = 1.0v + 2.0v₁₂₃
exp(pc2) = -1.1312043837568135v + 2.4717266720048188v₁₂₃ ; log(pc2) = 0.8047189562170501v + 1.1071487177940904v₁₂₃
log1p(pc2) = 1.0397207708399179v + 0.7853981633974483v₁₂₃ ; expm1(pc2) = -2.1312043837568133v + 2.4717266720048188v₁₂₃
exph(0.5v12) = 0.8775825618898637 + 0.4794255386164159v₁₂
tan(0.5v12) = 0.46211715724935354v₁₂ ; tanh(0.5v12) = 0.5463024898580239v₁₂
cosh(0.5v12) = 0.8775825618898637v ; sinh(0.5v12) = 0.4794255386164159v₁₂
asinh(0.5v12) = -5.551115123125783e-17 + 0.5235987755982989v₁₂ ; acosh(2.0+0.5v12) = 1.3618009008578458 + 0.27775425655771396v₁₂
atanh(0.5v12) = 0.0 + 0.4636476090008061v₁₂ ; asin(0.5v12) = 0.4812118250596034v₁₂
atan(0.5v12) = 0.5493061443340549v₁₂ - 0.0v₁₂₃ (PseudoCouple) ; acos(0.5v12) → error inv undefined
2^(0.5v12) = 0.9405421046832438 + 0.3396771251026685v₁₂ ; exp10(0.5v12) = 0.40730731015394683 + 0.9132911666577952v₁₂
log2(1+0.5v12) = 0.16096404744368117 + 0.6689021062254881v₁₂ ; log10(1+0.5v12) = 0.04845500650402821 + 0.20135959813668655v₁₂
Minkowski ⟨-+++⟩: exp(0.5v1) = 0.8775825618903728 + 0.479425538604203v₁ ; exp(0.5v2) = 1.1276259652063807 + 0.5210953054937474v₂
  exp(0.5v12) = 1.1276259652063807 + 0.5210953054937474v₁₂ ; exp(0.5v23) = 0.8775825618903728 + 0.479425538604203v₂₃
  exp(0.3v1+0.4v2) = 1.0352 + 0.303512v₁ + 0.404683v₂ ; exp(0.5v1+0.4v2) = 0.955336 + 0.492534v₁ + 0.394027v₂
  exp(0.3v12+0.4v23) = 0.965204 + 0.296512v₁₂ + … + 0.39535v₂₃ + 0.0v₁₂₃₄ ; log(Couple{v1}(2.0,0.5)) = 0.7234594914681627 + 0.24497866312686414v₁
PGA D"1,1,1,0": exp(0.3v12+0.2v13+0.1v14+0.4v23+0.5v24+0.7v34) = 0.85847 + 0.285709v₁₂ + 0.190473v₁₃ + 0.0758103v₁₄ + 0.380945v₂₃ + 0.485894v₂₄ + 0.652084v₃₄ + 0.142854v₁₂₃₄
  same bivector in ⟨++++⟩ (series) = 0.526907 + 0.219351v₁₂ + 0.189728v₁₃ + 0.0656178v₁₄ + 0.329963v₂₃ + 0.427077v₂₄ + 0.571811v₃₄ + 0.125354v₁₂₃₄
Docs (docs/src/tutorials/algebra-of-space.md): exp(π/4*v23) = 0.7071067811865476 + 0.7071067811865475v₂₃
  R12(π/2)=exp(π/4 v12) = 0.7071067811865476 + 0.7071067811865475v₁₂ ; ~R*(v1+v2+v3)*R = -1.0v₁ + 1.0v₂ + 1.0v₃ + 0.0v₁₂₃
  exp(π/8 v12) = 0.9238795325112867 + 0.3826834323650898v₁₂ ; exp(π/10 v23) = 0.9510565162951535 + 0.3090169943749474v₂₃
  exp(π/12 (v23+v12)) = 0.93224 + 0.255859v₁₂ + 0.0v₁₃ + 0.255859v₂₃
test/issuestests.jl:57-60: exp(0.5π/2·i) ≈ √2(1+i)/2 with i = v₂₃ ; exp(0.5π/2(a i + b j + c k)) = 0.707107 + 0.0v₁₂ - 0.5v₁₃ + 0.5v₂₃
Matrices (columns listed):
  A = (1.0v₁+3.0v₂)v₁ + (2.0v₁+4.0v₂)v₂  (= [1 2; 3 4])
  exp(A) = (51.969v₁+112.105v₂)v₁ + (74.7366v₁+164.074v₂)v₂  (Base: [51.968956198705 74.7365645670032; 112.10484685050483 164.07380304920986])
  inv(A) = (-2.0v₁+1.5v₂)v₁ + (1.0v₁-0.5v₂)v₂ ; det(A) = -2.0v ; adjugate(A) = (4.0v₁-3.0v₂)v₁ + (-2.0v₁+1.0v₂)v₂
  cofactor(A) = (4.0v₁-2.0v₂)v₁ + (-3.0v₁+1.0v₂)v₂ ; compound(A,2) = (-2.0v₁₂)v₁₂ ; compound(A,0) = (1v)v
  B = [2.0 0.1 0.2; 1.0 3.0 0.4; 0.5 0.7 1.5]: det = 8.15v ; adjugate(B) = (4.22v₁-1.3v₂-0.8v₃)v₁ + (-0.01v₁+2.9v₂-1.35v₃)v₂ + (-0.56v₁-0.6v₂+5.9v₃)v₃
  inv(B) = (0.517791v₁-0.159509v₂-0.0981595v₃)v₁ + (-0.00122699v₁+0.355828v₂-0.165644v₃)v₂ + (-0.0687117v₁-0.0736196v₂+0.723926v₃)v₃
  compound(B,2) = (5.9v₁₂+1.35v₁₃-0.8v₂₃)v₁₂ + (0.6v₁₂+2.9v₁₃+1.3v₂₃)v₁₃ + (-0.56v₁₂+0.01v₁₃+4.22v₂₃)v₂₃
  characteristic(B) = -8.15v₁ + 13.02v₂ - 6.5v₃ ; eigvals(B) = 1.31032v₁ + 1.87837v₂ + 3.31131v₃ ; eigpolys(B) = 2.16667v₁ + 4.34v₂ + 8.15v₃
  C = [2.0 0.1 0.2 0.3; 1.0 3.0 0.4 0.1; 0.5 0.7 1.5 0.2; 0.1 0.2 0.3 1.1]: det = 8.6522v ; characteristic = 8.6522v₁ - 22.114v₂ + 20.06v₃ - 7.6v₄
  eigvals(C) = 0.997754v₁ + 1.40762v₂ + 1.83212v₃ + 3.3625v₄ ; adjugate(C) = (4.469v₁-1.378v₂-0.857v₃+0.078v₄)v₁ + (0.014v₁+3.074v₂-1.416v₃-0.174v₄)v₂ + (-0.369v₁-0.68v₂+6.421v₃-1.594v₄)v₃ + (-1.153v₁+0.22v₂-0.805v₃+8.15v₄)v₄
  pfaffian(Chain{ℝ⁴,2}(1,2,3,4,5,6)) = 8.0v ; companion(1,2,3) = (0v₁+1v₂+0v₃)v₁ + (0v₁+0v₂+1v₃)v₂ + (-1.0v₁-2.0v₂-3.0v₃)v₃
cayley (docs/src/algebra.md:623-715), rows = left factor, columns = right factor, basis (v, v₁):
  Submanifold(1): ∧: [v v₁; v₁ 0]   ∨: [0 v; v v₁]   <: [v v₁; 0 v]   >: [v 0; v₁ v]   <<: [v v₁; 0 v]   >>: [v 0; v₁ v]
  S"-":           ∧: [v v₁; v₁ 0]   ∨: [0 v; v v₁]   <: [v v₁; 0 -1v] >: [v 0; v₁ -1v]
  Matrix(cayley(Submanifold(2))) = [v v₁ v₂ v₁₂; v₁ 1v v₁₂ 1v₂; v₂ -1v₁₂ 1v -1v₁; v₁₂ -1v₂ 1v₁ -1v]
docs/src/algebra.md:447: complexify(1+im) = 1 + 1im ; complexify(Chain(1,2)) = 1 + 2v₁₂ ; vectorize(1+2im) = 1v₁ + 2v₂ ; vectorize(Couple(1,2)) = 1v₁ + 2v₂
```

---------------------------------------------------------------------------------------------------

## 7. Dependencies on other chakravala packages

| package | symbols used by composite.jl |
|---|---|
| AbstractTensors | `TensorAlgebra, TensorGraded, TensorTerm, TensorMixed, Manifold, value, valuetype, scalar, isscalar, vector, bivector, volume, norm, isnull, ⟑/wedgedot, wedgedot_metric, contraction, log_metric, expm1/exp/cos/sin/sinh/cosh/sqrt/abs/inv/log/log1p/signbit wrappers (AT:597-605), Values, Variables, FixedVector, _diff, similar_type`, trig identities, pseudo/co family, `Postfix` operators |
| DirectSum | `Submanifold, Single, Zero, One, Infinity, Signature, DiagonalForm, diagonalform, metric, isinduced (via forms.jl), mdims, grade, basis, indices, indexbasis, Λ, ↓, getbasis, supermanifold, orand, submanifold` |
| Leibniz | `mvec, svec, svecs, insert_expr, cache_limit, gdims, binomial, indexbasis, d, ∂, ∇` (derivations), `list` conventions |
| StaticVectors | `Values` (immutable), `Variables` (mutable), `FixedVector`, broadcasting over them |
| AbstractLattices | `∧`, `∨` generics |
| Cartan (downstream, optional) | `points`, `isbundle`, `ChainBundle` for mesh helpers |
| Julia stdlibs | LinearAlgebra (`I`, `det`, `log(::Matrix)`, `eigen`, `eigvals` LAPACK), SparseArrays, Random |

---------------------------------------------------------------------------------------------------

## 8. Lean 4 porting notes

### 8.1 Types: indices vs runtime

* `V : Sig` (n, negative mask, zero mask, conformal flags) — **type index** (a `structure` with decidable
  equality, reducible defs for `bladeSqSign V B : Int`, `dim`). All Julia `@pure`/`@generated` decisions on
  `V` become `@[reducible]`/`@[specialize]` computations folded by the compiler.
* Grade `G : Nat`, blade `B : Fin (2^n)` (bitmask) — indices. `Couple V B`, `PseudoCouple V B` carry
  `[re, im] : Float × Float` at runtime; the elliptic/hyperbolic/parabolic branch is
  `match bladeSqSign V B with | -1 | 0 | 1` on an index → zero cost after specialization.
* Coefficient storage: `Chain V G := {v : FloatArray // v.size = Nat.choose n G}` or `Vector Float (choose n G)`;
  `Multivector V := Vector Float (2^n)`, `Spinor V := Vector Float (2^(n-1))`. Prefer `FloatArray` + size proof
  (unboxed); keep `Vector` for generic scalar types. Index order MUST follow §3.
* Matrices (Chain-of-Chain) → `Mat V W` column-major `FloatArray` of size `dim V * dim W` with the Chain view
  on demand; `TensorOperator` is a newtype.
* `hint` for `Chain`/`Multivector` is runtime (`isscalar` test); for `Couple`/`Single` it is static.
* Element kind dispatch (`Single`/`Couple`/`Chain`/`Spinor`/`Multivector`) → an inductive `Elem V` sum plus
  per-kind functions; do **not** replicate Julia's return-type promotion lattice with type classes
  (explodes instance search). Provide `toMultivector` normalisation for tests.

### 8.2 Where Julia gets its speed and how to match it

* `@generated` unrolled geometric products for n < 6 (`A:1829-1830`, `A:1843-1863`): every product in the
  series loops is straight-line code. Lean: implement the product as a loop over bitmask pairs with an
  on-the-fly sign `(-1)^{reorder(a,b) + popcount(a&b&negmask)}` and zero for `a&b&zeromask ≠ 0`
  (`reorder(a,b) = Σ_{k≥1} popcount((a >>> k) & b)`), specialized on `V` so `n` is a literal; the inner
  loop is `4^n` FMAs (1024 for n=5) — fine. Optionally precompute a `(index, sign)` table per `V` at compile
  time via `#eval`/`initialize` (Julia caches tables for n ≤ 8, `LZ:algebra_limit`).
* Spinor/Quaternion specialisations halve the work; keep separate `Spinor` product kernels.
* Series loops: allocate `S`, `term`, `out` once; update in place (unique `FloatArray` ⇒ destructive update).
* Closed forms dominate real workloads (rotors, Couples): make them `@[inline]` with no allocation.
* Matrix exp: Padé with at most 6 matrix products + one solve; use LU instead of Cramer for N ≥ 4 if you do
  not need bit-parity (Cramer is O(N!)-ish via wedges; fine for N ≤ 4).

### 8.3 Known Julia bugs / divergences — decide per item (recommend: implement the correct math, keep a
`JuliaCompat` flag or exclude these inputs from goldens)

1. `exp(Multivector|Spinor)` and `exp(Couple)` with nilpotent part (hint = 0) return `e^s(1+t)` instead of
   `e^s(1+mt)`; includes pure scalars (`exp(Multivector(2.0)) = 3e²`) (`C:90, C:104`).
2. `exp(Couple)` with `im = 0` (and B² ≠ 0) → NaN imaginary part (`C:105-106`); guard θ = 0 with sinc = 1.
3. Generated `cosh`/`sinh` (and hence `exph`, `cos/sin` of odd/mixed elements) throw `UndefVarError`
   (`C:491,496,549,554`: `$op` must be `$$op`). Implement per generic series.
4. `qlog_fast` broken (`$pinor`), unused.
5. PGA single-blade bivector → NaN (`C:143-146` with `u::Single`).
6. 2×2 real matrix exp with `v == 0` hangs (`C:215`).
7. `log(b::Real, t)` shadowed (`AT:401` vs `AT:330`).
8. `cbrt(elliptic Couple)` → MethodError.
9. `log_fast`/`logh_fast` unbounded loops; add a cap (e.g. 200) and return `Option`/`Except`.
10. `log(Zero)` hangs; `log1p(Zero)` ambiguity; generic `log` of non-versors errors (inv undefined).
11. `exp(Phasor)` wrong formula (`C:133`).
12. Hyperbolic `log`/`angle` ignore the sign of the real part; DomainError outside the light cone.
13. `expm1(Spinor(−c))` returns 0 (termination heuristic; `C:72` + `norms[3]=0`).
14. Quaternion `log/sqrt/cbrt` with zero bivector → NaN (no scalar guard, `C:442`, `C:632`).
15. Affine `in`, non-square `adjugate`, Couple element-wise ops, `rationalize(Couple)` are broken; mesh
    helpers need Cartan.
16. `coscalar`, `pseudodot` dangling exports; `Basesinc` typo (`C:411`).
17. `cos/sin` via pseudoscalar are only correct for central `I` with `I² = −1`.
18. Series accuracy ~1e-8…1e-12 (by design), including `log1p` of scalars and `cos(One)`.

### 8.4 Tricky semantics to preserve

* `isscalar` tolerance (≈1.7e-4 relative) chooses closed form vs series.
* Right-division everywhere (`a ⟑ inv b`); `inv` only defined when `~m⟑m` is single-grade.
* Series termination rule §4.1 exactly (it defines the numbers the oracle prints).
* The `(a[i]/k)·b[j]` product ordering in generated series (affects last-bit noise only).
* `norm` is the coefficient 2-norm (metric-free).
* `zero!` is a no-op except `-0.0 → +0.0`; `subzero` uses the ratio test.
* Output ordering of roots (quadratic ascending for real, cubic Viète ascending, one-real-root cubic puts the
  real root first only if it is `< x`, quartic returns second factor's roots first; ≥5 LAPACK `(re,im)` sort).
* `findfirst` returns 0 (not `none`).
* `compound(_, G > n)` throws a *string*.
* `in` uses `signbit`, so `-0.0` numerators matter.

### 8.5 What to skip / redesign

* `unabs!`, symbolic `Expr` paths, `Sym`/`SymField` generic-number plumbing, `@pure`, `Base.rand`
  samplers, SparseMatrixCSC overloads, `Requires` extensions — Julia-specific.
* The `_metric` twins: implement once with a `Metric` argument (a runtime bilinear form / outermorphism) only
  after the diagonal-metric version is solid; `isinduced g` → call the plain version.
* LAPACK-dependent paths (`log(Matrix)`, `eigen`, `eigvals` N ≥ 5, `vandermonde(Array)` QR) → native Lean
  implementations (Schur–Parlett or inverse scaling-and-squaring for `logm`; Francis QR for eigenvalues;
  Householder QR for least squares).

### 8.6 Proof hooks that pay for themselves

* `Fin`/size lemmas for `choose n G`, `2^n`, `2^(n-1)` storage (omega / `Nat.choose` simp).
* Blade sign algebra: `sign(a,b)·sign(b,a) = (−1)^{ga·gb − popcount(a&b)}·…`, reversion sign
  `(−1)^{g(g−1)/2}`, `bladeSqSign` — prove with `bv_decide` on `BitVec n` for fixed small n, or `decide`.
* Companion matrix: `charpoly (companion a) = X^n + Σ a_i X^i` (over a commutative ring; small `grind` proof
  for n ≤ 4 by expansion), and `characteristic` N ≤ 4 formulas equal Newton-identity expressions.
* Cramer: `inv t * t = I` for N ≤ 3 over `Int`/`Rat` by `decide`-style evaluation on symbolic polynomials
  (or `ring` if Mathlib is available); at least `#guard` tests on rationals (exact).
* Quadratic `quadratic` returns roots of `z² + a1 z + a0` (Vieta: sum = −a1, product = a0) over ℚ tests.
* PGA closed form: `(u + vI)(1/u − vI/u²) = 1` when `I² = 0` (one-line ring identity).

### 8.7 Suggested Lean module decomposition (rough LOC)

| module | contents | LOC |
|---|---|---|
| `Grassmann/Composite/Series.lean` | termination state machine §4.1, julia `≈`, `isScalarApprox` | 80 |
| `Grassmann/Composite/Exp.lean` | exp/expm1 for Single, Couple, PseudoCouple, Chain, Spinor, Multivector, Phasor, PGA, `Val hint` variants | 380 |
| `Grassmann/Composite/Log.lean` | qlog, log/log1p dispatch, Couple/Quaternion/Phasor logs, log_fast/logh_fast (capped), angle/radius, atanh2 | 330 |
| `Grassmann/Composite/Root.lean` | sqrt/cbrt | 70 |
| `Grassmann/Composite/Hyperbolic.lean` | cosh/sinh/exph + AbstractTensors trig/inverse identities | 260 |
| `Grassmann/Composite/Special.lean` | Zero/One/Infinity tables | 90 |
| `Grassmann/Composite/Pseudo.lean` | pseudo/co family, `@co`/`@pseudo` as Lean `macro` commands, geomabs/unit/counit | 110 |
| `Grassmann/Linalg/Cramer.lean` | prefix/suffix wedges, solve, in, inv, invdet, adjugate, cofactor, gradient, det | 380 |
| `Grassmann/Linalg/Compound.lean` | compound, pfaffian | 90 |
| `Grassmann/Linalg/MatrixExp.lean` | 1×1/2×2 closed forms, Padé 3/5/7/9/13 + scaling-squaring | 260 |
| `Grassmann/Linalg/Spectral.lean` | companion, characteristic(+exact), eigvals dispatch, Francis QR, eigpolys/sylvester/eigmults, cayley | 520 |
| `Grassmann/Poly/Roots.lean` | zero!/subzero/subsqrt, quadratic, cubic, cubicmax, quartic, monicroots* / roots* | 300 |
| `Grassmann/Linalg/Vandermonde.lean` | polynom, approx, vandermonde, interp (with own QR) | 150 |
| `Grassmann/Mesh/Simplex.lean` | affineframe, signscalar, find*, mean/centroid/barycenter, area, array/submesh | 170 |
| `Grassmann/Composite/Elementwise.lean` | map, div/rem/mod/…, round family, isfinite, rationalize, diff | 110 |
| `GrassmannTest/Composite*.lean` | JSONL golden loaders + tolerance comparators | 350 |
| **total** | | **≈ 3650** |

---------------------------------------------------------------------------------------------------

## 9. Oracle test plan

### 9.1 Encoding

One JSON object per line: `{"V": "<signature repr>", "fn": "<name>", "in": ENC, "status": "ok|err|hang",
"out": ENC?, "error": "<first line>"?}` with
`ENC = {"kind": "Couple|PseudoCouple|Chain|Spinor|CoSpinor|Multivector|Single|Real|Complex|Phasor|…",
"B": <blade bitmask, Couple/PseudoCouple only>, "full": [2^n coefficients in Multivector order]}` (Phasor:
`amp` + `angle.full`). Non-finite floats are encoded as the strings `"NaN"`, `"Inf"`, `"-Inf"`. Encoding everything as
the full 2^n vector makes the Lean comparator kind-agnostic; `kind` is compared separately (output kind is part
of the spec). A tested prototype is `.../scratchpad/comp/oracle_composite.jl` (runs each call on a worker
thread with a 5 s timeout because several Julia paths hang; aborts after 3 hangs since hung threads cannot be
killed; skips `log_fast/logh_fast` on non-elliptic Couples and on Chain/Multivector inputs).
Partial output from a run is in `.../scratchpad/comp/composite_goldens.jsonl`.

### 9.2 Functions × input distributions

| group | functions | inputs |
|---|---|---|
| Couple closed forms | exp, expm1, log, log1p, sqrt, cbrt, cosh, sinh, angle, radius, inv, ^n | every blade `B` of ℝ², ℝ³, ℝ⁴, `⟨-+++⟩`, `⟨1,1,1,0⟩`; (re, im) ~ N(0, σ²), σ ∈ {1e-3, 0.3, 2, 20}; edge: im = 0, re = 0, re < 0, |im| = |re| (hyperbolic), |im| > |re| |
| Single / Submanifold | exp, expm1, log, sqrt, cosh, sinh, cos, sin | every blade, coefficient ∈ {0, ±1e-8, ±0.5, ±3, ±50} |
| Chain | exp, expm1, log, sqrt, cosh, sinh, cos, sin | vectors (Euclidean, Minkowski timelike/spacelike/null), bivectors in 3D (simple → closed form), 4D (non-simple → series), PGA bivectors (Chain only), trivectors; include near-scalar-square cases around the 1.7e-4 isscalar threshold |
| Spinor / Quaternion | exp, expm1, log, log1p, sqrt, cbrt, log_fast | Euclidean 3D (closed-form log), `⟨-++⟩` (qlog path), norms 0.1–5; pure scalars ±; zero bivector |
| Multivector | exp, expm1 | 2D–5D random dense, scale 0.1–3; include `n = 6` to exercise the non-unrolled path |
| PseudoCouple | exp, expm1, log, log1p | B = scalar blade and non-scalar blades |
| Phasor | log, log1p, sqrt, inv, ^n, complexify, polarize (skip exp/expm1 or mark compat) | amplitude 0.1–5, angle bivector ±3 |
| series precision | expm1, cosh, sinh, qlog, log1p | graded norms 1e-6…30 to pin the termination rule (compare with 1e-12 once the Lean rule matches, 1e-7 before) |
| atanh(y,x) | 2-arg atanh | full special-case table §4.3.4 + random |y| < |x| both signs, Float32 and Float64 |
| matrix exp | exp, expm1 on Chain-of-Chain | 1×1…5×5 random with 1-norm in {0.01, 0.1, 0.5, 1.5, 3, 10, 50} (hits every Padé branch and scaling), 2×2 real with v>0, v<0, complex 2×2; **exclude v == 0** |
| Cramer family | `\`, inv, invdet, adjugate, cofactor, det, compound(G=0..N), in, gradient | N = 1..5 well-conditioned (cond < 1e3), Minkowski signatures (must equal Euclidean results), rank-deficient (det = 0 → Inf/NaN pattern), homogeneous simplices for `in`/`gradient`; non-square M < N for inv/invdet/`\` |
| pfaffian | pfaffian | 2D, 3D (vector result), 4D, 6D random bivectors |
| polynomials | roots, rootsreal, rootscomplex, monicroots*, cubicmax, quartic | products of chosen roots: distinct real, double/triple roots, complex pairs, mixed; coefficients scaled 1e-3…1e3; degrees 1–6 (≥5 compare as multisets sorted by (re,im)) |
| spectral | characteristic, eigvals*, eigpolys, companion, cayley(V, op) | N = 1..6 random; op ∈ {⟑, ∧, ∨, <, >, <<, >>} for n ≤ 3 (exact Int/±1 entries) |
| pseudo/co | every pseudo*/co* function | same distributions as base function after complement |
| special values | all functions in §4.18 on Zero/One/Infinity | exact table (status + value) |
| element-wise | map, round(digits), mod, div, isfinite, rationalize | random Chains/Multivectors |

### 9.3 Tolerances

* Closed forms (Couple, Single, simple Chain, quaternion log/sqrt, 2×2 matrix, Cramer, roots ≤ 4): relative
  1e-13 (absolute 1e-15 near zero).
* Series paths: 1e-10 relative if the Lean port reproduces §4.1 exactly, 1e-6 otherwise.
* Padé matrix exp: 1e-13 relative to the oracle (both ≈ 1e-15 from truth).
* LAPACK-backed paths (N ≥ 5 eigenvalues, matrix log): 1e-10 relative after sorting.
* Compare `status` exactly for error/NaN cases; treat `hang` records as "must terminate with an error/None"
  in Lean.
