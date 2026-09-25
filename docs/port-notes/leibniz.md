# Leibniz.jl → Lean 4 porting spec

Source: `/Users/alokbeniwal/chakravala/Leibniz.jl`, master `a319d27` (2026-01-12). `Project.toml` says version 0.3.1.
Oracle environment: Julia 1.13.0 with registered Leibniz **0.3.0**, which is loaded from `~/.julia/packages/Leibniz/jwJ5i`. Its source is identical to master except for one import line: master also imports `pseudoscalar` at `src/Leibniz.jl:31`. The environment also has Grassmann 0.8.46 and DirectSum `7b964d8`.
All `file:line` citations are relative to the Leibniz.jl repo root unless another package is named.
Every behaviour claimed below was checked in Julia, either by the probes in `scratchpad/probes/p*.jl` or by the oracle script (§9).

Ready-made oracle: `scratchpad/oracle/leibniz/leibniz_oracle.jl` writes 13 JSON golden files to `scratchpad/oracle/leibniz/golden/`. It has been run successfully (≈15 s, ≈1.3 MB).

---

## 1. Purpose & scope

Leibniz.jl is small: 1,129 lines in total, 1,047 of them in `src/`. It has two roles.

1. **Abstract differential operators** (`src/Leibniz.jl:107-175`):
   - `Derivation{T,O}` is a scalar coefficient times the formal operator `∂ₖ^O vₖ`.
   - It provides the constants `∇` (nabla) and `Δ = ∇^2` (Laplacian).
   - It declares the empty generic functions `differential`, `codifferential`, `boundary`, with aliases `d`, `δ`, `∂`. Their methods are defined downstream in Grassmann (`Grassmann.jl/src/Grassmann.jl:108-111`).
   - A Derivation only becomes a concrete multivector when a manifold is applied to it as a functor, `V(∇)`. Grassmann defines this at `Grassmann.jl/src/Grassmann.jl:88-106`.

2. **The foundation layer for DirectSum and Grassmann.** This is by far the larger role. When DirectSum's utilities moved here at v0.1.0 (commit `c90c0ee`, 2020-08-25), Leibniz took on:
   - bit-mask index algebra: `indices`, `indexbits`, `bit2int`, `lowerbits`=PEXT, `expandbits`=PDEP;
   - the combinatorial offset/rank tables for multivector storage: `binomsum*`, `spinsum*`, `antisum*`, `bladeindex`, `basisindex`, `spinindex`, `antiindex`, `indexbasis*`, `combo`;
   - grade-parity functions: reverse, involute, clifford, and the complement parities;
   - bit-level `complement`;
   - manifold-mode accessors with `Int` defaults (`grade`, `diffvars`, `dyadmode`, `hasinf`, …);
   - tangent/conformal masks: `diffmask`, `symmetricmask`, `diffcheck`, `mixed`, `combine`;
   - the whole index-label printing system: sub/superscript digit tables, alphanumeric indices past 9, the prefixes `v`/`w`/`∂`/`ϵ`, `printindices`, `printlabel`;
   - the coefficient printing helpers used by DirectSum/Grassmann `show`: `showvalue`, `showstar`, `showparens`;
   - the Euler characteristic `χ` / `count_gdims`;
   - code-generation helpers used by Grassmann's `@generated` functions: `insert_expr`, `mvec`, `svec`, …

**Historical `Monomial`.** The symmetric Leibniz monomial type `Monomial{V,G,D,O,T}` no longer exists. It was introduced in `f7cc9df` (2019-06-16) and deleted in `c90c0ee` (v0.1.0); the last copy is `git show c90c0ee^:src/Leibniz.jl`, lines 20-92. Its job, "∂ multi-indices with order ≤ μ", is now done by the **tangent-bundle bits of DirectSum basis masks**. Leibniz supports this through `diffvars`, `diffmode`, `diffmask`, `symmetricmask`, `diffcheck`, and the `∂`/`ϵ` label prefixes. **Do not port Monomial.**

**`symbolic.jl`** (the Reduce `@require` hook) was also removed (`src/Leibniz.jl:187-190`, commented out). Skip it.

**Port scope.**
- Port all live functions below, with the Julia-only items redesigned as listed in §8.4.
- Leibniz has to be ported **before** DirectSum, but its manifold accessors are *implemented* in DirectSum. The port therefore needs an abstract manifold interface (typeclass, §8.2).

---

## 2. Public API inventory

Legend:
- **E** = exported by `Leibniz`.
- **I:D / I:G / I:C / I:Cl** = explicitly imported, or used qualified, by DirectSum / Grassmann / Cartan+MeshTopology / Clifford.
- Downstream import lists: `DirectSum.jl/src/DirectSum.jl:34-48`, `DirectSum.jl/src/operations.jl:328,385`, `Grassmann.jl/src/Grassmann.jl:34-49,74`, `Grassmann.jl/src/parity.jl:15-16`, `Grassmann.jl/src/multivectors.jl:23,31`, `Grassmann.jl/src/algebra.jl:19-20`.

`names(Leibniz)` returns 65 exported symbols. **Four of them are exported but undefined** and throw `UndefVarError` if accessed:
- `Differential` (`src/Leibniz.jl:23`)
- `⊕`, `tangent`, `isorigin` (`src/generic.jl:6,166`)

DirectSum defines the last three. Several other exports are re-exports of AbstractTensors functions: `Manifold`, `basis`, `value`, `valuetype`, `norm`, `⋆`, `complementleft`, `complementright`, `complementlefthodge`, `complementrighthodge`.

### 2.1 Derivation operators (`src/Leibniz.jl`)

| Symbol (ASCII alias) | Signature | Semantics | Where | Flags |
|---|---|---|---|---|
| `Derivation{T,O}` | `struct Derivation{T,O}; v::UniformScaling{T}; end` | Coefficient `v.λ::T` times the operator `∂ₖ^O vₖ` (the `vₖ` factor is present only when O is odd). O is a *type parameter* (order). | `:109-111` | E |
| `Derivation{T}(v::UniformScaling{T})` | → `Derivation{T,1}(v)` | Default order 1. | `:113` | |
| `Derivation(v::UniformScaling{T})` | → `Derivation{T}(v)` | | `:114` | |
| `Nabla` | `const Nabla = Derivation{Bool,1}` | Type alias | `:162` | E |
| `Laplacian` | `const Laplacian = Derivation{Bool,2}` | Type alias | `:163` | E |
| `∇` (`nabla`) | `const ∇ = Derivation(LinearAlgebra.I)` | `Derivation{Bool,1}(UniformScaling(true))`; displays `∂ₖvₖ` | `:154,156` | E, I:G |
| `Δ` (`laplacian`) | `const Δ = ∇^2` | `Derivation{Bool,2}(I)`; displays `∂ₖ²v` | `:155-156` | E, I:G |
| `differential` (`d`) | `function differential end` | Empty generic. Grassmann: `d(ω) = Manifold(ω)(∇)∧ω` | `:158,161` | E, I:G |
| `codifferential` (`δ`) | `function codifferential end` | Grassmann: `δ(ω) = -∂(ω)` | `:159,161` | E, I:G |
| `boundary` (`∂`) | `function boundary end` | Grassmann: `∂(ω) = ω⋅Manifold(ω)(∇)`; for a Chain of Chains, `∧(ω)⋅Λ(W).v1` | `:160-161` | E, I:G |
| `show(io, ::Derivation{Bool,O})` | | See §5.6 | `:116` | |
| `show(io, ::Derivation{T,O})` | | See §5.6 | `:117` | |
| unary `-` | `-(::Derivation{Bool,O})` flips the Bool; `-(::Derivation{T,O})` negates λ | | `:119-120` | |
| `^` | `^(v::Derivation{T,O}, n::Integer) → Derivation{typeof(x),O*n}` | Bool: `x = isodd(n) ? λ : true`; else `x = λ^n` | `:122-126` | |
| `+ - *` (same O) | `op(a::Derivation{A,O}, b::Derivation{B,O}) = Derivation{promote_type(A,B),O}(op(a.v,b.v))` | **Order stays O, including for `*`.** | `:128-134` | |
| `+ - *` (with Number) | `op(a::Derivation{A,O}, b::Number)`, `op(a::Number, b::Derivation)` | Performs `op(UniformScaling, Number)`: fine for `*`; `+`/`-` throw `MethodError` | `:131-132` | |
| `unitype` | `unitype(::UniformScaling{T}) = T` | Internal | `:136` | |
| `/`, `\` | `a/b` (both Derivation, same O), `a/b::Number`, `a\b` (Derivation or Number on the left) | Coefficient division; result `T` = `unitype(x)` (e.g. Float64) | `:138-142` | |
| `op(::Derivation, ::TensorAlgebra)` and mirror, for `op ∈ (+,-,*,/,\,∧,∨,dot,cross)` | `op(a,b) = op(Manifold(b)(a), b)` | Materialises the Derivation in b's manifold, then applies op | `:147-152` | |
| docstrings | `∇, Nabla, nabla` and `Δ, Laplacian, laplacian` | | `:165-175` | |

### 2.2 Field/print-type registry (`src/Leibniz.jl`)

| Symbol | Definition | Semantics | Where | Flags |
|---|---|---|---|---|
| `parval` | `parval = (Expr,Complex,Rational,TensorAlgebra)` (**non-const global**) | Coefficient types printed in parentheses | `:63` | I:D, I:G |
| `parnot` | `parnot = (TensorTerm,)` (non-const global) | Types exempt from parentheses | `:64` | |
| `check_parval(::Type)` | true iff `T <: some parval` (eval-generated methods) | | `:66-70` | |
| `check_parnot(::Type)` | true iff `T <: some parnot`. Grassmann adds `Projector` (`Grassmann.jl/src/forms.jl:424`) | | `:67-73` | |
| `Fields` | `const Fields = (Real,Complex)` | | `:77` | I:D, I:G |
| `Field` | `const Field = Real` | | `:78` | I:G |
| `ExprField` | `const ExprField = Union{Expr,Symbol}` | | `:79` | I:G |
| `check_field(::Type)` | true for `<:Real` or `<:Complex`. Grassmann/ReduceExt add more | | `:81-84` | I:G |
| `extend_field(F=Field)` | `global parval = (parval...,F)` | Mutates a global | `:86` | I:G |
| `extend_parnot(F)` | `global parnot = (parnot...,F)` | Mutates a global | `:87` | I:G |
| `==(a::Real/Complex, b::TensorTerm{V,G})`, mirror | `G==0 ? a==value(b) : 0==a==value(b)` | A scalar equals a grade-0 term by value; it equals a higher-grade term only if both are 0 | `:89-94` | |
| `equal(a::TensorTerm, b::TensorTerm)` | `0 == value(a) == value(b)` | Fallback for terms on different bases (both must be zero). Extends `AbstractTensors.equal` | `:96` | |
| `getbasis(V,b)` | `getbasis(V,UInt(b))` | Integer→UInt shim; the real method is in DirectSum | `:105` | |

### 2.3 Utilities (`src/utilities.jl`)

| Symbol | Signature → result | Semantics | Where | Flags |
|---|---|---|---|---|
| `VTI` | `Union{Vector{Int},Tuple,NTuple}` | Index-list types | `:18` | I:D |
| `SVTI` | `VTI ∪ Values` | | `:19` | |
| `bit2int(b::BitVector)::UInt` | | `Σ b[i]·2^(i-1)`; empty → 0 | `:26-28` | I:D, I:G |
| `AbstractTensors.:-(::Values)`, `-(::Values{N,Any})`, `norm(::Values{N,Any})` | | Piracy shims: negation, and `sqrt(Σ zᵢ²)` | `:30-32` | |
| `gdimsall(N)` (`binomial_set`) | `→ Values{N+1,Int}` | `[C(N,0),…,C(N,N)]` | `:39-40` | E, I:D, I:G |
| `binomial` | `= AbstractTensors.gdims`, i.e. `Base.binomial(N,G)` | | `:40` | I:D, I:G |
| `gdimseven(N)` | `→ Values` | `[C(N,0),C(N,2),…]` | `:47` | E |
| `gdimsodd(N)` | `→ Values` | `[C(N,1),C(N,3),…]`. **Errors for N=0.** | `:54` | E |
| `intlog(M)` | `Int(log2(M))` | Exact log2 (InexactError if M is not a power of 2) | `:61` | I:D, I:G |
| `promote_type(t...)` | `Base.promote_type` | `@pure` alias | `:62` | I:D, I:G |
| `mvec(N,G,t)` | `Variables{C(N,G),t}` | Mutable static vector type | `:63` | I:D, I:G |
| `mvec(N,t)` | `Variables{2^N,t}` | | `:64` | |
| `svec(N,G,t)` | `FixedVector{C(N,G),t}` | | `:65` | |
| `svec(N,t)` | `FixedVector{2^N,t}` | | `:66` | |
| `mvecs(N,t)` | `Variables{2^(N-1),t}` | Half-size (even/odd subalgebra) | `:67` | I:G |
| `svecs(N,t)` | `FixedVector{2^(N-1),t}` | | `:68` | I:G |
| `assign_expr!(e,x,v,expr)` | | Pushes `:(v = expr)` into x if `v ∈ e` | `:72` | |
| `insert_expr(e, vec=:mvec, T, S, L; mv=0)` | `→ Vector{Any}` of assignment Exprs | Code-gen preamble for Grassmann `@generated` functions (§4.12). 124 uses in Grassmann | `:74-96` | I:D, I:G |
| `algebra_limit` | `= 8` | DirectSum: dimensions above this use extended (lazy) algebras | `:104` | I:D, I:G |
| `sparse_limit` | `= 22` | Cache split for combos/indexbasis/cumsums | `:105` | I:D, I:G |
| `cache_limit` | `= 12` | Cache split for blade/basis/spin/anti index and lowerbits | `:106` | I:D, I:G |
| `fill_limit` | `= 0.5` | Sparse→dense fill threshold (used downstream) | `:107` | I:D, I:G |
| `combinations` | re-export of `Combinatorics.combinations` | Used as `Leibniz.combinations` by Cartan/MeshTopology | `:109` | I:C |
| `combo(n::Int, g::Int)::Vector{Vector{Int}}` | | All g-subsets of `1:n`, lexicographic. `g==0 → [Int[]]`. **g>n with n≤22 → UndefRefError** | `:111-133` | I:D, I:G |
| `binomsum(n,i)::Int` | | `Σ_{q<i} C(n,q)`, i ∈ 0..n+1 (0-based offset of grade i) | `:138-161` | E, I:D, I:G |
| `spinsum(n,i)` | | `Σ_{q<i, q even} C(n,q)` | same | E, I:G |
| `antisum(n,i)` | | `Σ_{q<i, q odd} C(n,q)` | same | E, I:G |
| `binomcumsum(n)` (`binomsum_set`) | `→ Values{n+2,Int}` | `[binomsum(n,0..n+1)]` | `:162-176,179` | E, I:D, I:G |
| `spincumsum(n)` (`spinsum_set`) | | | same | E, I:D, I:G |
| `anticumsum(n)` (`antisum_set`) | | | same | E, I:D, I:G |
| `bladeindex(n::Int, s::UInt)::Int` | | 1-based lexicographic rank of mask s within its grade | `:181-219` | E, I:D, I:G |
| `basisindex(n,s)` | | `binomsum(n,|s|) + bladeindex(n,s)`: 1-based position in the full multivector | `:185` | E, I:D, I:G |
| `spinindex(n,s)` | | `spinsum(n,|s|) + bladeindex`: 1-based position in the even subalgebra (valid only for even \|s\|) | `:186` | E, I:G |
| `antiindex(n,s)` | | `antisum(n,|s|) + bladeindex`: 1-based position in the odd part (valid only for odd \|s\|) | `:187` | E, I:G |
| `index2int(k,c)` | `bit2int(indexbits(k,c))` | Index list → mask | `:221` | |
| `indexbasis(n::Int, g::Int)::Vector{UInt}` | | Masks of grade g in lexicographic combo order; `g==0 → [0]` (for n ≤ 22) | `:222-244` | E, I:D, I:G |
| `indexbasis(N)` | `→ Vector{UInt}` of length 2^N | Grade-major concatenation. **Errors for N ∈ {0,1}** | `:245` | E |
| `indexbasis_set(N)` | `→ Values{N,Vector{UInt}}` (N<22: grades 1..N) or `Values{N+1}` (N≥22: grades 0..N) | **Inconsistent shape across the 22 boundary** | `:246` | I:D, I:G |
| `indexeven(N)`, `indexeven_set(N)` | | **Buggy**: for N<22 identical to `indexbasis`/`indexbasis_set`; for N≥22 contains grade 0 twice | `:247-248` | E |
| `indexodd(N)`, `indexodd_set(N)` | | **Buggy**: N<22 identical to `indexbasis`; N≥22 includes `[0]` then the odd grades | `:249-250` | E |
| `lowerbits(N,S,B)::UInt` | | = `pext(S, B)`: bits of S at the positions of B's set bits. **Cache is history-dependent (bug)** | `:254-276` | E, I:D, I:G |
| `lowerbits_calc(N,S,B)` | | Correct reference implementation | `:256` | |
| `expandbits(N,S,B)::UInt` | | = `pdep(B, S)`: deposit the low bits of B into the set positions of S. BoundsError if B has more bits than popcount(S) | `:278-287` | E, I:D, I:G |

### 2.4 Generic manifold API (`src/generic.jl`)

Exports: `:5-7`, `:32`, `:166`, `:245`.

| Symbol (alias) | Signature | Semantics | Where | Flags |
|---|---|---|---|---|
| `grade(::Type{<:TensorGraded{V,G}})` | `G - (isdyadic(V) ? 2 : 1)*diffvars(V)` | DirectSum overrides for `Submanifold`/`Single` | `:9` | E, I:D, I:G |
| `pseudograde(::Type{<:TensorGraded{V,G}})` (`antigrade`) | `mdims(V) - G - k·diffvars(V)` | | `:10,33` | E, I:D, I:G |
| `pseudograde(V::Manifold)` | `mdims(V) - rank(V) - k·diffvars(V)` | For a full manifold rank = mdims, so the result is −k·diffvars (e.g. −1 for `tangent(ℝ^3)`) | `:11` | |
| `grade(V::Manifold)` | `rank(V) - k·diffvars(V)` | Number of Grassmann (non-diff) dimensions, v and w both counted for dyadic V | `:12` | |
| `grade(::Real)` | `= 0` | | `:13` | |
| `order(m)` | `= 0` | | `:14` | E, I:D, I:G |
| `order(V::Manifold)` | `= diffvars(V)` | | `:15` | |
| `options(::Int)` | `= 0` | | `:16` | E, I:D |
| `metric(::Int)` | `= zero(UInt)` | | `:17` | E, I:D, I:G |
| `metric(V::Manifold, b::UInt)` | `PROD(V[indices(b)])` | Product of diagonal metric entries over b (e.g. `S"-++"`, b=0b011 → −1). **No Int method** (MethodError) | `:18` | |
| `polymode(::Int)` | `= true` | | `:19` | E, I:D |
| `dyadmode(::Int)` (`mixedmode`) | `= 0` | <0 dyadic V⊕V′, >0 dual V′, 0 plain | `:20,33` | E, I:D, I:G |
| `diffmode(::Int)` | `= 0` | Tangent order μ | `:21` | E, I:D, I:G |
| `diffvars(::Int)` | `= 0` | Number of tangent variables ν | `:22` | E, I:D, I:G |
| mode forwarding | `options, polymode, dyadmode, diffmode, diffvars` of a `TensorAlgebra` value or type → apply to `Manifold(t)` | | `:23-28` | |
| `≅(a,b)` | `grade(a)==grade(b) && order(a)==order(b) && diffmode(a)==diffmode(b)` | Same kind of element. No ASCII alias; suggest `sameKind` | `:30` | E, I:D |
| `isdyadic(t)` | `dyadmode(Manifold(t)) < 0` | Methods for types, values and Int (false) | `:34,37,42` | E, I:D |
| `isdual(t)` | `dyadmode(...) > 0` | | `:35,38,43` | E, I:D |
| `istangent(t)` | `diffvars(...) ≠ 0` | | `:36,39,44` | E, I:D |
| `isbasis(x)` | false for anything except DirectSum `Submanifold` basis | | `:41,48-50` | E, I:D |
| `value_diff(m::TensorTerm)` | `(v=value(m); istensor(v) ? v : m)` | Unwrap a tensor-valued coefficient | `:46` | |
| `UInt(m::TensorTerm)` | `UInt(basis(m))` | Bit mask of a term | `:51` | |
| `hasconformal(V)` | `hasinf(V) && hasorigin(V)` | | `:53` | I:D, I:G |
| `hasinf(::Int)`, `hasorigin(::Int)` | `false` | | `:54,57` | E, I:D, I:G |
| `hasinf(t::Manifold)`, `hasorigin(t::Manifold)` | forward to `Manifold(t)` | | `:55,58` | |
| `hasorigin(V, B::UInt)` | `hasinf(V) ? (B&2)==2 : isodd(B)` | Does blade B contain ∅? **Does not check hasorigin(V)** | `:61` | |
| `hasinf(V,A,B)` | `hasconformal(V) && (isodd(A) \|\| isodd(B))` | | `:63` | |
| `hasorigin(V,A,B)` | `hasconformal(V) && (hasorigin(V,A) \|\| hasorigin(V,B))` | | `:64` | |
| `hasinf2(V,A,B)` | `hasconformal(V) && isodd(A) && isodd(B)` | | `:66` | |
| `hasorigin2(V,A,B)` | `hasconformal(V) && hasorigin(V,A) && hasorigin(V,B)` | | `:67` | |
| `diffmask(::Int)` | `0` | | `:69` | I:G |
| `diffmask(V)` | `UInt`, or `(UInt,UInt)` if dyadic | §4.7 | `:70-80` | I:G |
| `symmetricsplit(V,a)` | dyadic: `(sm&dm[1], sm&dm[2])`; else `sm` | | `:82-85` | I:G |
| `symmetricmask(V,a)` | `a & D` (D = union of diff masks) | | `:87-90` | I:D, I:G |
| `symmetricmask(V,a,b)` | `(a&~D, b&~D, (a&D)\|(b&D), (a&D)&(b&D))` | | `:92-97` | |
| `diffcheck(V,A,B)` | Bool | "Product is zero" test (§4.7) | `:99-105` | I:G |
| `mixed(V, ibk::UInt)` | `UInt` | Embed a V (or V′) mask into V⊕V′. **MethodError for dyadic tangent V** (tuple diffmask) | `:109-117` | I:D, I:G |
| `combine(v,w,iak,ibk)` | `UInt` | Direct-sum embedding of two masks; errors if dualities differ | `:119-130` | I:D |
| `loworder(N::Int)` | `= N` | DirectSum defines it for manifolds | `:134` | I:D, I:G |
| `supermanifold(N::Int)` | `= N` | | `:135` | I:D, I:G |
| `parityreverse(G)` (`parityconj`) | `isodd(G(G-1)/2)` | Sign of reversion for grade G | `:139,142` | I:D, I:G |
| `parityinvolute(G)` | `isodd(G)` | | `:140` | I:D, I:G |
| `parityclifford(G)` | `parityreverse(G) ⊻ parityinvolute(G)` | | `:141` | I:D, I:G |
| `grade_basis(V::Int,B)` | `B & (2^V - 1)` | | `:146` | I:G |
| `grade_basis(V,B)` | `B & (2^grade(V) - 1)` | Strip the diff bits | `:147` | |
| `grade(V, B::UInt)` | `count_ones(grade_basis(V,B))` | | `:148` | |
| `pseudograde(V::Int, B)` | `V - grade(V,B)` | | `:152` | |
| `pseudograde(V, B)` | `grade(V) - grade(V,B)` | | `:153` | |
| `isless`, `<=` on grade-0 `TensorTerm` vs term/number | compare `value`s | | `:157-162` | |
| `χ(t::TensorAlgebra)` | `sum(B[t]*(-1)^t for t ∈ 1:length(B))` with `B = count_gdims(t)` | **Sign: = −Σ_p (−1)^p b_p** (1-based offset), the opposite of the docstring | `:173` | E, I:G |
| `χ(t::TensorTerm)` | `χ(Manifold(t), UInt(basis(t)), t)` | | `:174` | |
| `χ(V,b,t)` | `iszero(t) ? 0 : isodd(|Grassmann bits of b|) ? 1 : -1` | | `:175` | |
| `count_gdims(t::TensorTerm)` | `Variables{N+1,Int}`: `abs(χ(t))` at grade g, 0 elsewhere | | `:177-181` | E, I:G |
| `count_gdims(t::TensorGraded{V,G})` | Counts nonzero components per Grassmann grade | | `:182-190` | |
| `∪(x::Manifold)`, `∪(a,b,c...)`, `∩` likewise | Variadic folds. Binary methods are in DirectSum | | `:194-198` | |
| `parityright(V::Int,B::Int,G,N=nothing)` | `isodd(B + G(G+1)/2)` | B = **sum of 1-based indices** | `:204` | I:D, I:G |
| `parityleft(V::Int,B::Int,G,N)` | `(isodd(G) && iseven(N)) ⊻ parityright` | | `:205` | I:D, I:G |
| `parityrighthodge(V::Int,B::Int,G,N=nothing)` | `isodd(V) ⊻ parityright` | V = number of negative-metric vectors in the blade | `:202` | I:D, I:G |
| `paritylefthodge(V::Int,B::Int,G,N)` | `(isodd(G)&&iseven(N)) ⊻ parityrighthodge` | | `:203` | I:D, I:G |
| `parityright(V::UInt,B::UInt,N::Int)` etc. | `p(0, sum(indices(B,N)), count_ones(B), N)`; hodge variants use `count_ones(V&B)` as first argument (V = metric bitmask) | | `:213-214` | |
| `parityrightnull(V,B,v)`, `parityleftnull` | `hasconformal(V) && count_ones(B&3)==1 ? (isodd(B) ? 2v : v/2) : v` | Null-basis rescaling for complements | `:215-219` | I:D |
| `parityrightnullpre`, `parityleftnullpre` | Same, but builds `Expr` (`:(2*v)`, `:(v/2)`) | Code-gen | `:220-224` | I:D, I:G |
| `complement(N::Int, B::UInt, D::Int=0, P::Int=0)::UInt` | | Bit complement with diff/conformal handling (§4.6) | `:233-237` | I:D, I:G |
| `complementleft/right/lefthodge/righthodge`, `⋆` | | AbstractTensors generics, documented here (`:247-269`) | `:241,245` | E |
| `LinearAlgebra.reflectorApply!(x, τ::TensorAlgebra, A)` | | Householder application with TensorAlgebra τ (QR over multivectors) | `:273-297` | |

### 2.5 Indices and printing (`src/indices.jl`)

| Symbol | Value / signature | Semantics | Where | Flags |
|---|---|---|---|---|
| `vio` | `('∞','∅')` | Labels of the infinity/origin indices (−1, 0) | `:6` | I:D |
| `digs` | `"1234567890"` | | `:7` | |
| `low_case`, `upp_case` | `"a…z"`, `"A…Z"` | | `:8` | |
| `low_greek`, `upp_greek` | 24- and 22-character strings | **Unused** (commented out of the alphanum tables) | `:9` | |
| `alphanumv` | `digs*low_case*upp_case` (62 chars) | Vector index alphabet | `:10` | I:D |
| `alphanumw` | `digs*upp_case*low_case` (62 chars) | Covector index alphabet | `:11` | I:D |
| `subs::Dict{Int,Char}` | −1→'∞', 0→'∅', 1..9→'₁'..'₉', 10→'₀', 11..36→`alphanumv[11..36]`='a'..'z' | | `:14-28` | I:D |
| `sups::Dict{Int,Char}` | −1→'∞', 0→'∅', 1..9→'¹'..'⁹', 10→'⁰', 11..36→`alphanumw[11..36]`='A'..'Z' | | `:31-45` | I:D |
| `pre` | `("v","w","∂","ϵ")` | Default prefixes: vector, covector, diff (∂), dual diff (ϵ, U+03F5) | `:48` | I:D, I:G |
| `PRE` | `("X","x","Y","y")` | ASCII prefixes for `indexstring`/`indexsymbol` | `:49` | I:D |
| `vsn` | `(:V,:VV,:W)` | Default names for the manifold variable in `@basis`/`@dualbasis`/`@mixedbasis` | `:52` | I:D, I:G |
| `VSN` | `(:Χ,:ΧΧ,:Υ)` | Greek Chi/Upsilon variants. Unused downstream | `:53` | |
| `indexbits(N, indices)::BitVector` | | `falses(N)` with the given 1-based positions set | `:62-68` | I:D, I:G |
| `index_limit` | `= 20` | | `:70` | |
| `digitsfast(b,N)` (`digits_fast`) | `→ Values{N+1,Int}` | Little-endian binary digits of b padded to N+1. **UB/UndefRefError if b ≥ 2^(N+1) for N ≤ 20** | `:73-98` | I:G |
| `indices(b::UInt)` | `→ Vector{Int}` | Ascending 1-based positions of set bits | `:106` | E, I:D, I:G |
| `indices(b::UInt, N::Int)` | `→ Vector{Int}` | The same **(N is effectively ignored)**. Result is cached in a global Dict keyed only on b and shared: callers must not mutate it (DirectSum copies before `shift_indices!`) | `:107-119` | |
| `shift_indices(V::Manifold, b)` | `shift_indices(supermanifold(V), b)` | DirectSum overrides for `TensorBundle` and `Submanifold` (`DirectSum.jl/src/DirectSum.jl:403-404`) | `:121` | I:D |
| `shift_indices!(s::Manifold, set)` | | Conformal renumbering in place (§4.9) | `:122-132` | I:D |
| `shift_indices(V::Int, b)` | `indices(b,V)` | | `:134` | |
| `shift_indices!(s::Int, set)` | identity | | `:135` | |
| `printindex(i, l=false, e=pre[1], pre=pre)` | `→ Char` or `Int` | §5.1 | `:139-142` | |
| `printindices(io, b::UInt, l, e, pre)` | `printindices(io, indices(b), l, e, pre)` | | `:144` | I:D, I:Cl |
| `printindices(io, b::VTI, l, e, pre)` | `print(io, e, printindex.(b)...)` | | `:145` | |
| `printindices(io, a, b, l, e, f)` | 4-list form with c = d = [] | | `:146` | |
| `printindices(io, a, b, c, d, l, e, f, g, h)` | | §5.2 | `:147-154` | |
| `printindices(io, V::Int, e::UInt, label=false)` | `printlabel(io, V, e, label, pre...)` | DirectSum defines the `Manifold` method using `namelist(V)` | `:156` | |
| `printlabel(io, V::Int, e, label, vec, cov, duo, dif)` | `printindices(io, indices(e,V), label, vec)` | | `:157-160` | I:D |
| `printlabel(io, V::Manifold, e, label, vec, cov, duo, dif)` | | §5.3 | `:162-181` | |
| `printlabel(V::Manifold, e, label, vec, cov, duo, dif)::String` | | String-returning variant | `:183` | |
| `showparens(T)` | `!check_parnot(T) && check_parval(T)` | | `:185` | |
| `showstar(io, v)` | | §5.5 | `:187-193` | I:G |
| `showvalue(io, V, B::UInt, i)` | | Coefficient then label (§5.5). Used by `Single` show and Multivector show | `:195-203` | I:D, I:G |
| `indexstring(V::Manifold, D)::String` | `printlabel(io, V, D, true, PRE...)` | ASCII-ish label, e.g. `X12`, `Y1X1` | `:205-209` | I:G |
| `indexsymbol(V, D)::Symbol` | `Symbol(indexstring(V,D))` | | `:211` | I:G |
| `indexsplit(B, N)::Vector{UInt}` | `[1<<(k-1) for k ∈ indices(B,N)]` | Split a blade into its single-bit vectors | `:213` | I:G |
| `indexparity!(ind::Values{N,Int})` | `→ (Bool, Variables)` | Gnome-sort with permutation parity (§4.8) | `:215-229` | I:D, I:C |
| `indexparity!(ind::Vector{Int}, s)` | `→ (Bool, Vector, Bool)` | Sort with metric contraction of equal pairs (§4.8). **Buggy** | `:230-247` | I:D |

### 2.6 Module initialisation (`src/Leibniz.jl:180-185`)

At load time (baked into precompile) Leibniz calls:
- `bladeindex(12,1)`, `basisindex(12,1)`, `spinindex(12,1)`, `antiindex(12,1)`, which fill the per-n caches for all n ≤ 12 and, as a side effect, `indices_cache` for every b < 4096;
- `indexbasis(17,1)`, which fills `indexbasis_cache` for n ≤ 17.

The Lean port should not replicate these caches (§8.3).

---

## 3. Data representations

### 3.1 Basis masks

- **Type.** A blade is a `UInt` (UInt64) bitmask. Bit `k-1` (LSB = bit 0) represents index `k`, which is 1-based everywhere in the Julia code. For example `0b1011` ↔ indices `[1,2,4]` (`indices(UInt(0xb)) == [1,2,4]`).
- **Size limits.** Masks cap the dimension at 64. Printing supports indices only up to 62 (§5.1).
- **Grade** = `count_ones(mask)` for plain spaces. With tangent/dyadic structure, only the "Grassmann bits" are counted: `grade(V,B) = count_ones(B & (2^grade(V) - 1))`.
- **Bit-layout conventions.** These are fixed by DirectSum and hard-coded in Leibniz's `diffmask`, `mixed`, `printlabel`, `hasorigin(V,B)` and `complement`. Let N = `mdims(V)`, n = number of Grassmann dimensions, d = `diffvars(V)`.

  | Space kind | Low bits → high bits |
  |---|---|
  | plain `ℝ^n` | `[v₁ … vₙ]` |
  | conformal `S"∞∅…"` | bit0 = `∞` (only if hasinf), next bit = `∅` (only if hasorigin), then `v₁…` |
  | dual `V′` (dyadmode>0) | same layout, printed with `w` and superscripts |
  | tangent `tangent(V,μ,d)` (N = n+d) | `[v₁…vₙ][∂₁…∂_d]`; `diffmask = (2^d−1) << (N−d)` |
  | dual tangent | `[w…][ϵ…]` |
  | dyadic `V⊕V′` (dyadmode<0, N = 2n) | `[v₁…vₙ][w¹…wⁿ]` |
  | dyadic tangent (N = 2n+2d) | `[v₁…vₙ][w¹…wⁿ][∂₁…∂_d][ϵ¹…ϵ^d]`; `diffmask = ((2^d−1)<<(N−2d), (2^d−1)<<(N−d))` |

  Verified: `diffmask(tangent(ℝ^3)) = 0x8`, `diffmask(tangent(ℝ^2,2,2)) = 0xc`, `diffmask(tangent((ℝ^2)')) = 0x4`, `diffmask(tangent(ℝ^2⊕(ℝ^2)')) = (0x10,0x20)`, `diffmask(tangent(ℝ^1)⊕tangent(ℝ^1)') = (0x4,0x8)`.

### 3.2 Multivector component ordering

This is the **most important convention to get right**; every Grassmann golden depends on it.

- **Grade-major.** Within a grade, blades come in **lexicographic order of their sorted index lists**, which is *not* numeric mask order. Example: `indexbasis(4,2) = [0b0011, 0b0101, 0b1001, 0b0110, 0b1010, 0b1100] = [3,5,9,6,10,12]`.
- **Full multivector**, position (1-based) of mask s = `basisindex(n,s) = binomsum(n, |s|) + bladeindex(n, s)`. For N=4, `basisindex` over s = 0..15 is `[1,2,3,6,4,7,9,12,5,8,10,13,11,14,15,16]`.
- **Even subalgebra** (spinor, length 2^(n−1)): grades 0,2,4,… in the same order; `spinindex = spinsum(n,|s|) + bladeindex`.
- **Odd part**: grades 1,3,…; `antiindex = antisum(n,|s|) + bladeindex`.
- **Cumulative offsets** (0-based start of grade g) are `binomcumsum(n)[g+1]`. Examples: `binomcumsum(4) = [0,1,5,11,15,16]`, `spincumsum(4) = [0,1,1,7,7,8]`, `anticumsum(4) = [0,0,4,4,8,8]`. The last entry is the total length.

### 3.3 Label indices

- Printing uses a separate signed index: −1 = ∞, 0 = ∅, 1.. = ordinary.
- `shift_indices` computes it from mask indices by removing the conformal slots (§4.9).
- Tangent/dual diff indices are renumbered from 1 by subtracting an offset inside `printlabel` (§5.3).

### 3.4 `Derivation{T,O}` (`src/Leibniz.jl:109`)

- **Fields.** One field `v::UniformScaling{T}`, whose only content is `v.λ::T`. `T` is the coefficient type; **`Bool` is special**: `true` means +1 and `false` means −1 (a sign, not 0/1).
- **Type parameters.** `O::Int` is the order. It is a compile-time type parameter, and `^` computes a new one from the runtime exponent (`O*n`).
- **Invariants.** None are enforced. `O` may be 0 (`∇^0`) or negative (`∇^k` with a runtime negative k).

### 3.5 Tables and constants

- `subs` and `sups` are `Dict{Int,Char}` with keys −1..36.
- `alphanumv`/`alphanumw` are 62-char `String`s.
- `pre`/`PRE` are 4-tuples of `String`; `vio` is a 2-tuple of `Char`.

### 3.6 Compile-time vs runtime in Julia

- **Compile-time:** everything about the manifold `V`: dimension, options (conformal / dyadic / polymode), metric bits, tangent `(μ, ν)`, name index. These are type parameters of DirectSum's `Signature{N,M,S,F,D,L}`. So `diffmask(V)`, `hasinf(V)` and similar are `@pure` constant-folded at compile time. Grade `G` and the basis mask `B` are also type parameters (of `Submanifold{V,G,B}` and `Single{V,G,B,T}`).
- **Runtime:** coefficient values. The cache lookups `bladeindex` and friends run at **code-generation time** inside Grassmann's `@generated` functions when `N ≤ cache_limit` / `algebra_limit`, and at runtime in loops for larger (sparse) N.

---

## 4. Algorithms

### 4.1 Bits

```
bit2int(bits) = Σ_{i: bits[i]} 2^(i-1)                               # utilities.jl:26
indexbits(N, idx) = BitVector of length N with idx set (1-based)     # indices.jl:62
indices(b)        = [i+1 for i in 0..63 if bit i of b]               # indices.jl:106 (also the 2-arg form)
indexsplit(B,N)   = [1<<(k-1) for k in indices(B)]                   # indices.jl:213
digitsfast(b,N)   = [bit 0 of b, …, bit N of b]  (length N+1, Int 0/1)   # indices.jl:80
                    N==0 → [0] regardless of b
lowerbits(N,S,B)  = pext(S,B):  j=0; r=0; for i in 0..63 where B has bit i:
                                   if S has bit i: r |= 1<<j;  j += 1
expandbits(N,S,B) = pdep(B,S):  j=0; r=0; for i in 0..63 where S has bit i:
                                   if B has bit j: r |= 1<<i;  j += 1
```

- Both `lowerbits_calc` (`utilities.jl:256`) and `expandbits_calc` (`:279`) match pext/pdep exactly. The oracle checked exhaustively: N=5 for lowerbits, N=8 for expandbits with in-range B.
- *Meaning:* for a submanifold `S ⊂ V` and an ambient blade `B ⊆ S`, `lowerbits(S,B)` gives B's coordinates in S's local basis. `expandbits(S,b)` maps a local blade b back to the ambient mask.
- **Cache bug:** `lowerbits` (`utilities.jl:270-273`) fills rows `s = len+1..S` using `k = indices(S)` (the queried S), not `indices(s)`. Rows for `s < S` created in the same batch are therefore wrong until overwritten, which never happens. Reproduction in a fresh process: `lowerbits(4,0b1011,0b1010)` gives 3 (correct), then `lowerbits(4,0b0011,0b1010)` gives **3**, where pext gives 1.
  - **Port:** implement pure pext. Generate goldens from `lowerbits_calc`.

### 4.2 Combinatorics and index ranks

- **Binomial sums** (`utilities.jl:135-137`):
  - `binomsum_calc(n) = [0, cumsum(C(n,0..n))...]` (length n+2)
  - `spinsum_calc(n)` uses `C(n,q)` for even q and 0 for odd q; `antisum_calc(n)` is the reverse.
- **Cache seeding bug** (`utilities.jl:145`): the caches start as `[Values(0), Values(0,1)]`, so the entries for n=0 and n=1 are placeholders, not `calc(0)`/`calc(1)`:

  | n | `binomcumsum` | correct | `spincumsum` | correct | `anticumsum` | correct |
  |---|---|---|---|---|---|---|
  | 0 | `[0]` | `[0,1]` | `[0]` | `[0,1]` | `[0]` | `[0,0]` |
  | 1 | `[0,1]` | `[0,1,2]` | `[0,1]` | `[0,1,1]` | `[0,1]` | `[0,0,1]` |

  Consequences: `antisum(1,1)=1` (correct: 0), `antiindex(1,0b1)=2` (correct: 1), and `binomsum(1,2)` reads out of bounds. From n ≥ 2 onward everything is correct.
  - **Port:** use the correct formulas. Mark n<2 goldens as quirks.
- **`bladeindex` closed form.** The combinatorial number system in lexicographic order. It equals Leibniz for all n ≤ 14 and all masks (exhaustively verified), and for spot checks at n=25.

  ```
  bladeindex(n, s):                     # 1-based
    if s == 0: return 1
    k = popcount(s);  r = C(n,k) - 1
    i = 1
    for c in indices(s) ascending:      # c is 1-based
        r -= C(n - c, k - i + 1);  i += 1
    return r + 1
  ```

- **Julia's actual paths** (`utilities.jl:196-217`):
  - `s==0 → 1`;
  - `n > index_limit (20)` → `bladeindex_calc`, a linear `findfirst` over `combo(n,k)`. This is O(C(n,k)) and infeasible for n≈40, k≈20;
  - `12 < n ≤ 20` → per-n `Vector{Int}` of length 2^n−1, filled lazily with −1 as the sentinel;
  - `n ≤ 12` → full eager tables.
  - `basisindex`, `spinindex` and `antiindex` are `sum(n,k) + bladeindex(n,s)`.
- **Unrank** (`indexbasis(n,g)`, `utilities.jl:222`): the masks of `combo(n,g)` in order. Pseudocode for element r (0-based):

  ```
  unrank(n, g, r): mask=0; x=1
    for i in 1..g:
      while C(n - x, g - i) <= r: r -= C(n - x, g - i); x += 1
      mask |= 1 << (x-1); x += 1
  ```

  The oracle verified that `bladeindex(n, indexbasis(n,g)[i]) == i` for all n ≤ 10.
- **`combo(n,g)`** (`utilities.jl:114-133`): `g==0 → [[]]`; otherwise a cached `collect(combinations(1:n,g))` in lexicographic order. When n ≤ 22 and g > n: `UndefRefError`.
- **`indexbasis(N)`** (`:245`) is `vcat([0], grades 1..N)`. It errors for N ∈ {0,1} (splat of a single Vector into `Values`).
- **`indexeven`/`indexodd`** (`:247-250`): the `_set` variants ignore the grade filter whenever `0<N<22`, so both return all grades. For N ≥ 22, `indexeven` has the scalar twice and `indexodd` starts with the scalar. Nothing downstream calls them except DirectSum `grade.jl:26`, which forwards `Grade{N}` specialisations.
  - **Port:** provide correct `indexEven`/`indexOdd` (the even and odd masks in spin/anti order). Record the Julia quirk; don't golden-test the Julia outputs.
- **`gdimsall/gdimseven/gdimsodd`** (`:39-54`): `[C(N,g)]` for g in 0..N, 0,2,…,≤N and 1,3,…,≤N. `evenvalues(1,N)` builds `Values{((N-1)÷2)+1}(1:2:N...)`; for N=0 this errors.

### 4.3 Grade parities (`generic.jl:139-142`)

| G mod 4 | 0 | 1 | 2 | 3 |
|---|---|---|---|---|
| `parityreverse` (= `parityconj`) — sign of `~` | F | F | T | T |
| `parityinvolute` — grade involution | F | T | F | T |
| `parityclifford` — Clifford conjugate | F | T | T | F |

`true` means the component is negated. The oracle confirms G = 0..8 and dumps G = 0..64.

### 4.4 Complement parities (`generic.jl:202-214`)

Let the blade have sorted 1-based indices `s₁<…<s_G` in an N-dimensional space, and let `Σ = Σ sᵢ`.

- `parityright = isodd(Σ + G(G+1)/2)`. This is the sign of the permutation `(S, Sᶜ)`, which makes `e_S ∧ ⋆e_S = I`.
- `parityleft = (isodd(G) && iseven(N)) ⊻ parityright`. The extra factor is `(−1)^{G(N−G)}`.
- The hodge variants additionally xor `isodd(#negative-metric indices in S)`. In the `UInt` form this is `count_ones(Vmetric & B)`, where the metric mask has a bit set for each negative basis vector.
- The UInt forms (`:213-214`) are `p(0, sum(indices(B,N)), count_ones(B), N)`. The non-hodge forms ignore their first argument.

Golden rows (N=4, V=0, B=0..15):
- right: `0,0,1,0,0,1,0,0,1,0,1,1,0,0,1,0`
- left: `0,1,0,0,1,1,0,1,0,0,1,0,0,1,0,0`

With metric mask V=1 (first vector negative):
- righthodge: `0,1,1,1,0,0,0,1,1,1,1,0,0,1,1,1`
- lefthodge: `0,0,0,1,1,0,0,0,0,1,1,1,0,0,0,1`

**Null rescaling** (`:215-224`): if V is conformal and B contains exactly one of the two lowest bits (∞ = bit0, ∅ = bit1), the value is multiplied by 2 when B contains ∞ and divided by 2 when it contains ∅. The `…pre` versions build `Expr`s; the Lean port should use a closure or a scalar factor instead.

### 4.6 `complement(N, B, D=0, P=0)` (`generic.jl:233-237`)

```
UP = (1 << (P == 1 ? 0 : P)) - 1           # conformal slot mask: P=0→0, P=1→0 (!), P=2→0b11
ND = N - D
C  = (~B & (UP ^ ((1<<ND)-1)))              # flip Grassmann bits in [0,ND), excluding UP bits
   | ( B & (UP ^ (((1<<D)-1) << ND)))       # keep B's UP bits and diff bits unchanged
return popcount(C & UP) != 1 ? C ^ UP : C  # if both/neither conformal bits set, flip both
```

- Callers pass `P = hasinf(V)+hasorigin(V)`, so P=1 (only one of ∞/∅) behaves like P=0.
- Examples, B = 0..15:
  - `complement(4,B) = 15−B`;
  - `complement(4,B,1) = [7,6,5,4,3,2,1,0,15,14,…,8]`;
  - `complement(4,B,0,2) = [15,13,14,12,11,9,10,8,7,5,6,4,3,1,2,0]`.

### 4.7 Tangent, conformal and dyadic masks (`generic.jl:69-130`)

```
diffmask(V):                                   # :70-80
  d = diffvars(V); N = mdims(V)
  if isdyadic(V):
     v = ((1<<d)-1) << (N-2d);  w = ((1<<d)-1) << (N-d)
     return d<0 ? (~v, ~w) : (v, w)            # typemax(UInt)-x == ~x
  else
     v = ((1<<d)-1) << (N-d);   return d<0 ? ~v : v
```

- Negative `d` is a rarely used DirectSum variant. In Julia, `1 << negative` is a right shift. The oracle only covers d ≥ 0; the port may reject d<0.

```
symmetricmask(V,a)     = a & D                 # D = diffmask, OR'ed if dyadic
symmetricmask(V,a,b)   = (a&~D, b&~D, (a&D)|(b&D), (a&D)&(b&D))
symmetricsplit(V,a)    = dyadic ? (sm & dm[1], sm & dm[2]) : sm

diffcheck(V,A,B):      # true ⇒ the product of blades A and B is zero
  v  = D
  hi = hasinf2(V,A,B)    && !hasorigin(V,A,B)   # both have ∞, neither has ∅
  ho = hasorigin2(V,A,B) && !hasinf(V,A,B)      # both have ∅, neither has ∞
  return hi || ho || (diffvars(V) != 0 && popcount(A&v) + popcount(B&v) > diffmode(V))
```

The last clause is the Leibniz-Taylor truncation: total derivative order above μ vanishes.

```
mixed(V, ibk):         # embed a mask of V (or V′) into V⊕V′
  N = mdims(V); D = diffvars(V); VC = isdual(V)
  if D != 0:
     A = ibk & ((1<<(N-D))-1);  B = ibk & diffmask(V)
     return VC ? (A << (N-D)) | (B << N)  :  A | (B << (N-D))
  else return VC ? ibk << N : ibk

combine(v, w, iak, ibk):  # direct-sum embedding
  error if isdual(v) != isdual(w)
  V, W = supermanifold(v), supermanifold(w)
  if istangent(V) || istangent(W):
     gV = V::Int ? V : grade(V);  gW likewise
     gras1 = iak & ((1<<gV)-1);  gras2 = ibk & ((1<<gW)-1)
     diffs = (iak & diffmask(W)) | (ibk & diffmask(W))
     return gras1 | (gras2 << gV) | (diffs << mdims(W))
  else return iak | (ibk << mdims(V))
```

- `mixed` examples: tangent(ℝ^3) with 0b1011 → `0x43`; its dual → `0x98`; `(ℝ^3)'` with 0b101 → `0x28`.
- `mixed` throws a `MethodError` for dyadic tangent V (`&` with a tuple).
- `combine(3,4,5,3) = 0x1d`.

### 4.8 `indexparity!` (`indices.jl:215-247`)

**Values version.** A gnome sort that tracks permutation parity. Duplicates are kept, since only a strict `>` swaps.

```
k=1; t=false
while k < len:
  if ind[k] > ind[k+1]: swap; t = !t; if k != 1: k -= 1
  else: k += 1
return (t, ind)
```

Examples: `(3,1,2) → (false,[1,2,3])`, `(3,2,1) → (true,…)`, `(2,1,4,3) → (false,…)`.

**Vector plus metric `s` version.** Used by DirectSum to parse basis names such as `v21`.

```
k=1; t=false
while k < len:
  if ind[k] == ind[k+1]:
     if ind[k]==1 && hasinf(s): return (t, ind, true)   # ∞∞ = 0 → "zero" flag
     if isone(s[ind[k]]): t = !t     # s[i]==true means negative signature → e_i² = −1
     deleteat!(ind, [k, k+1])        # BUG: k not decremented → no backtrack
  elif ind[k] > ind[k+1]: swap; t = !t; if k != 1: k -= 1
  else: k += 1
return (t, ind, false)
```

- **Known wrong outputs:**
  - `[1,2,2,1] → (false,[1,1],false)`: unreduced;
  - `[2,3,3,1] → (false,[2,1],false)`: unsorted;
  - an origin pair `[2,2]` under `S"∞∅+"` gives `(true,[],false)`: only ∞ is treated as null.
- The oracle flags these outputs with `"quirk": true` (18 of 480 random cases).
- **Port:** implement a correct sort-with-contraction and keep a `juliaCompat` variant only if DirectSum's name-parsing goldens need it.

### 4.9 `shift_indices!` (`indices.jl:122-132`)

```
M = supermanifold(s)
if set nonempty:
  k = 1
  if hasinf(M) && set[1] == 1: set[1] = -1; k += 1
  shift = hasinf(M) + hasorigin(M)
  if hasorigin(M) && len ≥ k && set[k] == shift: set[k] = 0; k += 1
  if shift > 0: set[k:end] .-= shift
```

- With `S"∞∅++"`, 0b1111 → `[-1,0,1,2]`. With `S"∅++"`, 0b111 → `[0,1,2]`. With `S"∞++"`, 0b111 → `[-1,1,2]`.
- For a `Submanifold{M,N,S}` (DirectSum), first map local → ambient with `indices(S)[indices(b)]` (i.e. pdep), then shift. Example: `Submanifold{ℝ^4}(0b1010)`, local 0b11 → `[2,4]` → label `v₂₄`.

### 4.10 Derivation algebra (`src/Leibniz.jl:116-152`)

**Julia semantics, as observed:**
- `-∇ = Derivation{Bool,1}(false)`, shown as `-∂ₖvₖ`.
- `(-∇)^n`: sign `λ` if n is odd, `true` if even; order `O·n`. So `(-∇)^2 == Δ`.
- `(2∇)^3`: coefficient `8`, order 3 (`8∂ₖ³vₖ`).
- `∇^0 = Derivation{Bool,0}`, shown as `∂ₖ∅v`.
- Same-order `+ - *` operate on λ with promoted T. With Bool:
  - `∇+∇` → InexactError, because `true+true=2` does not fit in `Bool`;
  - `∇-∇ = false`, shown as `-∂ₖvₖ`;
  - `∇*∇ = ∇` and `(-∇)*(-∇) = -∇`, because Bool `*` is AND. That is **mathematically wrong** for signs.
- `*` does **not** raise the order: `(2∇)*(3∇) = 6∂ₖvₖ`, order 1.
- `∇ + 1` → MethodError. Order mismatches → MethodError.
- `/` and `\` promote to Float64: `∇/2 = 0.5∂ₖvₖ`, `(2∇)\(4∇) = 2.0∂ₖvₖ`.

**Recommended Lean semantics:**
- `structure Derivation (R : Type) (O : Int)` with `coeff : R`.
- Add a `Sign` coefficient type (`pos`/`neg`, where multiplication is xor) with `Nabla := Derivation Sign 1` and `Laplacian := Derivation Sign 2`.
- `pow : Derivation R O → (n : Nat) → Derivation R (O*n)`.
- Treat `HMul` as a multiplication of coefficients that keeps the order, matching Julia, but with correct sign algebra.
- Document the divergences. Goldens that avoid them: `∇^k`, `(-∇)^k`, `c•∇`, `(a∇)±(b∇)`, `/`, `\`.

### 4.11 χ and `count_gdims` (`generic.jl:173-190`)

- `count_gdims(t::TensorGraded{V,G})`: for each nonzero component k, increment `out[grade(V, ib[k]) + 1]`, where `ib = indexbasis(N,G)` and the grade counts Grassmann bits only (via `symmetricmask(...)[1]`).
- `count_gdims(term)`: `abs(χ(term))` at the term's grade, 0 elsewhere.
- `χ(t) = Σ_{p≥0} (−1)^{p+1} · count_gdims(t)[p+1]`. For a single nonzero term: +1 for odd grade, −1 for even, 0 if zero.
- Goldens (ℝ^3):
  - `χ(v1)=1`, `χ(v12)=−1`, `χ(v123)=1`, `χ(0v1)=0`, `χ(v1+2v2)=2`, `χ(v12+v13)=−2`, `χ(v1+v12)=0`;
  - `count_gdims(v12)=[0,0,1,0]`, `count_gdims(v1+2v2)=[0,2,0,0]`.
- Grassmann adds methods for Chains, Multivectors and simplicial `Values` (`Grassmann.jl/src/multivectors.jl:1199-1233`).

### 4.12 `insert_expr` (`utilities.jl:74-96`): code-gen bindings

Given a set `e` of wanted names, it emits `name = expr` assignments. Assuming `V`, `G` and `a`/`b` are in scope:

| Name | Expression |
|---|---|
| `N` | `mdims(V)` |
| `M` | `Int(N/2)` |
| `t` | `promote_type(T,S)` for `mvec`/`mvecs` vec, else `Any` |
| `out` | `zeros(vec(N,t))`, or `convert(svec(N,Any),out)` if `mv≠0` |
| `r` | `binomsum(N,G)` |
| `rr` | `spinsum(N,G)` |
| `rrr` | `antisum(N,G)` |
| `bng` | `C(N,G)` |
| `bnl` | `C(N,L)` |
| `ib` | `indexbasis(N,G)` |
| `rs` | `spincumsum(N)` |
| `ps` | `anticumsum(N)` |
| `bs` | `binomcumsum(N)` |
| `bn` | `gdimsall(N)` |
| `df` | `dualform(V)` |
| `di` | `dualindex(V)` |
| `D` | `diffvars(V)` |
| `μ` | `istangent(V)` |
| `P` | `hasinf(V)+hasorigin(V)` |

**Lean:** replace this with a `structure AlgCtx (V)` whose fields are computed once, or with `@[inline]` accessor functions.

---

## 5. Display and printing rules

### 5.1 `printindex(i, l=false, e="v", pre=("v","w","∂","ϵ"))` (`indices.jl:139-142`)

```
t = i > 36;  j = t ? i - 26 : i
if l && 0 < j <= 10: return j                 # Int, printed as decimal: 1..10 (10 prints "10")
useSup = (e ∉ (pre[1], pre[3])) XOR t
return useSup ? sups[j] : subs[j]             # KeyError if j ∉ -1..36 (i.e. i<−1 or i>62)
```

The resulting character tables:

| i | subscript table (`v`,`∂`) | superscript table (`w`,`ϵ`, any other prefix) |
|---|---|---|
| −1 | ∞ | ∞ |
| 0 | ∅ | ∅ |
| 1–9 | ₁…₉ | ¹…⁹ |
| 10 | ₀ | ⁰ |
| 11–36 | a…z | A…Z |
| 37–62 | A…Z (from `sups[11..36]`) | a…z (from `subs[11..36]`) |

- With `l=true`, indices 1..10 print as decimal digits: `1`…`9`, then **`10`**. Indices 11..62, 0 and −1 still use the characters.
- **The sub/superscript choice depends on the *string value* of the prefix `e` compared with `pre[1]` and `pre[3]`.**
  - In the 1-list path, `pre` is the global default. Any custom prefix other than `"v"` or `"∂"` becomes superscript. For example, with `@basis` names `"e"` the label is `e¹²`, and PRE `"X"` gives `X¹²`.
  - In the 4-list path, `pre` is the tuple actually passed (§5.2), so the choice is **positional** (`e` and `g` subscript; `f` and `h` superscript) **unless the strings coincide**.

### 5.2 `printindices` (`indices.jl:144-154`)

- **1-list:** `print(e, printindex(i,l,e,pre) for i in idx)`. An empty list prints just `e` (e.g. the scalar `"v"`).
- **4-list** `(a, b, c, d, l, e, f, g, h)`:

  ```
  PRE = (e,f,g,h)
  if c nonempty: print1(c, prefix g, pre=PRE)      # ∂ part first
  if d nonempty: print1(d, prefix h, pre=PRE)      # ϵ part
  if !(a empty && (b or c or d nonempty)): print1(a, prefix e, pre=PRE)   # v part (bare "v" only when all empty)
  if b nonempty: print1(b, prefix f, pre=PRE)      # w part
  ```

- Output order: **∂, ϵ, v, w**. Example: `tangent(ℝ^2⊕(ℝ^2)')`, mask `0b110101` → `∂₁ϵ¹v₁w¹`.

### 5.3 `printlabel(io, V, e, label, vec, cov, duo, dif)` (`indices.jl:157-181`)

- **`V::Int`:** `printindices(io, indices(e), label, vec)`, 1-list with the default `pre`.
- **`V::Manifold`**: let `M = supermanifold(V)`, `N = mdims(M)`, `D = diffvars(M)`, `C = dyadmode(V)`, `db = diffmask(V)`, and `h = hasinf(M)+hasorigin(M)`.

```
if C < 0:                                  # dyadic V⊕V′
   es  = e & ~(db[1] | db[2])
   n   = (N - 2D) / 2
   eps = shift_indices(V, e & db[1]) .- (N - 2D - h)     # ∂ indices renumbered 1..
   par = shift_indices(V, e & db[2]) .- (N - D  - h)     # ϵ indices renumbered 1..
   printindices(io, shift(es & (2^n-1)), shift(es >> n), eps, par, label, vec, cov, duo, dif)
else:
   es  = e & ~db
   eps = shift_indices(V, e & db) .- (N - D - h)
   if eps nonempty:
      if C > 0: printindices(io, shift(es), [], [], eps, label, cov, cov, dif, dif)   # dual tangent
      else:     printindices(io, shift(es), [], eps, [], label, vec, cov, duo, dif)   # tangent
   else:
      printindices(io, shift(es), label, C > 0 ? cov : vec)     # 1-list, DEFAULT pre
```

**Quirk (dual tangent).** The prefix tuple is `(cov,cov,dif,dif)`, so both `w` and `ϵ` fall in `PRE[[1,3]]` and both print as **subscripts** once any ϵ is present. For `tangent((ℝ^2)')` the labels are `w w¹ w² w¹² ϵ₁ ϵ₁w₁ ϵ₁w₂ ϵ₁w₁₂`. Replicate this for display fidelity.

**Label goldens** (from `printlabel(V,b,false,pre...)` for b = 0..2^N−1; the `true` column is `label=true`):

| V | labels (b = 0,1,2,…) |
|---|---|
| ℝ^3 | `v v₁ v₂ v₁₂ v₃ v₁₃ v₂₃ v₁₂₃` (true: `v v1 v2 v12 v3 v13 v23 v123`) |
| (ℝ^3)′ | `w w¹ w² w¹² w³ w¹³ w²³ w¹²³` (true: `w w1 w2 …`) |
| S"∞∅++" | `v v∞ v∅ v∞∅ v₁ v∞₁ v∅₁ v∞∅₁ v₂ v∞₂ v∅₂ v∞∅₂ v₁₂ v∞₁₂ v∅₁₂ v∞∅₁₂` |
| S"∅++" | `v v∅ v₁ v∅₁ v₂ v∅₂ v₁₂ v∅₁₂` |
| S"∞++" | `v v∞ v₁ v∞₁ v₂ v∞₂ v₁₂ v∞₁₂` |
| tangent(ℝ^3) | `v v₁ v₂ v₁₂ v₃ v₁₃ v₂₃ v₁₂₃ ∂₁ ∂₁v₁ ∂₁v₂ ∂₁v₁₂ ∂₁v₃ ∂₁v₁₃ ∂₁v₂₃ ∂₁v₁₂₃` |
| tangent(ℝ^2,2,2) | `v v₁ v₂ v₁₂ ∂₁ ∂₁v₁ ∂₁v₂ ∂₁v₁₂ ∂₂ ∂₂v₁ ∂₂v₂ ∂₂v₁₂ ∂₁₂ ∂₁₂v₁ ∂₁₂v₂ ∂₁₂v₁₂` |
| tangent((ℝ^2)′) | `w w¹ w² w¹² ϵ₁ ϵ₁w₁ ϵ₁w₂ ϵ₁w₁₂` |
| ℝ^3⊕(ℝ^3)′ (first 16) | `v v₁ v₂ v₁₂ v₃ v₁₃ v₂₃ v₁₂₃ w¹ v₁w¹ v₂w¹ v₁₂w¹ v₃w¹ v₁₃w¹ v₂₃w¹ v₁₂₃w¹` |
| tangent(ℝ^2⊕(ℝ^2)′) (b=16..20, 32, 48) | `∂₁ ∂₁v₁ ∂₁v₂ ∂₁v₁₂ ∂₁w¹ …`, `ϵ¹`, `∂₁ϵ¹` |
| Submanifold{ℝ^4}(0b1010) | local 0b01 → `v₂`, 0b11 → `v₂₄` |

Custom names `("e","f","D","ϵ")`:
- `printlabel(ℝ^3,3,…) = "e¹²"` (1-list path → superscript);
- `printlabel((ℝ^3)′,3,…) = "f¹²"`;
- `printlabel(tangent(ℝ^2),0b101,…) = "D₁e₁"`;
- `printlabel(ℝ^2⊕(ℝ^2)′,0b0101,…) = "e₁f¹"`.

### 5.4 `indexstring` and `indexsymbol` (`indices.jl:205-211`)

`printlabel` with `label=true` and `PRE=("X","x","Y","y")`. Examples:
- ℝ^3: `X X1 X2 X12 X3 X13 X23 X123`
- tangent(ℝ^3): `… Y1 Y1X1 …`
- (ℝ^3)′: `x x1 …`
- dyadic tangent, mask 0b110101: `Y1y1X1x1`
- index 11 with an `"X"` prefix → `XA` (the 1-list path uses superscript tables because `"X"∉("v","∂")`).

### 5.5 Coefficient display: `showvalue(io, V, B, x)` (`indices.jl:185-203`)

```
if showparens(typeof(x)):        # T <: Expr|Complex|Rational|TensorAlgebra and not <: TensorTerm (or Projector)
    print("(", x, ")")
else:
    show(io, x); showstar(io, x)
printindices(io, V, B)           # label: Int V → default pre; Manifold V → namelist(V)
```

- `showstar(x)`:
  - prints `"⊗"` if x is a `TensorAlgebra`;
  - prints nothing if x is a non-Bool `Integer`, or an `AbstractFloat` that is finite;
  - prints `"*"` otherwise: Bool, Inf/NaN, Irrational `π`, Symbol, …
- Goldens, with `V=3` and `B=0b101` (the label part is `v₁₃`):

  | coeff | output |
  |---|---|
  | `1` | `1v₁₃` |
  | `-2` | `-2v₁₃` |
  | `2.5` | `2.5v₁₃` |
  | `-0.0` | `-0.0v₁₃` |
  | `Inf` | `Inf*v₁₃` |
  | `NaN` | `NaN*v₁₃` |
  | `true` | `true*v₁₃` |
  | `false` | `false*v₁₃` |
  | `1//2` | `(1//2)v₁₃` |
  | `1+2im` | `(1 + 2im)v₁₃` |
  | `1.0+0.0im` | `(1.0 + 0.0im)v₁₃` |
  | `:x` | `:x*v₁₃` |
  | `:(a+b)` | `(a + b)v₁₃` |
  | `big(3)` | `3v₁₃` |
  | `1.5f0` | `1.5f0v₁₃` |
  | `0x03` | `0x03v₁₃` |
  | `π` | `π*v₁₃` |

  With B=0 the label is just `v`, e.g. `1v`. `S"∞∅+"` with B=7 gives `1v∞∅₁`.
- **Julia `show(Float64)` must be replicated byte-exactly:**
  - use shortest round-trip digits (Ryu);
  - print plain decimal iff `1e-4 ≤ |x| < 1e6`, otherwise `d.ddde±X` with no `+` sign and no zero padding;
  - integer-valued numbers keep `.0`.
  - Verified: `100000.0`, `1.0e6`, `1.2345678e7`, `0.0001`, `1.0e-5`, `0.30000000000000004`, `5.0e-324`, `1.7976931348623157e308`, `Inf`, `-Inf`, `NaN`.
  - Float32 appends `f0` (`1.5f0`, `1.0f10`).
  - Complex prints as `a + bim` or `a - bim` (`0 + 2im`, `1.0 - 2.5im`); Rational as `n//d`.

### 5.6 Derivation `show` (`src/Leibniz.jl:116-117`)

- Bool: `(λ ? "" : "-") * "∂ₖ" * (O==1 ? "" : sups[O]) * "v" * (isodd(O) ? "ₖ" : "")`
- Otherwise: `print(λ)` (note: *print*, not *show*, so Complex gets no parentheses) followed by the same suffix.

Goldens:

| Expression | Output |
|---|---|
| `∇` | `∂ₖvₖ` |
| `Δ` | `∂ₖ²v` |
| `∇^3` | `∂ₖ³vₖ` |
| `∇^4` | `∂ₖ⁴v` |
| `∇^10` | `∂ₖ⁰v` |
| `∇^11` | `∂ₖAvₖ` |
| `∇^12` | `∂ₖBv` |
| `∇^36` | `∂ₖZv` |
| `∇^37` | KeyError |
| `∇^0` | `∂ₖ∅v` |
| `-∇` | `-∂ₖvₖ` |
| `(-∇)^3` | `-∂ₖ³vₖ` |
| `2∇` | `2∂ₖvₖ` |
| `2.5∇` | `2.5∂ₖvₖ` |
| `(1//2)∇` | `1//2∂ₖvₖ` |
| `(1+2im)∇` | `1 + 2im∂ₖvₖ` |
| `∇/2` | `0.5∂ₖvₖ` |
| `(3∇)^0` | `1∂ₖ∅v` |
| `2∇-3∇` | `-1∂ₖvₖ` |
| `(∇, Δ)` (tuple show) | `(∂ₖvₖ, ∂ₖ²v)` |

---

## 6. Examples and golden candidates

### 6.1 README (`README.md:17-53`, verbatim)

```julia
julia> Leibniz.printindices(stdout,Leibniz.indices(UInt(2^62-1)),false,"v")
v₁₂₃₄₅₆₇₈₉₀abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ

julia> Leibniz.printindices(stdout,Leibniz.indices(UInt(2^62-1)),false,"w")
w¹²³⁴⁵⁶⁷⁸⁹⁰ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz
```

Both reproduce exactly. The `∂` and `ϵ` versions are `∂₁…₀abc…zABC…Z` and `ϵ¹…⁰ABC…Zabc…z`. With `l=true`, `v` gives `v12345678910abc…zABC…Z`.

The README's Derivation block (`README.md:30-53`) is **stale**: it was written for an old Grassmann/Reduce setup. The last two lines still hold: `∇^2 == Δ` is `true`, and `(∇, Δ)` is `(∂ₖvₖ, ∂ₖ²v)`. Current Grassmann 0.8.46 prints the functor applications as follows (these are Grassmann-level goldens):

```
V = tangent(ℝ^3,4,3)   → T⁴⟨+++₁₂₃⟩
V(∇)   → 0v₁₂ + 0v₁₃ + 1∂₁v₁ + 0∂₂v₁ + 0∂₃v₁ + 0v₂₃ + 0∂₁v₂ + 1∂₂v₂ + 0∂₃v₂ + 0∂₁v₃ + 0∂₂v₃ + 1∂₃v₃ + 0∂₁₂ + 0∂₁₃ + 0∂₂₃
V(∇^2) → 0 + 1∂₁⊗∂₁ + 1∂₂⊗∂₂ + 1∂₃⊗∂₃
V(∇^3) → 0 + 1∂₁⊗∂₁⊗∂₁v₁ + 1∂₂⊗∂₂⊗∂₂v₂ + 1∂₃⊗∂₃⊗∂₃v₃ + 1∂₂⊗∂₁₂v₁ + 1∂₃⊗∂₁₃v₁ + 1∂₁⊗∂₁₂v₂ + 1∂₃⊗∂₂₃v₂ + 1∂₁⊗∂₁₃v₃ + 1∂₂⊗∂₂₃v₃
V(∇^4) → StackOverflowError (current Grassmann bug; README claimed 0.0 + 1∂₁∂₁∂₁∂₁ + …)
ℝ3(∇)  → 1v₁ + 1v₂ + 1v₃        ℝ3(Δ) → 1v₁ + 1v₂ + 1v₃ (O≥1 but diffvars=0 → λ·ones)
ℝ3(2∇) → 2v₁ + 2v₂ + 2v₃
tangent(ℝ^3)(∇) → 0v₁₂ + 0v₁₃ + 1∂₁v₁ + 0v₂₃ + 1∂₁v₂ + 1∂₁v₃
tangent(ℝ^3)(∇^2) → 0v⃖
tangent(ℝ^2,2,2)(∇^2) → 1 + 1∂₂⊗∂₂
```

### 6.2 Test suite (`test/runtests.jl:5`)

`@test ∇^2 == Δ` is the only test.

### 6.3 Additional goldens (from probes and the oracle)

- `indices(0xb) = [1,2,4]`; `indices(0) = []`
- `digitsfast(5,3) = [1,0,1,0]`
- `bit2int([1,0,1,1]) = 13`
- `indexbits(5,[1,3]) = [1,0,1,0,0]`
- `combo(4,2) = [[1,2],[1,3],[1,4],[2,3],[2,4],[3,4]]`; `combo(n,0) = [[]]`
- `gdimsall(4) = [1,4,6,4,1]`, `gdimseven(5) = [1,10,5]`, `gdimsodd(5) = [5,10,1]`
- `binomcumsum(3) = [0,1,4,7,8]`, `spincumsum(5) = [0,1,1,11,11,16,16]`, `anticumsum(5) = [0,0,5,5,15,15,16]`
- `bladeindex(4, s=0..15) = [1,1,2,1,3,2,4,1,4,3,5,2,6,3,4,1]`
- `indexbasis(5,2) = [3,5,9,17,6,10,18,12,20,24]`, `indexbasis(5,3) = [7,11,19,13,21,25,14,22,26,28]`
- `indexbasis(3) = [0,1,2,4,3,5,6,7]`
- Even blades of N=5 in spin order: `0,3,5,9,17,6,10,18,12,20,24,15,23,27,29,30` → spinindex 1..16
- Odd blades in anti order: `1,2,4,8,16,7,11,19,13,21,25,14,22,26,28,31` → antiindex 1..16
- `lowerbits(4,0b1011,b=0..15) = [0,1,1,3,0,1,1,3,1,3,3,7,2,5,5,11]` (= pext)
- `expandbits(4,0b1011,b=0..7) = [0,1,2,3,8,9,10,11]`; `expandbits(4,0b1101,b=0..7) = [0,1,4,5,8,9,12,13]`
- `indexsplit(0b1011,4) = [1,2,8]`
- `grade(3,0b101)=2`, `grade_basis(3,0b1101)=0b101`, `pseudograde(3,0b101)=1`
- `grade(tangent(ℝ^3), 0b1011)=2`, `pseudograde(tangent(ℝ^3), 0b1011)=1`
- `grade(V)` for tangent(ℝ^3) is 3; for ℝ^3⊕(ℝ^3)′ it is 6; for tangent(ℝ^2⊕(ℝ^2)′) it is 4
- `pseudograde(tangent(ℝ^3)) = −1`
- `symmetricmask(tangent(ℝ^3),0b1011,0b1001) = (3,1,8,8)`
- `diffcheck(tangent(ℝ^3),8,8) = true`, but `false` for `tangent(ℝ^3,2)`
- `diffcheck(S"∞∅++",1,1)=true`, `(2,2)=true`, `(3,3)=false`
- `metric(S"-++",0b011) = −1`, `metric(S"-++",0b110) = 1`
- DirectSum `labels` (combo order, `label=true`):
  - `tangent(ℝ,2,2)`: `[v, v1, ∂1, ∂2, ∂1v1, ∂2v1, ∂12, ∂12v1]`
  - `tangent(ℝ^1)⊕tangent(ℝ^1)′`: `[v, v1, w1, ∂1, ϵ1, v1w1, ∂1v1, ϵ1v1, ∂1w1, ϵ1w1, ∂1ϵ1, ∂1v1w1, ϵ1v1w1, ∂1ϵ1v1, ∂1ϵ1w1, ∂1ϵ1v1w1]`
  - `S"∞∅+"`: `[v, v∞, v∅, v1, v∞∅, v∞1, v∅1, v∞∅1]`
- `Λ(ℝ^12).v1a = v₁a`; `Λ(ℝ^12).v1ab = v₁ab`; `Λ((ℝ^3)').w123 = w¹²³`; `Λ(S"∞∅+").v∞∅1 = v∞∅₁`
- `printindices(io, 3, 0b101)` → `v₁₃`; with `label=true` → `v13`
- `printindices(io, 12, 1<<11|1)` → `v₁b`
- `printindices(io, 40, 1<<36|1<<9)` → `v₀A` (indices 10 and 37); with `label=true` → `v10A`

---

## 7. Dependencies

### 7.1 Upstream (Leibniz → other packages)

**AbstractTensors** (compat 0.8.1). Imports at `src/Leibniz.jl:30-35,144`, `src/utilities.jl:15-16`, `src/generic.jl:241`. Symbols used:
- abstract types: `TensorAlgebra{V,T}<:Number`, `Manifold{V,T}`, `TensorGraded{V,G,T}`, `TensorTerm{V,G,T}` (`AbstractTensors.jl/src/AbstractTensors.jl:32,49,64,108`);
- dimension functions: `mdims`, `rank` (for a Manifold type = mdims, `:154`), `gdims(N,G)=binomial` (`:181`);
- accessors and predicates: `value`, `valuetype`, `basis`, `scalar`, `isscalar`, `vector`, `isvector`, `bivector`, `isbivector`, `volume`, `isvolume`, `pseudoscalar`;
- involutions and complements: `involute`, `clifford`, `even`, `odd`, `complement`, `complementleft/right/lefthodge/righthodge`, `⋆`, `unit`;
- products and related: `∧`, `∨`, `equal`, `isnull`, `norm`, `interop`, `interform`;
- static vectors: `Values`, `Variables`, `FixedVector`, `TupleVector`, `countvalues`, `evenvalues`, `evens` (re-exported from StaticVectors, `StaticVectors.jl/src/StaticVectors.jl:79-93`);
- reductions: `PROD=∏`, `SUM=∑` (`AbstractTensors.jl:626`);
- arithmetic: `conj`, `inv`, `-`, `/`, `sqrt`, `abs`, `exp`, `expm1`, `log`, `log1p`, `sin`, `cos`, `sinh`, `cosh`, `^`.

Leibniz itself only *uses* `mdims`, `rank`, `gdims`, `value`, `basis`, `Manifold(x)`, `countvalues`, `evenvalues`, `Values`, `Variables`, `FixedVector`, `PROD`, `SUM`, `istensor` and the abstract types. The rest are imported so that Leibniz methods extend them.

**Combinatorics:** only `combinations` (`utilities.jl:109`).

**LinearAlgebra:** `UniformScaling`, `I`, `det`, `rank`, `dot`, `cross`, `reflectorApply!`, `has_offset_axes`.

### 7.2 Downstream (what imports Leibniz)

- **DirectSum.** Imports at `DirectSum.jl/src/DirectSum.jl:34-48` and `operations.jl:328,385`; uses `showvalue` at `:488` and `printlabel` in `basis.jl:26`. The symbols:
  - `Fields`, `pre`, `PRE`, `vsn`, `VTI`, `bit2int`, `combo`, `indexbits`, `indices`;
  - `printlabel`, `supermanifold`, `shift_indices`, `shift_indices!`, `printindices`;
  - `symmetricmask`, all parity functions and the `…null`/`…nullpre` variants, `combine`, `hasconformal`, `parval`, `TensorTerm`, `mixed`;
  - `subs`, `sups`, `vio`, `gdims`, the mode functions, `pseudograde`, `hasinf`, `hasorigin`, `norm`, `isbasis`, `≅`, `isdyadic`, `isdual`, `istangent`, `involute`, `basis`, `alphanumv`, `alphanumw`;
  - the limits, `binomial`, `gdimsall`, `binomsum`, `binomcumsum`, `lowerbits`, `expandbits`, `bladeindex`, `basisindex`, `indexbasis`, `indexbasis_set`, `loworder`, `intlog`, `promote_type`, `mvec`, `svec`, `insert_expr`, `indexparity!`;
  - `complementright`, `complementrighthodge`, `⋆`, `complement`.

  DirectSum defines methods of `grade`, `order`, `hasinf`, `diffvars`, `shift_indices`, `printindices(io,::Manifold,…)`, `supermanifold`, `loworder` and others for its types. `grade.jl:26` forwards `gdimsall`, `binomcumsum`, `spincumsum`, `anticumsum`, `indexbasis_set`, `indexeven_set`, `indexodd_set`, `indexbasis`, `indexeven` and `indexodd` for `Grade{N}`.
- **Grassmann.** Import lists as in §2. It uses `Derivation` in `(V::Signature)(::Derivation)` and `(::Submanifold)(::Derivation)` (`Grassmann.jl/src/Grassmann.jl:88-106`), and in `outer` (`forms.jl:883-884`).
  - Usage counts across Grassmann `src`: `insert_expr` 124, `indexbasis` 92, `svec` 74, `svecs` 52, `mvec` 46, `symmetricmask` 29, `mvecs` 25, `bladeindex` 24, `loworder` 22, `indices` 18, `complement` 18, `parityreverse` 18, `hasconformal` 15, `count_gdims` 14, `diffcheck` 12.
  - It calls `extend_field`/`check_field` (`products.jl:1083-1092`) and `ext/ReduceExt.jl:26-27`.
- **Cartan / MeshTopology:** `Leibniz.combinations`, `Leibniz.indexparity!` (`Cartan.jl/src/element.jl:211-276`, `MeshTopology.jl/src/element.jl:90-153`).
- **Clifford:** `Leibniz.printindices(io,V,ib[k])` (`Clifford.jl/src/multivectors.jl:46,57`), `basis`, `grade`, `order`.

---

## 8. Lean 4 porting notes

### 8.1 Types: indices vs runtime values

| Julia | Lean | Cost |
|---|---|---|
| `UInt` mask plus implicit dimension | `structure Mask (n : Nat) where bits : UInt64; lt : bits.toNat < 2^n`. A single relevant field is **unboxed to a raw `uint64_t`** by the LCNF trivial-structure rule (`~/lean4/src/Lean/Compiler/LCNF/MonoTypes.lean:33,74-76`). Use `n ≤ 64` as a hypothesis where needed. | zero |
| `BitVec n` | Avoid for hot paths: it is Nat-backed (bignum-capable, slower). Use it only for `bv_decide` proofs via `UInt64.toBitVec`. | – |
| `Values{N,T}` / `Variables{N,T}` | `Vector α n` (core; Array plus erased size proof). Use `FloatArray` for dense Float64 multivector storage downstream. | zero |
| `Derivation{T,O}` | `structure Derivation (R : Type) (O : Int) where coeff : R`; with `abbrev Nabla := Derivation Sign 1` and `abbrev Laplacian := Derivation Sign 2`. The order is a type index. `pow (d : Derivation R O) (n : Nat) : Derivation R (O * n)` is dependent in the runtime n (fine). | zero |
| `combo(n,g)::Vector{Vector{Int}}` | `Array (Vector Nat g)`, or better **masks** `Array UInt64` from `indexBasis` | – |
| `binomcumsum(n)::Values{n+2}` | `Vector Nat (n+2)` | – |
| manifold `V` type parameter | A value `V : Sig` (the DirectSum port) used as an index of downstream types. Leibniz functions take `[ManifoldInfo V]` or the `Sig` explicitly; use `@[specialize]` so closed `V` constants fold. | pointer argument |

Grade `G` and mask `B` as type indices (`Submanifold V G B`) belong to DirectSum. Keep `B` **runtime** in Lean, as a field. Making it an index would force dependent pattern matching on every product for no runtime gain; Julia only does it to trigger `@generated` specialisation.

### 8.2 Breaking the dependency cycle: manifold interface

Leibniz's generic functions take "any manifold" and are specialised by DirectSum. Define in Leibniz:

```lean
class ManifoldInfo (V : Type) where        -- or on a value `Sig`
  mdims : Nat
  diffvars : Int          -- ν (Julia allows <0; port may restrict to Nat)
  diffmode : Nat          -- μ
  dyadmode : Int          -- <0 dyadic, >0 dual, 0 plain
  hasinf : Bool
  hasorigin : Bool
  polymode : Bool := true
  options : Nat := 0
  metricBits : UInt64 := 0  -- negative-signature mask
  rank : Nat := mdims       -- = mdims for full manifolds, grade for submanifolds
  super : Option ...        -- supermanifold + parent mask S for Submanifold (pdep in shift)
```

`Int` is the default instance (all zero/false; `mdims = n`). Derive `diffmask`, `grade`, `pseudograde`, `hasconformal`, `symmetricmask` and so on from these fields. The simplest shape is a plain **structure `LabelCtx`** carrying `(N, D, C, hasinf, hasorigin, parentMask?)`, passed to the printing and mask functions. DirectSum builds it from its `Sig`.

### 8.3 Performance: how Julia gets its speed, and the Lean equivalent

- **Julia:**
  1. `@pure` plus global mutable caches, consulted at `@generated` code-gen time, so runtime cost is zero for N ≤ 12;
  2. lazy per-n tables for 12 < N ≤ 20/22;
  3. linear `findfirst` for N > 20 (slow).
- **Lean plan:**
  - **Closed forms everywhere.** `bladeIndex` is O(popcount) using a binomial table. `binomTable : Array (Array UInt64)` for n ≤ 64 is a top-level closed term, computed once at init; it is exact for C(64,32) ≈ 1.8e18 < 2^64. `unrank` is O(n). pext/pdep are loops over set bits. `indices` is a ctz loop.
  - **Bit intrinsics.**
    - Core has `UInt64.log2`, implemented via `lean_uint64_log2`, i.e. clz (`~/lean4/src/Init/Data/UInt/Log2.lean:81`).
    - Core has **no** `UInt64` popcount or ctz; `BitVec.clz/ctz` exist but are Nat-backed.
    - Implement SWAR `popcount` (≈12 ops) and `ctz x = log2 (x &&& (0 - x))` in pure Lean, `@[inline]`.
    - Optionally add a C shim via `@[extern]` for `__builtin_popcountll`, `__builtin_ctzll`, and BMI2 `_pext_u64`/`_pdep_u64` on x86_64 (not on aarch64/M-series), keeping the pure definition as the logical model.
  - **Per-n tables** (for Grassmann inner loops): `structure IndexTables (n) where ib : Array UInt64 (2^n); pos : Array UInt32 (2^n); bs ss as : Vector Nat (n+2)`. Memoise safely with a top-level `def tables : Array (Thunk IndexTables) := (List.range 25).toArray.map (fun n => Thunk.mk fun _ => build n)`. `Thunk` caches after the first force: pure, thread-safe and lazy. Fall back to closed forms for n > 24.
  - **Printing:**
    - build `String`s with `String.push`;
    - store `subs`/`sups` as `#[…]` arrays of `Char` indexed by `i+1` (keys −1..36);
    - never go through `Dict`.
  - **Avoid** `List`, `Nat`-heavy loops on hot paths, and `partial` where a fuel bound is obvious. Mark small helpers `@[inline]`, and higher-order ones (`printlabel` over a context) `@[specialize]`.

### 8.4 Julia-specific parts: skip or redesign

| Julia construct | Lean replacement |
|---|---|
| `@pure`, `@generated`, global `*_cache`/`*_extra` vectors and dicts | Pure functions, closed-term tables, `Thunk` memoisation (§8.3) |
| `insert_expr`, `assign_expr!`, `parity*nullpre` (Expr builders) | Skip. Downstream uses an `AlgCtx` record or plain lets; the null rescaling returns a factor (`Rat`/`Float`) |
| `parval`/`parnot`/`check_*`/`extend_*` (mutable global type registries) | `class CoeffShow (α) where showJ : α → String; parens : Bool := false; star : α → Bool := fun _ => false`, with instances for `Int`, `Float`, `Float32`, `Rat`, `Complex α`, `Bool`, and TensorAlgebra types (star `⊗`). Extensibility comes from new instances |
| `UniformScaling` wrapper in `Derivation` | Store `coeff : R` directly |
| `Bool` as a sign | `inductive Sign \| pos \| neg` with `mul = xnor` semantics (xor on "negative"). Julia's `*` bug is not reproduced (§4.10) |
| `mvec`/`svec`/`mvecs`/`svecs` (type-level constructors) | `abbrev MVec n α := Vector α (2^n)`, `ChainVec n g α := Vector α (n.choose g)`, `HalfVec n α := Vector α (2^(n-1))` |
| `reflectorApply!` (LinearAlgebra piracy) | Skip. Re-add in a linear-algebra module only if QR over multivectors is ported |
| `AbstractTensors.:-(::Values)`, `norm(::Values{N,Any})` piracy | Skip (belongs to the AbstractTensors port) |
| `getbasis(V,b::Integer)` shim, `UInt(::TensorTerm)` | Coercions in DirectSum |
| exported-but-undefined names (`Differential`, `⊕`, `tangent`, `isorigin`) | Omit |
| `low_greek`/`upp_greek`, `VSN`, `digs` | Unused. Optional constants |
| Module-init cache warm-up (`src/Leibniz.jl:180-185`) | Skip |

### 8.5 Unicode names in Lean

- **Valid identifier characters** (`isLetterLike`, `~/lean4/src/Init/Meta/Defs.lean:101-118`):
  - Greek except λ Π Σ: so `Δ`, `δ`, `χ`, `ϵ` (U+03F5, in the Coptic range), `ν`, `μ`;
  - subscripts `₀-₉`, `ₐ-ₜ`, `ᵢ-ᵪ`, `ⱼ`: so `v₁₂` is a valid identifier (useful for the DirectSum `@basis` port).
- **Not valid:** `∂` (U+2202), `∇` (U+2207), `∞`, `∅`, `⊗`, `≅` and superscripts `¹²³`.
- **Hence:**
  - `def nabla`, `notation "∇" => nabla`;
  - `def laplacian`, `abbrev Δ := laplacian` (allowed);
  - `def boundary`, `prefix:max "∂" => boundary` (Mathlib uses `∂` notation elsewhere, but this project has no Mathlib dependency);
  - `δ` = `codifferential` and `d` = `differential` as defs inside namespace `Leibniz` (avoid a global `d`);
  - `χ` = `eulerChar`;
  - `infix:50 " ≅ " => sameKind` (Mathlib uses `≅` for `Iso`; scope it with `scoped` notation);
  - `w¹²`-style basis names need ASCII aliases (`w12`) downstream.

### 8.6 Quirks: port faithfully or fix?

| # | Behaviour | Where | Recommendation |
|---|---|---|---|
| Q1 | `lowerbits` history-dependent wrong results | `utilities.jl:270-273` | **Fix** (pure pext); goldens from `lowerbits_calc` |
| Q2 | Cumsum caches wrong for n=0,1 | `utilities.jl:145` | **Fix**; oracle marks `quirk` |
| Q3 | `indexeven`/`indexodd` wrong | `utilities.jl:247-250` | **Fix** (true even/odd lists); no goldens |
| Q4 | `indexbasis(0\|1)`, `gdimsodd(0)`, `combo(n,g>n)`, `digitsfast` out of range: errors or UB | various | Total functions with correct results (empty or `[0]`) |
| Q5 | `indices(b,N)` ignores N | `indices.jl:116-119` | Pure `indices b` |
| Q6 | `indexparity!(vec,s)` no backtrack after delete; ∅² not null | `indices.jl:230-247` | **Fix**, plus an optional `juliaCompat` flag if DirectSum name-parsing goldens need it |
| Q7 | Derivation Bool arithmetic (`∇+∇` throws, `(-∇)*(-∇) = -∇`, `∇-∇ = -∇`) | `src/Leibniz.jl:128-134` | **Fix** with `Sign`; keep all other goldens |
| Q8 | Dual-tangent labels switch `w`/`ϵ` to subscripts | `indices.jl:175` | **Faithful** (display goldens) |
| Q9 | 1-list path: custom prefixes other than `v`/`∂` become superscript | `indices.jl:141` | **Faithful** |
| Q10 | `χ` sign opposite to its docstring | `generic.jl:173` | **Faithful** (Grassmann goldens depend on it); document it |
| Q11 | `∇^0` shows `∂ₖ∅v`; `∇^n` KeyError for n>36; label index > 62 KeyError | `src/Leibniz.jl:116`, `indices.jl:141` | Faithful for 0..36 and ≤62. Fall back to an out-of-table rendering (e.g. `⁽ⁿ⁾`) rather than panicking, and document it |
| Q12 | `mixed` MethodError for dyadic tangent | `generic.jl:112` | Return `Option`/panic with a message, or define component-wise; no goldens |
| Q13 | `pseudograde(V::Manifold)` negative for tangent manifolds | `generic.jl:11` | Faithful (Int result) |
| Q14 | `hasorigin(V,B)` does not check `hasorigin(V)` | `generic.jl:61` | Faithful; only called when conformal |

### 8.7 Proofs that pay for themselves

These are cheap and catch real bugs. Types are the spec; unproved items can carry `sorry` initially.
1. `bladeIndex_indexBasis : bladeIndex n (indexBasis n g i) = i+1` and the converse. `decide` works for n ≤ 6; for general n, prove the combinatorial-number-system lemma or property-test it with the oracle.
2. `binomCumsum_last : (binomCumsum n)[n+1] = 2^n`; `spin + anti = binom` pointwise; `spinCumsum_last = 2^(n-1)` for n ≥ 1.
3. `pext_pdep : lowerbits S (expandbits S B) = B` for `B < 2^popcount S`, and `expandbits S (lowerbits S B) = B &&& S`. Prove on a recursive Nat-bit spec, then relate the fast implementation by `bv_decide` at width 64 where possible.
4. `symmetricmask_partition : (a &&& ~~~D) ||| (a &&& D) = a` via `bv_decide`.
5. `complement_invol` for P ∈ {0,1}, and `complement` preserving the diff/UP bits, via `bv_decide` with symbolic shift amounts at width 64.
6. Parity closed forms `parityReverse g = (g % 4 ≥ 2)`, `parityClifford g = (g % 4 = 1 ∨ g % 4 = 2)` via `omega`/`decide` after unfolding.
7. `printIndex_injective` on 1..62 for each table, and table sizes (62 chars), via `decide`. This guards the round-trip needed by DirectSum name parsing.
8. `indexParity_spec`: the output is sorted, and the parity equals the inversion parity; prove, or property-test against a naive inversion count.
9. `Derivation.pow_mul : (d^m)^n = d^(m*n)` up to `O` arithmetic (needs `cast` on the index; state it via `HEq` or a coercion lemma).

### 8.8 Suggested module decomposition

The rough total is ≈1,700 LOC: code ≈1,100, proofs ≈350, tests ≈250.

| Module | Contents | LOC |
|---|---|---|
| `Leibniz/Bits.lean` | `Mask n`, `popcount`, `ctz`, `indices`, `indexbits`, `bit2int`, `indexsplit`, `digitsfast`, `pext` (lowerbits), `pdep` (expandbits), `intlog` | 170 |
| `Leibniz/Combinatorics.lean` | `binomTable`, `gdims`/`gdimsAll`/`Even`/`Odd`, binom/spin/anti sums and cumsums, `combo`, `bladeIndex`/`basisIndex`/`spinIndex`/`antiIndex`, `indexBasis` (unrank), `indexBasisAll`/`Set`/`Even`/`Odd`, `IndexTables` with `Thunk` memo, limit constants | 280 |
| `Leibniz/Parity.lean` | reverse/involute/clifford/conj, right/left(+hodge) in both the Int and mask forms, null rescaling factor, `complement` | 120 |
| `Leibniz/Manifold.lean` | `ManifoldInfo`/`LabelCtx`, `diffmask`, `symmetricmask`/`split`, `diffcheck`, `mixed`, `combine`, `hasconformal`, `hasinf`/`hasorigin` (V,B)/(V,A,B)/`…2`, `grade`/`pseudograde`/`gradeBasis`/`order`, `sameKind` (≅), `shiftIndices` | 200 |
| `Leibniz/IndexParity.lean` | Values version and metric-contraction version (plus optional `juliaCompat`) | 80 |
| `Leibniz/Print/Tables.lean` | `subs`, `sups`, `alphanumv`/`w`, `pre`, `PRE`, `vsn`, `vio`, `Names` struct | 60 |
| `Leibniz/Print/Label.lean` | `printIndex`, `printIndices` (1- and 4-list), `printLabel`, `indexString` | 140 |
| `Leibniz/Print/JuliaShow.lean` | Julia-exact `Float`/`Float32`/`Int`/`Rat`/`Complex`/`Bool` rendering (Ryu shortest plus Julia thresholds), `CoeffShow` class, `showStar`, `showParens`, `showValue`. Could be shared with the AbstractTensors/StaticVectors ports | 250 |
| `Leibniz/Derivation.lean` | `Sign`, `Derivation R O`, arithmetic, `pow`, `ToString`, `∇` `Δ` `Nabla` `Laplacian`, classes `HasDifferential`/`HasCodifferential`/`HasBoundary` with notations `d δ ∂`, `ApplyDerivation V` class for the `V(∇)` functor (instance in the Grassmann port) | 150 |
| `Leibniz/Euler.lean` | `countGdims`, `eulerChar` (χ) over a `GradeCounts` class | 50 |
| `Leibniz/Proofs/*.lean` | §8.7 | 350 |
| `Leibniz/Test/Golden.lean` | Loads `golden/*.json` with `Lean.Json`. **Parse integers exactly**: `JsonNumber` has an Int mantissa; never go through `Float` for masks up to 2^64. Compares everything and skips/labels `quirk` rows | 250 |

---

## 9. Oracle test plan

**Script:** `scratchpad/oracle/leibniz/leibniz_oracle.jl` (already runs).

```
julia --startup-file=no --project=scratchpad/juliaenv scratchpad/oracle/leibniz/leibniz_oracle.jl scratchpad/oracle/leibniz/golden
```

It uses a fixed `MersenneTwister(0x1eeb)` seed, and it deliberately takes values from the `*_calc`/reference paths wherever the cached Julia path is buggy. Rows are tagged `"quirk": true` where Julia is known-wrong (§8.6).

| File | Contents / input distribution | Lean checks |
|---|---|---|
| `tables.json` | `subs`, `sups` (−1..36), `alphanumv`/`w`, `pre`, `PRE`, `vio`, `vsn`, `VSN`, `digs`, the limit constants | Exact table equality |
| `printindex.json` | Full grid: i ∈ −1..62 × l ∈ {F,T} × e ∈ {v,w,∂,ϵ,X,x,Y,y,e,f} (1,280 rows) | `printIndex` (Char or decimal string) |
| `printindices1.json` | 400 random sorted index lists (size 0..8, values −1..62) × random prefix and l, plus both README 2^62−1 cases | 1-list `printIndices` |
| `printindices4.json` | 300 random (a,b,c,d) lists of values 1..12, sizes 0..3, with name tuples {pre, PRE, (w,w,ϵ,ϵ), (e,f,D,E)} | 4-list ordering and sub/sup rules |
| `manifolds.json` | 29 manifolds: ℝ^1..5 and duals; S"∞∅+", S"∞∅++", S"∅++", S"∞++", S"-++", S"+-+-"; ℝ^2⊕ and ℝ^3⊕ duals; tangent(ℝ^1), (ℝ^3), (ℝ^3,2), (ℝ,2,2), (ℝ^2,2,2), (ℝ^2,3,2); tangent((ℝ^2)′); tangent(ℝ^2⊕(ℝ^2)′); tangent(ℝ^1)⊕tangent(ℝ^1)′; two Submanifolds. Per manifold: metadata (mdims, diffvars, diffmode, dyadmode, hasinf, hasorigin, isdual, isdyadic, diffmask, grade, DirectSum `show`). Per mask b (all 2^N, or 2^grade locally for a Submanifold): label (pre, l=F), label (l=T), indexstring (PRE), custom-names label (e,f,D,E), shift_indices, symmetricmask, grade(V,b), mixed (skipped for dyadic tangent) | `printLabel`, `shiftIndices`, `symmetricMask`, `grade`, `mixed`, `diffmask`, and the ManifoldInfo derivations |
| `diffcheck.json` | All (A,B) pairs for S"∞∅+", S"∞∅++", tangent(ℝ^2,2,2), tangent(ℝ^3), ℝ^3 | `diffcheck`, `symmetricmask(V,a,b)` |
| `combinatorics.json` | `combo(n,g)` for n ≤ 8; cumsums n = 0..24, both the calc and cached versions, n<2 flagged; gdims n ≤ 20; blade/basis/spin/anti index for **all** masks with n ≤ 10 (spin only for even, anti only for odd), n=1 flagged; 500 random (n ∈ 11..64, popcount ≤ 10) from the verified closed form; `indexbasis(n,g)` for n ≤ 10; `indexbasis(n)` for n = 2..8 | All combinatorics, including the u64 ranges |
| `bits.json` | `indices` for b = 0..64, 200 random masks, 2^62−1 and 2^64−1; `indexsplit` for b ≤ 300; `bit2int`; `indexbits`; 600 random (N ≤ 16, S, B) pext rows and 600 pdep rows | `indices`, `pext`, `pdep`, … |
| `parity.json` | Grade parities for G = 0..64; complement parities for N ≤ 6 × {0 + 3 random metric masks} × all B; `complement(N,B,D,P)` for N ≤ 7, D ≤ 2, P ≤ 2 with D+P ≤ N; 300 random `indexparity!` Values (permutations and multisets); 480 metric `indexparity!` cases over 6 signatures (quirk-flagged); null rescaling for S"∞∅+" and ℝ^3 | Parity module |
| `derivation.json` | `show`, T and O for `∇^O` and `(-∇)^O`, O ∈ 0..36, plus 23 arithmetic expressions; the error kinds for `∇+∇`, `Δ+Δ`, `∇+1`, `∇^37`; `∇^2==Δ` and `(-∇)^2==Δ` | `Derivation` `ToString` and arithmetic (skip Bool `+`/`*` rows, per Q7) |
| `showvalue.json` | 18 coefficient kinds (Int, negative, 0, Float incl. −0.0/±Inf/NaN, Bool, Rational, Complex Int/Float, Symbol, BigInt, Float32, UInt8, π) × V ∈ {3, ℝ^3, S"∞∅+", tangent(ℝ^2)} × B ∈ {0,1,5,7} | `CoeffShow` + `showValue`. Lean has no Symbol/π/UInt8 coefficient types, so those rows are optional |
| `euler.json` | χ and count_gdims for 8 ℝ^3 terms and sums (via Grassmann) | `eulerChar`, `countGdims` |

**Extensions to add as the port grows:**
1. Julia float printing: a dedicated `floatshow.json` with about 10k random `Float64`s (uniform over bit patterns, log-uniform magnitudes, and edge values 1e-4, 1e6, subnormals), emitting `repr(x)`. This is the single highest-risk display dependency and is shared with every package.
2. **Cross-package:** once DirectSum and Grassmann are ported, dump `DirectSum.labels(V)` (combo-ordered names), `Λ(V).name` lookups (these exercise `indexparity!`), and `V(∇^k)` for `tangent(ℝ^n,μ,ν)` with small n, μ, ν. Avoid `tangent(ℝ^3,4,3)(∇^4)`, which overflows the Julia stack.
3. **Performance baselines:** time `bladeindex`/`basisindex`/`indexbasis` in Julia for n = 12, 20, 30 (and note the O(C(n,k)) cliff for n > 20), then benchmark the Lean closed forms against them.
