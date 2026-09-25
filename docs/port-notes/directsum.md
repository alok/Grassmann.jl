# DirectSum.jl -> Lean 4 porting spec

Scope: `DirectSum.jl` (all of `src/*.jl`, README, tests; `docs/` contains only a logo) plus every
`Leibniz.jl` symbol that DirectSum imports for index tables, bit helpers, parity and printing, because
the ordering/printing semantics of DirectSum live there.

Sources (latest master clones, byte-identical to the registered packages used by the oracle except for
two irrelevant lines):

| Package | Path | Commit | Version |
|---|---|---|---|
| DirectSum | `/Users/alokbeniwal/chakravala/DirectSum.jl` | `7b964d888d4795bac8822a8fd0e528a451744ec4` (2026-01-12) | 0.8.21 |
| Leibniz | `/Users/alokbeniwal/chakravala/Leibniz.jl` | `a319d2716b682e1f870deae6bd2d1f702689ee70` | 0.3.1 (registry 0.3.0; diff = one import line) |
| AbstractTensors | `/Users/alokbeniwal/chakravala/AbstractTensors.jl` | `65fc00f367e22dd38d3b42f7b914774d479df88e` | (registry diff = 2 `angle` methods) |

Citation shorthand used throughout:

* `DS/X.jl:N` = `/Users/alokbeniwal/chakravala/DirectSum.jl/src/X.jl` line N
* `LB/X.jl:N` = `/Users/alokbeniwal/chakravala/Leibniz.jl/src/X.jl` line N
* `AT:N` = `/Users/alokbeniwal/chakravala/AbstractTensors.jl/src/AbstractTensors.jl` line N
* `README:N` = `/Users/alokbeniwal/chakravala/DirectSum.jl/README.md` line N

Oracle artifacts produced while writing this spec (all runnable, Julia 1.13, `--startup-file=no`):

* Golden dumper: `/private/tmp/claude-502/-Users-alokbeniwal-Grassmann/c6cc2308-bfca-4b9a-ad33-d89b110132a8/scratchpad/ds_oracle/dump_directsum.jl`
* Golden JSON (1.1 MB, 24 sections, 3.5 min to regenerate): `.../scratchpad/ds_oracle/directsum_golden.json`
* Ad-hoc probe scripts with printed results: `.../scratchpad/ds_oracle/t1.jl` .. `t11.jl`

Every "Oracle:" line below was produced by actually running Julia against DirectSum 0.8.21.

---

## 1. Purpose and scope

DirectSum provides the *vector-space descriptor* layer for the whole chakravala ecosystem
(README:7 "Abstract tangent bundle vector space type operations at compile-time"):

1. A family of space descriptors `TensorBundle{n,Options,Metrics,Vars,Diff,Name}` (abstract) with
   concrete subtypes `Signature` (+/- metric as a bitmask), `DiagonalForm` (arbitrary diagonal metric,
   stored in a global cache) and, in Grassmann (not here), `MetricTensor`. A bare `Int n` is also accepted
   as a Euclidean space "of counted dimension".
2. Options on a space: point at infinity `∞`, origin `∅` (conformal/projective null basis), dual (`'`),
   dyadic/mixed (`V⊕V'`, printed `*`), polymode flag, number of tangent (differential) variables `ν`,
   tangent order `μ`, and a naming-scheme index.
3. `Submanifold{V,G,B}`: one type used for three roles -- a *subspace* of a space (bitmask of included
   generators), the *full-rank handle* of a space (`Submanifold(V)`), and a *basis blade* of the
   Grassmann algebra `Λ(V)` (when `V` itself is a `Submanifold`).
4. Scalar-times-blade `Single{V,G,B,T}`, and the special terms `Zero{V}`, `One{V}`, `Infinity{V}`.
5. The algebra basis containers `Basis` (= `Λ`), `SparseBasis`, `ExtendedBasis` with global caches keyed
   by space parameters, name generation (`labels`), name lookup with permutation parity
   (`indexparity`), and the `@basis`/`@dualbasis`/`@mixedbasis` macros.
6. Space algebra: direct sum `⊕`, dual `'`, `∪ ∩ ⊆ ⊇ ==`, `tangent`, `^`.
7. Basis-level involutions (reverse, involute, clifford and their pseudo/anti variants), Grassmann/Hodge
   complements with their parities, `metric`/`antimetric` of blades, grade/parity helpers.
8. Printing of spaces and basis names (`⟨+-+⟩`, `T¹⟨+++₁⟩'`, `v₁₂`, `w¹²`, `∂₁v₁`, `v∞∅₁`, ...).

Out of scope here (other packages): products of multivectors (Grassmann), `MetricTensor`
(`/Users/alokbeniwal/chakravala/Grassmann.jl/src/forms.jl:1603`), abstract type roots (AbstractTensors),
`Derivation`/`∇` (Leibniz.jl `LB/Leibniz.jl:109-175`).

---

## 2. Public API inventory

### 2.1 Export statements (exhaustive)

| File:line | Exported names |
|---|---|
| DS/DirectSum.jl:20 | `TensorBundle, Signature, DiagonalForm, Manifold, Submanifold, ℝ, ⊕, mdims` |
| DS/DirectSum.jl:426 | `@V_str, @S_str, @D_str` |
| DS/DirectSum.jl:444-450 | `ℝ0, ℝ1, ..., ℝ9` (one `export` per name inside the loop) |
| DS/DirectSum.jl:463 | `Single` |
| DS/DirectSum.jl:556 | `Zero, One` |
| DS/DirectSum.jl:629 | `Infinity` |
| DS/generic.jl:15 | `basis, grade, order, options, metrichash, polymode, dyadmode, diffmode, diffvars` |
| DS/generic.jl:16 | `valuetype, value, hasinf, hasorigin, isorigin, norm, indices, tangent, isbasis, ≅` |
| DS/generic.jl:17 | `pseudograde, pseudoreverse, pseudoinvolute, pseudoclifford, metric` |
| DS/generic.jl:64 | `isdyadic, isdual, istangent` |
| DS/generic.jl:168 | `involute, clifford` |
| DS/operations.jl:15 | `⊕, χ, gdims` |
| DS/operations.jl:330 | `complementleft, complementright, ⋆, complementlefthodge, complementrighthodge` |
| DS/operations.jl:331 | `complementleftanti, complementrightanti` |
| DS/basis.jl:49 | `@basis, @basis_str, @dualbasis, @dualbasis_str, @mixedbasis, @mixedbasis_str` |
| DS/basis.jl:204 | `Λ, @Λ_str, getalgebra, getbasis, TensorAlgebra, SubAlgebra` |
| DS/grade.jl:2 | `grade, gdims, Grade` |

Note: `metric` is exported by DirectSum, Leibniz *and* AbstractTensors with different bindings, so
`using DirectSum, Leibniz, AbstractTensors` makes bare `metric` ambiguous (Oracle: `UndefVarError`
ambiguity). Always qualify `DirectSum.metric`.

Non-exported symbols that downstream Grassmann imports explicitly and therefore must also be public in
the port (`/Users/alokbeniwal/chakravala/Grassmann.jl/src/Grassmann.jl:33-37`,
`.../Grassmann.jl/src/parity.jl:17-18`, plus `DirectSum.x` qualified uses):
`V0, generate, getalgebra, getbasis, dual, Basis, metrichash, antimetric, signbool, antireverse,
antiinvolute, anticlifford, paritymetric, parityanti, submanifold (12 uses), supermanifold, orand,
eval_shift, diagonalform, options, diagsig, indexparity! (Leibniz), TensorBundle, basis`.

### 2.2 Types

| Name | Declaration | Role | File:line |
|---|---|---|---|
| `TensorBundle{n,Options,Metrics,Vars,Diff,Name}` | `abstract type ... <: Manifold{n,Int}` | abstract space descriptor; `Manifold{V,T}` is from AbstractTensors (`AT:49`), so here the "V" slot of `Manifold` holds the Int `n` | DS/DirectSum.jl:64 |
| `Signature{Indices,Options,Signatures,Vars,Diff,Name}` | zero-field struct `<: TensorBundle{...}` | +/- metric as `UInt` bitmask | DS/DirectSum.jl:131-133 |
| `DiagonalForm{Indices,Options,Signatures,Vars,Diff,Name}` | zero-field struct | diagonal metric; `Signatures` = 1-based index into global `diagonalform_cache` | DS/DirectSum.jl:193-195 |
| `Submanifold{V,n,Indices}` | zero-field struct `<: TensorTerm{V,n,Int}` | subspace / space handle / basis blade (see 3.6) | DS/DirectSum.jl:252-254 |
| `Single{V,G,B,T}` | struct with field `v::T`, `<: TensorTerm{V,G,T}` | coefficient `v` times basis blade `B` | DS/DirectSum.jl:457-461 |
| `One{V}` | `const One{V} = Submanifold{V,0,UInt(0)}` | scalar unit blade | DS/DirectSum.jl:552 |
| `Zero{V}` | zero-field struct `<: TensorTerm{V,0,Int}` | additive zero; printed `𝟎` | DS/DirectSum.jl:563-565 |
| `Infinity{V}` | zero-field struct `<: TensorTerm{V,0,Float64}` | printed `∞` | DS/DirectSum.jl:636-638 |
| `SubAlgebra{V}` | `abstract type <: TensorAlgebra{V,Int}` | basis container root | DS/basis.jl:143 |
| `Basis{V}` (alias `Λ`) | `@computed struct` fields `b::Values{1<<mdims(V),Submanifold{V}}`, `g::Dict{Symbol,Int}` | dense cached basis, n <= 8 | DS/basis.jl:158-161, 206 |
| `SparseBasis{V}` | struct fields `b::Vector{Symbol}`, `g::Dict{Symbol,Int}` | label cache only, 8 < n <= 22 | DS/basis.jl:309-312 |
| `ExtendedBasis{V}` | zero-field struct | no cache, n > 22 | DS/basis.jl:356 |
| `Grade{N,G}` | zero-field struct `<: Integer` | typed grade marker, printed `Λ$G` | DS/grade.jl:4-10 |

Abstract roots used (AbstractTensors): `TensorAlgebra{V,T} <: Number` (`AT:32`), `Manifold{V,T} <:
TensorAlgebra{V,T}` (`AT:49`), `TensorGraded{V,G,T} <: Manifold{V,T}` (`AT:64`), `TensorTerm{V,G,T} <:
TensorGraded{V,G,T}` (`AT:108`). Consequence: every `Submanifold` and `Single` *is a* `Manifold`, which is
why Leibniz's `grade(V::Manifold)` (LB/generic.jl:12) applies to blades (see 4.7).

### 2.3 Constructors, constants, macros

| Name | Signature | Semantics | File:line |
|---|---|---|---|
| `Signature{N,M,S,F,D,L}()` | inner | raw constructor | DS/DirectSum.jl:132 |
| `Signature{N,M,S,F,D}()` | | `L=1` | :135 |
| `Signature{N,M,S}()` | | `F=0,D=0` | :136 |
| `Signature{N,M}(b::BitArray{1},f=0,d=0)` | | `S = bit2int(b[1:N])` | :137 |
| `Signature{N,M}(b::Vector{Bool},f=0,d=0)` | | via BitArray | :138 |
| `Signature{N,M}(s::String)` | | `b[k] = (s[k]=='-')` | :139 |
| `Signature(str::String)` | | `Signature{length(str)}(str)` (char count) | :140 |
| `Signature(n::Int,d=0,o=0,s::UInt=0)` | | `Signature{n,tensorhash(d,o),s}()` | :141 |
| `Signature{N}(s::String)` | | string grammar, 4.1 | :142-150 |
| `Signature(V::Submanifold)` | | subspace -> Signature (4.6) | :380-388 |
| `Signature(V::DiagonalForm)` | | `signbit` of each diag entry | :389 |
| `DiagonalForm{N,M,S,F,D,L}()` .. `{N,M,S}()` | | raw, defaults `L=1,F=0,D=0` | :194-198 |
| `DiagonalForm{N,M}(b::Values{N})` | | `S = diagsig(M,b)` (cache index) | :199 |
| `DiagonalForm{N,M}(b::Vector)`, `DiagonalForm(b::Values)`, `(b::Tuple)`, `(b::Vector)`, `(b...)` | | all `M=0` | :200-204 |
| `DiagonalForm(s::String)` | | `DiagonalForm(Meta.parse(s).args)` | :205 |
| `DiagonalForm(V::Signature)` | | entries `t ? -1 : 1` | :390 |
| `Submanifold{V,n,S}()` | inner | raw | :253 |
| `Submanifold(V::Int)` | | `Submanifold{V,V}()` = full subspace of Int space | :256 |
| `Submanifold(V::Manifold)` | | `Submanifold{V,rank(V)}()` | :257 |
| `Submanifold{V,N}()` | | bits `(1<<N)-1` (the first N generators) | :259 |
| `Submanifold{M,N}(b::UInt)` | | raw `Submanifold{M,N,b}` (no normalisation, no grade check) | :260 |
| `Submanifold{M,N}(b::Values{N})` | | bits from 1-based indices | :262 |
| `Submanifold{M}(b::UnitRange / Tuple / Values / b...)` | | subspace with those indices | :263-267 |
| `Submanifold{M}(b::Vector{Int})`, `Submanifold{V,G}(b::VTI)`, `Submanifold{V}(b::Int...)` | | *basis blade* via `getbasis` (dispatch quirk, 4.6) | :272-281 |
| `Submanifold{V}()`, `Submanifold{V}(i::UInt)`, `Submanifold{V}(b::BitArray)` | | `getbasis(V, ...)` (basis blade) | DS/basis.jl:286-288 |
| `Manifold(::Type{T})` | | `T()` for the three concrete kinds | DS/DirectSum.jl:363 |
| `Manifold(V::Submanifold{M})` | | `M` if `M` is a Submanifold or Int, else `V` | :376-379 |
| `submanifold(V)` | | `Submanifold(V)` for bundles/Ints; for basis blades `V(Manifold(V))` | :392-394 |
| `TensorBundle(s::Number)`, `TensorBundle(s::String)`, `Manifold(s::String/Number)` | | V-string dispatcher (4.1) | :410-424 |
| `@V_str`, `@S_str`, `@D_str` | macros | `TensorBundle(str)`, `Signature(str)`, `DiagonalForm(str)` evaluated at macro-expansion time | :428-438 |
| `V0` | const | `Signature(0)` | :442 |
| `ℝ` | const | `Signature(1)` = `⟨+⟩` | :443 |
| `ℝ0..ℝ9` | const | `Submanifold(n)` (Int-parented, prints `⟨111⟩` etc.) | :444-450 |
| `Single(...)` family | see 4.12 | | :464-493 |
| `Zero(V)`, `One(V)`, `Infinity(V)` (+ Type/Int/Submanifold variants) | | normalise `V` via `submanifold` | :566-574, 590-596, 639-655 |
| `Λ0`, `Λ0S` | const | `Λ{Submanifold(0)}()`, `Λ{ℝ0}()` | DS/basis.jl:223-224 |
| `Basis(s)` / `Λ(s)` | `Manifold`, `Int`, `(n,d,o=0,s=0)`, `String`, `(String,Symbol)` | `getalgebra` dispatch | DS/basis.jl:189-193 |
| `@Λ_str` | macro | `Basis(str)` | DS/basis.jl:208-210 |
| `collect(s::Manifold)` | | `Basis{s}()` (uncached, *direct* construction) | DS/basis.jl:183 |
| `SparseBasis(s)`, `SparseBasis(n,d,o,s)`, `SparseBasis(str)`, `SparseBasis(str,sym)` | | | DS/basis.jl:314-317, 341-343 |
| `ExtendedBasis(s)` etc. | | | DS/basis.jl:358-371 |
| `@basis q [sig=:V vec="v" cov="w" duo="∂" dif="ϵ"]` | macro | binds space + all blades | DS/basis.jl:88-92 |
| `@basis_str` | | `alloc(Manifold(str))` | :94-96 |
| `@dualbasis q [sig=:VV cov="w" dif="ϵ"]`, `@dualbasis_str` | | on `V'` | :106-112 |
| `@mixedbasis q [sig=:W ...]`, `@mixedbasis_str` | | on `V⊕V'`, then `V'`, then `V` | :122-132 |
| `Grade{N,G}()`, `Grade{N}(G)`, `Grade(N,G)` | | | DS/grade.jl:5-7 |

### 2.4 Functions and operators

Unicode operator -> ASCII alias is given where one exists.

| Name | Signature(s) | Semantics | File:line |
|---|---|---|---|
| `⊕` (`\oplus`), ASCII `+` | `(Signature,Signature)`, `(DiagonalForm,DiagonalForm)`, `(DiagonalForm,Signature)`, `(Signature,DiagonalForm)` | direct sum of spaces; `+` is literally the same method set | DS/operations.jl:36-68 |
| `⊕` | `(Submanifold,Submanifold)` | direct sum of subspaces/blades (no `+` alias here; `+` on blades is Grassmann's addition) | DS/operations.jl:69-74 |
| `⊕`, `+` | `(SubAlgebra,SubAlgebra)` | `getalgebra(V⊕W)` | DS/basis.jl:153-154 |
| `^` | `(TensorBundle{N,0 or 4}, i::Integer)` | repeated `⊕`; `i==0 -> V0` | DS/operations.jl:75-87 |
| `'` = `adjoint` | `Signature`, `DiagonalForm`, `Submanifold`, `SubAlgebra`, `Single` | dual space (error on dyadic) | DS/generic.jl:146-162; DS/basis.jl:145; DS/DirectSum.jl:527 |
| `dual` | `dual(V)`; `dual(V,B,M=rank(V)/2)` | `isdyadic(V) ? V : V'`; half-swap of a dyadic mask | DS/generic.jl:143-144 |
| `flipsign(N,S::UInt)` | | `(2^N-1) & ~S` (not exported; shadows nothing in Base because Base.flipsign is not imported) | DS/generic.jl:141 |
| `∪` | bundle/bundle, bundle/Submanifold, Submanifold/Submanifold | union (4.5) | DS/operations.jl:91-116; varargs LB/generic.jl:194-195 |
| `∩` | same | intersection | DS/operations.jl:118-140; LB/generic.jl:197-198 |
| `⊆`, `⊇` | same | subset; `a⊇b = b⊆a` | DS/operations.jl:142-168 |
| `==`, `equal` | pairs of Signature/DiagonalForm/Submanifold (and their Types) | `equal(a,b) = a⊆b && a⊇b`; AbstractTensors routes `==` of any two `TensorAlgebra` to `equal` (`AT:298`) | DS/DirectSum.jl:362-372 |
| `equal` | `(TensorTerm{V,G},TensorTerm{V,G})` | same basis -> compare values, else both values must be 0 | DS/DirectSum.jl:510 |
| `tangent` | `(Signature or DiagonalForm, d=1, f=(F≠0 ? F : 1))` | add tangent variables/order (4.5.7) | DS/generic.jl:128-129 |
| `subtangent(V)` | | `V(grade(V)+1:mdims(V)...)` | DS/generic.jl:131 |
| `loworder` | Signature/DiagonalForm/Submanifold/Type | `diffmode - 1` (floor 0) | DS/generic.jl:133-137 |
| `rank`, `mdims`, `length`, `firstindex`, `lastindex` | bundles | `n`; `firstindex=1` | DS/DirectSum.jl:65-66, 159-161 |
| `mdims(::Submanifold{M,G})` | | `isbasis ? mdims(M) : G` | DS/generic.jl:43 |
| `getindex` | `Signature[i]` -> Bool (true = negative), `[vector/range]`, `[:]` (drops tangent slots) | | DS/DirectSum.jl:152-158 |
| `getindex` | `DiagonalForm[i]`, `[:]` | diag value (negated if dual) | DS/DirectSum.jl:219-224 |
| `getindex` | `Submanifold[i]`, `[:]`, iteration | metric of i-th *included* generator (4.6) | DS/DirectSum.jl:283-318 |
| `V(b::Int...)`, `V(b::AbstractVector{Int})`, `V(b::AbstractRange{Int})` | callable spaces | build Submanifold (4.6) | DS/generic.jl:23-35 |
| `(M::Submanifold{V})(b::Int)`, `(M)(Val(G))`, `(M::Single)(G)` | | grade projection for basis blades | DS/generic.jl:26-29 |
| `(W::Submanifold)(b::Submanifold)`, `(W::Submanifold)(b::Zero)`, `(T::Signature)(::Signature)`, `(W::Signature)(b::Submanifold)` | | restriction/embedding/evaluation (4.6.4) | DS/operations.jl:191-238 |
| `(V::Signature/DiagonalForm/Submanifold)(s::UniformScaling)` | | pseudoscalar of the non-tangent part, scaled | DS/DirectSum.jl:533-536 |
| `(W::bundle)(b::Single)` | | re-home a Single | DS/DirectSum.jl:537 |
| `options`, `options_list` | bundle / Submanifold | raw `M`; `(hasinf,hasorigin,dyadmode,polymode)` | DS/generic.jl:46-47 |
| `polymode`, `dyadmode`, `diffmode`, `diffvars` | bundle, Submanifold, Int | decode (3.3) | DS/generic.jl:52-62; LB/generic.jl:19-28 |
| `_polymode,_dyadmode,_hasinf,_hasorigin` | `(M::Int)` | option decoders | DS/generic.jl:37-40 |
| `isdyadic`, `isdual`, `istangent` | any | `dyadmode<0`, `dyadmode>0`, `diffvars≠0` | LB/generic.jl:34-44 |
| `hasinf`, `hasorigin` | bundle, Submanifold, Single, Int | 4.7 | DS/generic.jl:115-120 |
| `hasconformal(V)` | | `hasinf && hasorigin` | LB/generic.jl:53 |
| `isinf(e::Submanifold)`, `isorigin(e)` | | 4.7 (isorigin buggy) | DS/generic.jl:121-122 |
| `metric` | `(bundle)` -> raw S; `(Signature,b::UInt)` -> ±1; `(Submanifold basis)`; `(Single)` | 4.9 | DS/generic.jl:20-21; DS/operations.jl:358-381 |
| `metrichash` | `(Int)`, `(bundle)`, `(Manifold,b)`, `(Signature,b)` | same as metric (legacy) | DS/generic.jl:48-51 |
| `antimetric` | `(Submanifold basis)`, `(Single)` | 4.9 | DS/operations.jl:371-379 |
| `det` | Signature -> ±1; DiagonalForm -> product | | DS/generic.jl:87-88 |
| `abs` | Submanifold, bundle | `sqrt(abs(det))`; broken (StackOverflow in oracle) | DS/generic.jl:89-90 |
| `isdiag` | Signature -> `!hasconformal`; DiagonalForm -> true; Submanifold -> of parent | | DS/generic.jl:66-68 |
| `value` | bundle/Submanifold -> `one(T)`; Single -> `v` (converted if T given) | | DS/generic.jl:70-72 |
| `basis` | Zero -> `getbasis(V,0)`; Submanifold -> itself if basis else `Submanifold(m)`; Single -> `B` | | DS/generic.jl:74-86 |
| `isbasis` | Submanifold -> `issubmanifold(V)`; bundles/Single -> false | | DS/generic.jl:79-81 |
| `UInt(b)` | Submanifold/Single | the bitmask `B` | DS/generic.jl:83-84 |
| `supermanifold` | bundle -> itself; `Submanifold{M}` -> `M` | | DS/generic.jl:91-92 |
| `volume`, `isvolume`, `scalar`, `vector`, `bivector`, `trivector`, `isscalar`... | Submanifold | keep if grade matches else `Zero(V)`; `isvolume` references undefined `V` (bug) | DS/generic.jl:94-103 |
| `grade(t,G::Int)` / `grade(t,Val(G))` | | grade projection | DS/generic.jl:108-111 |
| `pseudograde(t,G)` | | `grade(t, grade(V)-G)` | DS/generic.jl:112-113 |
| `grade_basis(v,b)`, `grade(v,b)`, `pseudograde(v,b)` | `(any, Submanifold)` | delegate to `(V,B)` forms | DS/generic.jl:170-172 |
| `grade(V,B::UInt)`, `grade_basis(V,B)`, `pseudograde(V,B)` | | 4.7 | LB/generic.jl:146-153 |
| `grade(V::Manifold)`, `pseudograde(V::Manifold)`, `grade(::Type{<:TensorGraded})` | | 4.7 | LB/generic.jl:9-13 |
| `order` | Submanifold, Single, Manifold, any | number of tangent bits; 0 default | DS/generic.jl:44-45; LB/generic.jl:14-15 |
| `≅` (`\cong`) | any | same `grade`, `order`, `diffmode` | LB/generic.jl:30 |
| `reverse`, `~` (ASCII for reverse), `conj` (identical to reverse), `involute`, `clifford` | Submanifold, Single, Zero, Infinity | sign flips by grade parity (4.8) | DS/generic.jl:187, 220-233; DS/DirectSum.jl:618-619, 677-678 |
| `pseudoreverse`, `pseudoinvolute`, `pseudoclifford` (aliases `antireverse`, `antiinvolute`, `anticlifford`) | same | by pseudograde parity | DS/generic.jl:228-234 |
| `even`, `odd` | `TensorGraded{V,G}` | keep if `G` even/odd | DS/operations.jl:387-388 |
| `real`, `imag` | `TensorGraded{V,G}` | keep if reverse-even / reverse-odd | DS/operations.jl:395, 402 |
| `complementright` (alias `!` and `complement` in AbstractTensors `AT:309-310`) | Submanifold, Single | Euclidean right complement | DS/operations.jl:339-356 |
| `complementleft` | same | Euclidean left complement | same |
| `complementrighthodge` (`⋆`, `hodge` in AbstractTensors `AT:311-312`) | Submanifold, Single (+ metric arg `g`) | Hodge right complement | same |
| `complementlefthodge` | same | Hodge left complement | same |
| `complementrightanti(t)`, `complementleftanti(t)` | | `complement*(antimetric(t))` | DS/operations.jl:333-334 |
| `parityleft/right`, `paritylefthodge/righthodge` | `(DiagonalForm or Submanifold, B, G)`, `(Submanifold)` | ±1 (or signed metric product) | DS/operations.jl:277-310 |
| `paritymetric`, `parityanti` | `(DiagonalForm or Submanifold, B)`, `(Submanifold)` | product of metric over blade / over complement | DS/operations.jl:312-324 |
| `signbool(t)` | | `Bool -> t ? -1 : 1`, else identity | DS/operations.jl:336-337 |
| `χ` | `TensorAlgebra`, `TensorTerm` | Euler characteristic (Leibniz) | LB/generic.jl:173-175 |
| `labels(V, vec, cov, duo, dif)` | | label Symbols in basis order | DS/basis.jl:19-32 |
| `generate(V)`, `generate(V,N)` | | Vector of basis `Submanifold{V}` in basis order | DS/basis.jl:36-47 |
| `alloc(V, sig, vec, cov, duo, dif)` | | macro body builder | DS/basis.jl:57-78 |
| `lookup_basis(V, v::Symbol)` | | name -> blade with sign | DS/basis.jl:134-139 |
| `indexparity(V, v::Symbol)` | | `(parity, indices, space, iszero)` | DS/basis.jl:429-458 |
| `getalgebra` | `(V)`, `(n,m,s,S,vs,f,d)`, `(n,d,o,s,c)`, `(n,m,s)` | cached `Basis`/`SparseBasis`/`ExtendedBasis` | DS/basis.jl:226-268 |
| `getsparse`, `getextended` | same shapes | | DS/basis.jl:380-425 |
| `getbasis(V,b)` | `b::UInt`, `Integer`, `Symbol` | blade from the optimal container | DS/basis.jl:276-284 |
| `getproperty(::Basis/SparseBasis/ExtendedBasis, ::Symbol)` | | `.b`, `.g`, label, or parsed name | DS/basis.jl:173-181, 331-339, 361-367 |
| `getindex(::Basis, i)`, `(::SparseBasis, i)` | | i-th blade in basis order | DS/basis.jl:169-171, 319-329 |
| `one`, `zero` | Submanifold types/values, bundles, Single | `One`/`Zero` | DS/basis.jl:289-300 |
| `evaluate1`, `evaluate2`, `eval_shift` | | covector-on-vector evaluation; `evaluate2` is broken (references undefined `N`) | DS/operations.jl:172-189 |
| `tensorhash(d,o,c=0,C=0)` | | options encoder (3.3) | DS/DirectSum.jl:83-85 |
| `nameindex`, `namelist`, `namecache` | | naming scheme registry (3.9) | DS/DirectSum.jl:87-127 |
| `diagonalform(V)`, `diagsig(M,b)`, `diagonalform_cache` | | DiagonalForm metric store | DS/DirectSum.jl:207-217 |
| `shift_indices`, `printindices` | | index display helpers | DS/DirectSum.jl:403-406 |
| `sig`, `printsep` | | display helpers | DS/DirectSum.jl:167-173, 323 |
| `orand(T=Float64)` | | `2(rand(T)-0.5)` uniform in [-1,1) | DS/generic.jl:253 |
| `rand(::SamplerType{...})` | Manifold/Submanifold/Single samplers | Julia-only | DS/generic.jl:255-265 |
| `div, rem, mod, mod1, fld, fld1, cld, ldexp, mod2pi, rem2pi, rad2deg, deg2rad, round, rationalize` on Submanifold/Single | | apply to coefficient (Submanifold versions construct `Submanifold{V,G}(Int)` -- nonsensical) | DS/generic.jl:236-249 |
| conversions `Real, Float64, Bool, Int, Rational, Complex` of Single/Submanifold/Zero/Infinity | | value extraction; `Complex(Single grade>0)` puts value in imaginary part | DS/DirectSum.jl:495-508, 576-588, 644-647 |
| `isapprox` Single vs number | | via `Single{Manifold(a)}(b)` | DS/DirectSum.jl:512-517 |
| `*` number x Submanifold, number x Single | | `Single{V}(a,b)`; for Single multiplies values | DS/DirectSum.jl:519-529 |
| `adjoint(::Single)` | | `Single{dual(V),G,B',T}(conj(v))` | DS/DirectSum.jl:527 |
| `iszero, isone, isinf, value, abs2, show, ==` for Zero/Infinity | | | DS/DirectSum.jl:598-622, 657-681 |
| `convert`, `copysign` for Single | | | DS/operations.jl:406-409 |
| `mdims, tdims, grade, grades, gdims, combo, binomsum, spinsum, antisum, indexbasis, gdimsall, ... on Grade` | | forward to `(N,G)` | DS/grade.jl:15-28 |
| `+,-,==` on Grade | | `Grade{N,G+F}` etc. | DS/grade.jl:30-41 |

### 2.5 Leibniz symbols DirectSum depends on (imported at DS/DirectSum.jl:34-48)

These define index ordering, printing and parity and must be ported together with DirectSum:

| Symbol | Meaning | File:line |
|---|---|---|
| `vio = ('∞','∅')` | projective glyphs | LB/indices.jl:6 |
| `digs, low_case, upp_case, alphanumv, alphanumw` | `alphanumv = "1234567890abc..zABC..Z"`, `alphanumw = "1234567890ABC..Zabc..z"` | LB/indices.jl:7-11 |
| `subs::Dict{Int,Char}` | `-1=>'∞', 0=>'∅', 1..9=>'₁'..'₉', 10=>'₀', 11..36 => alphanumv[11..36]` (= `'a'..'z'`) | LB/indices.jl:14-28 |
| `sups::Dict{Int,Char}` | `-1=>'∞', 0=>'∅', 1..9=>'¹'..'⁹', 10=>'⁰', 11..36 => alphanumw[11..36]` (= `'A'..'Z'`) | LB/indices.jl:31-45 |
| `pre = ("v","w","∂","ϵ")`, `PRE = ("X","x","Y","y")` | name prefixes: vector, covector, tangent-derivation, tangent-function | LB/indices.jl:48-49 |
| `vsn = (:V,:VV,:W)`, `VSN` | default macro variable names | LB/indices.jl:52-53 |
| `indexbits(N, indices)` | BitVector length N with given 1-based positions true | LB/indices.jl:62-68 |
| `index_limit = 20`, `digitsfast` | cached binary digit vectors | LB/indices.jl:70-98 |
| `indices(b)`, `indices(b,N)` | ascending 1-based positions of set bits | LB/indices.jl:106-119 |
| `shift_indices`, `shift_indices!` | map positions to display indices (∞ -> -1, ∅ -> 0, rest shifted) | LB/indices.jl:121-135 |
| `printindex`, `printindices`, `printlabel`, `showvalue`, `indexstring`, `indexsymbol`, `indexsplit` | printing | LB/indices.jl:139-213 |
| `indexparity!` | bubble sort with parity (+ cancellation variant) | LB/indices.jl:215-247 |
| `bit2int(b::BitVector)` | little-endian bits -> UInt | LB/utilities.jl:26-28 |
| `gdimsall, gdimseven, gdimsodd` (`binomial`, `binomial_set`) | binomial rows | LB/utilities.jl:39-54 |
| `intlog(M)` | `Int(log2(M))` (exact only for powers of 2) | LB/utilities.jl:61 |
| `mvec, svec, mvecs, svecs, insert_expr, promote_type` | Grassmann codegen helpers | LB/utilities.jl:62-96 |
| `algebra_limit=8, sparse_limit=22, cache_limit=12, fill_limit=0.5` | size thresholds | LB/utilities.jl:104-107 |
| `combo(n,g)` | lexicographic g-subsets of 1:n (cached) | LB/utilities.jl:109-133 |
| `binomsum, binomcumsum, spinsum, spincumsum, antisum, anticumsum` | grade offset prefix sums | LB/utilities.jl:135-179 |
| `bladeindex, basisindex, spinindex, antiindex` | ranks (1-based) | LB/utilities.jl:181-219 |
| `indexbasis(n,g)`, `indexbasis(N)`, `indexbasis_set`, `indexeven(_set)`, `indexodd(_set)` | masks in basis order | LB/utilities.jl:221-250 |
| `lowerbits(N,S,B)`, `expandbits(N,S,B)` | subspace coordinate maps (pext/pdep; lowerbits buggy) | LB/utilities.jl:254-287 |
| `grade, pseudograde, order, options, metric, polymode, dyadmode, diffmode, diffvars` for Int and fallbacks | | LB/generic.jl:9-28 |
| `hasconformal, hasinf/hasorigin(V,A,B), hasinf2, hasorigin2` | conformal product helpers | LB/generic.jl:53-67 |
| `diffmask, symmetricsplit, symmetricmask, diffcheck` | tangent-bit masks | LB/generic.jl:69-105 |
| `mixed(V,ibk)`, `combine(v,w,iak,ibk)` | embed masks into `V⊕V'` / `V⊕W` | LB/generic.jl:109-130 |
| `parityreverse, parityinvolute, parityclifford, parityconj` | grade-parity predicates | LB/generic.jl:139-142 |
| `parityright/left(V::Int,B::Int,G,N)`, `parityrighthodge/lefthodge`, `parity{left,right}null(pre)` | complement parities | LB/generic.jl:202-231 |
| `complement(N,B,D=0,P=0)` | complement mask | LB/generic.jl:233-237 |
| `χ`, `count_gdims` | Euler characteristic | LB/generic.jl:173-190 |


---

## 3. Data representations

### 3.1 What is compile-time vs runtime in Julia

Everything describing a space is a *type parameter*; all space and blade values are zero-byte
singletons:

| Julia object | Type params (compile-time) | Runtime payload |
|---|---|---|
| `Signature{N,M,S,F,D,L}()` | N::Int, M::Int, S::UInt, F::Int, D::Int, L::Int | none |
| `DiagonalForm{N,M,S,F,D,L}()` | same, but S::Int = cache index | none (values live in global `diagonalform_cache`) |
| `Submanifold{V,G,B}()` | V (a space value or Int), G::Int, B::UInt | none |
| `Single{V,G,B,T}` | V (a Submanifold handle), G, B (a Submanifold value), T | `v::T` only |
| `Zero{V}`, `Infinity{V}`, `One{V}` | V | none |
| `Basis{V}` | V | `b::Values{2^n}` of singletons (i.e. nothing), `g::Dict{Symbol,Int}` |
| `Grade{N,G}` | N, G | none |

All metadata functions are `@pure` so they constant-fold; the global caches are consulted only during
compilation/generated-function expansion in Grassmann. A `Single` at runtime is literally its
coefficient; a basis blade costs nothing. This is the performance model the Lean port has to emulate
(section 8).

### 3.2 `TensorBundle{n,Options,Metrics,Vars,Diff,Name}` parameters

| Param | Julia name in docs | Type | Meaning |
|---|---|---|---|
| `n` (`Indices`) | rank | Int | total number of generators, *including* ∞/∅ slots and all tangent slots |
| `Options` (`M`) | ℙ | Int | bit field, 3.3 |
| `Metrics` (`S`) | g | `UInt` for Signature; `Int` cache index for DiagonalForm | metric, 3.4 |
| `Vars` (`F`) | ν | Int | number of tangent (differential) variables per side; can be negative in raw types (tangent slots first); 0 = none |
| `Diff` (`D`) | μ | Int | tangent order = multiplicity limit of Leibniz-Taylor monomials (`diffmode`) |
| `Name` (`L`) | -- | Int | 1-based index into `namecache`; 1 = `("v","w","∂","ϵ")`, 2 = `("X","x","Y","y")` |

Accessors: `rank/mdims = n` (DS/DirectSum.jl:65-66), `options = M` (DS/generic.jl:46),
`metric/metrichash = S` (DS/generic.jl:20,49), `diffvars = F` (:55), `diffmode = D` (:54),
`nameindex = L` (DS/DirectSum.jl:112). For `Int` spaces (LB/generic.jl:16-22): options 0, metric
`UInt(0)`, polymode true, dyadmode 0, diffmode 0, diffvars 0.

### 3.3 Options bit layout and `tensorhash`

`tensorhash(d,o,c=0,C=0) = (1<<(d-1)) | (1<<(2o-1)) | (c<0 ? 8 : (1<<(3c-1))) | (1<<(5C-1))`
(DS/DirectSum.jl:83-85) with Julia shift semantics: a *negative* shift count shifts the other way, so
`1<<(-1) == 0`. Hence for the intended inputs:

| bit | value | set by | decoder (DS/generic.jl:37-40) |
|---|---|---|---|
| 0 | 1 | `d=1` (has ∞) | `_hasinf(M) = M%16 ∈ (1,3,5,7,9,11)` |
| 1 | 2 | `o=1` (has ∅) | `_hasorigin(M) = M%16 ∈ (2,3,6,7,10,11)` |
| 2 | 4 | `c=1` (dual space `V'`) | `_dyadmode(M) = M%16 ∈ 8:11 ? -1 : Int(M%16 ∈ (4,5,6,7))` |
| 3 | 8 | `c=-1` (dyadic `V⊕V'`, "mixed") | (same) |
| 4 | 16 | `C=1` (polymode = false) | `_polymode(M) = iszero(M & 16)` |

Oracle decode table for M = 0..31 (`t3.jl`): 0..11 as expected; **M%16 ∈ 12..15 decodes to
hasinf=false, hasorigin=false, dyadmode=0** (bits ignored); 16..27 = same as 0..11 with polymode=false.

Other `tensorhash` inputs (only reachable via the digit-string grammar) collide: `d=2 -> 2` (looks like
∅), `d=3 -> 4` (dual), `o=2 -> 8` (dyadic), ... Oracle: `S"12"` = `⟨∅⟩` (n=1, d=2 gives origin bit).

`dyadmode`: 0 plain, +1 dual (printed `'`), -1 dyadic/mixed (printed `*`).
`polymode` only affects tangent-index glyphs (sub vs superscript) in printing.

### 3.4 Metric storage

* **Signature**: bit `k-1` of `S` set iff generator `k` squares to -1 (`getindex(::Signature,i)` returns
  `Bool`, true = negative; DS/DirectSum.jl:152-155). `V[:]` returns the first
  `n - (isdyadic ? 2F : F)` entries (tangent slots excluded; ∞/∅ slots *included*;
  DS/DirectSum.jl:158). For conformal strings the ∞ slot gets `+` (0) and the ∅ slot gets `-` (1) by
  character replacement (DS/DirectSum.jl:148): `S"∞∅+++"` has `S = 0b00010`.
  Dual flips *all n bits* (`flipsign(n,S) = (2^n-1) & ~S`, DS/generic.jl:141), including tangent slots
  and ∞/∅ slots: `tangent(ℝ^3)'` has S = 0b1111; `S"∞∅+++"'` has S = 0b11101.
  `det(Signature) = (-1)^popcount(S)` (DS/generic.jl:87) -- over all bits.
  `metric(V::Signature,b::UInt) = (-1)^popcount(S & b)` (DS/generic.jl:21, 51).
* **DiagonalForm**: `S` is a 1-based index into the global append-only
  `diagonalform_cache::Vector{Values}` (DS/DirectSum.jl:208); `diagsig(M,b)` (DS/DirectSum.jl:209-217)
  stores `SUB(b)` (negated) when `dyadmode(M) > 0`, deduplicates with `==`, returns the index.
  `diagonalform(V) = isdual(V) ? -cache[S] : cache[S]` (DS/DirectSum.jl:207). So the cache always holds
  *primal* values and the dual negates on read. Adjoint keeps `S`. The index is **session dependent**
  (Oracle: `V"1,1,1,0"` got index 4 because three earlier mis-parsed V-strings had been cached).
  Entries may be Int, Float, `Expr` (e.g. `1//2` stays an unevaluated Expr) or `Symbol`.
  `det(DiagonalForm) = prod(diagonalform)` (DS/generic.jl:88).
* **Int n**: Euclidean, every metric entry 1; `sig` prints `'1'`.

### 3.5 Generator (bit) layout -- the index ordering convention

Generators are numbered 1..n; generator `k` is bit `k-1` of every mask (`B & (1<<(k-1))`).

Non-dyadic space with `P = hasinf + hasorigin` and `F ≥ 0` tangent variables:

```
position:  1      2       P+1 ... n-F      n-F+1 ... n
meaning:   ∞      ∅       ordinary gens     tangent gens ∂1..∂F   (ϵ1..ϵF if dual)
           (only present when the option bit is set; ∅ is position 1 when there is no ∞)
```

Dyadic space `V⊕V'` (dyadmode -1) with `m` ordinary generators per side and `F` tangent variables,
`n = 2m + 2F` (conformal+dyadic is not constructible through ⊕):

```
1..m : v1..vm      m+1..2m : w1..wm     2m+1..2m+F : ∂1..∂F     2m+F+1..2m+2F : ϵ1..ϵF
```

`diffmask(V)` (LB/generic.jl:70-80): non-dyadic `((1<<F)-1) << (n-F)`; dyadic returns the pair
`(((1<<F)-1) << (n-2F), ((1<<F)-1) << (n-F))`. Oracle: `diffmask(tangent(ℝ^3)) = 0x8`,
`diffmask(tangent(ℝ^3,1,2)) = 0x18`, `diffmask(tangent(ℝ^3)⊕tangent(ℝ^3)') = (0x40, 0x80)`,
`diffmask(tangent(ℝ^3,1,2)⊕tangent(ℝ^3,1,2)') = (0xc0, 0x300)`.

`symmetricmask(V,a,b) = (a&~D, b&~D, (a&D)|(b&D), (a&D)&(b&D))` with `D` = union of diffmask(s)
(LB/generic.jl:92-97); `symmetricmask(V,a) = a & D`.

Basis ordering of the Grassmann algebra (`indexbasis`, `Λ(V).b`, `labels`, `generate`): **grade-major,
then lexicographic on the ascending index list** (combinations of `1:n` in `Combinatorics.combinations`
order). For n = 4:

```
k:     1  2  3  4  5  6   7   8   9  10  11  12   13   14   15   16
mask:  0  1  2  4  8  3   5   9   6  10  12   7   11   13   14   15
blade: 1  e1 e2 e3 e4 e12 e13 e14 e23 e24 e34 e123 e124 e134 e234 e1234
```

This is *not* colex/binary order within a grade (`e12,e13,e23,e14,...`); it is lex (`e12,e13,e14,e23`).

### 3.6 `Submanifold{V,G,B}` -- three roles in one type

`isbasis(s::Submanifold{V}) = issubmanifold(V)` (DS/generic.jl:79; DS/DirectSum.jl:269-270), i.e. a
Submanifold is a *basis blade* exactly when its parent `V` is itself a Submanifold.

1. **Subspace** of a bundle (`V` = Signature/DiagonalForm/Int): `B` = mask of included generators,
   `G` = popcount (not checked by the raw constructor). Printed `⟨+_+⟩`. Created by `V(i,j,...)`,
   `Submanifold{V,G}(B)`, ranges, etc.
2. **Full-rank handle** `Submanifold(V) = Submanifold{V,n,2^n-1}` (DS/DirectSum.jl:257, 259). This is
   what every algebra element carries as its `V`. `ℝ3 = Submanifold{3,3,0x7}` (Int parent) prints `⟨111⟩`;
   the Signature handle prints exactly like the Signature (`⟨+++⟩`) except for conformal/non-diagonal
   parents (`⟨∞∅11⟩`, see 5.3).
3. **Basis blade** `Submanifold{H,G,B}` with `H` a handle (or a proper-subspace handle): `B` is a mask
   in the *handle's local coordinates* (for a proper subspace handle with mask `S`, local bit j means
   parent generator `indices(S)[j]`). Printed via labels: `v₁₂`, `w¹`, `∂₁v₂`, `v∞∅₁`.
   `One{V} = Submanifold{V,0,0}` (DS/DirectSum.jl:552).

`supermanifold(::Submanifold{M}) = M` (DS/generic.jl:92). `Manifold(V::Submanifold{M})` returns `M` when
`M` is a Submanifold or Int, otherwise `V` itself (DS/DirectSum.jl:376-379).

### 3.7 `Single`, `Zero`, `One`, `Infinity`, `Grade`

* `Single{V,G,B,T}`: `V` normalised by `submanifold(V)` (handle), `B` normalised by `basis(C)`
  (DS/DirectSum.jl:459-460). Field `v::T`. Value type `T` may be any Number, `Expr`, `Symbol`, `Any`
  (when the coefficient is itself a TensorTerm).
* `Zero{V}`: `V` normalised; `value = 0`; `iszero` true; all involutions/complements return itself;
  `abs2` itself; equals any `TensorAlgebra` or number that `iszero` (DS/DirectSum.jl:563-622).
* `Infinity{V}`: `value = Inf` (Float64); `isinf` true; equality via `isinf(norm(x))`
  (DS/DirectSum.jl:636-683). Note `complementright` is *not* in its identity list (only
  hodge, clifford, complementleft, complementlefthodge, involute, conj, reverse; DS/DirectSum.jl:677).
* `One{V}`: the grade-0 basis blade.
* `Grade{N,G} <: Integer`: typed grade marker, `+`/`-` of two Grades gives a Grade, with Int gives Int;
  `==` true iff same `N,G` (DS/grade.jl:4-41).

### 3.8 Algebra containers, thresholds, caches

Thresholds (LB/utilities.jl:104-107, LB/indices.jl:70):

| const | value | meaning |
|---|---|---|
| `algebra_limit` | 8 | `Basis` (dense, all blades + label dict) for n <= 8 |
| `sparse_limit` | 22 | `SparseBasis` (labels only) for 8 < n <= 22; also combo/indexbasis cache boundary |
| (dyadic rule) | 16 | dyadic spaces with n > 2*algebra_limit go straight to `ExtendedBasis` (DS/basis.jl:263) |
| `cache_limit` | 12 | blade/basis/spin/anti index tables fully precomputed for n <= 12, lazily for 12 < n <= 20 |
| `index_limit` | 20 | digit/index caches; above it `bladeindex` is recomputed by linear search each call |
| `fill_limit` | 0.5 | (Grassmann sparsity heuristic) |

`getalgebra` cache (DS/basis.jl:226-261): four global caches `algebra_cache_{Int,Signature,
DiagonalForm,MetricTensor}` indexed `[f+1][d+1][n][S][m+1][s]` where f = diffvars, d = diffmode,
n = mdims, S = the handle mask (Dict key), m = options (a Vector of **12** Dicts -- options >= 12 index
out of bounds under `@inbounds`; Oracle: `Λ(Signature{3,16,UInt(0),0,0}())` **segfaults**), s = metric
(Dict key). The `Name` parameter is **not** part of the key (Oracle: after `Λ(Signature{3,0,0,0,0,2}())`,
`Λ(ℝ^3)` returns the `₂`-named basis -- collision bug). `getsparse`/`getextended` have identical
caches (DS/basis.jl:380-425).

Leibniz caches (all global, append-only): `combo_cache/extra`, `{binom,spin,anti}sum_cache/extra`,
`{blade,basis,spin,anti}index_cache/extra`, `indexbasis_cache/extra`, `digitsfast_cache/extra`,
`indices_cache` (Dict keyed by the mask **only**, ignoring N), `lowerbits_cache/extra`,
`expandbits_cache`. Module init prebuilds `bladeindex/basisindex/spinindex/antiindex` for n <= 12
and `indexbasis` for n <= 17 (LB/Leibniz.jl:180-185).

### 3.9 Naming schemes

`namecache::Vector{NTuple{4,String}}` initialised with `pre` then `PRE` (DS/DirectSum.jl:87-105).
`nameindex(t::NTuple{4,String})` returns the existing index or appends. `namelist(V) =
namecache[nameindex(V)]` gives `(vec, cov, duo, dif)` prefixes used by basis printing. Oracle:
`Λ(Signature{3,0,0,0,0,2}())` prints `DirectSum.Basis{⟨+++⟩₂,8}(X, X¹, X², X³, X¹², X¹³, X²³, X¹²³)`
(note: vector prefix `X` but superscripts, because `"X" ∉ ("v","∂")`, see 5.4).

---

## 4. Algorithms

### 4.1 String grammars

#### `S"..."` / `Signature(str)` (DS/DirectSum.jl:140-150)

```
Signature(str) = SignatureN(length(str) /*Unicode chars*/, str)
SignatureN(N, s):
  if s matches ^[0-9]+$:                                  # digit grammar, N ignored
      if length(s) < 4: s = s * "0"^(5 - length(s))       # "3"->"30000", "31"->"31000", "311"->"31100"
      n = digit s[1]; d = digit s[2]; o = digit s[3]; m = parse decimal s[4:end]
      return Signature{n, tensorhash(d,o), UInt(m), 0, 0, 1}
  else:
      opts = tensorhash(Int('∞' ∈ s), Int('∅' ∈ s))
      s2 = replace(s, '∞' => '+', '∅' => '-')
      bits[k] = (s2[k] == '-') for k in 1..N                # any other char counts as '+'
      return Signature{N, opts, bit2int(bits), 0, 0, 1}
```

Faithful quirks (Oracle, `t2/t9`): `S"3"=⟨+++⟩`, `S"31"=⟨∞++⟩` (3 generators incl. ∞), `S"311"=⟨∞∅+⟩`,
`S"3005"=⟨-+-⟩` (metric decimal 5 = 0b101), `S"30012"=⟨++-⟩` with S=0xc (bit beyond n kept),
`S"12"=⟨∅⟩`, `S"0"=⟨⟩`, `S""=⟨⟩`. Position is literal: `S"∅∞++"` = options 3 with S=0b0001 (the ∅ glyph
at position 1 got the `-`), printed `⟨∞∅++⟩`; `S"+∞+"` = `⟨∞++⟩` with S=0. No validation.

Intended grammar the Lean port should *accept* (and treat everything else as an error):
`^(∞)?(∅)?[+-]*$` plus the legacy digit form `^[0-9]{1,}$`.

#### `D"..."` / `DiagonalForm(str)` (DS/DirectSum.jl:205)

`DiagonalForm(Meta.parse(s).args)` -- the string is parsed as Julia and the *arguments of the top
expression* become the diagonal. Works for comma tuples of >= 2 literals: `D"1,1,1,0"`, `D"1,-1,2"`,
`D"1.5,2"` (-> `⟨1.5,2.0⟩`, promoted to Float64), `D"0.3,2.4,1"`. `D"1//2,3"` stores an *unevaluated*
`Expr` and prints `⟨1 // 2,3⟩`. `D"a,b"` stores Symbols. `D"3"` fails (`Int` has no `.args`).
Port grammar: comma-separated numeric literals (Int, decimal, `p//q` rational), length >= 1.

#### `V"..."` / `TensorBundle(str)` / `Manifold(str)` (DS/DirectSum.jl:410-424)

```
try parse(Int, s) -> return that Int (not a Signature!)        # V"3" == 3, V"30012" == 30012
catch; try DiagonalForm(s) catch; Signature(s)
```

Because `Meta.parse` accepts many sign strings as expressions, `V"..."` is **broken for many sign
patterns** (Oracle `t7`): `V"+-" = ⟨+,-⟩` (2-dim DiagonalForm of Symbols `:+`, `:-`), `V"-+" = ⟨-,+⟩`,
`V"+-+" = ⟨+,-(+)⟩`, `V"-++" = ⟨-,++⟩`, `V"-+-+" = ⟨-,+(-(+))⟩`, `V"∞∅+++" = ⟨++,∞∅,+⟩`
(3-dim DiagonalForm), `V"∞+++" = ⟨++,∞,+⟩`; correct Signatures only when `Meta.parse` throws:
`V"+++", V"++", V"--", V"+", V"-", V"++-", V"+--", V"---", V"-+++"`. The README claim
`V"∞∅+++"` is `TensorBundle{5,3}` is stale. The same bug affects `Λ"..."`, `basis"..."`,
`Basis(str)`, `SparseBasis(str)`, `ExtendedBasis(str)` (all go through `Manifold(str)`):
`Λ("+-+")` = `DirectSum.Basis{⟨+,-(+)⟩,4}(...)`, `basis"+-"` gives a 2-dim DiagonalForm.
Port: `V"..."` = if all digits -> Int space; elif contains `,` -> DiagonalForm; else Signature.
Golden tests for V-strings must be restricted to the inputs where Julia is correct, or flagged.

`TensorBundle(s::Number) = Signature(s)`: only `Int` works (`TensorBundle(3.0)` -> MethodError).

### 4.2 Index tables (Leibniz)

```
combo(n, g)       = all g-subsets of 1..n in lexicographic order (g=0 -> [[]])     # LB/utilities.jl:114
binomsum(n, i)    = Σ_{q=0}^{i-1} C(n,q)                  (i in 0..n+1)                 # :135,147
binomcumsum(n)    = [0, C(n,0), C(n,0)+C(n,1), ..., 2^n]  (length n+2)
spinsum(n, i)     = Σ_{q<i, q even} C(n,q);   spincumsum(n) likewise                 # :136
antisum(n, i)     = Σ_{q<i, q odd}  C(n,q);   anticumsum(n) likewise                 # :137
bladeindex(n, b)  = 1 if b == 0 else 1-based position of indices(b) in combo(n, popcount b)   # :181-184
basisindex(n, b)  = binomsum(n, popcount b) + bladeindex(n, b)                          # :185
spinindex(n, b)   = spinsum(n, popcount b) + bladeindex(n, b)     # meaningful for even b # :186
antiindex(n, b)   = antisum(n, popcount b) + bladeindex(n, b)     # meaningful for odd b  # :187
indexbasis(n, g)  = [bit2int(indexbits(n, c)) for c in combo(n,g)];  g == 0 -> [0]     # :222-244
indexbasis(n)     = vcat(indexbasis(n,0), indexbasis(n,1), ..., indexbasis(n,n))       # :245
```

Closed-form lex rank (use this in Lean instead of search/tables for n > 12):

```
bladeindex(n, b):                    # 1-based
  if b == 0: return 1
  c[1..k] = ascending positions of set bits of b (1-based)
  r = 0; prev = 0
  for i in 1..k:
    for j in prev+1 .. c[i]-1: r += C(n - j, k - i)
    prev = c[i]
  return r + 1
unrank(n, g, r):  inverse (greedy): for i in 1..g choose smallest c_i > c_{i-1} with cumulative
                  count C(n-j, g-i) not exceeding the remaining rank.
```

Oracle for n = 4, `b = 0..15`:

```
bladeindex = [1,1,2,1,3,2,4,1,4,3,5,2,6,3,4,1]
basisindex = [1,2,3,6,4,7,9,12,5,8,10,13,11,14,15,16]
spinindex  = [1,2,3,2,4,3,5,8,5,4,6,9,7,10,11,8]
antiindex  = [1,1,2,5,3,6,8,5,4,7,9,6,10,7,8,9]
binomcumsum(4) = [0,1,5,11,15,16]; spincumsum(4) = [0,1,1,7,7,8]; anticumsum(4) = [0,0,4,4,8,8]
indexbasis(4,2) = [0x3,0x5,0x9,0x6,0xa,0xc]
indexbasis(5,3) = [0x07,0x0b,0x13,0x0d,0x15,0x19,0x0e,0x16,0x1a,0x1c]
```

Known Leibniz defects to *not* port: `indexeven_set(N)`/`indexodd_set(N)` return **all** grades
`1..N` for `0 < N < 22` (they index `indexbasis_cache[N]` unfiltered; LB/utilities.jl:248-250);
`indexbasis(n,g)` for `g > n` is a BoundsError; `indices(b,N)` caches by `b` only and truncates to
bits `1..N+1` of the *first* call (LB/indices.jl:107-119).

### 4.3 Bit helpers

```
bit2int(bits::BitVector)    = Σ_k bits[k] << (k-1)                       # LB/utilities.jl:26
indexbits(N, idx)           = BitVector(N) with idx positions true        # LB/indices.jl:62
indices(b)                  = ascending 1-based set-bit positions          # LB/indices.jl:106
intlog(M)                   = Int(log2(M))   (exact for powers of 2)       # LB/utilities.jl:61
flipsign(N, S)              = (2^N - 1) & ~S                               # DS/generic.jl:141
dual(V, B, M = rank(V)/2)   = ((B << M) & (2^rank - 1)) | (B >> M)         # DS/generic.jl:144 (swap halves)
expandbits(N, S, B)         = pdep(B, S): local bit j of B -> j-th set bit of S   # LB/utilities.jl:279
lowerbits(N, S, B) (Julia)  = bits 1..|{i ∈ indices(B) : i ∈ indices(S)}|, i.e. (1<<popcount(B&S))-1
                              when B ⊆ S  -- BUG; intended pext(B, S)       # LB/utilities.jl:256
mixed(V, ibk)               = embed V or V' mask into V⊕V' layout (3.5):  # LB/generic.jl:109-117
    N = mdims V, D = diffvars V
    D ≠ 0:  A = ibk & (2^(N-D)-1); B = ibk & diffmask(V)
            isdual ? (A << (N-D)) | (B << N) : A | (B << (N-D))
    D == 0: isdual ? ibk << N : ibk
combine(v, w, iak, ibk)     = embed pair into v⊕w (non-dual pair):          # LB/generic.jl:119-130
    isdual(v) ≠ isdual(w) -> error
    if tangent on either:  gV = grade(V) (or V if Int), gW likewise
        (iak & (2^gV-1)) | ((ibk & (2^gW-1)) << gV) | (((iak|ibk) & diffmask(W)) << mdims(W))
        # the tangent part lands at the wrong offset (quirk; Oracle combine(T(ℝ²),T(ℝ²),0b101,0b011)=0x2d)
    else: iak | (ibk << mdims(V))
```

Oracle: `expandbits(5,0b10110,0b101) = 0x12`, `expandbits(4,0b1011,0b101) = 0x9`;
`lowerbits(5,0b10110,0b10100) = 0x3` (pext would give 0x6), `lowerbits(4,0b1011,0b1001) = 0x3`
(pext 0x5). `mixed(ℝ^3,0b101)=0x5`, `mixed((ℝ^3)',0b101)=0x28`, `mixed(tangent(ℝ^2),0b101)=0x11`,
`mixed(tangent(ℝ^2)',0b101)=0x24`, `dual(ℝ^3⊕(ℝ^3)',0b000101)=0x28`, `flipsign(3,0b010)=0b101`.

### 4.4 Space algebra

#### 4.4.1 Adjoint / dual (DS/generic.jl:143-162)

```
adjoint(V::Signature{N,M,S,F,D}):
  C = dyadmode(V); C < 0 -> error "$V is the direct sum of a vector space and its dual space"
  Signature{N, tensorhash(hasinf V, hasorigin V, Int(!Bool(C))), flipsign(N,S), F, D}   # Name -> 1, polymode -> true
adjoint(V::DiagonalForm{N,M,S,F,D}): same options rule, S unchanged (values negate on read)
adjoint(V::Submanifold{M,N,S}):     C<0 -> error; Submanifold{(M isa Int ? Signature(M)' : M'), N, S}
adjoint(G::SubAlgebra{V}) = Λ(dual(V));   dual(V) = isdyadic(V) ? V : V'
```

`V''` = V for plain/dual spaces with polymode true and Name 1. Oracle: `ℝ' = ⟨-⟩'`
(Signature{1,4,0x1}), `(ℝ'⊕ℝ^3)' = ⟨+---⟩'`, `S"∞∅+++"' = ⟨∞∅---⟩'` (options 7, S=0x1d),
`(ℝ^3⊕(ℝ^3)')' -> error`, `D"1,1,1,0"' = ⟨-1,-1,-1,0⟩'`.

#### 4.4.2 Direct sum ⊕ (DS/operations.jl:19-74)

```
oplus(a::Signature{N,X,A,F,D}, b::Signature{M,Y,B,F,D}):    # F, D must match or MethodError
  (i1,o1,c1) = (hasinf a, hasorigin a, dyadmode a); (i2,o2,c2) likewise
  opt = case (i1,o1,c1,i2,o2,c2) of
    (0,0,0, 0,0,0) -> 0
    (0,0,1, 0,0,1) -> 4                                              # dual ⊕ dual = dual
    (0,0,0, 0,0,1) -> (N == M && B == flipsign(N,A)) ? 8 : 0          # V ⊕ V' is dyadic only if exact dual
    (0,0,1, 0,0,0) -> (N == M && A == flipsign(N,B)) ? 8 : 0
    otherwise      -> error "arbitrary TensorBundle direct-sums not yet implemented"   # any ∞/∅, any dyadic
  Signature{N+M, opt, bit2int([a[:]; b[:]]), F, D}                    # Name 1, polymode true
```

Consequences (Oracle `t2`): `S"+-" ⊕ S"+-"'` = `⟨+--+⟩*` (S=6); `S"+-"' ⊕ S"+-"` = `⟨-++-⟩*` (S=9;
the dual half comes *first* in bit order -- the dyadic layout assumption of 3.5 is violated);
`S"+-" ⊕ S"-++"'` = `⟨+-+--⟩` with options 0 (**the dual flag is silently dropped**);
`S"+-"' ⊕ S"-+"'` = `⟨-++-⟩'`. With tangent: `tangent(ℝ^3) ⊕ tangent(ℝ^3)'` = `T¹⟨+++---₁¹⟩*`
(N=8, S=0x38) -- consistent; but non-dual `tangent(ℝ^3) ⊕ tangent(ℝ^2)` = `T¹⟨++++++₁⟩` (N=7, F=1:
two tangent slots collapse into one ordinary-looking slot -- **inconsistent**; forbid in Lean).

```
oplus(a::DiagonalForm, b::DiagonalForm):   opt = combine_options(a,b); vals = [a[:]; b[:]]
                                           DiagonalForm{N+M, opt, diagsig(opt, vals), F, D}
combine_options: same table as above but "exact dual" test is (N == M && A == B)  (same cache index)
oplus(DiagonalForm, Signature) / (Signature, DiagonalForm): intended to convert ±1; **MethodError in
  Julia** (diagsig gets a Vector, not Values; DS/operations.jl:59-66). Port the intended semantics.
oplus(a::Submanifold{V,N,X}, b::Submanifold{W,M,Y}):
  Z  = (isdual(V) == isdual(W) || V ≠ W') ? combine(V,W,X,Y) : (mixed(V,X) | mixed(W,Y))
  VW = V,W both Int ? V+W : V Int ? Signature(V)⊕W : W Int ? V⊕Signature(W) : V⊕W
  Submanifold{VW, popcount Z, Z}
```

Oracle: `D"1,2,3" ⊕ D"4,5" = ⟨1,2,3,4,5⟩`, `D"1,2,3" ⊕ D"1,2,3"' = ⟨1,2,3,-1,-2,-3⟩*`,
`(ℝ^3)(1,3) ⊕ (ℝ^2)(2) = ⟨+_+_+⟩` (bits 0x15), `Λ(ℝ^3).v13 ⊕ Λ(ℝ^2).v2 = v₁₃₅`,
`Λ(ℝ^3).v13 ⊕ Λ((ℝ^3)').w2 = v₁₃w²` (in ⟨+++---⟩*, bits 0x15), `Λ(ℝ^3).v12 ⊕ Λ(ℝ^3).v12' = v₁₂w¹²`
(bits 0x1b), `ℝ5 ⊕ ℝ3 = ⟨11111111⟩` (Submanifold{8,8,0xff}), `Submanifold(3) ⊕ Submanifold(ℝ^2) = ⟨+++++⟩`.

`SubAlgebra ⊕/+`: `Λ(V) ⊕ Λ(W) = getalgebra(V⊕W)` (DS/basis.jl:153-154).

`V^i` (DS/operations.jl:75-87): only for options exactly 0 or 4; `i == 0 -> V0`; otherwise `v⊕v⊕...`
(i copies); negative `i` returns `v` (loop empty). Oracle `(ℝ^2)^3 = ⟨++++++⟩`, `(ℝ')^2 = ⟨--⟩'`.

#### 4.4.3 Union ∪ (DS/operations.jl:91-116, LB/generic.jl:194-195)

```
union(a, b) where typeof params (N,M,S) of a and b equal -> a     # ignores F, D, Name, and concrete kind
union(bundle a, Submanifold{m} b) = a ∪ m;   union(Submanifold{m} a, bundle b) = m ∪ b
union(Submanifold{M,_,A}, Submanifold{M,_,B}) = Submanifold{M, popcount(A|B), A|B}      # same parent
union(a::Submanifold{N}, b::Submanifold{M}) (different parents):
  ma, mb = dyadmode(a), dyadmode(b); mc = (ma == mb)
  if (mc ? a ⊆ b : (mb < 0 && b(a) ⊆ b)) return b
  elif (mc ? b ⊆ a : (ma < 0 && a(b) ⊆ a)) return a
  else return ma > 0 ? b ⊕ a : a ⊕ b
union(a::bundle, b::bundle) generic:
  if (M1,S1) == (M2,S2) && (F1,D1) ≠ (F2,D2): Kind{max N, M1, S1, max F, max D}  # DiagonalForm branch: typo `DiagnoalForm` -> UndefVarError
  elif c1 ≠ c2 && c1 ≥ 0 && c2 ≥ 0 && a == b': return c1 > 0 ? b ⊕ a : a ⊕ b
  elif min(c1,c2) < 0 && max(c1,c2) ≥ 0: require (c1 < 0 ? b ⊆ a : a ⊆ b) else error "TensorBundle union $(a)∪$(b) incompatible!"; return the dyadic one
  elif (N1,i1,o1) == (N2,i2,o2) || N1 == N2: error "TensorBundle intersection $(a)∩$(b) incompatible!"   # sic
  else error "arbitrary TensorBundle union not yet implemented."
union(x) = x; union(a,b,c...) = union(union(a,b), c...)
```

Oracle: `ℝ ∪ ℝ' = ⟨+-⟩*`; `ℝ^3 ∪ ℝ^2 -> error`; `S"+-" ∪ S"-+" -> "TensorBundle intersection ⟨+-⟩∩⟨-+⟩
incompatible!"`; `ℝ^2 ∪ tangent(ℝ^2) = T¹⟨++₁⟩`; `tangent(ℝ^2,1,2) ∪ tangent(ℝ^2,2,1) = T²⟨++₁₂⟩`
(N = max(4,3) = 4); `(ℝ^3⊕(ℝ^3)') ∪ ℝ^3 = ⟨+++---⟩*`; `(ℝ^3)(1,3) ∪ (ℝ^3)(2) = ⟨+++⟩` (Submanifold);
`(ℝ^3)(1,3) ∪ ℝ^3 = ⟨+++⟩` (Signature).

#### 4.4.4 Intersection ∩ (DS/operations.jl:118-140)

```
same (N,M,S) -> a;   same N otherwise -> V0
Signature/DiagonalForm A ∩ Submanifold b = b ⊆ A ? b : V0   (and symmetric)
Submanifold{M,_,A} ∩ Submanifold{M,_,B} = Submanifold{M, popcount(A&B), A&B}
generic: (M,S) equal & (F,D) differ -> Kind{min N, M, S, min F, min D}   (DiagonalForm typo again)
         c1 ≠ c2, both ≥ 0 -> V0
         one dyadic: Y = c1 < 0; (Y ? b⊕b' : a⊕a') == (Y ? a : b) ? (Y ? b : a) : V0
         else error "arbitrary TensorBundle intersection not yet implemented."
```

Oracle: `ℝ ∩ ℝ' = ⟨⟩`, `ℝ^3 ∩ ℝ^2 -> error`, `(ℝ^3⊕(ℝ^3)') ∩ ℝ^3 = ⟨+++⟩`,
`S"+-" ∩ S"-+" = ⟨⟩`, `tangent(ℝ^2,1,2) ∩ tangent(ℝ^2,2,1) = T¹⟨++₁⟩`, `(ℝ^3)(1,3) ∩ (ℝ^3)(1,2) = ⟨+__⟩`,
`(ℝ^3)(1,3) ∩ ℝ^3 = ⟨+_+⟩`, `Λ(ℝ^3).v12 ∩ Λ(ℝ^3).v23 = v₂`, `v1 ∩ v2 = v` (One).

#### 4.4.5 Subset ⊆ / ⊇ (DS/operations.jl:142-168)

```
a ⊇ b = b ⊆ a
same (N,M,S) -> true;  same N otherwise -> false
Bundle A ⊆ Submanifold{M,Y} b = mdims(M) == Y ? A ⊆ M : error "$A ⊆ $b not computable"
Submanifold{M} a ⊆ Bundle B = M ⊆ B
Submanifold{M,X,A} ⊆ Submanifold{M,_,B} = popcount(A & B) == X
Submanifold a ⊆ Submanifold{M,Y} b (other parent) = mdims(M) == Y ? a ⊆ M : interop(⊆, a, b)   # interop = coerce both to Manifold(a) ∪ Manifold(b)
Submanifold{V} ⊆ Int b = V ⊆ b
Signature{A,M,S,F,D} ⊆ Signature{B,M,S,F,D} = A ≤ B            # prefix-by-integer-equality of S
generic: (M,S) equal & (F,D) differ -> F1 ≤ F2 && D1 ≤ D2
         (c1 ≠ c2 && c1,c2 ≥ 0) || (c1 < 0 && c2 ≥ 0) -> false
         c2 < 0 && c1 ≥ 0 -> (c1 > 0 ? a'⊕a : a⊕a') == b
         else error "arbitrary TensorBundle subsets not yet implemented."
```

Oracle: `ℝ^2 ⊆ ℝ^3` true, `ℝ^3 ⊆ ℝ^2` false, `(ℝ^3)' ⊆ ℝ^3⊕(ℝ^3)'` true, `ℝ^3⊕(ℝ^3)' ⊆ ℝ^3` false,
`ℝ^2 ⊆ tangent(ℝ^2)` true, `tangent(ℝ^2,1,2) ⊆ tangent(ℝ^2,2,1)` false,
`v1 ⊆ v12` true, `v12 ⊆ V` true, `ℝ^3 ⊆ ℝ3` true (Int handle).

Equality: `equal(a,b) = a ⊆ b && a ⊇ b` for every pair of Signature/DiagonalForm/Submanifold values or
types (DS/DirectSum.jl:362-372). Oracle: `ℝ^3 == Submanifold(ℝ^3) == (ℝ^3)(1,2,3) == ℝ3` all true,
`ℝ^3 == D"1,1,1"` false, `typeof(ℝ^3) == ℝ^3` true, `v12 == v13` false.

#### 4.4.6 Tangent (DS/generic.jl:128-137)

```
tangent(s::Signature{N,M,S,F,D}, d = 1, f = (F ≠ 0 ? F : 1)) =
    Signature{N + (isdyadic(s) ? 2f : f), M, S, f, D + d}       # likewise DiagonalForm
loworder(V{N,M,S,F,D}) = D ≠ 0 ? V{N,M,S,F,D-1} : V               # Submanifold: loworder of parent
subtangent(V) = V(grade(V)+1 : mdims(V) ...)                       # subspace of tangent generators
```

**N grows on every call even when F is unchanged**: `tangent(tangent(ℝ^3)) = T²⟨++++₁⟩` (N=5, F=1,
D=2: the old tangent slot becomes an ordinary `+` generator). README relies on this
(`tangent(V') = T²⟨----¹⟩'`), so replicate faithfully. `tangent(ℝ^3,2,3) = T²⟨+++₁₂₃⟩` (N=6,F=3,D=2);
`tangent(ℝ^3⊕(ℝ^3)',1,2) = T¹⟨+++---₁₂¹²⟩*` (N=10). `loworder(tangent(ℝ^3)) = ⟨+++₁⟩` (D=0 but F=1).
`subtangent(tangent(ℝ^3)) = T¹⟨___₁⟩`. Tangent of a DiagonalForm keeps the cache index (only non-tangent
values stored); `tangent(tangent(D"1,2,3"))` errors in display (BoundsError).

### 4.5 Submanifold construction and call semantics

#### 4.5.1 Constructors (see 2.3). Dispatch subtleties (DS/DirectSum.jl:259-281, DS/basis.jl:286-288):

| Call | Result kind | Oracle |
|---|---|---|
| `(ℝ^5)(3,5)` (Int varargs -> Tuple) | subspace | `⟨__+_+⟩` :: `Submanifold{⟨+++++⟩, 2, 0x14}` |
| `(ℝ^5)(5,3)` | same (order ignored) | `⟨__+_+⟩` |
| `(ℝ^5)(2:4)` | subspace | `⟨_+++_⟩` |
| `(ℝ^5)([1,3])` (Vector{Int} -> VTI method -> getbasis) | **basis blade** | `v₁₃` |
| `Submanifold{ℝ^3,2}(UInt(5))` | subspace | `⟨+_+⟩` |
| `Submanifold{ℝ^3}(UInt(5))` / `getbasis(ℝ^3,5)` | basis blade | `v₁₃` |
| `Submanifold{ℝ^3}(1,3)` | basis blade | `v₁₃` |
| `Submanifold{ℝ^3}()` | One | `v` |
| `One(3)` | `Submanifold{3,0,0}` subspace of Int space | `⟨___⟩` |
| `ℝ3(1,2)` | subspace of Int space | `⟨11_⟩` |

#### 4.5.2 Calling a Submanifold (DS/generic.jl:23-35)

* `M(b::Int...)`, `M(vector)`, `M(range)` for a Submanifold `M`: `Submanifold{supermanifold(M)}(b)` --
  indices are relative to the *parent space*, not to M. Oracle: `(ℝ^5)(3,5)(1) = ⟨+____⟩`.
* `M(b::Int)` single Int: if `M` is a basis blade -> **grade projection** (`grade(M)==b ? M : Zero`);
  else subspace `{b}` of the parent. Oracle: `v12(2) = v₁₂`, `v12(1) = 𝟎`, `(3v12)(1) = 𝟎`.
* `M(Val(G))`, `Single(G)`: grade projection.

#### 4.5.3 `getindex` on a Submanifold (DS/DirectSum.jl:283-312)

```
s[i]  (s = Submanifold{M,N,S}):
  M isa Submanifold (s is a basis blade): Bool: is bit i set in M's mask        # NOT a metric!
  M isa Int: 1
  else: val = M[indices(S)[i]]   (metric of the i-th included generator)
        M Signature ? (val ? -1 : 1) : (val isa Values ? val[Values(ind...)] : val)   # MetricTensor rows
s[:]:  M Int -> ones(M) (length M, not N); otherwise [s-style metric for each included generator],
       for a basis blade: the parent handle's metric at the blade's indices
```

Oracle: `(S"-+-")(1,3)[:] = [-1,-1]`; `Λ(S"-+-").v12[:] = [-1,1]` but `Λ(S"-+-").v13[2] = true`;
`(D"4,5,6")(1,3)[:] = [4,6]`; `ℝ3(1,2)[:] = [1,1,1]`. Iteration uses `length(::Number) = 1` so only the
first entry is produced; `collect(v12)` errors.

#### 4.5.4 Evaluation / restriction `(W::Submanifold)(b::Submanifold)` (DS/operations.jl:191-238)

```
W(b::Zero) = Zero(W)
W(b::Submanifold{V,G,R}), W::Submanifold{Q,M}:
  if isbasis(W) && !isbasis(b):           RS = R & UInt(W); L = popcount RS; L == G ? b : Submanifold{V,L,RS}
  elif isbasis(W):
     if Q == V:
        G == M == 1: (y,v) = evaluate1(W,b); y ? Zero(V) : v * One(V)          # scalar
        G == 1 && M == 2: dyadic only; evaluate2 (BROKEN: undefined N)
        else error "unsupported transformation"
     else interform(W, b)
  elif V == W:  Submanifold{Submanifold(W), G}(R)       # quirk: double-wrapped handle, prints Submanifold{v₁₂₃,...}
  elif W ⊆ V:   S = UInt(W); popcount(R & S) == G ? getbasis(W, lowerbits(mdims V, S, R)) : Zero(W)   # lowerbits bug
  elif V ⊆ W:   WC, VC = isdyadic W, isdyadic V; B = isbasis(b) ? expandbits(mdims W, UInt(V), R) : R
                WC && !VC -> getbasis(W, mixed(V, B));  !WC && !VC -> getbasis(W, B);  else error
  elif V isa Int: W(Submanifold{Signature(V),G,R}())
  else error "cannot convert from $(V) to $(W)"
(T::Signature)(::same Signature) = Submanifold(Submanifold(T));  (W::Signature)(b::Submanifold) = Submanifold(W)(b)
evaluate1(V, A, B) = X = isdyadic(V) ? A >> (mdims V / 2) : A;  B ∉ (A, X) ? (true, false) : (false, V[intlog(B)+1])
```

Oracle: in `X = S"-++"⊕S"-++"'`: `w1(v1) = -1v`, `w2(v2) = 1v`, `v1(v1) = -1v`, `v1(w1) = 𝟎`;
`(ℝ^3)(1,3)(Λ(ℝ^3).v12) = 𝟎`, `(ℝ^3)(1,3)(Λ(ℝ^3).v3) = v₁` (in ⟨+_+⟩),
`(ℝ^4)(1,2,4)(Λ(ℝ^4).v14) = v₁₂` (**wrong**, pext gives local v₁₃ which prints `v₁₄`).
Single forms `(a::Single{V,1})(b)` multiply coefficients (DS/operations.jl:242-273).

`(V)(I)` / `(V)(λI)` (DS/DirectSum.jl:533-536): `b = getbasis(V, 2^(mdims V - diffvars V) - 1)`
(pseudoscalar of non-tangent part); `Bool` -> `b`, else `Single{V}(λ, b)`. Oracle: `(ℝ^3)(I) = v₁₂₃`,
`(ℝ^3)(2I) = 2v₁₂₃`, `tangent(ℝ^3)(I) = v₁₂₃`.

`Signature(V::Submanifold)` (DS/DirectSum.jl:380-388): basis blade -> `Signature(parent)`; diagonal
parent -> `Signature{G, options}(signbit.(V[:]), diffvars(V), diffmode(V))`; else a Euclidean
`Signature{G,options,0,...}`. Oracle `Signature((S"-+-")(1,3)) = ⟨--⟩`.

### 4.6 Metadata on blades (the formulas Grassmann relies on)

For a basis blade `b = Submanifold{H,G,B}` with handle `H` over space `V` (n = mdims V, F = diffvars V,
k = isdyadic ? 2 : 1):

| Function | Formula | File:line |
|---|---|---|
| `rank(b)` | `G` | AT:152 |
| `mdims(b)` | `n` (basis) / `G` (subspace) | DS/generic.jl:43 |
| `diffvars(b)` | Julia: `n, C = mdims(M), diffmode(M)`; count `i ∈ indices(B)` with `1 + n - (C<0 ? 2 : 1)*F ≤ i ≤ n`. Because `C` is the *diffmode* (never negative) the factor is always 1, so only the **last F positions** are counted: correct for non-dyadic spaces, but in dyadic spaces `∂` bits are not counted and `ϵ` bits are (Oracle in `T(ℝ²)⊕T(ℝ²)'`: `diffvars(∂₁)=0`, `diffvars(ϵ¹)=1`) | DS/generic.jl:56-59 |
| `order(b)` | `order(V) > 0 ? popcount(B & tangentmask) : 0` (tangentmask = union of diffmask halves, so ∂ and ϵ both count) | DS/generic.jl:44 |
| `grade(b)` | `rank(b) - k * diffvars(b)` (Leibniz `grade(::Manifold)`, since blades are Manifolds). Non-dyadic: number of non-tangent generators. Dyadic tangent: Oracle `grade(∂₁) = 1`, `grade(ϵ¹) = -1`, `grade(ϵ¹v₁) = 0` (quirk) | LB/generic.jl:12 |
| `grade(V)` (space/handle) | `rank(V) - k*diffvars(V)` | LB/generic.jl:12 |
| `grade(V, B)` | `popcount(B & (2^grade(V) - 1))` (Int V: `2^V - 1`) | LB/generic.jl:146-148 |
| `pseudograde(V, B)` | `grade(V) - grade(V,B)` (Int V: `V - grade`) | LB/generic.jl:152-153 |
| `pseudograde(V::Manifold)` | `mdims(V) - rank(V) - k*diffvars(V)` | LB/generic.jl:11 |
| `hasinf(b)` | `hasinf(V) && isodd(B)` | DS/generic.jl:116 |
| `hasorigin(b)` | `hasorigin(V) && (hasinf(V) ? B & 2 ≠ 0 : isodd(B))` | DS/generic.jl:119 |
| `isinf(b)` | `hasinf(b) && popcount(B) == 1` | DS/generic.jl:121 |
| `isorigin(b)` | Julia: `hasorigin(V) && popcount(B)==1 && b[hasinf(V)+1]`; `b[i]` tests the *parent* mask so it is true for every 1-blade (Oracle: `isorigin(v∞) == true`). Intended: `B == originbit` | DS/generic.jl:122 |
| `value(b)` | 1 | DS/generic.jl:71 |
| `UInt(b)` | `B` | DS/generic.jl:83 |
| `isdiag(V)` | Signature: `!hasconformal`; DiagonalForm: true; Int: true | DS/generic.jl:66-68 |
| `χ(b)` | `iszero ? 0 : (odd popcount of non-tangent bits ? 1 : -1)` | LB/generic.jl:175 |
| `≅(a,b)` | `grade, order, diffmode` equal | LB/generic.jl:30 |

Oracle for `Λ(tangent(ℝ^2,2,2)).b` (16 blades, basis order): `order = diffvars =
[0,0,0,1,1,0,1,1,1,1,2,1,1,2,2,2]`, `grade = [0,1,1,0,0,2,1,1,1,1,0,2,2,1,1,2]`,
`rank = [0,1,1,1,1,2,2,2,2,2,2,3,3,3,3,4]`.

`diffcheck(V,A,B)` (product vanishing test, LB/generic.jl:99-105):
`(hasinf2(V,A,B) && !hasorigin(V,A,B)) || (hasorigin2(V,A,B) && !hasinf(V,A,B)) ||
(F ≠ 0 && popcount(A & tangent) + popcount(B & tangent) > diffmode(V))`, with
`hasinf2 = hasconformal && isodd(A) && isodd(B)`, `hasorigin(V,A,B) = hasconformal && (hasorigin(V,A) ||
hasorigin(V,B))`, `hasorigin(V,X) = hasinf(V) ? X & 2 ≠ 0 : isodd(X)`.

### 4.7 Involutions (DS/generic.jl:220-234; LB/generic.jl:139-142)

```
parityreverse(G)  = isodd((G-1)*G/2)          # G mod 4 ∈ {2,3}
parityinvolute(G) = isodd(G)
parityclifford(G) = parityreverse(G) xor parityinvolute(G)     # G mod 4 ∈ {1,2}
parityconj = parityreverse                    # so conj ≡ reverse ≡ ~
r ∈ {reverse, involute, conj, clifford}, p = matching parity:
  r(b::Submanifold{V,G,B})       = p(grade(V,B)) ? Single{V}(-1, b) : b
  pseudo_r(b::Submanifold{V,G,B}) = p(pseudograde(V,B)) ? Single{V}(-1, b) : b
  r(b::Single) = value(b) ≠ 0 ? Single(value(b), r(basis(b))) : Zero(V)
  r(Zero) = Zero;  r(Infinity) = Infinity
```

Uses `grade(V,B)` (non-tangent low bits) not `G`. Oracle for G = 0..7: reverse `F F T T F F T T`,
involute `F T F T F T F T`, clifford `F T T F F T T F`. In ℝ^3: `reverse(v12) = -1v₁₂`,
`reverse(v1) = v₁`, `involute(v1) = -1v₁`, `clifford(v123) = v₁₂₃`, `pseudoreverse(v1) = -1v₁`,
`pseudoinvolute(v1) = v₁`, `pseudoclifford(v12) = v₁₂`... (full tables in the golden JSON section
`involutions`).

`even(t) = isodd(G) ? Zero : t`, `odd(t) = isodd(G) ? t : Zero`, `imag(t) = parityreverse(G) ? t :
Zero`, `real(t) = parityreverse(G) ? Zero : t` using the type-level `G` (= rank, tangent bits
included) (DS/operations.jl:387-402).

### 4.8 Complements, parities, metric (DS/operations.jl:277-381; LB/generic.jl:202-237)

Complement mask:

```
complement(N, B, D = 0, P = 0):                              # LB/generic.jl:233
  UP = (1 << (P == 1 ? 0 : P)) - 1       # 0b11 when both ∞ and ∅ present (P = 2), else 0
  ND = N - D
  C  = (~B & (UP xor (2^ND - 1))) | (B & (UP xor ((2^D - 1) << ND)))
  return popcount(C & UP) ≠ 1 ? C xor UP : C
# ordinary generators complemented; tangent bits copied from B; for the conformal pair, B's null bits
# are copied and then toggled when the result holds 0 or 2 of them.
```

Leibniz scalar parities (B = sum of 1-based indices, G = grade, N = dimension):

```
parityright(V, B, G, N)      = isodd(B + (G+1)G/2)
parityleft(V, B, G, N)       = (isodd(G) && iseven(N)) xor parityright(...)
parityrighthodge(V, B, G, N) = isodd(V) xor parityright(...)                 # V = #negative gens in blade
paritylefthodge(V, B, G, N)  = (isodd(G) && iseven(N)) xor parityrighthodge(...)
parity{side}null(V, B, v)    = (hasconformal(V) && popcount(B & 3) == 1) ? (isodd(B) ? 2v : v/2) : v
```

DirectSum wrappers for DiagonalForm / Submanifold spaces (the only ones used; the Signature variants are
commented out, DS/operations.jl:282-292):

```
ind = indices(B & (2^(n-F) - 1), n)                     # non-tangent positions incl. ∞/∅
parity{side}(V, B, G = popcount B)      = parity{side}(0, sum(ind), G, n-F) ? -1 : 1
parity{side}hodge(V, B, G = popcount B) =
    g = isempty(ind) ? 1 : Π signbool(V[i] for i in ind)   # handle metric: ±1 or diag values
    c = hasconformal(V) && (B & 3 == 2)                    # has ∅ but not ∞
    (parity{side}(0, sum(ind), G, n-F) xor c) ? -g : g
paritymetric(V, B, G) = Π signbool(V[i] for i in ind)  (1 if empty)
parityanti(V, B)      = paritymetric(V, complement(n, B, F, hasinf+hasorigin))
```

Complements of a basis blade `b = Submanifold{V,G,B}` (always return a `Single`, even for
coefficient 1, because `V` is a Submanifold handle, never a Signature):

```
complementright/left(b):   d = getbasis(V, complement(n, B, F, 0))           # P = 0 here
                           dyadic -> error "Complement for mixed tensors is undefined"
                           coef = parity{side}(b) * parity{side}null(V, B, 1)   # may be Float 2.0/0.5
complementrighthodge(b):   (!isdiag(V) && !hasconformal(V)) -> reverse(b) * V(I)    # MetricTensor path (Grassmann)
complementlefthodge(b):    (!isdiag(V) && !hasconformal(V)) -> complementleft(metric(b))
                           otherwise d = getbasis(V, complement(n, B, F, hasinf+hasorigin)); coef = parity{side}hodge(b)
complement*(s::Single) = f(value(s)) * complement*(basis(s)),  f = identity (Euclidean) / conj (hodge)
complementrightanti(t) = complementright(antimetric(t));  complementleftanti likewise
```

Metric / antimetric of a basis blade:

```
metric(b):   !isbasis(b) -> metrichash(V)
             (!isdiag(V) || hasconformal(V)) -> complementleft(complementrighthodge(b))
             dyadic -> error
             (hasorigin(b) && !hasinf(b)) || (hasinf(b) && !hasorigin(b)) -> Zero(V)     # lone null vector
             Single{V}(paritymetric(b), b)
antimetric(b): (!isdiag(V) || hasconformal(V)) -> antimetric_term(b)   # UNDEFINED -> UndefVarError (bug)
               dyadic -> error; lone ∞ or ∅ -> Zero; Single{V}(parityanti(b), b)
metric(s::Single) = conj(value(s)) * metric(basis(s))
```

Oracle highlights (full tables in golden `complements`): ℝ^3: `complementright(v1) = 1v₂₃`,
`(v2) = -1v₁₃`, `(v3) = 1v₁₂`, `(v12) = 1v₃`, `(v) = 1v₁₂₃`, `(v123) = 1v`; `complementleft(v2) = -1v₁₃`.
S"-+-": `complementrighthodge(v1) = -1v₂₃`, `complementright(v1) = 1v₂₃`. S"-+--":
`complementleft(v1) = -1v₂₃₄`, `complementright(v1) = 1v₂₃₄`. D"2,3,5": `complementrighthodge(v1) = 2v₂₃`,
`metric(v13) = 10v₁₃`, `parityanti(v1) = 15`. S"∞∅+" (bits ∞=1, ∅=2, e1=4):

| bits | complementright | complementrighthodge | metric |
|---|---|---|---|
| 0 | 1v∞∅₁ | 1v∞∅₁ | 1v |
| 1 (∞) | 2v∅₁ | 1v∞₁ | -2v∅ |
| 2 (∅) | -0.5v∞₁ | -1v∅₁ | -0.5v∞ |
| 3 (∞∅) | 1v₁ | -1v₁ | -1v∞∅ |
| 4 (e1) | 1v∞∅ | 1v∞∅ | 1v₁ |
| 5 (∞1) | -2v∅ | -1v∞ | -2v∅₁ |
| 6 (∅1) | 0.5v∞ | 1v∅ | -0.5v∞₁ |
| 7 | 1v | -1v | -1v∞∅₁ |

S"∞+": `metric(v∞) = 𝟎`, `metric(v1) = 1v₁`; S"∅+": `metric(v∅) = 𝟎`.

### 4.9 Name generation and lookup

`labels(V, vec="v", cov="w", duo="∂", dif="ϵ")` (DS/basis.jl:19-32): element 1 is `Symbol(vec)`; then
for each grade and each lex combination, `printlabel(io, V, mask, true, vec, cov, duo, dif)` (label
mode, 5.4). `generate(V)` (DS/basis.jl:36-47) produces blades in the same order.

`Basis{s}()` builds `Basis{s}(generate(s), Dict(labels(s)[i] => i))` (DS/basis.jl:184-187).
`getproperty(a::Basis{V}, v)` (DS/basis.jl:173-181): `:b`/`:g` fields; label in dict -> element;
otherwise `lookup_basis(V, v)`.

`lookup_basis(V, v)` (DS/basis.jl:134-139): `(p, idx, w, z) = indexparity(V, v)`;
`z -> Zero(V)` (but the return type annotation `::Union{Single,Submanifold}` makes this throw -- bug);
`d = Submanifold{w}(indexbits(mdims(w), idx))` (a basis blade via getbasis); `p ? Single(-1, d) : d`.

`indexparity(V::T, v)` (DS/basis.jl:429-458):

```
vs = string(v); vt = (first char ≠ "v")
Z = match(r"([v]([0-9a-vx-zA-VX-Z]+))?([w]([0-9a-zA-Z]+))?", vs)   # first (possibly empty) match; not anchored at end
ef = [Z[2], Z[4]] without nothings;  isempty(ef) -> (false, [], V, true)
C  = dyadmode(V)
X  = C ≥ 0 && mdims(V) < 33
W  = X ? (V Int ? 2V : (C > 0 ? V'⊕V : V⊕V')) : V
V2 = (vt xor (vt ? C ≠ 0 : C > 0)) ? V' : V
L  = length(ef) > 1
M  = X ? mdims(W)/2 : mdims(W)
m  = (!L && vt && C < 0) ? M : 0
chars = (L || Z[2] ≠ nothing) ? alphanumv : alphanumw
(es, e, et) = indexparity!([position of ch in chars for ch in ef[1]] .+ m, C < 0 ? V : V2)
et -> zero
if L: (fs, f, ft) = indexparity!([position of ch in alphanumw for ch in ef[2]] .+ M, W); ft -> zero
      return (es xor fs, [e; f], W, false)
return (es, e, V2, false)
# The method's return type is Tuple{Bool,Vector,T,Bool} with T = typeof(V): whenever the result space
# (V2 or W) differs from V, conversion throws (Oracle: Λ(ℝ^3).w1, Λ(ℝ^3).v1w1, Λ(3).w1 all MethodError).
```

`indexparity!(ind::Vector{Int}, s)` (LB/indices.jl:230-247):

```
k = 1; t = false
while k < length(ind):
  if ind[k] == ind[k+1]:
     ind[k] == 1 && hasinf(s) -> return (t, ind, true)        # ∞∞ = 0 (∅∅ is NOT zeroed)
     isone(s[ind[k]]) && (t = !t)                              # metric sign
     delete ind[k], ind[k+1]                                   # k NOT decremented (bug: can leave unsorted)
  elif ind[k] > ind[k+1]: swap; t = !t; k ≠ 1 && (k -= 1)
  else: k += 1
return (t, ind, false)
```

Sign bug: for a `Signature` argument `s[i]` is `Bool` (true = negative) so `isone` flips exactly for
negative generators (correct); but `Basis.getproperty` passes the *handle* Submanifold, whose `s[i]` is
`±1`, so `isone` flips for **positive** generators. Oracle: `Λ(3).v11 = -1v`, `Λ(ℝ^3).v11 = -1v`,
`Λ(S"-+-").v11 = v`, `Λ(S"-+-").v22 = -1v`, but `lookup_basis(S"-++", :v11) = -1v` (direct Signature,
correct). Pure permutations (no repeats) are correct: `Λ(3).v21 = -1v₁₂`, `Λ(3).v321 = -1v₁₂₃`,
`Λ(62).v32a87Ng = -1v₂₃₇₈agN`.

Further lookup limits: v-names cannot contain `w` (index 33) or `W` (index 59) because the v-regex
excludes them; only canonical `v...w...` order parses (`w2v1` -> BoundsError); labels for index 10
are `v10` (label mode prints the number), which parses back as {1,10} only through the dict.

Correct Lean semantics: parse name into (prefix block, index list) pairs, map to 1-based generator
positions in the target space (V, V' or V⊕V'), then multiply generators left to right with the
canonical reordering sign and metric contraction `e_i e_i = g_i` (0 for null ∞/∅ generators).

### 4.10 getalgebra / getbasis (DS/basis.jl:226-288)

```
getalgebra(V::bundle)            = getalgebra(Submanifold(V))
getalgebra(V::Submanifold{M,N,S}) = isdyadic(V) && N > 16 ? getextended(V)
                                  : getalgebra(mdims(M), options(M), metric(M), S, typeof(M), diffvars(M), diffmode(M))
getalgebra(n, m, s, S, vs, f, d) = n == 0 ? (vs Int ? Λ0 : Λ0S)
                                 : n > 22 ? getextended(...) : n > 8 ? getsparse(...)
                                 : cached Basis{Submanifold{vs Int ? n : vs(), popcount S, S}()}()
getalgebra(n, d, o, s, c=0)      = getalgebra(n, tensorhash(d,o,c), s)
getalgebra(n, m, s)              = getalgebra(n, m, UInt(s), 2^n - 1, Signature{n,m,UInt(s),0,0})
getbasis(V, B::UInt) = mdims(V) ≤ 8 ? getalgebra(V).b[basisindex(mdims V, B)] : Submanifold{V, popcount B}(B)
getbasis(V, v::Symbol) = getproperty(getalgebra(V), v)
SparseBasis getindex(i) (n > 8): G = grade with binomsum(N,G) < i ≤ binomsum(N,G+1);
                                 B = indexbasis(N,G)[i - binomsum(N,G)]; Submanifold{V, popcount B}(B)
```

Note `getbasis(Signature, B)` for n > 8 returns a *subspace* type (V not a handle); Oracle
`getbasis(ℝ^30, 3)` prints `⟨++____________________________⟩` while `Λ(ℝ^30).v1a = v₁a`.
`Λ(n::Int,d,o,s)`: Oracle `Λ(2,1,1) = DirectSum.Basis{⟨∞∅⟩,4}(v, v∞, v∅, v∞∅)`.

### 4.11 Single construction and Taylor truncation (DS/DirectSum.jl:457-493)

```
Single(v::Real|Complex)            = Single{Submanifold(0)}(v)            # space ⟨⟩, prints "3.0v"
Single(b::Submanifold{V,G})        = Single{V,G,b,Int}(1)                 # prints "1v₁₂"
Single{V}(v)                       = Single{V,0,One(V),typeof v}(v)
Single{V}(v::TensorTerm)           = v
Single{V}((bits, v)::Tuple{UInt,T}) = Single{V}(v, Submanifold{V}(bits))
Single{V}(v, b::TensorAlgebra)     = v * b
Single{V}(v, b::Submanifold{_,G})  = Single{V,G}(v, b)
Single{V,G}(v, b)                  = order(v) + order(b) > diffmode(V) ? Zero(V) : Single{V,G,(b or V(b)),T}(v)
Single{V,G}(v::TensorTerm, b)      = ... Single{V,G,b,Any}(v)
Single{V,G,B}(b::TensorTerm)       = order(B) + order(b) > diffmode(V) ? Zero(V) : Single{V,G,B,Any}(b)
Single{V[,G]}(v, b::Single)        = order check; Single{V,G,basis(b)}(v * b.v)
number * Submanifold{V} = Single{V}(number, b);  number * Single = Single{V,G}(number * v, basis)   # Real/Complex only
adjoint(Single) = Single{dual(V), G, B', T}(conj(v))
```

`order(number) = 0`; `order(Single) = order(basis) + order(value)`. Oracle:
`Single{Submanifold(tangent(ℝ^2))}(2∂₁, ∂₁) = 𝟎` (order 2 > μ = 1). `Symbol * blade` has no method in
DirectSum alone (Grassmann adds it). Conversions: `Real/Float/Int(Single)` = value;
`Complex(Single grade 0) = v + 0im`, `Complex(Single grade > 0) = 0 + v im` (Oracle
`Complex(2v12) = 0 + 2im`), `Complex(Submanifold) = 0 + 1im`, `Complex(One) = 1`.


---

## 5. Display / printing (exact rules)

### 5.1 Glyphs

| Item | Chars |
|---|---|
| brackets | `⟨` U+27E8, `⟩` U+27E9 |
| dual / dyadic suffix | `'` (U+0027), `*` |
| projective | `∞` U+221E, `∅` U+2205 |
| subscripts `subs[j]` | j=1..9 `₁₂₃₄₅₆₇₈₉` (U+2081..2089), 10 `₀` (U+2080), 11..36 `a`..`z` (plain ASCII), -1 `∞`, 0 `∅` |
| superscripts `sups[j]` | j=1..9 `¹²³⁴⁵⁶⁷⁸⁹` (U+00B9, U+00B2, U+00B3, U+2074..2079), 10 `⁰` (U+2070), 11..36 `A`..`Z` (plain ASCII), -1 `∞`, 0 `∅` |
| tangent header | `T` + `sups[μ]` + `⟨` (μ = diffmode; μ = 10 prints `T⁰`, μ > 36 KeyError) |
| zero / infinity | `𝟎` U+1D7CE, `∞` |
| Grade | `Λ` + decimal G |
| prefixes | `v w ∂ ϵ` (ϵ is U+03F5), scheme 2 `X x Y y` |

### 5.2 `printindex(i, label, prefix, pre)` (LB/indices.jl:139-142)

```
t = i > 36;  j = t ? i - 26 : i
if label && 0 < j ≤ 10: return decimal j            # label mode: "1".."10"
return ((prefix ∉ (pre[1], pre[3])) xor t) ? sups[j] : subs[j]
```

With the default `pre = ("v","w","∂","ϵ")`: `v`/`∂` indices are subscripts for 1..36 and superscript
capitals `A..Z` for 37..62; `w`/`ϵ` indices are superscripts for 1..36 and subscript lowercase
`a..z` for 37..62. Oracle:
`printindices(stdout, indices(2^62-1), false, "v")` = `v₁₂₃₄₅₆₇₈₉₀abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ`
and with `"w"` = `w¹²³⁴⁵⁶⁷⁸⁹⁰ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz` (README:96-101).
Label mode for `i ≤ 10` yields the integer (so index 10 is `"10"`, index 11 `"a"`).

### 5.3 Spaces

`Signature` (DS/DirectSum.jl:175-189):

```
μ = diffmode; out = μ > 0 ? "T" * sups[μ] * "⟨" : "⟨"
C = dyadmode; d = diffvars (F); N = n - (d > 0 ? (C < 0 ? 2d : d) : 0)
hasinf -> "∞";  hasorigin -> "∅"
d < 0 -> subs[|d|] ... subs[1]            # descending
for k in (hasinf + hasorigin + 1 + (d < 0 ? |d| : 0)) .. N:  out += (bit k-1 of S) ? '-' : '+'
d > 0 -> for x in 1..d: (((C > 0) xor !polymode) ? sups : subs)[x]
d > 0 && C < 0 -> for x in 1..d: sups[x]
out += "⟩";  C ≠ 0 -> (C < 0 ? "*" : "'");  name > 1 -> subs[name]
```

`DiagonalForm` (DS/DirectSum.jl:226-243): identical frame, but each slot prints `print(value)` followed
by `","` when `k ≠ n` (compares with the *total* n, so tangent spaces get a trailing comma:
`T¹⟨1,2,3,₁⟩`; dual prints negated values `⟨-1,-2,-3⟩'`).

`Int n` prints as `n` (it is just an Int); its handle `Submanifold(n)` prints `⟨111⟩`.

Oracle examples: `⟨+++⟩`, `⟨-+++⟩`, `⟨+---⟩'`, `⟨-++++---⟩*`, `⟨∞∅+++⟩`, `⟨∞∅---⟩'`, `⟨∞++⟩*`
(options 9), `T¹⟨+++₁⟩`, `T²⟨++++₁⟩`, `T¹⟨---¹⟩'`, `T¹⟨+++---₁¹⟩*`, `T²⟨+++₁₂₃⟩`,
`T¹⟨+++---₁₂¹²⟩*`, `T¹⟨++¹⟩` (polymode false), `T¹⟨--₁⟩'` (dual + polymode false), `T¹⟨₁+++⟩`
(F = -1), `⟨+++⟩₂` (name 2), `⟨1,1,1,0⟩`, `⟨1.5,2.0⟩`, `⟨1 // 2,3⟩`, `⟨1,2,3,-1,-2,-3⟩*`, `⟨⟩`.

### 5.4 Submanifold: subspaces and handles (DS/DirectSum.jl:325-356)

```
if isbasis(s): print basis label (5.5) and return
P = V isa Int ? V : parent(V);  PnV = typeof(P) ≠ typeof(V)       # effectively always false (dead code)
PnV -> "Λ" * sups[rank V]
M = PnV ? supermanifold(P) : V
μ = diffmode(s); out = μ > 0 ? "T"*sups[μ]*"⟨" : "⟨"
C = dyadmode(s); d = diffvars(s)       # blade-style count (4.6, last-F quirk)
N  = G - (d > 0 ? (C < 0 ? 2d : d) : 0)
dM = diffvars(M); NM = mdims(M) - (dM > 0 ? (C < 0 ? 2dM : dM) : 0)
hasinf(s) -> "∞"                       # hasinf(M) && bit 0 of S
hasorigin(s) -> "∅"
ind = indices(S)
for k in (hasinf(s) + hasorigin(s) + 1 + (d < 0 ? |d| : 0)) .. NM:
   if k ∈ ind:
      m = isdiag(V) ? sig(V, k) : s[position of k in ind]
          # sig(Signature,k) = '-'/'+', sig(DiagonalForm,k) = value, sig(Int,k) = '1';
          # non-diagonal (conformal) parent: s[j] is ±1 Int -> printed "1" / "-1"
      out += (m isa Bool ? (m ? '-' : '+') : string(m))
   else out += '_'
   M is DiagonalForm && k ≠ NM -> ","
d > 0 -> for x in ind[N+1 .. N+|d|]: (((C>0) xor !polymode) ? sups : subs)[x - NM]
d > 0 && C < 0 -> for x in ind[N+|d|+1 .. end]: sups[x - NM]
"⟩";  C ≠ 0 -> "*"/"'";  name > 1 -> subs[name];  PnV -> "×" * length(V)
```

The loop start depends on whether the *subspace* contains ∞/∅, so an omitted ∞ slot is printed as `_`,
and a contained ∅ without ∞ prints `∅` followed by the ∅ slot's own metric (`-1`). Oracle (golden
`subspace_show`, `signature_sweep`):

```
ℝ^4 masks 0..15:  ⟨____⟩ ⟨+___⟩ ⟨_+__⟩ ⟨++__⟩ ⟨__+_⟩ ⟨+_+_⟩ ⟨_++_⟩ ⟨+++_⟩ ⟨___+⟩ ⟨+__+⟩ ⟨_+_+⟩ ⟨++_+⟩ ⟨__++⟩ ⟨+_++⟩ ⟨_+++⟩ ⟨++++⟩
S"∞∅+-" 0..15:    ⟨____⟩ ⟨∞___⟩ ⟨∅-1__⟩ ⟨∞∅__⟩ ⟨__1_⟩ ⟨∞_1_⟩ ⟨∅-11_⟩ ⟨∞∅1_⟩ ⟨___-1⟩ ⟨∞__-1⟩ ⟨∅-1_-1⟩ ⟨∞∅_-1⟩ ⟨__1-1⟩ ⟨∞_1-1⟩ ⟨∅-11-1⟩ ⟨∞∅1-1⟩
S"∞+-" 0..7:      ⟨___⟩ ⟨∞__⟩ ⟨_+_⟩ ⟨∞+_⟩ ⟨__-⟩ ⟨∞_-⟩ ⟨_+-⟩ ⟨∞+-⟩
D"1,2,3" 0..7:    ⟨_,_,_⟩ ⟨1,_,_⟩ ⟨_,2,_⟩ ⟨1,2,_⟩ ⟨_,_,3⟩ ⟨1,_,3⟩ ⟨_,2,3⟩ ⟨1,2,3⟩
tangent(ℝ^3):     T¹⟨___⟩ ... T¹⟨+++⟩ (0..7), T¹⟨___₁⟩ ... T¹⟨+++₁⟩ (8..15)
ℝ^2⊕(ℝ^2)':       ⟨____⟩* ⟨+___⟩* ⟨_+__⟩* ⟨++__⟩* ⟨__-_⟩* ... ⟨++--⟩*
(ℝ^3)':           ⟨___⟩' ⟨-__⟩' ⟨_-_⟩' ⟨--_⟩' ...
Int 3:            ⟨___⟩ ⟨1__⟩ ⟨_1_⟩ ⟨11_⟩ ⟨__1⟩ ⟨1_1⟩ ⟨_11⟩ ⟨111⟩
handles:          Submanifold(S"∞∅++") = ⟨∞∅11⟩;  Submanifold(tangent(ℝ^3)⊕tangent(ℝ^3)') = T¹⟨+++---₁²⟩*
                  Submanifold(tangent(ℝ^3,1,2)⊕tangent(ℝ^3,1,2)') = T¹⟨+++---₁₂³⁴⟩*
```

(`T(ℝ²)⊕T(ℝ²)'` subspaces containing the ϵ slot raise KeyError or print `∞²`: do not replicate.)

### 5.5 Basis blade labels: `printlabel(io, V, e, label, vec, cov, duo, dif)` (LB/indices.jl:156-183)

`V` is the blade's handle; `shift_indices(V, b)` maps local positions to parent positions (for a
proper-subspace handle, through `indices(S_handle)`; DS/DirectSum.jl:404) and then applies
`shift_indices!` (LB/indices.jl:122-132): if the parent has ∞ and the first index is 1 it becomes
-1; if it has ∅ and the next index equals `P` it becomes 0; all remaining indices are decreased by
`P = hasinf + hasorigin`.

```
M = supermanifold(V); N = mdims(M); D = diffvars(M); C = dyadmode(V); P = hasinf(M) + hasorigin(M)
if C < 0:                                            # dyadic
   (db1, db2) = diffmask(V); es = e & ~(db1 | db2); n = (N - 2D) / 2
   eps = shift_indices(V, e & db1) .- (N - 2D - P)   # ∂ indices, 1..D
   par = shift_indices(V, e & db2) .- (N - D - P)    # ϵ indices, 1..D
   print4(a = shift(es & (2^n - 1)), b = shift(es >> n), c = eps, d = par, label, vec, cov, duo, dif)
else:
   db = diffmask(V); es = e & ~db
   eps = shift_indices(V, e & db) .- (N - D - P)
   if eps nonempty:
      print4(a = shift(es), b = [], c = (C > 0 ? [] : eps), d = (C > 0 ? eps : []),
             label, (C > 0 ? cov : vec), cov, (C > 0 ? dif : duo), dif)
   else:
      print1(shift(es), label, C > 0 ? cov : vec, pre = GLOBAL ("v","w","∂","ϵ"))
print4(a, b, c, d, label, e, f, g, h):   PRE = (e, f, g, h)
   c nonempty -> print1(c, label, g, PRE)
   d nonempty -> print1(d, label, h, PRE)
   unless ((b or c or d nonempty) and a empty) -> print1(a, label, e, PRE)
   b nonempty -> print1(b, label, f, PRE)
print1(list, label, prefix, pre) = prefix followed by printindex(i, label, prefix, pre) for each i
```

Block order: `∂` block, `ϵ` block, `v` block, `w` block; the scalar blade prints just the vector
prefix (`v`, or `w` in a dual space). The sub/superscript decision compares the prefix with the
*passed* tuple, which creates two faithful quirks:

* dual space with tangent bits: `PRE = (cov, cov, dif, dif)`, so the covector block uses **subscripts**:
  `Λ(tangent(ℝ^2)')` = `(w, w¹, w², ϵ₁, w¹², ϵ₁w₁, ϵ₁w₂, ϵ₁w₁₂)`;
* non-default name schemes use the *global* default tuple in the 1-block path: scheme 2 prints
  `X, X¹, X², X¹²` (superscripts because `"X" ∉ ("v","∂")`).

`labels(V)` = label mode strings, except element 1 is always `vec` (`"v"`) even for dual spaces
(Oracle `labels((ℝ^3)')[1] = :v` while the blade prints `w`).

Oracle label/print pairs (golden `bases`):

```
ℝ^3:          v v₁ v₂ v₃ v₁₂ v₁₃ v₂₃ v₁₂₃                 labels v v1 v2 v3 v12 v13 v23 v123
(ℝ^3)':       w w¹ w² w³ w¹² w¹³ w²³ w¹²³                 labels v w1 w2 w3 w12 w13 w23 w123
ℝ^2⊕(ℝ^2)':   v v₁ v₂ w¹ w² v₁₂ v₁w¹ v₁w² v₂w¹ v₂w² w¹² v₁₂w¹ v₁₂w² v₁w¹² v₂w¹² v₁₂w¹²
S"∞∅++":      v v∞ v∅ v₁ v₂ v∞∅ v∞₁ v∞₂ v∅₁ v∅₂ v₁₂ v∞∅₁ v∞∅₂ v∞₁₂ v∅₁₂ v∞∅₁₂      labels v∞∅1 ...
S"∞∅+-"':     w w∞ w∅ w¹ w² w∞∅ w∞¹ w∞² w∅¹ w∅² w¹² w∞∅¹ w∞∅² w∞¹² w∅¹² w∞∅¹²
tangent(ℝ^2): v v₁ v₂ ∂₁ v₁₂ ∂₁v₁ ∂₁v₂ ∂₁v₁₂                labels v v1 v2 ∂1 v12 ∂1v1 ∂1v2 ∂1v12
tangent(ℝ^2,1,2): v v₁ v₂ ∂₁ ∂₂ v₁₂ ∂₁v₁ ∂₂v₁ ∂₁v₂ ∂₂v₂ ∂₁₂ ∂₁v₁₂ ∂₂v₁₂ ∂₁₂v₁ ∂₁₂v₂ ∂₁₂v₁₂
T(ℝ²)⊕T(ℝ²)': v v₁ v₂ w¹ w² ∂₁ ϵ¹ v₁₂ v₁w¹ v₁w² ∂₁v₁ ϵ¹v₁ v₂w¹ v₂w² ∂₁v₂ ϵ¹v₂ w¹² ∂₁w¹ ϵ¹w¹ ∂₁w² ϵ¹w² ∂₁ϵ¹ ...
tangent(S"∞∅+"): v v∞ v∅ v₁ ∂₁ v∞∅ v∞₁ ∂₁v∞ v∅₁ ∂₁v∅ ∂₁v₁ v∞∅₁ ∂₁v∞∅ ∂₁v∞₁ ∂₁v∅₁ ∂₁v∞∅₁
subspace handle (ℝ^4)(1,2,4):  Λ = DirectSum.Basis{⟨++_+⟩,8}(v, v₁, v₂, v₄, v₁₂, v₁₄, v₂₄, v₁₂₄)
                               but lookup .v13 (local indices) = v₁₄
```

### 5.6 Terms and containers

* `Single` (DS/DirectSum.jl:488 -> LB/indices.jl:195-203): if the coefficient type is `Expr`,
  `Complex`, `Rational` or a non-term `TensorAlgebra` print `"(" * print(v) * ")"`; otherwise
  `show(v)` then `showstar(v)`, which prints `⊗` for TensorAlgebra coefficients and `*` unless the
  coefficient is a non-Bool Integer or a finite AbstractFloat; then the basis label (label=false).
  Oracle: `2v₁₂`, `2.5v₁₂`, `-2.5v₁₂`, `-0.0v₁`, `NaN*v₁`, `Inf*v₁`, `true*v₁`, `2v₁` (BigInt),
  `2.0f0v₁`, `π*v₁`, `:x*v₁`, `(x + y)v₁`, `(1 + 2im)v₁`, `(1//2)v₁₂`, `2v`, `3.0v` (`Single(3.0)`,
  space ⟨⟩), `2w¹²` (adjoint), `1v₁₂` (`Single(v12)`).
* `Zero` -> `𝟎`; `Infinity` -> `∞`; `Grade{3}(2)` -> `Λ2`.
* `Basis` (DS/basis.jl:195-202): `"DirectSum.Basis{" * show(V) * "," * string(2^n) * "}(" * join(show.(elements), ", ") * ")"`.
  `collect(V)` on a Signature builds `Basis{V}` whose elements are *subspaces* (README's `⟨____⟩, ⟨-___⟩ ...`).
* `SparseBasis` (DS/basis.jl:345-347): `"DirectSum.SparseBasis{" * show(V) * "," * 2^n * "}(" * show(a[1]) * ", ..., " * show(a[end]) * ")"`.
* `ExtendedBasis` (DS/basis.jl:373-376): `"DirectSum.ExtendedBasis{" * show(V) * "," * 2^n * "}(" * show(getbasis(V,0)) * ", ..., " * show(getbasis(V,2^n-1)) * ")"`.

Oracle: `DirectSum.SparseBasis{⟨111111111⟩,512}(v, ..., v₁₂₃₄₅₆₇₈₉)`,
`DirectSum.ExtendedBasis{⟨11111111111111111111111111111111111111111111111111111111111111⟩,4611686018427387904}(v, ..., v₁₂₃₄₅₆₇₈₉₀abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ)`,
`DirectSum.SparseBasis{⟨+++++++-------⟩*,16384}(v, ..., v₁₂₃₄₅₆₇w¹²³⁴⁵⁶⁷)`,
`DirectSum.ExtendedBasis{⟨++++++++++++++--------------⟩*,268435456}(v, ..., v₁₂₃₄₅₆₇₈₉₀abcdw¹²³⁴⁵⁶⁷⁸⁹⁰ABCD)`.

Julia type strings (`Signature{3, 0, 0x0000000000000000, 0, 0, 1}`,
`Submanifold{⟨+++⟩, 2, 0x0000000000000005}`) are Julia-specific; a Lean `Repr` can mimic them for debug
but they are not part of the golden contract.

---

## 6. Examples and golden candidates

### 6.1 README (verbatim input -> expected, with oracle status)

| README line | Input | Expected (README) | Current oracle |
|---|---|---|---|
| 35-36 | `ℝ^3 == V"+++" == TensorBundle(3)` | `true` | same |
| 43-44 | `V = ℝ'⊕ℝ^3` | `⟨-+++⟩` | same |
| 46-47 | `V'` | `⟨+---⟩'` | same |
| 49-50 | `W = V⊕V'` | `⟨-++++---⟩*` | same |
| 54-55 | `collect(V)` | `DirectSum.Basis{⟨-+++⟩,16}(⟨____⟩, ⟨-___⟩, ⟨_+__⟩, ⟨__+_⟩, ⟨___+⟩, ⟨-+__⟩, ⟨-_+_⟩, ⟨-__+⟩, ⟨_++_⟩, ⟨_+_+⟩, ⟨__++⟩, ⟨-++_⟩, ⟨-+_+⟩, ⟨-_++⟩, ⟨_+++⟩, ⟨-+++⟩)` | same |
| 57-58 | `collect(Submanifold(V'))` | `DirectSum.Basis{⟨+---⟩',16}(w, w¹, w², w³, w⁴, w¹², w¹³, w¹⁴, w²³, w²⁴, w³⁴, w¹²³, w¹²⁴, w¹³⁴, w²³⁴, w¹²³⁴)` | same |
| 60-61 | `collect(Submanifold(W))` | 256-element string at README:61 | byte-identical |
| 69-70 | `ℝ⊕ℝ' ⊇ TensorBundle(1)` | `true` | same |
| 72-73 | `ℝ ∩ ℝ' == TensorBundle(0)` | `true` | same |
| 75-76 | `ℝ ∪ ℝ' == ℝ⊕ℝ'` | `true` | same |
| 84-85 | `(ℝ^5)(3,5)` | `⟨__+_+⟩` | same |
| 87-88 | `dump(ans)` | `Submanifold{2,⟨+++++⟩,0x0000000000000014} ⟨__+_+⟩` | **stale**: type is `Submanifold{⟨+++++⟩, 2, 0x0000000000000014}` |
| 96-97 | `printindices(stdout, indices(UInt(2^62-1)), false, "v")` | `v₁₂₃₄₅₆₇₈₉₀abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ` | same |
| 99-100 | same with `"w"` | `w¹²³⁴⁵⁶⁷⁸⁹⁰ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz` | same |
| 109-110 | `Signature("∞∅++")` | `⟨∞∅++⟩` | same |
| 112 | `V"∞∅+++"` is `TensorBundle{5,3}` | -- | **stale**: `V"∞∅+++"` is a 3-dim DiagonalForm (Q1); `S"∞∅+++"` is `Signature{5,3,0x2,0,0,1}` |
| 118-119 | `V = tangent(ℝ^3)` | `T¹⟨+++₁⟩` | same |
| 121-122 | `tangent(V')` | `T²⟨----¹⟩'` | same (N-growth quirk Q10) |
| 124-125 | `V+V'` | `T¹⟨+++---₁¹⟩*` | same |
| 158-159 | `@basis ℝ^3` | `(⟨+++⟩, v, v₁, v₂, v₃, v₁₂, v₁₃, v₂₃, v₁₂₃)` | same |
| 161-162 | `typeof(V)` | `Signature{3,0,0x0000000000000000,0,0,1}` | **stale**: after `@basis`, `V` is the handle `Submanifold{⟨+++⟩, 3, 0x0000000000000007}` |
| 164-165 | `typeof(v13)` | `Submanifold{⟨+++⟩,2,0x0000000000000005}` | same modulo `, ` spacing |
| 167-171 | `v1 ⊆ v12`, `v12 ⊆ V` | `true`, `true` | same |
| 179-183 | `indices(Λ(3).v12)` | `[1, 2]` | same |
| 201-202 | `Λ(22)` | `DirectSum.SparseBasis{⟨++++++++++++++++++++++⟩,4194304}(v, ..., v₁₂₃₄₅₆₇₈₉₀abcdefghijkl)` | **stale**: now `⟨1111111111111111111111⟩` (Int space) |
| 195 | volume element of `Λ(62)` | `v₁₂₃₄₅₆₇₈₉₀abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ` | same |

### 6.2 `test/runtests.jl` (all pass on the oracle)

```julia
@test (ℝ'⊕ℝ^3) == V"-+++"                                   # line 5
@test (ℝ⊕ℝ') ⊇ TensorBundle(1)                              # line 6
@test (print(devnull,ℝ) == nothing)                          # line 7
@test (DirectSum.dual(ℝ) == ℝ')                              # line 8
@test (ℝ∩(ℝ') == TensorBundle(0))                            # line 9
@test (ℝ∪(ℝ') == ℝ⊕ℝ')                                      # line 10
@test indices(Λ(3).v12) == [1,2]                             # line 11
@test (@basis ℝ^3; v1 ⊆ v12 && v12 ⊆ V)                      # line 12
!Sys.iswindows() && @test Λ(62).v32a87Ng == -1Λ(62).v2378agN # line 13
@test Λ(ℝ^14) ⊕ Λ(ℝ^14)' == Λ(TensorBundle(14)⊕TensorBundle(14)')   # line 15
```

### 6.3 Grassmann docs that exercise DirectSum (`/Users/alokbeniwal/chakravala/Grassmann.jl/docs/src`)

* `algebra.md:283-297`: `Submanifold(4)` -> `⟨1111⟩`; `dump(V)` -> `Submanifold{4, 4, 0x000000000000000f} ⟨1111⟩`;
  `collect(V)` -> `DirectSum.Basis{⟨1111⟩,16}(v, v₁, v₂, v₃, v₄, v₁₂, v₁₃, v₁₄, v₂₃, v₂₄, v₃₄, v₁₂₃, v₁₂₄, v₁₃₄, v₂₃₄, v₁₂₃₄)`;
  `dump(G4.v12)` -> `Submanifold{⟨1111⟩, 2, 0x0000000000000003} v₁₂` (oracle-confirmed).
* `algebra.md:309-310`: `collect(V(1,4))` -> `DirectSum.Basis{⟨1__1⟩,4}(v, v₁, v₄, v₁₄)` (confirmed).
* `algebra.md:320-321`, `934-935`: `@basis 3` / `basis"3"` -> `(⟨111⟩, v, v₁, v₂, v₃, v₁₂, v₁₃, v₂₃, v₁₂₃)`.
* `algebra.md:1397-1398`: `@mixedbasis tangent(ℝ^1)` docs show the old `(⟨+-₁¹⟩*, v, v₁, w¹, ϵ₁, ∂¹, ...)`;
  current oracle: `(T¹⟨+-₁²⟩*, v, v₁, w¹, ∂₁, ϵ₁, v₁w¹, ∂₁v₁, ϵ¹v₁, ∂₁w¹, ϵ₁w₁, ∂₁ϵ¹, ∂₁v₁w¹, ϵ¹v₁w¹, ∂₁ϵ¹v₁, ∂₁ϵ¹w¹, ∂₁ϵ¹v₁w¹)`.
* `design.md:115-116`: `Λ(7) ⊕ Λ(7)'` -> `DirectSum.SparseBasis{⟨+++++++-------⟩*,16384}(v, ..., v₁₂₃₄₅₆₇w¹²³⁴⁵⁶⁷)` (confirmed).
* `design.md:68,79`: `@basis S"-++"` -> `(⟨-++⟩, v, v₁, v₂, v₃, v₁₂, v₁₃, v₂₃, v₁₂₃)`;
  `DirectSum.Basis(V)` -> `DirectSum.Basis{⟨-++⟩,8}(v, v₁, v₂, v₃, v₁₂, v₁₃, v₂₃, v₁₂₃)`.

### 6.4 Additional oracle goldens worth hard-coding as Lean `#guard`s

```
Signature("∞∅+++")        -> n=5 opts=3 S=0x02         show ⟨∞∅+++⟩
Signature("∞∅+++")'       -> n=5 opts=7 S=0x1d         show ⟨∞∅---⟩'
Signature("-+-+")         -> S=0x05;  Signature("+-+") -> S=0x02
(ℝ^3)'                    -> opts=4 S=0x07;  ℝ^3⊕(ℝ^3)' -> n=6 opts=8 S=0x38
tangent(ℝ^3)              -> Signature{4,0,0x0,1,1}    T¹⟨+++₁⟩
tangent(ℝ^3)'             -> Signature{4,4,0xf,1,1}    T¹⟨---¹⟩'
tangent(ℝ^3)⊕tangent(ℝ^3)'-> Signature{8,8,0x38,1,1}   T¹⟨+++---₁¹⟩*
Signature(3,1,1)          -> ⟨∞∅+⟩;  Signature(3,1,0,UInt(5)) -> ⟨∞+-⟩
Λ(3)                      -> DirectSum.Basis{⟨111⟩,8}(v, v₁, v₂, v₃, v₁₂, v₁₃, v₂₃, v₁₂₃)
Λ(ℝ^3)'                   -> DirectSum.Basis{⟨---⟩',8}(w, w¹, w², w³, w¹², w¹³, w²³, w¹²³)
Λ(D"1,2,3")'              -> DirectSum.Basis{⟨-1,-2,-3⟩',8}(w, w¹, w², w³, w¹², w¹³, w²³, w¹²³)
Λ(2,1,1)                  -> DirectSum.Basis{⟨∞∅⟩,4}(v, v∞, v∅, v∞∅)
Λ(ℝ^9)[100]               -> v₃₄₉ (bits 0x10c);  Λ(62).v2378agN bits 0x00020000000104c6 (grade 7)
Λ(3).v21 = -1v₁₂;  Λ(3).v321 = -1v₁₂₃;  Λ(S"-++").v1321... (see golden `lookup`, 373 entries)
(ℝ^5)(3,5) bits 0x14;  (ℝ^5)(2:4) = ⟨_+++_⟩;  (ℝ^3⊕(ℝ^3)')(1,5) = ⟨+___-_⟩*;  (ℝ^3)'(1,2) = ⟨--_⟩'
(tangent(ℝ^3))(1,4) = T¹⟨+__₁⟩;  (D"1,2,3"⊕D"1,2,3"')(2,5) = ⟨_,2,_,_,-2,_⟩*
complement(3,1)=0x6; complement(3,2)=0x5; complement(5,1,0,2)=0x1d; complement(5,2,0,2)=0x1e;
complement(5,3,0,2)=0x1c; complement(5,4,0,2)=0x1b; complement(5,0,0,2)=0x1f; complement(4,1,1,0)=0x6;
complement(4,9,1,0)=0xe
```

---

## 7. Dependencies

DirectSum `Project.toml`: `AbstractTensors 0.8.3`, `Leibniz 0.2-0.3`, `ComputedFieldTypes 1`
(not chakravala; provides `@computed` so `Basis{V}` can have a field of size `1<<mdims(V)`),
`LinearAlgebra`, `Random`.

### 7.1 From AbstractTensors (DS/DirectSum.jl:22, 28-32; DS/operations.jl:329; DS/generic.jl:15, 167)

`TensorAlgebra, Manifold, TensorGraded, TensorTerm, scalar, isscalar, involute, vector, isvector,
bivector, isbivector, volume, isvolume, equal, ⋆, value, valuetype, interop, interform, even, odd,
isnull, norm, SUM, PROD, SUB, TupleVector, Values, Variables, FixedVector, basis, mdims, Scalar,
GradedVector, Bivector, Trivector, pseudoscalar, hodge, clifford, complementright, complementleft,
complementlefthodge, complementleftanti, complementrightanti, antimetric, pseudometric, cometric,
wedgedot_metric, unit, ∏` (via `AbstractTensors.∏`, DS/DirectSum.jl:491).
Semantics needed: `Manifold(t)` returns the space param (AT:138-140), `rank(t::TensorGraded{V,G}) = G`
(AT:152), `mdims(t) = mdims(Manifold(t))` (AT:161), `gdims(N,G) = binomial` (AT:181),
`==(a::TensorAlgebra,b::TensorAlgebra) = equal(a,b)` (AT:298), `interop(op,a,b)` coerces both to
`Manifold(a) ∪ Manifold(b)` when spaces differ (AT:244-256), `Values` = static vector (StaticVectors).
`PROD, SUM, SUB = ∏, ∑, -` (AT:626).

### 7.2 From Leibniz (DS/DirectSum.jl:34-48 and 2.5 above)

`Fields, pre, PRE, vsn, VTI, bit2int, combo, indexbits, indices, printlabel, supermanifold,
shift_indices, shift_indices!, printindices, symmetricmask, parityleft, parityright, paritylefthodge,
combine, parityrighthodge, parityclifford, parityconj, parityreverse, parityinvolute, parityrightnull,
parityleftnull, parityrightnullpre, parityleftnullpre, hasconformal, parval, TensorTerm, mixed, subs,
sups, vio, gdims, grade, order, options, metric, polymode, dyadmode, diffmode, diffvars, pseudograde,
hasinf, hasorigin, norm, isbasis, ≅, isdyadic, isdual, istangent, involute, basis, alphanumv,
alphanumw, algebra_limit, sparse_limit, cache_limit, fill_limit, binomial, gdimsall, binomsum,
binomcumsum, lowerbits, expandbits, bladeindex, basisindex, indexbasis, indexbasis_set, loworder,
intlog, promote_type, mvec, svec, insert_expr, indexparity!` plus `complementright,
complementrighthodge, ⋆, complement` (DS/operations.jl:328), `showvalue` (DS/DirectSum.jl:488),
`Leibniz.parityinvolute/parityreverse` (DS/operations.jl:385), `Leibniz.$fun` for Grade forwarding
(DS/grade.jl:26-28: `gdimsall, binomcumsum, spincumsum, anticumsum, indexbasis_set, indexeven_set,
indexodd_set, indexbasis, indexeven, indexodd`), and `spinsum, antisum` via Grade forwarding.

### 7.3 Downstream (who consumes DirectSum)

Grassmann imports (Grassmann.jl:33-37, parity.jl:17-18) listed in 2.1. Grassmann's
`MetricTensor{n,ℙ,g,Vars,Diff,Name} <: TensorBundle` (Grassmann.jl/src/forms.jl:1603) plugs into the
`algebra_cache_MetricTensor` slot and the `!isdiag(V)` branches of complements/metric. Cartan, Adapode,
MeshTopology etc. reach DirectSum through Grassmann.

---

## 8. Lean 4 porting notes

### 8.1 Representation: what becomes a type index vs a runtime value

Recommended core types (all in `namespace DirectSum`):

```lean
inductive Dyad | plain | dual | mixed            deriving DecidableEq, Repr, Hashable
structure Options where
  inf : Bool := false; origin : Bool := false; dyad : Dyad := .plain; poly : Bool := true
  deriving DecidableEq, Repr, Hashable
inductive Metric                                   -- runtime data, stored inside Space
  | euclid                                         -- Julia `Int n`
  | sig  (neg : UInt64)                            -- bit k-1 set = generator k squares to -1
  | diag (vals : Array Coeff)                      -- primal values (Int/Rat/Float literal)
structure Space where
  n : Nat; opts : Options; metric : Metric; vars : Nat := 0; order : Nat := 0; names : Nat := 0
  -- invariant (Prop field or separate predicate): n ≤ 62, vars/opts layout consistent (3.5)
structure Blade (V : Space) where                 -- basis blade, runtime = one UInt64 (trivial structure)
  bits : UInt64
  lt   : bits.toNat < 2 ^ V.n                      -- erased
structure Sub (V : Space) where mask : UInt64     -- subspace (Julia non-basis Submanifold)
structure Term (V : Space) (α : Type) where coef : α; blade : Blade V     -- Julia `Single`
```

* **Type index (zero cost):** the `Space` value itself (as the parameter of `Blade`, `Sub`, `Term`,
  and later Grassmann's `Chain V g α := Vector α (V.n.choose g)` / `Multivector V α := Vector α
  (2^V.n)`). This reproduces Julia's "the space is a type parameter" discipline: mixing blades from
  different spaces is a type error unless an explicit coercion (Julia `interop`/`∪`) is inserted.
  The grade `g` of `Chain` belongs in the type (sizes), and `Fin`-valued `basisindex/bladeindex`
  give statically in-bounds storage access.
* **Proof fields (zero cost):** `bits < 2^n`, `popcount bits = g` for graded blades, `n ≤ 62`, dyadic
  layout invariants. Lean erases them; `Blade V` is a trivial structure and is represented as an
  unboxed `UInt64` (verify with `set_option trace.compiler.ir.result true`).
* **Runtime values:** metric bits/diag values, options, names. Do not split them into separate type
  parameters: one `Space` value is enough, is `DecidableEq`, and spaces are usually closed terms
  (compile-time constants) anyway. Functions taking `{V : Space}` do receive `V` at runtime (it is
  data, not a type), so hot loops should read `V.metric`/`V.n` once and work on `UInt64`s;
  `@[specialize]`/`@[inline]` on small helpers lets the compiler fold them when `V` is a literal.
* **DiagonalForm values:** store the values in the Space (no global cache, no session-dependent
  index). Use a `Coeff` sum type or `Rat`; do not make Floats part of a type index (no lawful
  `DecidableEq`). Keep "primal values, negate on read when dual" semantics.
* **Drop:** Julia's negative `vars`, the `DiagonalForm` cache index, `Name` as a cache-colliding type
  param (keep `names : Nat` only for printing), `Int` vs `Signature` duplication (model `Int n` as
  `Metric.euclid` but keep its distinct display `⟨111⟩`).
* **Zero/One/Infinity:** `One V` = `Blade V` with bits 0; `Zero`/`Infinity` as constructors of a
  small sum type returned by operations that can vanish (`inductive TermResult V α | zero | inf |
  term (t : Term V α)`), or `Option (Term V α)` for zero.
* **Failing operations:** Julia throws (`⊕` on conformal spaces, `'` on dyadic, arbitrary unions).
  Either return `Except String Space`, or require a decidable precondition
  `(h : a.oplusOk b := by decide)` so literal spaces are checked at compile time.

### 8.2 Where Julia gets its speed and what to do in Lean

* Julia: every space/blade is a type parameter; `@pure` metadata constant-folds; Grassmann's
  `@generated` product kernels call `indexbasis`, `basisindex`, `bladeindex`, `binomsum`, parity and
  `complement` at *code-generation* time (via `insert_expr`, LB/utilities.jl:74-96), so the caches
  (`bladeindex_cache` up to n = 12, `indexbasis_cache` up to 22) are compile-time only. Runtime cost of
  DirectSum itself is ~0.
* Lean hot paths (consumed by the Grassmann port):
  1. `basisindex n b`, `bladeindex n b`, `indexbasis n g`, unrank: precompute `Array UInt32` tables
     for n ≤ 12 as **closed terms** (evaluated once at module initialisation; total Σ 2^n ≈ 8K entries),
     and use the O(popcount) closed-form lex rank (4.2) with a 65×65 binomial table beyond. Keep both
     and property-test equality.
  2. Bit primitives on `UInt64`: Lean core (checked `~/lean4` 2026-07) has `UInt64.log2` (C loop, not
     clz), `BitVec.clz/ctz` (spec-level, slow), `BitVec.cpopNatRec` (spec), **no fast
     popcount/ctz extern**. Implement SWAR popcount (~12 ops) and `ctz x = popcount((x &&& -x) - 1)`;
     optionally a tiny C FFI (`__builtin_popcountll`, `__builtin_ctzll`) behind `@[extern]` with the
     SWAR version as `@[implemented_by]` reference and a `bv_decide` equivalence proof.
  3. Shifts: Lean `UInt64` shifts are **mod 64** (`lean_uint64_shift_left(a,b) = a << (b % 64)`),
     Julia's are saturating (`1 << 64 == 0`, negative counts reverse). Always go through
     `lowMask n := if n ≥ 64 then ~~~0 else (1 <<< n) - 1` and never shift by a possibly-negative
     `Int` (port `tensorhash` by explicit cases, not by shifting).
  4. pdep/pext for subspace coordinates (4.3): loop over set bits of the mask (≤ 64 iterations) or
     table per mask for n ≤ 8.
  5. Display is cold; build `String` with a `String.Iterator`-free append loop.
* Global mutable caches are unnecessary in Lean (pure functions + closed-term tables); do not port
  `algebra_cache_*`, `combo_cache`, `indices_cache`, `digitsfast_cache`, `lowerbits_cache`.

### 8.3 Semantics decisions: quirk catalog

Tag each golden with these IDs so the Lean test harness can skip or compat-check them. "Port" says
what Lean should do.

| ID | Julia behaviour (evidence) | Port |
|---|---|---|
| Q1 | `V"..."`/`Λ"..."`/`basis"..."`/`Manifold(str)` misparse sign strings via `Meta.parse` (4.1) | correct grammar; skip those goldens |
| Q2 | digit grammar: `tensorhash` collisions (`S"12" = ⟨∅⟩`), metric decimal may exceed n (`S"30012"`) | accept digit grammar only for d,o ∈ {0,1} and metric < 2^n, else error; keep goldens for valid inputs |
| Q3 | `S"..."` positions literal (`S"∅∞++"`, `S"+∞+"`) | reject (grammar `^(∞)?(∅)?[+-]*$`) |
| Q4 | DiagonalForm `S` is a session-dependent cache index | store values; compare goldens on `diag` lists |
| Q5 | `getalgebra` cache ignores `Name`; options ≥ 12 segfault | no caches |
| Q6 | `'` and `⊕` reset `Name` to 1 and polymode to true | replicate (cheap) -- affects display only |
| Q7 | `V ⊕ W'` silently drops the dual flag unless W is exactly V; `V' ⊕ V` is dyadic with the dual half first | replicate for display; document; Grassmann assumes vector-half-first -- consider rejecting dual-first |
| Q8 | `DiagonalForm ⊕ Signature` MethodError | implement intended (±1 conversion) |
| Q9 | non-dual `tangent ⊕ tangent` keeps F, sums N (inconsistent); `combine` misplaces tangent bits | reject non-dual tangent sums |
| Q10 | `tangent(tangent(V))` adds another slot while F stays (README relies on it) | replicate |
| Q11 | `∪/∩` DiagonalForm branch typo `DiagnoalForm` (UndefVarError); union error text says "intersection" | implement intended |
| Q12 | `lowerbits` is not pext -> `W(b)` restriction to a subspace wrong | use pext; skip those goldens |
| Q13 | `blade[i]` returns parent-mask Bool, `blade[:]` returns metric list; iteration yields 1 element | expose explicit `metricAt` API; no indexing sugar |
| Q14 | `isorigin` true for every 1-blade | correct (`bits == originBit`) |
| Q15 | blade `diffvars` counts only the last F slots; dyadic `grade(ϵ¹) = -1` | correct for non-dyadic; flag dyadic-tangent goldens |
| Q16 | name lookup: repeated-index sign inverted through `Λ`; `∞∞` throws instead of Zero; `∅∅` not zeroed; deletion does not back up (can mis-sign e.g. `v2331`); `w`-names on non-dual spaces MethodError; `w`/`W` unusable in v-names; `w2v1` BoundsError | correct geometric-product semantics; only pure permutations are goldens |
| Q17 | `antimetric` for conformal/non-diagonal spaces calls undefined `antimetric_term` | implement via complements or leave to Grassmann |
| Q18 | `evaluate2` references undefined `N`; `abs` on spaces/blades StackOverflow; `isvolume` UndefVarError; `div/rem/...` on Submanifold nonsense | omit |
| Q19 | display quirks: DiagonalForm tangent trailing comma; conformal subspace prints `1`/`-1` and `∅-1`; dual-tangent covectors subscripted (`ϵ₁w₁`); dyadic-tangent handle suffix `₁²`; `labels[1] = "v"` in dual spaces; `sups[10] = '⁰'` | replicate exactly (goldens depend on them) except dyadic-tangent subspaces with ϵ bits (KeyError in Julia) |
| Q20 | `V([1,3])` -> basis blade but `V(1,3)` -> subspace; `getbasis(Signature, B)` for n > 8 returns a subspace | separate `V.sub [..]` vs `V.blade [..]` APIs |
| Q21 | `W(b)` with `V == W` double-wraps the handle (`Submanifold{v₁₂₃,...}`) | return b unchanged |
| Q22 | Leibniz `indexeven_set/indexodd_set` unfiltered for 0 < n < 22; `indices(b,N)` cache keyed by b only | correct |
| Q23 | `V^i` for `i < 0` returns V; only options 0/4 allowed | `i : Nat` |
| Q24 | `options % 16 ∈ 12..15` decode to plain | `Options` structure makes it unrepresentable |
| Q25 | `metric(b)`/`metrichash` on a non-basis Submanifold return the raw metric bits | separate API |
| Q26 | `isapprox`, `rand` samplers, conversions to Julia numeric types, `promote_rule` | skip / `Coe` instances only as needed |

### 8.4 Julia-specific machinery to redesign

* String macros `S"..." D"..." V"..." Λ"..." basis"..."`: Lean `syntax "S!" str : term` style
  elaborators that run the parser at elaboration time and emit a `Space` literal (compile-time errors
  for bad strings -- the Lean analogue of macro-expansion-time evaluation).
* `@basis V` injecting locals: a command `#basis V as W v w ∂ ϵ` that generates `def`s (or an
  `abbrev` namespace `Basis.R3` with `v`, `v1`, `v12`, ...), plus a term elaborator
  `blade!(V, v12)` that resolves a label (with permutation sign) at compile time.
* `Basis.getproperty` dynamic field access -> `Basis.get? (V) (name : String) : Option (Term V Int)`.
* `@pure`, `@computed`, `@generated`, global caches, `@inbounds` -> pure functions + closed-term tables.
* Notation: Lean core already uses `⊕` for `Sum` (types); define `scoped infixl:65 " ⊕ " =>
  Space.oplus` (overloaded notation resolves by type since `Space` is not a `Type`), or use `⊞`.
  `'` cannot be a postfix operator (identifiers may contain `'`); use `Space.dual`/`V.dual` and a
  postfix notation such as `V†` or `V′` (U+2032; verify it tokenises). `ℝ` collides with Mathlib's
  reals if Mathlib is ever imported -- use `R n`/`Space.euclid n` with scoped notation `ℝ^n`.
  `Λ` is a legal identifier. `∪ ∩ ⊆` via `Union/Inter/HasSubset` instances only for total variants;
  partial ones as named functions returning `Except`.

### 8.5 Suggested Lean module decomposition (rough LOC)

| Module | Contents | LOC |
|---|---|---|
| `DirectSum/Glyphs.lean` | `vio`, `subs`, `sups` (as `Int → Char` functions), `alphanumv/w`, prefixes, `printIndex` | 90 |
| `DirectSum/Bits.lean` | SWAR popcount, ctz, `lowMask`, `indices` (ascending list/array), `indexBits`, `flipsign`, pdep (`expandbits`), pext (correct `lowerbits`) + Julia-compatible `lowerbitsJl`, `dualSwap` | 220 |
| `DirectSum/Combinatorics.lean` | binomial table, `binomsum/spinsum/antisum` (+cumsums), lex `combo`, `indexbasis`, `bladeindex` (table ≤ 12 + closed form), `basisindex`, `spinindex`, `antiindex`, `unrank` | 280 |
| `DirectSum/Options.lean` | `Dyad`, `Options`, `tensorhash` encode/decode (Julia ints for goldens) | 110 |
| `DirectSum/Space.lean` | `Metric`, `Space`, accessors (`mdims`, `grade`, `pseudograde`, `hasinf`, `hasorigin`, `hasconformal`, `isdiag`, `isdual`, `isdyadic`, `istangent`, `diffmask`, `symmetricmask`, `metricAt`, `det`), constructors (`R n`, `euclid n`, `sig`, `diag`) | 330 |
| `DirectSum/Parse.lean` | S/D/V grammars, digit grammar, `S!`/`D!`/`V!` elaborators | 220 |
| `DirectSum/SpaceOps.lean` | `dual`, `oplus`, `pow`, `union?`, `inter?`, `subset`, `beq`, `tangent`, `loworder`, `subtangent`, `mixed`, `combine` | 360 |
| `DirectSum/Blade.lean` | `Blade`, `Sub`, `Term`, `TermResult`, grade/rank/order/diffvars on blades, grade projection, restriction/embedding, evaluation, `(V)(I)` pseudoscalar | 380 |
| `DirectSum/Involution.lean` | parity predicates, reverse/involute/clifford/conj + pseudo variants, even/odd/real/imag | 120 |
| `DirectSum/Complement.lean` | `complement(N,B,D,P)`, parities (left/right/hodge/null), Euclidean and Hodge complements, `metric`, `antimetric`, `paritymetric`, `parityanti` | 260 |
| `DirectSum/Show.lean` | `ToString`/`Repr` for Space, Sub, Blade (`printlabel` incl. label mode), Term (`showvalue` rules), containers; `labels` | 380 |
| `DirectSum/Basis.lean` | `Basis` container (Array of blades + `Std.HashMap String Nat`), sparse/extended as one lazy structure (`get`, `size`, `unrank`), name lookup with correct sign, `#basis` command, `blade!` | 300 |
| `DirectSum/Grade.lean` | `Grade n g` | 50 |
| `DirectSum/Proofs/*.lean` | see 8.6 | 500 |
| `test/DirectSumGolden.lean` | JSON loader (`Lean.Json`) + checkers per golden section, quirk-ID skip lists | 450 |
| **Total** | | **≈ 4,050** (≈ 3,100 code + 500 proofs + 450 tests) |

### 8.6 Proofs that pay for themselves (speed up development, catch port bugs)

* `Options.decode (Options.encode o) = o` -- `decide` over the 24 cases.
* `flipsign_flipsign (h : n ≤ 64) : flipsign n (flipsign n s) = s &&& lowMask n` -- `bv_decide` after
  case split on `n` or via `BitVec` lemmas; gives `dual_dual : V.opts.dyad ≠ .mixed → V.dual.dual ≅ V`.
* `oplus_n : (a.oplus b).n = a.n + b.n`, `tangent_n`, `dual_n` -- `simp`/`omega`.
* `complement_involutive (euclid, D = 0, P = 0)` and the conformal toggle lemma -- `bv_decide` with
  fixed width, `n` as a symbolic mask.
* `basisindex_bij (n ≤ 8)`: `indexbasis n` is a permutation of `[0, 2^n)` and `basisindex` its inverse
  -- `decide`/`native_decide` for small n; state the general theorem (lex rank is a bijection onto
  `Fin (choose n g)`) as the specification with `sorry` initially.
* `bladeindex_lt : bladeindex n b ≤ choose n (popcount b)` (makes `Chain` indexing total without
  runtime checks).
* `parityreverse_iff : parityreverse g ↔ g % 4 = 2 ∨ g % 4 = 3` and `reverse ∘ reverse = id`,
  `clifford = involute ∘ reverse` -- `omega`/`decide`.
* `pext_pdep : pext (pdep b s) s = b &&& lowMask (popcount s)` -- property-tested, then proved.
* `mixed` places V and V' masks in disjoint halves of the dyadic layout -- `bv_decide`.

---

## 9. Oracle test plan

### 9.1 Existing dumper

`.../scratchpad/ds_oracle/dump_directsum.jl` (run:
`julia --startup-file=no --project=<juliaenv> dump_directsum.jl out.json`; ~3.5 min). Every value that
threw in Julia is recorded as `{"error": "<first line>"}`. Terms are normalised as
`{"coef": "<string(value)>", "bits": Int, "grade": Int, "show": "<repr>"}` or `{"zero": true}`;
spaces as `{"kind","n","options","metric","diag","diffvars","diffmode","name","show","hasinf",
"hasorigin","dyadmode","polymode"}`.

| Section | Contents / input distribution | Size |
|---|---|---|
| `index_tables` | exhaustive n = 0..10: `indexbasis` per grade, `combo`, `bladeindex`, `basisindex`, `spinindex`, `antiindex` for all masks, `binom/spin/anticumsum`, `gdimsall` | 11 |
| `index_spots` | deterministic LCG masks for n ∈ {13,16,20,22,30,62} (24 each), blade/basis index for n ≤ 22 | 144 |
| `signature_parse` | 33 S-strings incl. digit grammar and malformed positions | 33 |
| `signature_sweep` | **exhaustive** `{"",∞,∅,∞∅} × {+,-}^{0..5}`: params, adjoint, handle show; for n ≤ 4 also `Λ(V)`, `Λ(V)'` and every subspace display | 252 |
| `diagonal_parse` | 7 D-strings | 7 |
| `tensorbundle_parse` | 16 V-strings (documents Q1) | 16 |
| `spaces` | 29 named spaces (plain, dual, dyadic, conformal, tangent variants, DiagonalForm, polymode): params, `'`, `dual`, `tangent`, `tangent(V,2,3)`, handle show, `V[:]`, mdims/grade/pseudograde/isdiag/det/order/diffmask | 29 |
| `space_pairs` | all 21×21 ordered pairs of a representative set: `⊕`, `∪`, `∩`, `⊆`, `==` (≈1070 recorded errors are expected Julia "not implemented") | 441 |
| `powers` | `^` | 4 |
| `bases` | 19 spaces: `labels`, `labels(V,"X","x","Y","y")`, `Λ(V)` show, every element's bits/show/grade/rank/order/diffvars, `collect(V)` show | 19 |
| `sparse_show` | Sparse/Extended container displays | 7 |
| `subspace_show` | every mask of 9 spaces | 9 |
| `printindex` | i ∈ -1..62 × label ∈ {false,true} × prefix ∈ {v,w,∂,ϵ} | 504 |
| `printindices_62` | README strings | 2 |
| `lookup` | every permutation of every subset (size ≤ 4) of indices for ℝ^3, ℝ^4, S"-+-+", ℝ^5; repeated-index cases tagged `"quirk":"repeat"`; dual/mixed/62-dim/invalid names | 373 |
| `involutions` | every blade of ℝ^4, T(ℝ²), S"∞∅+", ℝ²⊕ℝ²': reverse/involute/clifford/conj/pseudo*/even/odd/real/imag | 48 |
| `parity_tables` | parityreverse/involute/clifford for g = 0..12 | 1 |
| `complements` | every blade of 12 spaces: 4 complements, metric, antimetric, 6 parities | 99 |
| `complement_bits` | `complement(N,B,D,P)` exhaustive for 7 (N,D,P) configs | 184 |
| `single_show` | 23 coefficient/term displays | 23 |
| `subspace_setops` | all 16×16 subspace pairs of ℝ^4: ∪, ∩, ⊆, ⊕ | 256 |
| `subspace_call` | `V(indices...)` | 5 |
| `pdep_pext` | `expandbits` and Julia `lowerbits` for 3 masks × all local masks (documents Q12) | 32 |
| `readme` | README / test assertions | 25 |

### 9.2 Comparison policy for the Lean harness

1. Strings (`show`, labels) compare byte-exactly (Unicode as listed in 5.1).
2. Space params: compare `n, options (Julia int), metric (Signature bits) or diag (strings), diffvars,
   diffmode, name`.
3. Entries with `"error"`: Lean must either also fail (for "not implemented" set operations, dyadic
   adjoint, conformal ⊕) or match a documented quirk ID from 8.3 where Lean deliberately succeeds.
   Keep an explicit allow-list keyed by `(section, input)`.
4. `lookup` entries tagged `repeat` and inputs covered by Q1/Q12/Q15/Q16/Q19-exceptions are compared
   against Lean's *corrected* semantics computed independently (sign via geometric product), not the
   Julia value.
5. Coefficients are compared as strings for Int, and parsed floats (tolerance 0) for Float.

### 9.3 Additions worth dumping later (when Grassmann's product port starts)

* `basisindex`/`indexbasis` for n = 11..16 exhaustive (tables the Lean closed terms will embed).
* `labels` + display for n = 9..12 (SparseBasis path) and a 30-dim sample (ExtendedBasis).
* `diffcheck`, `symmetricmask`, `mixed`, `combine` over exhaustive masks for tangent(ℝ²), tangent(ℝ²,2,2),
  S"∞∅+" (Grassmann's product kernels depend on them).
* Name-scheme 2 (`PRE`) printing for a few spaces (`indexstring(V,D)` uses `PRE`, LB/indices.jl:205-211;
  Oracle `indexstring(Submanifold(ℝ^3),5) = "X13"`).
* Random `Single` displays with Float64 coefficients drawn from `orand()` (uniform [-1,1)) to lock
  Julia's float `show` formatting (shortest round-trip repr).
