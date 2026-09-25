# AbstractTensors.jl + StaticVectors.jl: Lean 4 porting spec

Scope: `AbstractTensors.jl` (abstract tensor type hierarchy, generic operator interface and fallbacks) and `StaticVectors.jl` (the `Values`/`Variables`/`FixedVector` statically sized vectors used as coefficient storage across the whole chakravala ecosystem). `AbstractLattices.jl` (19 lines, the source of `∧`/`∨`) is covered in §7 because AbstractTensors re-exports from it.

## 0. Provenance and conventions

| Item | Value |
|---|---|
| AbstractTensors.jl master | commit `65fc00f` (2025-09-03), `Project.toml` version **0.8.12** |
| AbstractTensors registered (oracle env) | **0.8.11**. Its `src/` differs from master only by the two lines `Base.angle(t::Real,g)` / `Base.angle(t::Complex,g)` (master L441-442). |
| StaticVectors.jl master | commit `0dc6e05` (2025-08-04), version **1.0.9**. The registered copy is byte-identical (`diff -r` is empty). |
| AbstractLattices.jl | master 0.2.2; the registered 0.3.1 source is identical. |
| Oracle | Julia **1.13.0**, env `/private/tmp/claude-502/-Users-alokbeniwal-Grassmann/c6cc2308-bfca-4b9a-ad33-d89b110132a8/scratchpad/juliaenv`. The probe scripts that produced every "oracle:" line below are in `.../scratchpad/probe/` (`sv1.jl`, `sv2.jl`, `at1.jl`, `gr1.jl`, `gr2.jl`, `attest.jl`, `oracle_skeleton.jl`). |

Citation shorthand:
- `AT:n` = `/Users/alokbeniwal/chakravala/AbstractTensors.jl/src/AbstractTensors.jl` line n. This is the whole package: one 648-line file.
- `SV/<file>:n` = `/Users/alokbeniwal/chakravala/StaticVectors.jl/src/<file>` line n.
- `ATtest:n` = `AbstractTensors.jl/test/runtests.jl`. StaticVectors' test file only contains `@test 1 == 1`.
- `ATREADME:n`, `SVREADME:n` = the README files.

Julia indices are **1-based**. In Lean, every `Values` index `i` becomes `Fin n` with value `i-1`. Values produced by `countvalues`/`evenvalues` are data, not indices, and keep their Julia values. Downstream code that feeds them back in as indices must shift by 1 (see §8.6).

---

## 1. Purpose and scope

**AbstractTensors** is the "universal interoperability" layer (ATREADME:14-19). It:
1. declares the abstract type tree `TensorAlgebra{V,T} <: Number` → `Manifold`, `TensorGraded{V,G,T}`, `TensorTerm`, `TensorMixed` (AT:27-132). `V` is a manifold/vector-space *value* stored in the type (a DirectSum `TensorBundle`/`Submanifold` instance, or a bare `Int n` for a bundle itself). `G` is the grade. `T` is the scalar field.
2. gives type-parameter accessors (`Manifold`, `mdims`, `tdims`, `gdims`, `rank`, `valuetype`) and boolean kind predicates.
3. declares the **generic operator vocabulary** shared by DirectSum, Grassmann, Cartan and others: `⟑ ⟇ ∧ ∨ ⨼ ⨽ ⋆ ⊛ ∗ ⊘ ⊖ ⊗ ⊙ ⊠ × ∘ | < > << >> >>>` and postfix `⁻¹ ǂ ₊ ₋ ˣ`. It wires Base `+ - * / \ ^ == dot` to the internal generic functions `plus minus times/wedgedot contraction equal`.
4. provides **fallbacks** in two directions:
   - cross-manifold interop: `op(a::TA{V}, b::TA{W}) = op((V∪W)(a), (V∪W)(b))`.
   - `UniformScaling` (`LinearAlgebra.I`) as a dimension-agnostic unit pseudoscalar.
5. defines generic **derived math** that concrete packages inherit, written only in terms of a few primitives (`⟑`, `inv`, `~`, `cosh`, `sinh`, `expm1`, `log`, `sqrt`, `V(I)`, `one(V)`, `zero(V)`, complements):
   - trig, inverse trig and inverse hyperbolic functions
   - `exp2/exp10/log2/log10`, `b^t`, `log(b,t)`
   - `/` and `\`
   - `abs/abs2/unit/counit/unitnorm/geomabs`
   - the "co"/"pseudo" complement-conjugated variants
   - a parallel metric (`g`-argument) variant of most of these
6. adds scalar (`Real`/`Complex`) instances of the interface (`scalar`, `involute`, `even` are identity, `odd(x)=0`, `!x = x*I`).
7. adds symbolic-coefficient hooks (`norm`, `signbit`, `≈`, `∑`, `∏` on `Expr`/`Symbol`) that Leibniz/Grassmann's symbolic mode extends.
8. re-exports StaticVectors types and adds `FloatVector`/`RealVector`-style array aliases.

**StaticVectors** (a trimmed fork of StaticArrays.jl, `SV/StaticVectors.jl:2-3`) provides `TupleVector{N,T} <: AbstractVector{T}` and three concrete types:
- `Values{N,T}`: immutable, NTuple-backed, alias `SVector`.
- `Variables{N,T}`: mutable, NTuple-backed, alias `MVector`.
- `FixedVector{N,T,TData}`: wraps a `Vector`, alias `SizedVector`.

It also provides fully-unrolled `@generated` arithmetic, map/reduce, broadcasting, indexing, norms and dot products, and the integer range builders `countvalues`/`evenvalues`/`evens`. **Every coefficient container in Grassmann is a `Values`**: `Chain{V,G,T}.v::Values{binomial(n,G),T}` (Grassmann `multivectors.jl:68-71`) and `Multivector{V,T}.v::Values{2^n,T}` (`multivectors.jl:229-232`). Accumulation buffers are `Variables` (Leibniz `utilities.jl:63-67`: `mvec(N,G,t)=Variables{gdims(N,G),t}`). So `Values` is the single most performance-critical data structure of the port.

Out of scope and to be skipped in Lean (§8.5):
- the `STATICJL` env switch that aliases these types to StaticArrays (`SV/StaticVectors.jl:22-25`, ATREADME:23)
- pointer / `unsafe_convert` / `dataids` plumbing
- `Base.rest` destructuring
- multidimensional `TupleIndexing` machinery
- `similar`/`similar_type` type computation (Lean result types are static)
- `BroadcastStyle` plumbing (replace with explicit `map`/`zipWith`)

---

## 2. Public API inventory

### 2.1 AbstractTensors: all 107 exports

These come from `names(AbstractTensors)` under the oracle. The exports are spread over AT:278-283 plus AT:225, 540, 552, 630, 633, 638, 643.

`×` is exported (AT:283) but **never defined in AbstractTensors**: `isdefined(AbstractTensors, :×) == false`. The user gets `LinearAlgebra.×` (= `cross`), which AT extends at AT:349. `valtype` is exported (AT:225) but **clashes with `Base.valtype`**, so an unqualified `valtype` in `Main` throws `UndefVarError` (oracle).

#### 2.1.1 Types

| Julia | Kind / definition | Semantics | Line | Lean mapping |
|---|---|---|---|---|
| `TensorAlgebra{V,T} <: Number` | abstract | Root: element over manifold `V` (a value lifted into the type domain) with scalar field `T`. **Subtypes `Number`**, so Base treats tensors as scalars in broadcasting and promotion, and `Values{N,<:Number}` arithmetic applies to tensor-valued entries. | AT:32 | marker class + indices (§8.2) |
| `TensorAlgebra{V}(t::TensorAlgebra{V})` | ctor | identity | AT:33 | `id` |
| `TensorAlgebra{V}(t::TensorAlgebra{W})` | ctor | `(V∪W)(t)`: embed into the union space | AT:34 | `embed (V ∪ W)` |
| `Manifold{V,T} <: TensorAlgebra{V,T}` | abstract | "basis parameter locally homeomorphic to `V::Submanifold{M}`". Supertype of DirectSum's `TensorBundle{n,…} <: Manifold{n,Int}` (DirectSum `DirectSum.jl:64`, so a vector space has `V = n::Int`), of all `TensorGraded`, and of Grassmann's `ChainBundle`/`TensorNested`. | AT:49 | marker class |
| `TensorGraded{V,G,T} <: Manifold{V,T}` | abstract | homogeneous grade `G::Int` | AT:64 | class with `G : outParam Nat` |
| `Scalar{V,T}` | `const = TensorGraded{V,0,T}` | grade 0 | AT:80 | abbrev (G=0) |
| `GradedVector{V,T}` | `const = TensorGraded{V,1,T}` | grade 1 | AT:87 | abbrev |
| `Bivector{V,T}` | `const = TensorGraded{V,2,T}` | grade 2 | AT:94 | abbrev |
| `Trivector{V,T}` | `const = TensorGraded{V,3,T}` | grade 3 | AT:101 | abbrev |
| `TensorTerm{V,G,T} <: TensorGraded{V,G,T}` | abstract, **not exported** | single-coefficient element: `Submanifold`, `Single`, `Zero`, `Infinity` in DirectSum | AT:108 | class with `coeff` |
| `TensorMixed{V,T} <: TensorAlgebra{V,T}` | abstract, **not exported** | non-homogeneous: `Multivector`, `Spinor`, `CoSpinor`, `Couple`, `PseudoCouple`, `Phasor` in Grassmann | AT:124 | marker class |
| `FloatVector{T<:AbstractFloat}` | `= AbstractVector{T}` | alias | AT:634 | skip (use `Values n Float`) |
| `FloatMatrix{T<:AbstractFloat}` | `= AbstractMatrix{T}` | alias | AT:635 | skip |
| `FloatArray{N,T<:AbstractFloat}` | `= AbstractArray{T,N}` (**N first**, reversed from Base) | alias | AT:636 | skip. **Name clash with Lean core `FloatArray`**, so do not reuse the name. |
| `RealVector`, `RealMatrix`, `RealArray{N,T}` | same pattern with `T<:Real` | alias | AT:639-641 | skip |
| `TupleVector`, `Values`, `Variables`, `FixedVector` | re-exported from StaticVectors | see §2.2 | AT:643-645 | §8 |

Internal (not exported) types:
- `Postfix{Op}`, an empty struct used as a postfix-operator token (AT:573).
- `const TAG = (:TensorAlgebra,:TensorGraded)`, the code-generation list (AT:65). Grassmann imports it.

#### 2.1.2 Kind predicates (all `Base.@pure`, return `Bool` from the type)

| Julia | Semantics | Line |
|---|---|---|
| `istensor(t)` | `t isa TensorAlgebra` | AT:41-42 |
| `ismanifold(t)` | `t isa Manifold` | AT:56-57 |
| `isgraded(t)` | `t isa TensorGraded` | AT:72-73 |
| `isterm(t)` | `t isa TensorTerm` | AT:115-116 |
| `ismixed(t)` | `t isa TensorMixed` | AT:131-132 |
| `isscalar(t::TensorGraded)` | `rank(t)==0 \|\| iszero(t)` | AT:194 (loop AT:183-196) |
| `isvector(t::TensorGraded)` | `rank(t)==1 \|\| iszero(t)` | AT:194 |
| `isbivector(t::TensorGraded)` | `rank(t)==2 \|\| iszero(t)` | AT:194 |
| `istrivector(t::TensorGraded)` | `rank(t)==3 \|\| iszero(t)`. **Not exported**; Grassmann imports it. | AT:194 |
| `isvolume(t::TensorGraded)` | `rank(t)==mdims(t) \|\| iszero(t)` | AT:206 |
| `Base.isfinite(b::TensorTerm)` | `isfinite(value(b))` | AT:117 |
| `isnull(n)` (not exported) | `iszero(n)`. Always `false` for `Expr`/`Symbol`. | AT:590-592 |

Note: `isscalar` etc. for `TensorMixed` are **not** defined here; Grassmann defines them. On a `Real` they have no method.

#### 2.1.3 Dimension and type-parameter accessors

| Julia | Signature | Semantics | Line |
|---|---|---|---|
| `Manifold(x)` | `x::TensorAlgebra{V}` or `Type{<:TensorAlgebra{V}}` | returns `V` (the value) | AT:136-139 |
| `Manifold(x::Manifold)` | instance or type | returns `x` itself. More specific than the above, so **a manifold is its own `Manifold`**. | AT:140 |
| `Base.parent(x::TensorAlgebra)` | | `Manifold(x)` | AT:141 |
| `rank(t::TensorGraded{V,G})` | `LinearAlgebra.rank` extended | `G` | AT:153 |
| `rank(::Type{M<:Manifold})` | | `mdims(M)` | AT:154 |
| `mdims(t)` | `TensorAlgebra` instance or type | `mdims(Manifold(t))`. **Requires** the downstream manifold type (DirectSum) to define `mdims`; otherwise it recurses forever. | AT:161-162 |
| `mdims(M::Int)` | | `M` | AT:163 |
| `tdims(t)` / `tdims(M::Int)` | | `1 << mdims(t)`, i.e. `2^n` (full algebra dimension) | AT:170-172 |
| `gdims(t::TensorGraded{V,G})` | | `binomial(mdims(t), G)` | AT:179-180 |
| `gdims(N,G)` | | `Base.binomial(N,G)`: 0 when `G<0` or `G>N` (oracle: `gdims(4,5)==0`) | AT:181 |
| `value(t::Number)`, `value(t::AbstractArray)` | | identity. Concrete tensor types override this to return their `Values` storage. | AT:213-214 |
| `valuetype(x)` | instance or type of `TensorAlgebra{V,K}` | `K` | AT:221-222 |
| `valuetype(x::Number)` | instance or type | `typeof(x)` | AT:223-224 |
| `valtype` | `const = valuetype` | exported; clashes with Base | AT:225 |
| `Base.real(::Type{<:TensorAlgebra})` | | `real(valuetype(T))` | AT:227 |
| `Base.rtoldefault(::Type{<:TensorAlgebra})` | | `rtoldefault(valuetype(T))`: `2^-26 = 1.4901161193847656e-8` for Float64, `0.00034526698` for Float32, `0` for integers (oracle) | AT:228 |

#### 2.1.4 Grade projections and involutions

| Julia | Semantics | Line |
|---|---|---|
| `scalar(t::TensorGraded{V})` | `zero(V)` when grade ≠ 0 | AT:192 |
| `scalar(t::TensorGraded{V,0})` | `t` | AT:193 |
| `vector`, `bivector`, `trivector` | same rule for G = 1, 2, 3. `trivector` is **not exported**. | AT:183-196 |
| `pseudoscalar(t::Manifold)` | `t` (not exported) | AT:203 |
| `volume` | `const volume = pseudoscalar`, so both names bind **the same function** | AT:204 |
| `volume(t::TensorGraded{V,G})` | `G == mdims(t) ? t : zero(V)` | AT:205 |
| `scalar(t::Real)`, `involute(t::Real)`, `even(t::Real)` | `t` | AT:345-347 |
| `odd(::Real)` | **`0` (an `Int`, whatever the input type)**. Oracle: `odd(2.5) === 0`. | AT:348 |
| `involute`, `even`, `odd`, `scalar` on `Complex` | **no method** (MethodError). Oracle confirms. | (none) |
| `clifford`, `basis`, `complementleft`, `complementlefthodge`, `complementleftanti`, `complementrightanti`, `⊙`, `⊠`, `¬` | declared with **zero methods** (`function f end`) and implemented downstream. `⋆` also appears in that list, but it is already `const ⋆ = complementrighthodge`, so the declaration is a no-op. | AT:342-344 |

#### 2.1.5 Complement / Hodge family

| Julia | Definition | Line |
|---|---|---|
| `!(t::Real)`, `!(t::Complex)` (Base piracy; `Bool` keeps Base's more specific method) | `UniformScaling(t)`, i.e. `t*I`: the complement of a scalar is a scaled unit pseudoscalar. Oracle: `!2 == UniformScaling{Int64}(2)`, `!true == false`. | AT:303-307 |
| `complementrighthodge(t::Real/Complex, g=nothing)` | `UniformScaling(t)` | AT:303-307 |
| `complement`, `complementright` | `const = Base.:!` | AT:309-310 |
| `⋆`, `hodge` | `const = complementrighthodge` | AT:311-312 |
| `Base.:!(t::UniformScaling{T})` | `T<:Bool ? (t.λ ? 1 : 0) : t.λ`: the complement of the pseudoscalar is the scalar. Oracle: `!I === 1`, `!(2I) === 2`, `!(0.5I) === 0.5`, `!UniformScaling(false) === 0`. | AT:316 |
| unary `Base.:|(t::TensorAlgebra)` | `hodge(t)` | AT:315 |
| `LinearAlgebra.cross(a::TA, b::TA)` (exported as `×` via LinearAlgebra) | `hodge(a ∧ b)` | AT:349 |

#### 2.1.6 Binary product vocabulary

ASCII names are Julia's own aliases. The Lean column is a suggestion.

| Unicode | ASCII / aliases | Definition in AT | Julia prec | Line |
|---|---|---|---|---|
| `*` | `times`, `wedgedot`, `⟑`, `⊖` | `*(a::TA, b::TA) = times(a,b)`. `times === wedgedot`. **`*` is the geometric product.** Non-tensor fallback: `wedgedot(a,b) = a*b`. Unary `*(t)=t`, `wedgedot(t)=t`. | 12 (`⊖` is 11) | AT:296, 314, 340, 350 |
| `+` | `plus` | `+(a::TA,b::TA) = plus(a,b)`, unary `+(t)=t` | 11 | AT:294, 340 |
| `-` | `minus` | `-(a::TA,b::TA) = minus(a,b)` | 11 | AT:295 |
| `==` | `equal` | `==(a::TA,b::TA) = equal(a,b)` | 7 | AT:298 |
| `⋅` / `dot` | `contraction`, `\|`, `⨽`, `>` | same V: `dot`, `\|`, `⨽`, `>` all equal `contraction(a,b)`. Non-tensor fallback: `contraction(a,b) = LinearAlgebra.dot(a,b)`, which conjugates `a`. | 12 / 11 (`\|`) / 7 (`>`) | AT:264-265, 297, 351, 447 |
| `⨼` | `<` | `⨼(a,b) = contraction(b,a)`, and `<(a,b) = contraction(b,a)` | 12 / 7 | AT:259, 262 |
| `<<` | | `contraction(b, ~a)` | 14 | AT:260 |
| `>>` | | `contraction(~a, b)` | 14 | AT:261 |
| `∗` | | `(~a) ⟑ b`: reverse-geometric product | 12 | AT:257 |
| `⊛` | | `scalar(contraction(a,b))`: scalar product | 12 | AT:258 |
| `∘` | `expansion`, `antidot`, `pseudodot`, `codot` | `∘(a::TA,b::TA) = expansion(a,b)`. `expansion` has no same-V method here (Grassmann: `antidot(a,b) = complementleft(contraction(complementright(a), complementright(b)))`). | 12 | AT:314, 337 |
| `⟇` | `veedot` | `const ⟇ = veedot` (Julia ≥ 1.10). Implemented downstream (Grassmann: `complementleft(complementright(a)*complementright(b))`). | 11 | AT:628-631 |
| `∧` | `wedge` (AbstractLattices) | re-exported by `import`, **not exported** by AT. `∧()=1`, `∧(x)=x`, `∧(p::Bool,q::Bool)=p&&q`. | 12 | AT:271-273 |
| `∨` | `vee` (AbstractLattices) | `∨()=I`, `∨(x)=x`, `∨(p::Bool,q::Bool)=p\|\|q` | 11 | AT:271, 274 |
| `⊘` | `sandwich` | same V: downstream (Grassmann: `x ⊘ R = R⟑x⟑inv(R)`; oracle `v1 ⊘ v12 == -v1`) | 12 | AT:313 |
| `>>>` | | downstream (Grassmann: `R >>> x` = sandwich with the arguments swapped) | 14 | AT:287, 299 |
| `⊗` | | `⊗(a::TA, b::Real\|Complex) = a*b` and symmetrically. On two scalars: **no method** (oracle). Downstream: Grassmann tensor/dyadic product. | 12 | AT:333-336 |
| `⊙`, `⊠` | | declared only (Grassmann: symmetrized/antisymmetrized products) | 12 | AT:342 |
| `div`, `rem`, `&` | | interop and UniformScaling lifts only | | AT:287, 299 |
| `/` | | `a/b = a ⟑ inv(b)` (**right** division) | 12 | AT:320 |
| `\` | | `a\b = inv(a) ⟑ b` | 12 | AT:323 |
| `^` | | `b::Number ^ t::TA = exp(t ⟑ log(b))` | 15 | AT:326 |
| `LinearAlgebra.norm(a,b)` | | `norm(a-b)` for mixed/mixed and graded/graded only | | AT:366-367 |
| `metric(a,b)` | | `abs(a-b)` (tensor pairs and scalar pairs) | | AT:368-379 |
| `cometric(a,b)` | `pseudometric`, `antimetric` | `pseudoabs(a-b)`. **Ambiguity bug** on `Single` pairs with DirectSum (oracle MethodError). | | AT:368-379, 551 |

"Interop list": `plus, minus, wedgedot, wedgedot_metric, contraction, contraction_metric, equal, sandwich, ⊛, ∗, |, <, >, <<, >>, >>>, div, rem, &` get the cross-manifold fallback `op(a::TA,b::TA) = interop(op,a,b)` (AT:299-301).

"UniformScaling list": `+, -, *, sandwich, ⊛, ∗, ⨼, ⨽, contraction, contraction_metric, expansion, veedot, wedgedot, wedgedot_metric, dot, |, ==, <, >, <<, >>, >>>, div, rem, &` get `op(a::TA, J::UniformScaling) = op(a, Manifold(a)(J))` and the mirrored method (AT:287-292).

#### 2.1.7 Interop

| Julia | Definition | Line |
|---|---|---|
| `interop(op, a::X{V}, b::Y{V})` (X,Y ∈ `TAG`) | same `V`: `op(a,b)` | AT:246 |
| `interop(op, a, b)` otherwise | `M = Manifold(a) ∪ Manifold(b); op(M(a), M(b))` | AT:249-252 |
| `interform(a::X{V}, b::Y{V})` | `a(b)` (evaluate form `a` at `b`) | AT:247 |
| `interform(a, b)` otherwise | `M(a)(M(b))` with `M = V∪W` | AT:253-256 |

**Contract for implementors** (ATREADME:55-66, ATtest:10-38):
1. The same-V method is the real implementation.
2. The cross-V method calls `interop`.
3. A conversion morphism `(W::Manifold)(x)` must exist.
4. `Manifold(op(a,b)) == Manifold(a) ∪ Manifold(b)` must hold.

If only the generic fallback exists, `op(a,a)` (same V) recurses forever: `plus → interop → plus → …`. The oracle confirms `a - b`, `a == b`, `a * b` and `isapprox` all throw `StackOverflowError` on a type that implements nothing (`probe/attest.jl`).

#### 2.1.8 Norms and normalizations

| Julia | Definition | Line |
|---|---|---|
| `abs(t::TA)` | `sqrt(abs2(t))` | AT:435 |
| `abs(t::TA, g)` | `sqrt(abs2(t,g), g)` | AT:436 |
| `abs2(t::TA)` (mixed) | `a = (~t) ⟑ t; isscalar(a) ? scalar(a) : a`. **May return a non-scalar multivector.** Oracle: `abs2(1+2v1+3v12) == 14+4v1+12v2`, and then `abs` throws because the sqrt of that is undefined. | AT:437 |
| `abs2(t::TA, g)` | same with `wedgedot_metric(~t,t,g)` | AT:438 |
| `abs2(t::TensorGraded)` | `contraction(t,t)` | AT:439 |
| `abs2(t::TensorGraded, g)` | `contraction_metric(t,t,g)` | AT:440 |
| `norm(t::TA)` | `norm(value(t))`: **Euclidean 2-norm of the coefficient storage**, not the geometric norm. Oracle: `norm(1+2v1+3v12) == 3.7416573867739413`. | AT:444 (plus module-local `norm(z)=LinearAlgebra.norm(z)` at AT:443) |
| `iszero(t::TA)` | `norm(t) ≈ 0`. With default tolerances this means **exactly `norm(t) == 0`**: `isapprox(x,0)` needs `abs(x) ≤ rtol*abs(x)` with rtol < 1. Oracle: `iszero(1e-300v1) == false`. | AT:445 |
| `isone(t::TA)` | `norm(t) ≈ value(scalar(t)) ≈ 1` (a chained comparison, i.e. both hold) | AT:446 |
| `geomabs(t)`, `geomabs(t,g)` | `abs(t) + coabs(t)` | AT:454-455 |
| `unit(t::Number)`, `unit(t,g)` | `t / abs(t)` (metric: `/(t, abs(t,g), g)`). Scalars: `unit(-2) == -1.0`, `unit(3+4im) == 0.6+0.8im`. | AT:462-463 |
| `counit`, alias `unitize` (only `unitize` exported) | `t / value(coabs(t))`. **Fails on plain scalars**: no `coabs(::Float64)`. | AT:470-472 |
| `unitnorm(t)` | `t / norm(geomabs(t))`. Fails on scalars (no `geomabs(::Float64)`). | AT:479-480 |
| `isapprox(a::TA, b::TA; atol=0, rtol=rtoldefault(a,b,atol), nans=false, norm=LinearAlgebra.norm)` | `x,y = norm(a),norm(b); (isfinite(x)&&isfinite(y)&& norm(a-b) ≤ max(atol, rtol*max(x,y))) \|\| (nans&&isnan(x)&&isnan(y))` | AT:229-232 |
| `isapprox(a::TensorGraded, b::TensorGraded; …)` | `Manifold(a)==Manifold(b) && (rank(a)==rank(b) ? [the same test] : isnull(a) && isnull(b))`. Oracle: `isapprox(0.0v1, 0.0v12) == true`, `isapprox(1.0v1, 1.0v12) == false`. | AT:233-240 |

#### 2.1.9 Transcendental functions (generic, inherited by Grassmann)

A single code-generation loop (AT:318-332 and AT:405-431) produces two families:
- plain: `op = ⟑`, `logm = Base.log`, no extra args.
- metric: `op = wedgedot_metric`, `logm = log_metric`, extra trailing argument `g`.

`V` is the manifold. `i = V(I)` is the **unit pseudoscalar of V** (not an imaginary unit!). `1` is `one(V)`.

| Function | Definition (plain family; the metric family threads `g` through every call) | Line |
|---|---|---|
| `a / b` | `a ⟑ inv(b)` | AT:320 |
| `J / b` (J a UniformScaling) | `V(J) ⟑ inv(b)` | AT:321 |
| `a / J` | `a ⟑ inv(V(J))` | AT:322 |
| `a \ b` | `inv(a) ⟑ b` | AT:323 |
| `J \ b` | `inv(V(J)) ⟑ b` | AT:324 |
| `a \ J` | `inv(a) ⟑ V(J)` | AT:325 |
| `b::Number ^ t` | `exp(t ⟑ log(b))` | AT:326 |
| `a ^ J`, `J ^ b` | `a ^ V(J)`, `V(J) ^ b` | AT:327-328 |
| `exp(t)` | `one(V) + expm1(t)` | AT:329 |
| `log(b, t)` | `log(t) / log(b)`. **Shadowed for `b::Real`** by AT:401 (see §8.4 bug B1). | AT:330 |
| `log2(t)` | `log2(ℯ) * log(t)`, with `log2(ℯ)=1.4426950408889634` | AT:383 |
| `log10(t)` | `log10(ℯ) * log(t)` = `0.4342944819032518*log(t)` | AT:383 |
| `exp2(t)` | `exp(log(2) * t)`, with `log(2)=0.6931471805599453` | AT:384 |
| `exp10(t)` | `exp(log(10) * t)`, with `log(10)=2.302585092994046` | AT:384 |
| `cos(t)` | `cosh(i ⟑ t)` | AT:407 |
| `sin(t)` | `sinh(i ⟑ t) / i` | AT:408 |
| `tan(t)` | `sin(t) / cos(t)` | AT:409 |
| `cot(t)` | `cos(t) / sin(t)` | AT:410 |
| `sec(t)` | `inv(cos(t))` | AT:411 |
| `csc(t)` | `inv(sin(t))` | AT:412 |
| `asec(t)` | `acos(inv(t))` | AT:413 |
| `acsc(t)` | `asin(inv(t))` | AT:414 |
| `sech(t)` | `inv(cosh(t))` | AT:415 |
| `csch(t)` | `inv(sinh(t))` | AT:416 |
| `asech(t)` | `acosh(inv(t))` | AT:417 |
| `acsch(t)` | `asinh(inv(t))` | AT:418 |
| `tanh(t)` | `sinh(t) / cosh(t)` | AT:419 |
| `coth(t)` | `cosh(t) / sinh(t)` | AT:420 |
| `asinh(t)` | `log(t + sqrt(1 + t⟑t))` | AT:421 |
| `acosh(t)` | `log(t + sqrt(t⟑t - 1))` | AT:422 |
| `atanh(t)` | `(log(1+t) - log(1-t)) / 2` (the `/2` is the 2-arg scalar division; no `g`) | AT:423 |
| `acoth(t)` | `(log(t+1) - log(t-1)) / 2` | AT:424 |
| `asin(t)` | `(-i) ⟑ log(i⟑t + sqrt(1 - t⟑t))` | AT:425 |
| `acos(t)` | `(-i) ⟑ log(t + i⟑sqrt(1 - t⟑t))` | AT:426 |
| `atan(t)` | `it = i⟑t; ((-i)/2) ⟑ (log(1+it) - log(1-it))` | AT:427 |
| `acot(t)` | `((-i)/2) ⟑ (log(t-i) - log(t+i))` | AT:428 |
| `sinc(t)` | `iszero(t) ? one(V) : (x = π*t; sin(x)/x)` | AT:429 |
| `cosc(t)` | `iszero(t) ? zero(V) : (x = π*t; cos(x)/t - sin(x)/(x⟑t))` | AT:430 |

**Primitives the implementor must provide** (not defined in AT for tensors): `⟑`, `+`, `-`, `inv`, `~` (reverse), `cosh`, `sinh`, `expm1` (or override `exp`), `log`, `sqrt`, scalar×tensor, tensor÷scalar, `one(V)`, `zero(V)`, `V(I)`, `iszero` (default through `norm`), and `complementleft`/`complementright` for the co/pseudo family. Grassmann overrides `exp`, `expm1`, `log`, `cosh`, `sinh`, `inv`, `sqrt`, `^`, `abs2` (partly) and **inherits** `cos`, `sin`, `tan`, `cot`, `sec`, `csc`, `tanh`, `coth`, `sech`, `csch`, `asinh`, `acosh`, `atanh`, `acoth`, `asin`, `acos`, `atan`, `acot`, `sinc`, `cosc`, `exp2`, `exp10`, `log2`, `log10`, `/`, `\` from AT (checked by `rg` over Grassmann `src/`).

Scalar pass-throughs, so that the metric forms also work on plain numbers:
- `f(t::Real/Complex, g) = f(t)` for `f ∈ abs abs2 cos sin tan cot sec csc asec acsc sech csch asech acsch cosh sinh tanh coth asinh acosh atanh acoth asin acos atan acot sinc cosc cis sqrt cbrt exp exp2 exp10 log2 log10` (AT:395-400)
- `/(a,b,g)` and `^(a,b,g)` for Real/Complex pairs: plain op (AT:387-394)
- `log(t::Real/Complex, g::TensorAlgebra) = log(t)` (AT:401-402)
- `log_metric(t::Real/Complex, g) = log(t)` (AT:403-404)
- `angle(t::Real/Complex, g) = angle(t)` (AT:441-442, master only)
- `wedgedot_metric(a,b,g) = a*b` when either side is Real/Complex (AT:352-359)
- `contraction_metric(a,b,g) = contraction(a,b)` for scalar/tensor combos (AT:360-365)

#### 2.1.10 co/pseudo (complement-conjugated) family

For `fun ∈ (abs, abs2, sqrt, cbrt, exp, log, inv, sin, cos, tan, sinh, cosh, tanh)` (AT:532-548), AT generates **both** `pseudo<fun>` and `co<fun>`, all exported:
- `co<fun>(t::TA) = complementleft(fun(complementright(t)))`
- `co<fun>(t::TA, g) = complementleft(fun(complementright(t), g))`, for every fun except `log`

The 26 names:
- `coabs coabs2 cosqrt cocbrt coexp colog coinv cosin cocos cotan cosinh cocosh cotanh`
- `pseudoabs pseudoabs2 pseudosqrt pseudocbrt pseudoexp pseudolog pseudoinv pseudosin pseudocos pseudotan pseudosinh pseudocosh pseudotanh`

**`cotan` means "complemented tan", not cotangent. `cosin` means complemented sin.**

Extras:
- `colog_metric`, `pseudolog_metric` (AT:549-550)
- `const antiabs, antiabs2, antimetric, pseudometric = coabs, coabs2, cometric, cometric` (AT:551)
- `cosandwich(x,R) = complementleft(sandwich(complementright(x), complementright(R)))`, alias `pseudosandwich`, plus a `g` variant (AT:559-561)
- `antisandwich(R,x) = complementleft(complementright(R) >>> complementright(x))`, plus a `g` variant (AT:568-569)

Macros:
- `@co f(a,b,…)` defines `cof(a,b,…) = complementleft(f(complementright(a), complementright(b), …))` (AT:500-505)
- `@pseudo` is identical with the `pseudo` prefix (AT:525-530)

Docstring examples: AT:487-498 and AT:512-523.

#### 2.1.11 Postfix operators

AT:573-582:

```julia
struct Postfix{Op} end
Base.:*(t, op::Postfix) = op(t)   # ANY t
⁻¹ = Postfix{:⁻¹}() → inv(t)
ǂ  = Postfix{:ǂ}()  → conj(t)
₊  = Postfix{:₊}()  → even(t)
₋  = Postfix{:₋}()  → odd(t)
ˣ  = Postfix{:ˣ}()  → involute(t)
```

Julia parsing constraint: these characters are identifier-continuation characters, so `x⁻¹` is a *single identifier*. Users must write `(x)⁻¹`, which is juxtaposition, i.e. `(x)*⁻¹`, or `x * ⁻¹` with spaces. `t*⁻¹` without spaces parses as the operator `*⁻¹` (operator suffix) and fails (oracle `ParseError`). Lean has no such issue (§8.3).

#### 2.1.12 Module-local shadow functions (symbolic hooks)

These are not exported, but downstream packages import them explicitly: Leibniz `utilities.jl:15-16`, DirectSum `DirectSum.jl:30-32`, and Grassmann qualified calls such as `AbstractTensors.sinh` (9 uses) and `AbstractTensors.exp` (8).

| Julia | Definition | Line |
|---|---|---|
| `inv, /, -, ∏, ∑` | imported from StaticVectors: `inv(z)=Base.inv(z)`, `/(a,b)`, `-(a,b)`, `-(x)`, `-(x::Symbol)=:(-x)`, `∏(x...)=Base.*(x...)`, `∑(x...)=Base.+(x...)` | AT:586, SV/StaticVectors.jl:7-14 |
| `inv(z::TA)` | `Base.inv(z)` | AT:599 |
| `conj sqrt abs expm1 log log1p sin cos sinh cosh signbit` | `f(z)=Base.f(z)`, plus a `TA` method | AT:600-605 |
| `exp(z)`, `dot(x,y)` | Base / LinearAlgebra forwarding | AT:596-597 |
| `^`, `≈` | Base forwarding (also for TA pairs, together with `-` and `/`) | AT:607-612 |
| `≈(a::Expr\|Symbol, b)` | `a == b` for same kind, else `false` | AT:614-620 |
| `norm(z::Expr)` | `abs(z)` (needs a symbolic backend) | AT:588 |
| `norm(z::Symbol)` | `z` | AT:589 |
| `signbit(x::Symbol)` | `false` | AT:593 |
| `signbit(x::Expr)` | `x.head == :call && x.args[1] == :-`, true for both `:(-x)` and `:(x-y)` (oracle) | AT:594 |
| `∏(x::AbstractVector)`, `∑(x::AbstractVector)` | `*(x...)`, `+(x...)` | AT:622-624 |
| `const PROD, SUM, SUB, √ = ∏, ∑, -, sqrt` | | AT:626 |

Oracle checks: `SUB(5) == -5`, `AT.:-(:x) == :(-x)`, `∑(1,2,3) == 6`, `∏(Values(2,3,4)) == 24`, `AT.norm(3) == 3.0`.

### 2.2 StaticVectors: API

Exports: `TupleVector, Values, Variables, FixedVector` (`SV/StaticVectors.jl:18`). Everything below is reachable through `StaticVectors.<name>` and used downstream: `countvalues` (MeshTopology 53 uses), `evens`/`evenvalues` (Grassmann 39), `_diff` (Cartan 46), `similar_type` (Grassmann 1).

#### 2.2.1 Types and aliases

| Julia | Definition | Line |
|---|---|---|
| `TupleVector{N,T} <: AbstractVector{T}` | abstract, size in the type | SV/StaticVectors.jl:27 |
| `TupleMatrixLike{n,T}` | `Union{Transpose, Adjoint, Diagonal}` of `TupleVector{n,T}` | :33-37 |
| `TupleVectorLike{n,T}` | `Union{TupleVector{n,T}, TupleMatrixLike{n,T}}` | :38 |
| `Values{N,T} <: TupleVector{N,T}` | `struct` with the single field `v::NTuple{N,T}`. Inner ctors take `NTuple{N,T}` directly or `NTuple{N,Any}` via `convert_ntuple(T,x)`. | SV/Values.jl:7-11 |
| `Variables{N,T} <: TupleVector{N,T}` | `mutable struct` with `v::NTuple{N,T}`. Inner ctors take `NTuple{N,T}`, `NTuple{N,Any}` (converted), or `undef`. | SV/Variables.jl:7-12 |
| `FixedVector{N,T,TData<:AbstractVector{T}} <: TupleVector{N,T}` | `struct` with `v::TData`. Checks 1-based indexing and `length(a)==N`, else `DimensionMismatch("Dimensions $(length(a)) don't match static size $N")`. Also has an `undef` ctor. **Aliases the wrapped array (no copy)**: oracle shows that mutating the source `Vector` changes the `FixedVector`. | SV/FixedVector.jl:8-20 |
| `SVector`, `MVector`, `SizedVector` | `const = Values, Variables, FixedVector` | SV/StaticVectors.jl:63 |
| `SOneTo{n} <: AbstractUnitRange{Int}` | static axis `1:n`. `SOneTo(n)`, `SOneTo{n}(r)` (checks `first==1 && last==n`, else `DimensionMismatch("$r is inconsistent with SOneTo{$n}")`), `first=1`, `last=n`, iterate, `.start`/`.stop`, shown as `SOneTo(n)`. | SV/SOneTo.jl:5-62 |
| `TV{T}` (with `TV_F32`, `TV_F64`) | literal syntax `TV[1.0,2.0]`, which builds `Values{2,Float64}`; `TV{T}[…]` forces the element type | SV/initializers.jl:23-37 |
| `_InitialValue` | the "no init" sentinel for reductions | SV/mapreduce.jl:23 |

#### 2.2.2 Construction and conversion

| Call | Result | Line |
|---|---|---|
| `Values(x...)` | via `SA(x...) = SA(x)` (SV/convert.jl:8), then `Values(x::NTuple{N,Any}) = Values{N}(x)`, then `Values{N}(x::T<:Tuple) = Values{N,promote_tuple_eltype(T)}(x)`. **Element types are promoted** with `promote_type`: `Values(1,2.0)::Values{2,Float64}`, `Values(1,"b")::Values{2,Any}`, `Values(1.0f0,2)::Values{2,Float32}`. `Values()` and `Values(())` **error** (oracle UndefVarError). | SV/Values.jl:84-86 |
| `Values{N,T}(x...)` | converts each element with `convert(T,·)`: `Values{2,Int}(1,2.5)` → `InexactError`, `Values{2,Int}(1,2.0)` → `[1,2]` | SV/Values.jl:10, SV/util.jl:6-14 |
| `Values{N}(a::AbstractVector)`, `Values{N,T}(a)` | `convert(SA,a)` checks `length(a)==N`, else `DimensionMismatch("expected input vector of length $N, got length $(length(a))")`, then `unroll_tuple(a,Val(N))` | SV/convert.jl:10, 24-34, 46-52 |
| `Values{N}(gen)`, `Values{N,T}(gen)` | `tvcollect`: pull exactly N items, else `"Generator produced too few elements: Expected exactly 3 elements, but generator stopped at 3"` or `"Generator produced too many elements: Expected exactly 3 elements, but generator yields more"` | SV/Values.jl:20-71, 88-89 |
| `Values(a::TupleVector)`, `Variables(a)`, `SA(a::TupleVector)` | `SA(Tuple(a))` | SV/Values.jl:73, SV/Variables.jl:14, 72, SV/convert.jl:9 |
| `FixedVector(a::TupleVector)` | **ambiguous, throws MethodError** (oracle) | SV/FixedVector.jl:74 |
| `FixedVector{N}(a::AbstractVector)`, `FixedVector{N,T}(x::Tuple)` | wrap, or build a `Vector` and fill it | SV/FixedVector.jl:22-41 |
| `convert(Values{N,T}, sa::TupleVector)` | `SA(Tuple(sa))` | SV/convert.jl:13-15 |
| `convert(Values, CartesianIndex)` | `Values(I.I)` | SV/Values.jl:96-100 |
| `Tuple(v)` | `v.v` for Values/Variables, `unroll_tuple` in general | SV/Values.jl:75, SV/Variables.jl:49, SV/convert.jl:22 |
| `Vector(tv::FixedVector)` | copies; `convert(Vector, FixedVector{…,Vector})` returns the **underlying** array | SV/FixedVector.jl:48-62 |
| `AbstractVector{T}(sa)` | identity if same T, else `similar_type(...)(sa)` | SV/convert.jl:18-19 |
| `zeros(Values{N})`, `ones(Values{N})` | default to **Float64** | SV/Values.jl:92-93 |
| `zeros(SA)`, `ones(SA)`, `zero(a)` | tuple of `zero(T)`/`one(T)`. **When `T==Any` the values are Float64 but the container stays `Values{N,Any}`** (oracle: `zeros(Values{3,Any}) == Any[0.0,0.0,0.0]`). | SV/arraymath.jl:5-32 |
| `fill(val, SA)` | N copies of `val`, **converted to SA's T** (`fill(7, Values{3})` gives `Values{3,Int}`) | SV/arraymath.jl:34-42 |
| `rand`, `randn`, `randexp`, `rand(range, SA)`, and the `!` in-place forms | per-element RNG draws | SV/arraymath.jl:48-148 |
| `similar(v)`, `similar(SA)` | **uninitialized `Variables{N,T}`** (mutable) | SV/abstractvector.jl:48-61 |
| `copy(a)` | `typeof(a)(Tuple(a))`. `FixedVector` copies its array. | SV/abstractvector.jl:82-83 |
| `float(Values{…})`, `real(Values{…})` (type forms) | **broken** (parameter-order bug: `TupleVector{T,_N}` binds N as T) | SV/convert.jl:55-56 |

#### 2.2.3 Size, axes, indexing

| Call | Semantics | Line |
|---|---|---|
| `length(v)`, `length(SA)`, `lastindex(v)` | `N` | SV/StaticVectors.jl:40-42 |
| `size(v)`, `size(SA)` | `(N,)` | :43-44 |
| `size(v,d)` | `d > 1 ? 1 : N` | :45-46 |
| `axes(v)` | `(SOneTo(N),)` | SV/abstractvector.jl:5-8 |
| `IndexStyle` | `IndexLinear()` | :16 |
| `v[i::Int]` | for Values: `v.v[i]`. **BoundsError message is Tuple-flavored**: `"attempt to access Tuple{Int64, Int64, Int64} at index [4]"`. | SV/Values.jl:74 |
| `v[i]` on Variables | unsafe pointer load for isbits T, else `v.v[i]` | SV/Variables.jl:28-35 |
| `v[i] = x` on Variables | isbits T: pointer store of `convert(T,x)` (an `InexactError` when lossy). Non-isbits: `error("setindex!() with non-isbitstype eltype is not supported by TupleVectors. Consider using FixedVector.")`. | SV/Variables.jl:36-47 |
| `v[i]`, `v[i] = x` on FixedVector | forwards to the wrapped array | SV/FixedVector.jl:64-65 |
| `v[:]` | a new vector of the same `similar_type`. For Values it is `===` the original (oracle). | SV/indexing.jl:78-88 |
| `v[idx::TupleVector{M,Int}]` | gather into a static result of length M: `Values(1,2,3)[Values(3,1,1,2)] == Values(3,1,1,2)` | SV/indexing.jl:90-100, 193-195, 206-214 |
| `v[[1,2,3]]` (dynamic `Vector` index) | a plain `Vector` (size unknown statically) | Base fallback |
| `v[SOneTo(2)]` | **broken** (MethodError, oracle) | SV/indexing.jl:39 |
| `v[:] = x` | fill with a scalar, or copy elementwise from a vector (checks length) | SV/indexing.jl:102-135 |
| `v[idx::TupleVector] = vec` | scatter. With a **scalar** RHS it is **broken** (undefined `s`, SV/indexing.jl:146). | SV/indexing.jl:137-170 |
| `view(v::Values, i)` | `getindex` (no SubArray) | SV/abstractvector.jl:119-121 |
| `view(::Variables, idx)` | **broken** (new_out_size signature) | SV/Variables.jl:60-66 |
| `view(::FixedVector, idx)` | `FixedVector` over a view | SV/FixedVector.jl:110-115 |
| `strides` | Variables: `(1,)`; FixedVector: forwards | SV/abstractvector.jl:13-14 |

#### 2.2.4 Arithmetic (SV/linalg.jl)

| Call | Semantics | Result container | Line |
|---|---|---|---|
| `-a` | `map(-, a)` | like `a` | :9-10 |
| `a + b`, `a - b` (TupleVector/AbstractVector in any order) | `map(+,a,b)` with runtime length check (`same_size`). For non-`Number` elements it uses `∑`, the symbolic hook. | `similar_type` of the **first** argument (Vector first gives `Values`) | :14-28 |
| `s::Number * a` | `map(c -> s*c, a)`. **Left multiplication; order is preserved.** This matters for non-commutative `T`, e.g. tensor entries. | like `a` | :31 |
| `a * s::Number` | `map(c -> c*s, a)` | | :32 |
| `s * a`, `a * s` with non-Number elements or s | `broadcast(∏, s, a)` | | :34-37 |
| `x::Expr\|Symbol * a` | `broadcast(∏, Ref(x), a)` | | :39-43 |
| `a / s` | `broadcast(/, a, s)`: **true division** per element | | :45, 48, 50 |
| `s \ a` | `broadcast(\, s, a)` | | :46, 49, 51 |
| `muladd(s,a,b)`, `muladd(a,s,b)` | elementwise `muladd`, which may fuse to FMA | | :54-55 |
| `a * b` (two TupleVectors) | **ambiguous, throws** | | |
| `a' * b` | **ambiguous, throws** | | |

#### 2.2.5 Map, reduce, scan (SV/mapreduce.jl)

| Call | Semantics | Line |
|---|---|---|
| `map(f, a::TupleVector, as...)`, `map(f, a1::AbstractArray, a2::TupleVector, as...)` | unrolled `f(a1[i], a2[i], …)`. Runtime `same_size` check. Result is `similar_type(typeof(first arg), eltype(elements), Val(N))`, so `map(+, Variables, Values)` gives Variables and `map(+, Values, Variables)` gives Values. **N==0 is broken** (undefined `first_staticarray`, :66). | :34-82 |
| `map!(f, dest, a...)` | in-place | :84-107 |
| `mapreduce(f, op, a, b...; dims=:, init)` | left fold `op(op(g1,g2),g3)…`, where the first element is `Base.reduce_first(op, f(a1))` (identity for `+ * max min`; `Bool` becomes `Int` under `+`). With `init`: `op(init, f(a1))`. Empty input with no init: `Base.mapreduce_empty(f,op,T)` (`0` for `+`, `1` for `*`, error for max/min). With several inputs: `ArgumentError("reducing over an empty collection is not allowed")`. | :113-146 |
| `mapreduce(...; dims=1)` | 1-element vector | :148-181 |
| `reduce(op, a; init)`, `foldl`, `mapfoldl` | same fold. Oracle: `foldl(-, Values(1,2,3)) == -4`, and with `init=10` it is `4`. | :187-217 |
| `reduce(vcat, A)`, `reduce(hcat, A)` | concatenation | :191-199 |
| `iszero(a)` | `reduce((x,y)->x && iszero(y), a, init=true)` | :240 |
| `sum(a)`, `sum(f,a)`, `prod(a)`, `prod(f,a)` | fold with `+` / `*`. Empty: `0` / `1`. **No widening for `+`**: `sum(Values(Int8(100),Int8(100))) == Int8(-56)`. | :242-248 |
| `count(a::TupleVector{N,Bool})`, `count(f,a)` | | :250-251 |
| `all(a)`, `any(a)` | `reduce(&, …; init=true)` / `reduce(\|, …; init=false)`: non-short-circuit | :253-257 |
| `in(x,a)` | `mapreduce(==(x), \|, a; init=false)` | :259 |
| `minimum(a)`, `maximum(a)` | fold with Julia `min`/`max`: **NaN-propagating, `-0.0 < 0.0`**. Oracle: `maximum(Values(0.0,-0.0)) == 0.0`, `minimum(Values(0.0,-0.0)) == -0.0`, `maximum(Values(1.0,NaN,3.0))` is NaN. | :269, 272 |
| `minimum(f,a)`, `maximum(f,a)` | **broken** (min passes the type `Val{N}`; max references an undefined `N`) | :270, 273 |
| `diff(a)` (`LinearAlgebra.diff`) | `_diff(Val(N), a, Val(1))`: `Snew = N-1`, `out[i] = a[i+1]-a[i]`. N==1 gives `Values{0,Union{}}`. **N==0 errors.** | :276-294 |
| `_diff(sz::Val, a, D::Int)` | forwards `D` as `Val(D)` | :278-280 |
| `accumulate(op, a; init)` | left scan; `rf(x,y) = x isa _InitialValue ? reduce_first(op,y) : op(x,y)`. `accumulate(-, Values(1,2,3)) == [1,-1,-4]`. | :300-335 |
| `cumsum`, `cumprod` | `accumulate(Base.add_sum)` / `accumulate(Base.mul_prod)`. **`add_sum` widens small ints**, unlike `sum`. | :337-338 |

#### 2.2.6 Linear algebra (SV/linalg.jl)

| Call | Semantics | Line |
|---|---|---|
| `dot(a,b)` (`LinearAlgebra.dot`) | `∑(dot(a[1],b[1]), dot(a[2],b[2]), …)` for `0 < N < 4096`. `∑ = Base.+` over varargs, which is a **left fold**. The per-element `dot` **conjugates the left argument**. Oracle: `dot(Values(1+1im,2), Values(1im,3)) == conj(1+i)·i + 2·3 == 7+1im`. N==0: `dot(zero(eltype a), zero(eltype b))`. N ≥ 4096: `@simd` loop (reassociable). | :59-84 |
| `bilinear_vecdot(a,b)` | the same with `*`, so no conjugation. Oracle: `5+1im`. | :60 |
| `norm(a)` | `sqrt(norm_sqr(a[1]) + norm_sqr(a[2]) + …)` (left-assoc). `norm_sqr(x) = abs2(x)` for numbers, recursive for nested. **No scaling**: `norm(Values(1e200,1e200)) == Inf`, whereas `norm([1e200,1e200]) == 1.414e200` for a Base Vector. `Int` input gives `Float64`. **N==0 is broken.** | :96-109 |
| `LinearAlgebra.norm_sqr(a)` | **broken** (unqualified `norm` in `_init_zero`) | :88-94 |
| `norm(a, p)` | `p==Inf`: `mapreduce(norm, max, a)`. `p==1`: `Σ norm(a_i)` (left-assoc). `p==2`: `norm(a)`. `p==0`: **broken**. Otherwise `(Σ norm(a_i)^p) ^ inv(p)`. Element norms are `LinearAlgebra.norm(x::Number) = abs(float(x))`. Oracle: `norm(Values(1,-2,3),3) == 3.3019272488946263 == 36.0^(1/3)`. | :116-144 |
| `normalize(a)`, `normalize(a,p)` | **`inv(norm(a)) * a`, multiplying by the reciprocal, not dividing**. Oracle: `normalize(Values(3.0,4.0)) == [0.6000000000000001, 0.8]`. | :146-147, 152-153 |
| `normalize!(a)`, `normalize!(a,p)` | `a .*= inv(norm(a))` | :149-150, 155-156 |
| `isapprox(a,b)` | Base `AbstractArray` fallback, using the norm above | Base |

#### 2.2.7 Structure operations (SV/abstractvector.jl, SV/StaticVectors.jl)

| Call | Semantics | Line |
|---|---|---|
| `reverse(v::Values)` | `(v[N],…,v[1])` | :85-89 |
| `vcat(a,b)`, `vcat(a,b,c...)` | `Values{Na+Nb, promote_type(Ta,Tb)}` whose container follows **`a`** (`vcat(Variables, Values)` gives Variables). The n-ary form is `vcat(vcat(a,b), vcat(c...))`. | :93-107 |
| `Base.rest(a, i)` | **broken**: `a, b... = v` throws BoundsError (oracle) | :109-115 |
| `countvalues(a::Int, b::Int)` (also pirated as `Base.count(a::Int,b::Int)`) | `Values{max(0,b-a+1),Int}(a:b...)`. `countvalues(3,1) == Int64[]`, `countvalues(-2,2) == [-2,-1,0,1,2]`. | SV/StaticVectors.jl:72, 79 |
| `evenvalues(a::Int, b::Int)`, alias `evens` | `Values{((b-a)÷2)+1, Int}(a:2:b...)` with **truncating `÷`**. Valid for `b ≥ a` (`evens(0,5)==[0,2,4]`, `evens(1,6)==[1,3,5]`) and for `b ∈ {a-2, a-3}` (empty). **Errors** for `b == a-1` (N=1 but the range is empty: MethodError) and for `b ≤ a-4` (N<0: DimensionMismatch). | :86, 93 |

#### 2.2.8 Broadcasting (SV/broadcast.jl)

- `BroadcastStyle(::Type{<:TupleVector{N}}) = TupleVectorStyle{N}()`, also for Transpose/Adjoint wrappers (:10-14).
- Mixing with `DefaultArrayStyle{M}` (M ≥ 1) gives `DefaultArrayStyle` (:16-17), so `Values .+ Vector` **returns a `Vector`**. `Values + Vector` (non-broadcast) returns `Values`.
- Mixing with a 0-dim style (scalars, `Ref`) keeps `TupleVectorStyle` (:18-19).
- `copy(bc)`: flatten, `argsizes = (length or 0 for scalars)`, `newsize = max(argsizes)` (:21-26, 53-80).
- Axis compatibility is checked earlier by Base `_bcs1`: `Values(1,2,3) .+ Values(1,2)` gives `DimensionMismatch("arrays could not be broadcast to a common size")`; a length-1 vector broadcasts (:42-44).
- Element j of an arg with `oldsize==1` uses index 1; scalars use `scalar_getindex` (`Ref` is dereferenced) (:59-67, 82-83).
- Result: `similar_type(first static arg, eltype(elements), Val(newsize))` (:85-111). In-place `copyto!` is at :28-39 and :117-134.
- Outer-product broadcast (`Values .* Values'`) is **broken** (BoundsError).

#### 2.2.9 Misc helpers (not exported, used internally or downstream)

- `similar_type(v)`, `similar_type(v, T)`, `similar_type(v, T, Val(N))`: result container family. Values maps to Values, Variables to Variables, FixedVector to FixedVector, any other `AbstractArray` to Values (SV/abstractvector.jl:18-46).
- `unroll_tuple(a, Val(N))` (SV/convert.jl:46-52)
- `convert_ntuple` and `promote_tuple_eltype` (SV/util.jl)
- `same_size` (SV/traits.jl:19-28), which throws `DimensionMismatch("Sizes $(map(_size, as)) of input arrays do not match")`
- `length_val` (SV/convert.jl:40-44)
- the `∏ ∑ - / inv` hooks (SV/StaticVectors.jl:7-14)

---

## 3. Data representations

### 3.1 AbstractTensors

| Parameter | Kind | Meaning | Compile-time or runtime |
|---|---|---|---|
| `V` in `TensorAlgebra{V,T}` | **value in the type domain** (isbits). One of: a DirectSum `Submanifold{V,n,bits}` instance (ordinary elements, e.g. `⟨111⟩::Submanifold{3,3,0x07}`), a `Signature`/`DiagonalForm`/`MetricTensor` (a TensorBundle) or, **for a TensorBundle itself, an `Int n`** (`TensorBundle{n,…} <: Manifold{n,Int}`). This is why `mdims(M::Int)=M` and `tdims(M::Int)=1<<M` exist. | Compile-time. Every method specializes on it. |
| `T` | a Julia type | scalar field of the coefficients | compile-time |
| `G` in `TensorGraded{V,G,T}` | `Int` | grade `0 ≤ G ≤ n` | compile-time |
| `Op` in `Postfix{Op}` | `Symbol` | postfix op tag | compile-time (singleton) |

There are no fields: every type in AT is abstract. Invariants and conventions:
- A `Manifold` is its own `Manifold` (AT:140). DirectSum's `Submanifold` is simultaneously a basis blade and a (sub)space: `Submanifold{V,n,bits} <: TensorTerm{V,n,Int}`, and the space `V` itself is the top blade (DirectSum `DirectSum.jl:252`). Oracle: `Manifold(v1) == ⟨111⟩`, `V(I) == v₁₂₃`, `V(2I) == 2v₁₂₃`.
- `UniformScaling` (`λ*I`) carries no dimension. It becomes concrete only via `V(J)`, the λ-scaled unit pseudoscalar of V.
- `zero(V)` gives DirectSum `Zero{V}`, printed as `𝟎`. `one(V)` gives the grade-0 unit, printed as `v`.

### 3.2 StaticVectors

| Type | Storage | Mutability | Julia runtime layout |
|---|---|---|---|
| `Values{N,T}` | `v::NTuple{N,T}` | immutable | **inline**; isbits when T is isbits, so it lives in registers or on the stack. Zero heap allocation. `===` compares bitwise. |
| `Variables{N,T}` | `v::NTuple{N,T}` | mutable heap object | one heap box holding the inline tuple. `setindex!` does a raw pointer store (isbits T only). |
| `FixedVector{N,T,TData}` | `v::TData` (usually `Vector{T}`) | mutable through the wrapped array | heap `Vector`, aliased, not copied |
| `SOneTo{n}` | none | | singleton |

Invariants:
- `length(v.v) == N` (by construction).
- `FixedVector` requires `length(data) == N` and 1-based axes.
- Index ordering: dense linear `1..N`. There is no other layout.
- Element types are homogeneous (`T`) but may be abstract (`Any`, `Union`), in which case Julia boxes them.
- Equality `==` is elementwise with AbstractArray semantics: `Values(1,2)==Values(1.0,2.0)` holds, and lengths may differ (then `false`). `isequal`/`hash` match `Vector`: `hash(Values(1,2,3)) == hash([1,2,3])`. `isless`/`<` is lexicographic (AbstractVector fallback).
- Type-level: `N ≥ 0` is a `Int` type parameter. `Values{-1,…}` can be requested and fails at construction (evenvalues bug).

---

## 4. Algorithms

### 4.1 StaticVectors: exact evaluation order

Order matters for bitwise Float goldens.

```
-- all folds are LEFT folds in index order 1..N
sum(a)        = ((a1 + a2) + a3) + … ;   N==0 → zero(T)
prod(a)       = ((a1 * a2) * a3) * … ;   N==0 → one(T)
maximum(a)    = max(max(a1,a2),a3)…      -- Julia max: NaN-propagating; max(-0.0,0.0)=0.0
dot(a,b)      = ((conj(a1)*b1 + conj(a2)*b2) + conj(a3)*b3) + …   -- Base.+ vararg = left fold
bilinear(a,b) = ((a1*b1 + a2*b2) + a3*b3) + …
norm(a)       = sqrt(((abs2(a1) + abs2(a2)) + abs2(a3)) + …)       -- abs2(x)=x*x, complex: re²+im²
norm(a,1)     = ((|a1| + |a2|) + |a3|) + …                        -- |x| = abs(float(x))
norm(a,Inf)   = max(max(|a1|,|a2|),|a3|)…
norm(a,p)     = (((|a1|^p + |a2|^p) + …)) ^ (1/p)                  -- 1/p computed as inv(p)
normalize(a)  = map(x -> inv(norm(a)) * x, a)                      -- NOT x / norm(a)
a / s         = map(x -> x / s, a)                                  -- true division
s * a         = map(x -> s * x, a);   a * s = map(x -> x * s, a)
cumsum(a)[k]  = (…((a1 + a2) + a3) … + ak)
accumulate(op,a)[1] = a1;  [k] = op([k-1], ak)
diff(a)[i]    = a[i+1] - a[i],  i = 1..N-1
reverse(a)[i] = a[N+1-i]
vcat(a,b)     = (a1..aNa, b1..bNb) with eltype promote_type(Ta,Tb)
countvalues(a,b) = [a, a+1, …, b]   (length max(0, b-a+1))
evenvalues(a,b)  = [a, a+2, …, ≤ b] (Julia length ((b-a)÷2)+1 with truncation; see bug list)
```

Constructor pseudocode (`Values(x...)`):
```
T = foldl(promote_type, typeof.(x); init = Union{})   # promote_tuple_eltype
return Values{length(x), T}(map(xi -> convert(T, xi), x))
```

Broadcast pseudocode:
```
args = flatten(bc)
sizes = [a isa AbstractArray||Tuple ? length(a) : 0 for a in args]
axes compatibility checked by Base: each length ∈ {1, L} else DimensionMismatch
L = maximum(sizes)
if any arg is a non-static AbstractArray with ndims ≥ 1 → fall back to Base (result Vector)
out[j] = f( (sizes[k]==0 ? deref(args[k]) : sizes[k]==1 ? args[k][1] : args[k][j]) for k )
container = similar_type(first TupleVector arg, eltype(out), Val(L))
```

### 4.2 AbstractTensors algorithms

Interop:
```
interop(op, a, b):
  if Manifold(a) == Manifold(b): return op(a, b)       # resolved by dispatch, same V
  M = Manifold(a) ∪ Manifold(b)                        # DirectSum union
  return op(M(a), M(b))                                # M(x): embedding morphism
interform(a, b): same, returns M(a)(M(b))
```

UniformScaling lift, for op in the UniformScaling list:
```
op(a::TA, J::UniformScaling) = op(a, Manifold(a)(J))     # V(λI) = λ · pseudoscalar(V)
op(J::UniformScaling, b::TA) = op(Manifold(b)(J), b)
```

Scalar complement:
```
!x (x Real/Complex, non-Bool) = x·I   (UniformScaling)
!(λI) = λ   (Bool λ: true→1, false→0)
```

Transcendental kernel. **One** generic definition is parameterized by `(mul, logm, extra args)`:
```
generic(mul, logm, g...):
  i = V(I)                       # unit pseudoscalar
  cos(t)   = cosh(mul(i,t), g...)
  sin(t)   = div(sinh(mul(i,t), g...), i, g...)      # div(a,b,g...) = mul(a, inv(b,g...), g...)
  tan(t)   = div(sin(t), cos(t))   … (see table §2.1.9)
  asinh(t) = logm(t + sqrt(1 + mul(t,t)))
  ...
  sinc(t)  = iszero(t) ? one(V) : (x = π*t; div(sin(x), x))
  cosc(t)  = iszero(t) ? zero(V) : (x = π*t; div(cos(x), t) - div(sin(x), mul(x,t)))
plain  family = generic(⟑, log)
metric family = generic((a,b)->wedgedot_metric(a,b,g), (x)->log_metric(x,g), g)
```

**Semantic consequence (important).** `cos(t) = cosh(I⟑t)` equals the true cosine only when `(I⟑t)² = -(t²)`. For a **scalar** argument this requires `I² = -1`. In Euclidean signatures `I² = (-1)^{n(n-1)/2}`, which is `+1` for n ≡ 0,1 (mod 4). Oracle over Grassmann, `cos(1.0v)` on a grade-0 Single:

| n | I*I | cos(1v) | sin(1v) |
|---|---|---|---|
| 1 | `1v` | 1.543080634803725 (= cosh 1) | 1.175201193643034 (= sinh 1) |
| 2 | `-1v` | 0.5403023058795628 | 0.8414709848086585 |
| 3 | `-1v` | 0.5403023058795628 | 0.8414709848086585 |
| 4 | `1v` | 1.543080634803725 | 1.175201193643034 |
| 5 | `1v` | 1.543080634803725 | 1.175201193643034 |

In 3D: `cos(1.0v1) = 0.5403023058795628v` (true cos, because `(I v1)² = v23² = -1`) and `cos(1.0v12) = 1.543080634803725v` (cosh, because `v12² = -1` makes `cos(i·1) = cosh 1`). Also note Grassmann's series `cosh` has ~1e-11 absolute error (true `cos(1)=0.5403023058681398`, `cosh(1)=1.5430806348152437`).

Norm family:
```
abs2(t::Graded) = contraction(t,t);   abs2(t::Mixed) = let a=(~t)⟑t in isscalar(a) ? scalar(a) : a
abs(t)      = sqrt(abs2(t))
coabs(t)    = complementleft(abs(complementright(t)))
geomabs(t)  = abs(t) + coabs(t)
unit(t)     = t / abs(t)            # right division by a tensor → t ⟑ inv(abs(t)) for tensors
counit(t)   = t / value(coabs(t))   # divide by coefficient
unitnorm(t) = t / norm(geomabs(t))  # divide by Float
isapprox: see §2.1.8
iszero(t)   = norm(value(t)) ≈ 0    (≡ exactly zero for finite)
isone(t)    = (norm(t) ≈ value(scalar(t))) && (value(scalar(t)) ≈ 1)
```

Isapprox scalar rule (Julia Base):
```
isapprox(x::Number, y::Number; atol=0, rtol = atol>0 ? 0 : rtoldefault)
  = x == y || (isfinite(x) && isfinite(y) && |x-y| ≤ max(atol, rtol*max(|x|,|y|)))
rtoldefault: Float64 → 2^-26, Float32 → sqrt(eps(Float32)), Int/Rational → 0
```

Contraction variants, same V:
```
a ⨽ b = a > b = a | b = a ⋅ b = contraction(a,b)
a ⨼ b = a < b = contraction(b,a)
a << b = contraction(b, ~a);   a >> b = contraction(~a, b)
a ∗ b = (~a) ⟑ b;   a ⊛ b = scalar(contraction(a,b))
cross(a,b) = hodge(a ∧ b)
```

Postfix: `x⁻¹ = inv x`, `xǂ = conj x`, `x₊ = even x`, `x₋ = odd x`, `xˣ = involute x`.

Lattice identities: `∧()=1`, `∨()=I`, `∧(x)=x`, `∨(x)=x`, `Bool ∧ Bool = &&`, `Bool ∨ Bool = ||`.

Dims: `mdims`, `tdims(n) = 2^n`, `gdims(n,g) = binomial(n,g)`, which is 0 outside `0..n`. Identity: `Σ_{g=0}^{n} gdims(n,g) = tdims(n)`.

---

## 5. Display and printing

AbstractTensors defines **no** `show` methods. StaticVectors only defines `show(io, ::SOneTo{n}) = print(io, "SOneTo(", n, ")")` (SV/SOneTo.jl:56). Everything else is Julia's `AbstractVector` printing. Exact strings from the oracle (Julia 1.13):

**Compact form** (`print`/`show`/`repr`, also used for nested elements): `[e1, e2, …]`, separated by `", "`, where each element uses its own compact `show`.
- An **eltype prefix** is added when the element type is not the "default" for its literals. The prefix is omitted for `Int64`, `Float64`, `String`, `Symbol`. It is added for everything else:
  - `Bool[1, 0]` (Bools print as `1`/`0`)
  - `Float32[1.0, 2.0]`, `Int32[1, 2]`, `UInt8[0x03, 0x04]`, `Rational{Int64}[1//2, 3//4]`
  - `ComplexF64[1.0 + 2.0im, -0.0 - 1.5im]`, `Complex{Int64}[1 + 2im, 3 + 0im]`
  - `Any[1, "b"]`, `BigInt[1180591620717411303424, 1]`
  - nested: `Values{2, Int64}[[1, 2], [3, 4]]`
- Empty: `Int64[]`, `Float64[]` (text/plain prints the same).
- Float64 elements print with Julia's shortest round-trip repr: `1.0`, `0.30000000000000004`, `0.3333333333333333`, `1.0e10`, `1.0e-5`, `1.0e20`, `-1.0e-20`, `NaN`, `Inf`, `-Inf`, `0.6000000000000001`.
  - Exponent form is used when `|x| < 1e-4` or `|x| ≥ 1e6`. Oracle: `100000.0`, `123456.0` and `0.0001` stay plain; `1.0e6`, `1.234567e6`, `1.0e-5`, `9.007199254740992e15` and `5.0e-324` switch.
  - The exponent is written as `e6`/`e-5`: no `+`, no zero padding.
  - Compact mode (`:compact=>true`, used inside Grassmann multivector printing) rounds to 6 significant digits: `1.23457e6`, `9.0072e15`, `0.285714`.
- Strings are quoted (`["a", "bc"]`); symbols print as `[:x, :y]`.

**text/plain** (REPL display):
```
3-element Values{3, Int64} with indices SOneTo(3):
 1
 2
 3
```
- Header: `"$N-element $(typeof(v)) with indices SOneTo($N):"`, with type printing `Values{3, Int64}`, `Variables{2, Float64}`, `FixedVector{2, Float64, Vector{Float64}}`, `Values{2, Values{2, Float64}}`.
- Each element is on its own line prefixed by one space, and **aligned**: the integer part is right-justified and the fractional part left-justified to a common column (Base `alignment`). Examples with `⏎` for newlines:
  - `Values(-1.5, 2.25, 100.0)` → `…SOneTo(3):⏎  -1.5⏎   2.25⏎ 100.0`
  - `Values(1.5,-2.0)` → `⏎  1.5⏎ -2.0`
  - `Values(NaN,Inf,-Inf)` → `⏎ NaN⏎  Inf⏎ -Inf`
  - `ComplexF64[1.0+2.0im, -0.0-1.5im]` → `⏎  1.0 + 2.0im⏎ -0.0 - 1.5im`
- Long vectors print in full for N=30. Vertical elision (`⋮`) appears only past the terminal height; ignore it.

Recommended Lean printing:
- `ToString`/`Repr` for `Values n α` produce the compact form `[e1, e2, …]`. The eltype prefix is only needed for exact string goldens of non-Int/Float element types.
- A Julia-compatible Float64 printer (shortest round-trip, Ryu-style, with Julia's exponent rules) is a **cross-cutting requirement**. Grassmann's multivector display also uses Julia float printing, including `:compact=>true` (6 significant digits, e.g. `0.285714`). Put it in one shared module (§8.7).

---

## 6. Examples and expected outputs (golden candidates)

Verbatim from README/tests/docstrings, with results confirmed by the oracle.

### 6.1 StaticVectors README quick start (SVREADME:24-46, ATREADME:115-137)

```julia
v1 = Values(1, 2, 3)
v1.v === (1, 2, 3)                  # true
v2 = Values{3,Float64}(1, 2, 3)     # [1.0, 2.0, 3.0] :: Values{3,Float64}
v5 = zeros(Values{3})               # [0.0, 0.0, 0.0] :: Values{3,Float64}
v7 = Values{3}([1, 2, 3])           # [1, 2, 3] :: Values{3,Int64}
size(v1) == (3,)                    # true
size(typeof(v1)) == (3,)            # true
v7 = v1 + v2                        # [2.0, 4.0, 6.0] :: Values{3,Float64}
v8 = sin.(v2)                       # [0.8414709848078965, 0.9092974268256817, 0.1411200080598672] :: Values{3,Float64}
v1[1] === 1                         # true
v1[:] === v1                        # true
typeof(v1[[1,2,3]]) <: Vector       # true
```

### 6.2 AbstractTensors test suite (ATtest:1-46; run under the oracle, all pass)

```julia
struct SpecialTensor{V} <: TensorAlgebra{V,Float64} end
a,b = SpecialTensor{ℝ}(), SpecialTensor{ℝ'}()        # ℝ = ⟨+⟩, ℝ' = ⟨-⟩'
ndims(+(a)) == ndims(b)                               # 0 == 0
op(s::SpecialTensor{V},::SpecialTensor{V}) where V = s
op(a::TensorAlgebra{V},b::TensorAlgebra{W}) where {V,W} = interop(op,a,b)
(W::Signature)(s::SpecialTensor{V}) where V = SpecialTensor{W}()
Manifold(op(a,b)) == ℝ⊕ℝ'          # ⟨+-⟩*
Manifold(interop(op,a,b)) == ℝ⊕ℝ'
Manifold(op(a,a)) == ℝ
AbstractTensors.plus(s::SpecialTensor{V},::SpecialTensor{V}) where V = s
Manifold(+(a,b)) == ℝ⊕ℝ'  ;  Manifold(+(a,a)) == ℝ
op(a::TensorAlgebra{V},b::UniformScaling) where V = op(a,V(b))
(W::Signature)(s::UniformScaling) = SpecialTensor{W}()
Manifold(op(a,I)) == ℝ ; Manifold(op(I,a)) == ℝ ; Manifold(a+I) == ℝ ; Manifold(I+a) == ℝ
(a::SpecialTensor{V})(b::SpecialTensor{V}) where V = a
(a::SpecialTensor{W})(b::SpecialTensor{V}) where {V,W} = interform(a,b)
Manifold(b(a)) == ℝ⊕ℝ' ; Manifold(interform(a,a)) == ℝ
!I == 1
(2)⁻¹ == 1/2              # 0.5
(im)ǂ == -im              # 0 - 1im
(sqrt(2))ˣ == sqrt(2)
(sqrt(2))₊ == sqrt(2)
(sqrt(2))₋ == 0           # returns Int 0
```

Extra oracle facts from the same probe:
- `mdims(a)=1`, `tdims(a)=2`, `parent(a)=⟨+⟩`, `valuetype(a)=Float64`, `rank(typeof(ℝ))=1`.
- `a - b`, `a == b`, `a*b`, `isapprox(a,a)` give StackOverflowError (no concrete impl).
- `a + 1` errors: "promotion of types … failed to change any arguments".

### 6.3 Docstring examples (AT:487-498, 512-523)

```julia
julia> @co myfun(x)            # comyfun (generic function with 1 method)
       # comyfun(x) = complementleft(myfun(complementright(x)))
julia> @co myproduct(a,b)      # comyproduct(a,b) = complementleft(myproduct(!a,!b))
julia> @pseudo myfun(x)        # pseudomyfun(x) = complementleft(myfun(complementright(x)))
```

### 6.4 Oracle-harvested StaticVectors goldens (Julia 1.13, SV 1.0.9)

`repr(r) :: typeof(r)` pairs from `probe/sv1.jl`, `probe/sv2.jl`:

```
zeros(Values{3,Int})          [0, 0, 0] :: Values{3,Int64}
zeros(Variables{3})           [0.0, 0.0, 0.0] :: Variables{3,Float64}
fill(7, Values{3})            [7, 7, 7] :: Values{3,Int64}
Values{2}([1,2,3])            DimensionMismatch: expected input vector of length 2, got length 3
size(v1,2)                    1
axes(v1)                      (SOneTo(3),)
v1 - v2                       [0.0, 0.0, 0.0] :: Values{3,Float64}
-v1                           [-1, -2, -3]
v1 .+ 1                       [2, 3, 4] :: Values{3,Int64}
v1 .* v2                      [1.0, 4.0, 9.0] :: Values{3,Float64}
v1 .+ [1,2,3]                 [2, 4, 6] :: Vector{Int64}
v1 + [1,2,3]                  [2, 4, 6] :: Values{3,Int64}
[1,2,3] + v1                  [2, 4, 6] :: Values{3,Int64}
v1[Values(3,1)]               [3, 1] :: Values{2,Int64}
v1[4]                         BoundsError: attempt to access Tuple{Int64, Int64, Int64} at index [4]
v1 / 2                        [0.5, 1.0, 1.5] :: Values{3,Float64}
2 \ v1                        [0.5, 1.0, 1.5]
v1 * 2.5                      [2.5, 5.0, 7.5]
muladd(2, v1, v1)             [3, 6, 9]
countvalues(1,4)              [1, 2, 3, 4] :: Values{4,Int64}
countvalues(3,1)              Int64[] :: Values{0,Int64}
countvalues(3,3)              [3]
evenvalues(0,5)               [0, 2, 4]
evenvalues(1,6)               [1, 3, 5]
evenvalues(0,6)               [0, 2, 4, 6]
evenvalues(2,2)               [2]
evenvalues(3,2)               MethodError (bug)
evenvalues(4,2)               Int64[] :: Values{0,Int64}
evenvalues(6,2)               DimensionMismatch (bug)
evens(2,7)                    [2, 4, 6]
evenvalues(-3,3)              [-3, -1, 1, 3]
_diff(Val(3), Values(1,4,9), Val(1))   [3, 5]
diff(Values(1,4,9))           [3, 5]
diff(Values(1))               Union{}[] :: Values{0,Union{}}
reverse(v1)                   [3, 2, 1]
vcat(v1, v2)                  [1.0, 2.0, 3.0, 1.0, 2.0, 3.0] :: Values{6,Float64}
vcat(v1, Values(4), Values(5,6))  [1, 2, 3, 4, 5, 6]
sum(abs2, v1)                 14
prod(Values{0,Int}())         1
sum(Values{0,Int}())          0
norm(Values(3,4))             5.0
norm(Values(1,-2,3),1)        6.0
norm(Values(1,-2,3),Inf)      3.0
norm(Values(1,-2,3),3)        3.3019272488946263
norm(Values(1,-2,3),2)        3.7416573867739413
norm(Values(3.0,4.0),2.5)     4.688140842343588
norm(Values(1+2im, 3))        3.7416573867739413
norm(Values(1e200,1e200))     Inf
norm(Values(1e-200,1e-200))   0.0
normalize(Values(3.0,4.0))    [0.6000000000000001, 0.8]
normalize(Values(3.0,4.0),1)  [0.42857142857142855, 0.5714285714285714]
dot(v1, v2)                   14.0
dot(Values(1+1im,2), Values(1im,3))            7 + 1im
bilinear_vecdot(Values(1+1im,2), Values(1im,3)) 5 + 1im
dot(Values{0,Int}(), Values{0,Int}())          0
dot(Values(Values(1,2),Values(3,4)), same)     30
cumsum(v1) [1, 3, 6] ; cumprod(v1) [1, 2, 6] ; accumulate(-, v1) [1, -1, -4]
iszero(Values(0,0)) true ; 2 in v1 true ; count(iseven, v1) 1
map(+, Variables(1,2), Values(3,4))   [4, 6] :: Variables{2,Int64}
map(+, Values(1,2), Variables(3,4))   [4, 6] :: Values{2,Int64}
similar(v1)                   (garbage) :: Variables{3,Int64}
similar_type(FixedVector{3,Int}) FixedVector{3, Int64, TData} where TData<:AbstractVector{Int64}
Values(1, 2.0, 3//1)          [1.0, 2.0, 3.0] :: Values{3,Float64}
Values{2}((1, 2.5))           [1.0, 2.5]
Values(1,"b")                 Any[1, "b"] :: Values{2,Any}
Values{3,Int}(2i+1 for i in 1:3)  [3, 5, 7]
Values{3}(2i+1 for i in 1:4)  error "Generator produced too many elements: Expected exactly 3 elements, but generator yields more"
Values{3}(2i+1 for i in 1:2)  error "Generator produced too few elements: Expected exactly 3 elements, but generator stopped at 3"
TV[1.0,2.0]  [1.0, 2.0] :: Values{2,Float64} ; TV_F32[1,2]  Float32[1.0, 2.0]
v1 == Values(1.0,2.0,3.0) true ; Values(1,2) == Values(1,2,3) false ; hash(v1)==hash([1,2,3]) true
Values(1,2) < Values(1,3)     true (lexicographic)
Values(1,2) .< Values(2,1)    Bool[1, 0] :: Values{2,Bool}
foldl(-, Values(1,2,3); init=10) 4 ; reduce(+, Values(1,2,3); init=10) 16
reduce(vcat, Values(Values(1,2),Values(3,4))) [1, 2, 3, 4]
2 * Values(Values(1,2),Values(3,4))  Values{2, Int64}[[2, 4], [6, 8]]
Values(1,2,3) .+ Values(1,2)  DimensionMismatch: arrays could not be broadcast to a common size
Values(1,2,3) .+ Values(10)   [11, 12, 13]
Values(1,2,3) .+ (10,20,30)   [11, 22, 33] :: Values{3,Int64}
Values(1, 2) ./ 0             [Inf, Inf] :: Values{2,Float64}
let v=Variables(1,2,3); v[Values(1,3)] = Values(7,8); v end   [7, 2, 8]
let v=Variables(3.0,4.0); normalize!(v); v end              [0.6000000000000001, 0.8]
FixedVector{2}([1,2,3])       DimensionMismatch: Dimensions 3 don't match static size 2
SOneTo{3}(1:4)                DimensionMismatch: 1:4 is inconsistent with SOneTo{3}
maximum(Values(-0.0,0.0)) 0.0 ; minimum(Values(0.0,-0.0)) -0.0 ; maximum(Values(1.0,NaN,3.0)) NaN
sum(Values(0.1,0.2,0.3))      0.6000000000000001
```

### 6.5 Oracle-harvested AbstractTensors scalar goldens (`probe/at1.jl`)

```
!I → 1 :: Int64 ; !(2I) → 2 ; !(2.5I) → 2.5 ; !2 → UniformScaling{Int64}(2) ; !2.5 → UniformScaling{Float64}(2.5)
!true → false ; !(1+2im) → UniformScaling{Complex{Int64}}(1 + 2im)
hodge(3) → UniformScaling{Int64}(3) ; complementrighthodge(2, nothing) → UniformScaling{Int64}(2)
(2)⁻¹ → 0.5 ; (im)ǂ → 0 - 1im ; (sqrt(2))ˣ → 1.4142135623730951 ; (sqrt(2))₋ → 0 :: Int64
mdims(3) → 3 ; tdims(3) → 8 ; gdims(4,2) → 6 ; gdims(4,5) → 0
wedge() → 1 ; vee() → UniformScaling{Bool}(true) ; wedge(true,false) → false ; vee(true,false) → true ; wedge(5) → 5
∑(1,2,3) → 6 ; ∏(2,3,4) → 24 ; SUB(5,3) → 2 ; AT.:-(:x) → :(-x) ; AT.:/(6,4) → 1.5 ; AT.inv(4) → 0.25 ; √(4) → 2.0
AT.norm(:x) → :x ; AT.norm(3) → 3.0 ; isnull(0) → true ; isnull(:x) → false
signbit(:x) → false ; signbit(:(-x)) → true ; signbit(:(x-y)) → true
≈(:x,:x) → true ; ≈(:x,1) → false
scalar(3) → 3 ; involute(3) → 3 ; even(3) → 3 ; odd(3) → 0 ; value([1,2]) → [1,2] ; valuetype(Float32) → Float32
unit(3.0) → 1.0 ; unit(-2) → -1.0 ; unit(3+4im) → 0.6 + 0.8im
unitize(3.0), unitnorm(3.0), cometric(2,5) → MethodError (need tensor-only methods)
wedgedot(2,3) → 6 ; contraction(2,3) → 6 ; contraction(Values(1,2),Values(3,4)) → 11
wedgedot_metric(2,3,nothing) → 6 ; metric(2,5) → 3
/(6,3,nothing) → 2.0 ; ^(2,3,nothing) → 8 ; cos(0.0,nothing) → 1.0 ; log_metric(2.0,nothing) → 0.6931471805599453
log(2.0, nothing) → MethodError ; 2 ⊗ 3 → MethodError
```

### 6.6 Oracle-harvested generic-formula goldens through Grassmann (3D Euclidean `basis"3"`)

These test the AT *formulas* using Grassmann as the concrete carrier. Use a tolerance of about 1e-9 relative, because Grassmann's series `exp`/`cosh`/`sinh` are only accurate to about 1e-11. Carriers:
- `x = 1.0 + 2.0v1 + 3.0v12` (a `Multivector`)
- `y = 0.5v2 - 1.0v3 + 2.0v123` (a `CoSpinor`)

```
contraction(x,y) = x⋅y = x|y = x⨽y = x>y   → 0.0 - 1.5v₁
x ⨼ y = x < y                              → 0.0 + 0.5v₂ + 5.0v₃ + 4.0v₂₃ + 2.0v₁₂₃
x << y                                     → 0.0 + 0.5v₂ - 7.0v₃ + 4.0v₂₃ + 2.0v₁₂₃
x >> y                                     → 0.0 + 1.5v₁
x ∗ y                                      → 0.0 - 1.5v₁ + 0.5v₂ + 5.0v₃ + 1.0v₁₂ - 2.0v₁₃ + 4.0v₂₃ + 5.0v₁₂₃
x ⊛ y                                      → 0.0v
x * y = x ⟑ y                              → 0.0 + 1.5v₁ + 0.5v₂ - 7.0v₃ + 1.0v₁₂ - 2.0v₁₃ + 4.0v₂₃ - 1.0v₁₂₃
x / y                                      → 0.0 + 0.285714v₁ + 0.0952381v₂ + 0.952381v₃ + 0.190476v₁₂ - 0.380952v₁₃ - 0.761905v₂₃ - 0.952381v₁₂₃
x \ y                                      → error "inv(1.0 + 2.0v₁ + 3.0v₁₂) is undefined"
x × y                                      → -1.0 + 2.0v₂ + 1.0v₃ - 1.0v₁₂ - 0.5v₁₃
cross(2.0v1+v2, v3)                        → 1.0v₁ - 2.0v₂ + 0.0v₃
x ∘ y                                      → 2.0 + 4.0v₁ + 5.0v₁₂ - 0.5v₁₃
!x = ⋆x = hodge(x)                         → 0.0 + 3.0v₃ + 2.0v₂₃ + 1.0v₁₂₃
(x)ǂ = conj(x) = ~x                        → 1.0 + 2.0v₁ - 3.0v₁₂
(x)₊ = even(x)                             → 1.0 + 3.0v₁₂ + 0.0v₁₃ + 0.0v₂₃
(x)₋ = odd(x)                              → 2.0v₁ + 0.0v₂ + 0.0v₃ + 0.0v₁₂₃
involute(x)                                → 1.0 - 2.0v₁ + 3.0v₁₂
abs2(x)                                    → 14.0 + 4.0v₁ + 12.0v₂   (non-scalar!)
abs(2.0v1+v2) → 2.23606797749979v ; abs2(2.0v1+v2) → 5.0v
norm(x) → 3.7416573867739413
x + I → 1.0 + 2.0v₁ + 3.0v₁₂ + 1.0v₁₂₃ ; x * I → -0.0 - 3.0v₃ + 2.0v₂₃ + 1.0v₁₂₃
x / I → 0.0 + 3.0v₃ - 2.0v₂₃ - 1.0v₁₂₃ ; I / (2.0v1) → 0.5v₂₃
2 ^ (1.0v1) → 1.25 + 0.75v₁
exp2(1.0v12) → 0.7692389013639721 + 0.6389612763136348v₁₂
exp10(0.5v12) → 0.40730731015394683 + 0.9132911666577952v₁₂
log2(2.0+0.0v12) → 1.0 + 0.0v₁₂
cos(1.0v12) → 1.543080634803725v ; sin(1.0v12) → 1.175201193643034v₁₂
tan(0.5v12) → 0.46211715724935354v₁₂ ; cot(0.5v12) → -2.1639534137885525v₁₂
sec(0.5v12) → 0.8868188839704753v ; csc(0.5v12) → -1.9190347513800643v₁₂
cos(1.0v1) → 0.5403023058795628v ; sin(1.0v1) → 0.8414709848086585v₁
cos(0.5v1) → 0.8775825618898637v ; sin(0.5v1) → 0.4794255386164159v₁ ; tan(0.5v1) → 0.5463024898580239v₁
cos(0.5v12) → 1.1276259652058704v ; sin(0.5v12) → 0.5210953054814953v₁₂
cos(0.5v123) → 1.1276259652063807v ; sin(0.5v123) → 0.5210953054937474v₁₂₃
sec(0.5v1) → 1.13949392732521v
tanh(0.5v1) → 0.46211715724935354v₁
sinc(0.5v12) → 1.4650523833327447v ; sinc(0.0v12) → v (One) ; sinc(0.25v1) → 0.900316316148285v
cosc(0.25v1) → -0.7728381398453945v₁
asinh(0.5v1) → 0.4812118250596034v₁ ; asinh(0.5v12) → -5.551115123125783e-17 + 0.5235987755982989v₁₂
atanh(0.5v1) → 0.0 + 0.5493061443340549v₁ ; atanh(0.25v12) → 0.0 + 0.24497866312686414v₁₂
acosh(2.0+0.0v12) → 1.3169578969248168 + 0.0v₁₂
asin(0.5v1) → 0.5235987755982989v₁ + 5.551115123125783e-17v₁₂₃
atan(0.5v1) → 0.4636476090008061v₁ - 0.0v₁₂₃
acoth(2.0v1) → DomainError with -3.0 ; acos(0.5v1), acot(2.0v1) → "inv(...) is undefined"
2.0 ^ (0.5v12) = exp2(0.5v12) → 0.9405421046832438 + 0.3396771251026685v₁₂
log2(exp(0.5v12)) → 6.00642469465297e-17 + 0.7213475204444817v₁₂
log10(exp(0.5v12)) → 1.808113999787413e-17 + 0.2171472409516259v₁₂
exp10(0.5v1) → 1.7392527130926088 + 1.423024947075771v₁
log(2.0, exp(1.0v12)) → 0.6931471805599453 :: Float64      ← BUG B1 (returns log(2.0))
unit(3.0v1+4.0v2) → 0.6v₁ + 0.8v₂ + 0.0v₃ ; coabs(3.0v1+4.0v2) → 5.0v₁₂₃
geomabs(3.0v1+4.0v2) → 5.0 + 5.0v₁₂₃ ; unitize(3.0v1+4.0v2) → 0.6v₁ + 0.8v₂ + 0.0v₃
unitnorm(3.0v1+4.0v2) → 0.424264v₁ + 0.565685v₂ + 0.0v₃ ; unitnorm(3.0v123) → 0.7071067811865476v₁₂₃
cotan(0.5v12) → 0.5463024898580239v₁₂ ; cosqrt(4.0v123) → 2.0v₁₂₃ ; coexp(0.5v123) → 1.6487212707001282v₁₂₃
coabs2(2.0v12) → 4.0v₁₂₃ ; cosandwich(1.0v1,1.0v12) → 1.0v₁ ; antisandwich(1.0v12,1.0v1) → 1.0v₁
(1.0v1) ⊘ (1.0v12) = sandwich → -1.0v₁ ; (1.0v12) >>> (1.0v1) → -1.0v₁
metric(1.0v1,1.0v2) → 1.4142135623730951v ; cometric(1.0v1,1.0v2) → MethodError ambiguity (bug B4)
isapprox(x, x+1e-12v1) true ; isapprox(1.0v1, 1.0v2) false ; isapprox(1.0v1, 1.0v12) false ; isapprox(0.0v1,0.0v12) true
isapprox(a, a+1e-9v1) true ; isapprox(a, a+1e-7v1) false ; with rtol=1e-6 true ; isapprox(a, a+1e-3v1; atol=1e-2) true   (a = 1.0v1+2.0v2)
iszero(1e-300v1) false ; iszero(0.0v1+0.0v2) true ; isone(1.0+1e-12v1) true ; isone(1.0+0.1v1) false ; isone(2.0+0.0v1) false
rtoldefault(1.0v1,1.0v1,0) 1.4901161193847656e-8 ; rtoldefault(v1,v1,0) 0
V(I) → v₁₂₃ ; V(2I) → 2v₁₂₃ ; Manifold(v1) → ⟨111⟩ ; mdims(v1) 3 ; tdims(v1) 8 ; gdims(v12) 3 ; rank(v12) 2
scalar(1+v1) → 1v ; vector(1+v1) → 1v₁ ; scalar(v1) → 𝟎 ; isvector(0v12) → true
```

---

## 7. Dependencies on other chakravala packages

| Package | Relationship | Symbols used |
|---|---|---|
| **StaticVectors.jl** | hard dependency of AT (`Project.toml` compat "1") | `import StaticVectors: inv, ∏, ∑, -, /` (AT:586), `Values, Variables, FixedVector, TupleVector, evens, _diff` (AT:645), `SVector, MVector, SizedVector, countvalues, evenvalues` (AT:646). Re-exports `TupleVector, Values, Variables, FixedVector`. |
| **AbstractLattices.jl** | hard dependency (compat 0.2, 0.3) | `import AbstractLattices: ∧, ∨, wedge, vee` (AT:271). AbstractLattices itself is: `function wedge end; function vee end; const ∧=wedge; const ∨=vee; wedge(x)=x; vee(x)=x; wedge(p::Bool,q::Bool)=p&&q; vee(p::Bool,q::Bool)=p\|\|q; function dist end` (19 lines). AT adds `∧()=1`, `∨()=I` (AT:273-274). |
| **DirectSum.jl** | **test-only** dependency, but its semantics are **assumed by the contract** | `ℝ`, `ℝ'`, `⊕`, `∪` (manifold union), `Signature` call-as-morphism `(W::Signature)(x)`, `V(I)`, `one(V)`, `zero(V)`, `mdims(::TensorBundle)`, `Submanifold`, `Single`, `Zero`. AT calls `Manifold(a) ∪ Manifold(b)` (AT:250, 254) and `(V∪W)(t)` (AT:34) without importing `∪`: it is `Base.∪`, extended by DirectSum. |
| Leibniz.jl | consumer | imports `TensorAlgebra, Manifold, TensorGraded, TensorTerm, scalar, isscalar, involute, equal, complement, pseudoscalar, vector, isvector, bivector, isbivector, volume, isvolume, ⋆, mdims, value, valuetype, interop, interform, even, odd, isnull, norm, TupleVector, Values, Variables, FixedVector, basis, complementleft, complementlefthodge, unit, clifford, ∧, ∨, complementrighthodge, complementright, gdims, conj, inv, PROD, SUM, -, /, countvalues, evenvalues, evens, sqrt, abs, exp, expm1, log, log1p, sin, cos, sinh, cosh, ^` (Leibniz `Leibniz.jl:30-35,144`, `generic.jl:241`, `utilities.jl:15-16`) |
| DirectSum.jl | consumer | `TensorAlgebra, Manifold, TensorGraded, Scalar, GradedVector, Bivector, Trivector, scalar, isscalar, involute, vector, isvector, bivector, isbivector, volume, isvolume, equal, ⋆, value, valuetype, interop, interform, even, odd, isnull, norm, SUM, SUB, PROD, TupleVector, Values, Variables, FixedVector, basis, mdims, pseudoscalar, hodge, clifford, complementright, complementleft, complementlefthodge, complementleftanti, complementrightanti, antimetric, pseudometric, cometric, wedgedot_metric, unit` (DirectSum `DirectSum.jl:28-32,617,676`, `operations.jl:329`, `basis.jl:15`, `generic.jl:167`) |
| Grassmann.jl | consumer | everything above, plus `plus, minus, times, contraction, equal, wedgedot, veedot, ∧, ∨, ⟑, ⊖, ⊘, ⊗, ⊛, ⊙, ⊠, ⨼, ⨽, ⋆, ∗, rem, div, TAG, SUB, pseudosandwich, antisandwich, cosandwich, antidot, codot, ⟇, antiabs, antiabs2, geomabs, unit, unitize, unitnorm, wedgedot_metric, contraction_metric, log_metric, trivector, istrivector, clifford, hodge, wedge, vee, complement` (Grassmann `algebra.jl:16-27`, `Grassmann.jl:23-41`, `multivectors.jl:21-22,962-964`). Uses `Values`/`Variables`/`FixedVector` pervasively (§8.6). |
| Cartan, MeshTopology, FieldAlgebra, Similitude, MeasureSystems, Geophysics, Adapode, AbstractAnalysis | consumers of StaticVectors | `Values` (hundreds of uses), `countvalues` (MeshTopology: 53), `_diff` (Cartan: 46), `Variables`, `.v` field access |

---

## 8. Lean 4 porting notes

### 8.1 Index vs runtime decisions

| Julia parameter | Lean | Runtime cost | Rationale |
|---|---|---|---|
| `N` in `Values{N,T}` | **type index** `(n : Nat)` in `Values n α` | Zero in the data (`Vector`'s size proof is erased; `n` is a structure parameter). Functions taking `{n}` receive one unboxed scalar. | Statically rejects length mismatch. This is exactly the Julia dispatch error surface (`DimensionMismatch` becomes a type error). `vcat : Values n α → Values m α → Values (n+m) α`, `diff : Values (n+1) α → Values n α`, and gather `Values m (Fin n) → Values m α` are all total. |
| `T` | type parameter `α` (erased) | none | |
| `V` (manifold value) | **type index** `(V : M)` where `M` is the manifold type from the DirectSum port | Zero in the data. A pointer to a (usually shared, closed-term) structure is passed to functions. | Mirrors Julia exactly (a value in the type). Keep it an index so `Chain V G T` differs for different V. **Do not try to get Julia-style per-V code specialization** from the Lean compiler. Precompute per-V tables at runtime and cache them (§8.2), or pass an explicit precomputed "algebra context". |
| `G` (grade) | type index `(G : Nat)` | same | Storage size `gdims n G` is computed in the type: `Chain V G T := Values (gdims (mdims V) G) T`. |
| `Op` in `Postfix{Op}` | **no type**: Lean `postfix` notation | none | |
| `UniformScaling λ` | `structure UScale (α) where val : α` (note: `λ` is reserved in Lean) | one field | A dimension-agnostic literal, resolved to `V`'s pseudoscalar by instances `HAdd (X V) (UScale α) (X V)`, etc. |
| `TensorAlgebra <: Number` | no subtyping. Generic `Values` arithmetic needs only `[Add α] [Mul α] …`, so tensor-valued entries work automatically. | | |

**Performance-safe dependent types:**
- Every size and grade index lives in *types*.
- Every length cast (`gdims n G = gdims n (n-G)` for complements, `(n+1)-1 = n`, …) goes through `Vector.cast h`. That is the identity on the underlying array, and `h` is erased.
- Never use `Subtype`/`Sigma` packing in hot paths. The proof components are erased, but a Sigma allocates a pair.

**Kernel-evaluation caveat.** Mathlib's `Nat.choose` is the naive Pascal recursion, so `whnf`/`decide` on `Nat.choose 20 10` is exponential. Define `gdims` with a **multiplicative formula over kernel-accelerated `Nat.mul`/`Nat.div`**:
```
gdims n k = if k > n then 0 else (∏_{i<k} (n-i)) / k!
```
or with a `Nat.rec` loop that keeps the running product. Then prove `gdims n k = Nat.choose n k` once and use `gdims` in all types. `tdims n := 2 ^ n` (`Nat.pow` is GMP-accelerated).

### 8.2 Mapping the AbstractTensors hierarchy

The Julia abstract types serve three purposes:
- (a) dispatch grouping
- (b) parameter extraction (`Manifold`, `valuetype`, `rank`)
- (c) a home for generic fallbacks

Recommended Lean design:

1. **Kind/parameter classes** (a, b). These are pure compile-time facts:
   ```lean
   class TensorAlgebra (X : Type) (M : outParam Type) (V : outParam M) (T : outParam Type) : Prop
   class IsManifold (X) … extends TensorAlgebra X M V T
   class TensorGraded (X) (M : outParam Type) (V : outParam M) (G : outParam Nat) (T : outParam Type) : Prop
   class TensorTerm … extends TensorGraded …  -- + `coeff : X → T` in a data class
   class TensorMixed … : Prop
   ```
   - `Manifold x := V`, `rank x := G`, `valuetype x := T`, and `mdims`/`tdims`/`gdims` are defined through them.
   - `istensor`/`isgraded`/… become `Bool` via a `TensorKind` class with a default low-priority instance returning `false`, or they are simply dropped: no downstream runtime logic needs them except `istensor` in Grassmann's `value_diff`.

2. **Operation classes** (heterogeneous, with `outParam` result types like `HMul`). This mirrors Julia's type-dependent result types, e.g. `Chain V G ⟑ Chain V H` is a `Multivector`:
   - `WedgeDot` (⟑, `*`), `VeeDot` (⟇), `Wedge` (∧), `Vee` (∨), `Contraction` (⨽), `Expansion` (∘), `Sandwich` (⊘), `Hodge` (⋆), `ComplementLeft`, `ComplementRight` (`!`), `Reverse` (~), `Involute`, `Clifford`, `Conj` (ǂ), `GradeProj` (`scalar`, `vector`, `bivector`, `trivector`, `volume`, `even`, `odd`)
   - `Inv` (Lean core), `HPow`
   - a **transcendental kernel**: `Cosh`, `Sinh`, `Expm1`, `Log`, `Sqrt`

   Julia's `plus`/`minus`/`times`/`equal` map to Lean `HAdd`/`HSub`/`HMul`/`BEq`.

3. **Derived algorithms** (c). Implement once, generically, over a *homogeneous* carrier. The transcendental formulas chain many ops, so heterogeneous result types would explode. Two options:
   - (preferred) a class `TensorRing (X : Type)` bundling `+ - ⟑ inv? ~ one zero pseudoscalar smulFloat divScalar cosh sinh log sqrt expm1 iszero norm scalar isscalar complementLeft complementRight ∧ hodge`, instantiated by Grassmann's dense `Multivector V T` and by its closed dynamic sum type `Tensor V T`.
   - For Julia's `(op, logm, g…)` generator loop (AT:318, 405), write **one** generic definition taking `(mul : X → X → X) (logm : X → X) (coshF sinhF sqrtF invF : X → X)` and instantiate it twice: plain, and with a metric `g`. This reproduces the "metric family" without code duplication.

4. **Interop**: provide `interop (op) (a : X V) (b : Y W) := op (embed (V ∪ W) a) (embed (V ∪ W) b)` explicitly, with `embed : X V → (W : M) → (V ≤ W) → X W`. **Do not** add implicit mixed-V `HAdd` instances by default: a `HAdd (X V) (X W) (X (V ∪ W))` instance overlaps with the same-V one. If you want it, register it at low priority. Cross-V arithmetic is rare in hot code.

5. **Scalar instances**: `Float`, `Int`, `Rat`, and a computable `Complex α` (Lean core has none; Mathlib's `Complex` is over noncomputable `ℝ`). Instances:
   - `scalar = id`, `involute = id`, `even = id`, `odd = 0` for **real** types only. Julia gives no method for Complex; the port may extend this.
   - `conj` (identity on reals)
   - `complement x = UScale.mk x`, `hodge x = UScale.mk x`
   - `wedgedot = (*)`, `contraction a b = conj a * b`
   - metric pass-throughs are just the plain functions

### 8.3 Notation and precedence

Julia precedence levels (oracle `Base.operator_precedence`) map to Lean as follows:
- 15 → 75 (right-assoc). This is `^`.
- 14 → 75. This is `<< >> >>>`, tighter than `*`.
- 12 → 70. This covers `* / \ ∧ ⟑ ⊘ ⊗ ⊛ ⊙ ⊠ × ⨼ ⨽ ⋆(binary) ∗ ⋅ ∘ &`.
- 11 → 65. This covers `+ - ∨ ⟇ ⊖ | ∪ ⊕`. **`∨` binds looser than `∧`, and `⊖` is geometric product at *plus* precedence.**
- 7 → 50. This covers `< > == ≈`, which are non-associative / chained in Julia.
- Unary `! ~ ⋆ - √` bind tighter than all binary operators: `!a*b == (!a)*b`, `⋆a ∧ b == (⋆a) ∧ b`.

Conflicts in Lean:

| Julia | Problem in Lean | Recommendation |
|---|---|---|
| `∧`, `∨` | core `And`/`Or` (Prop) | A scoped overloaded notation can coexist through choice nodes, but it is fragile, especially with different precedences (Prop `∧` is 35, the tensor wedge must be 70). **Recommend distinct tokens** such as `⋏`/`⋎`, or `∧ᵍ`/`∨ᵍ`, plus `wedge`/`vee` functions. |
| `<`, `>` | Prop-valued `LT`/`GT` | Use only `⨼`/`⨽` for contractions (same tokens as Julia). |
| `<<`, `>>` | free but confusable | `scoped infixl:75`. |
| `>>>` | `HShiftRight` exists | Give tensors an `HShiftRight` instance, or use a scoped `⋙` alternative. |
| `×` | `Prod` type former | Name it `cross`. |
| `∘` | `Function.comp` (90) | Use `expansion`/`antidot` names; optionally `⊚`. |
| `\|` | syntax | `contraction`. |
| `⋆` | Mathlib uses it only as a file-`local postfix:max "⋆" => star` (e.g. `Mathlib/Algebra/Star/Pointwise.lean:32`), so there is no global conflict | Scoped prefix `⋆`. |
| `ˣ` | Mathlib **global** `postfix:1024 "ˣ" => Units` (`Mathlib/Algebra/Group/Units/Defs.lean:61`) | Scoped postfix. The choice node disambiguates by type; add a regression test. Alternatively use `involute` only. |
| `⊗` | Mathlib `scoped[TensorProduct] infixl:100`, `scoped` in MonoidalCategory | Keep scoped. |
| `⁻¹` | core `Inv` postfix | Just give `Inv` instances. |
| `ǂ`, `₊`, `₋` | none. `₊`/`₋` (U+208A/B) are **not** Lean identifier characters (`isSubScriptAlnum` covers only digits, letters, ⱼ). U+01C2 `ǂ` is not letter-like for Lean. | `scoped postfix:max`. Unlike Julia, `x₊` works without parentheses. |
| `⟑ ⟇ ⊘ ⊖ ⊛ ∗ ⊙ ⊠ ⨼ ⨽ ⋅` | free | scoped infix at the levels above |

### 8.4 Tricky semantics and bugs: decide *replicate vs fix* explicitly

**AbstractTensors:**
- **B1**: `log(b::Real, t::TensorAlgebra)` returns `log(b)`. AT:401 (`log(t::Real, g::TensorAlgebra) = log(t)`, the metric pass-through) is more specific than AT:330 (`log(b, t) = log(t)/log(b)`). **Fix** in Lean: `logBase b t := log t / log b`, and name the metric version `logMetric`. Exclude it from oracle goldens.
- **B2**: `cos`/`sin`/… of **scalars** in dimensions with `I² = +1` (Euclidean n ≡ 0,1 mod 4) return `cosh`/`sinh` (§4.2 table). **Replicate** for oracle agreement: `cos t := cosh (I ⟑ t)` literally. Document it, and optionally add `cosTrue`.
- **B3**: `odd(x::Real) = 0` is an `Int` regardless of the input type. In Lean return `0 : α`.
- **B4**: `cometric(a::Single, b::Single)` is a method ambiguity with DirectSum (oracle). Lean: `cometric a b := pseudoabs (a - b)`.
- **B5**: `counit`/`unitize`/`unitnorm`/`geomabs`/`cometric` have **no scalar methods** (MethodError). Lean may define them for scalars. Exclude them from scalar goldens.
- **B6**: `×` is exported but undefined in AT; `valtype` clashes with Base. Irrelevant in Lean.
- **B7**: the generic fallbacks recurse infinitely when the concrete type lacks a same-V method. Lean's class design eliminates this: missing instance becomes a compile error.

`abs2` of a mixed element can be non-scalar (§2.1.8). `iszero` means exact zero. `isone` is chained. `a / b` is `a ⟑ inv(b)` (**right** division). `b ^ t = exp(t ⟑ log b)`. `exp t = 1 + expm1 t`: if Lean implements `exp` directly, keep `exp` and `1 + expm1` numerically consistent.

**StaticVectors:**
- **B8**: `maximum(f,a)` and `minimum(f,a)` are broken (SV/mapreduce.jl:270, 273).
- **B9**: `norm` of an empty vector, `norm_sqr`, and `norm(a,0)` are broken (SV/linalg.jl:90, 113).
- **B10**: `map` over N=0 is broken (SV/mapreduce.jl:66).
- **B11**: `FixedVector(v::TupleVector)` is ambiguous.
- **B12**: `float`/`real` type forms are broken (SV/convert.jl:55-56).
- **B13**: `Base.rest` destructuring is broken.
- **B14**: `v[SOneTo(k)]` is broken.
- **B15**: `view(::Variables, idx)` is broken.
- **B16**: scatter-assign of a scalar through a `TupleVector` index is broken (SV/indexing.jl:146).
- **B17**: `evenvalues(a,a-1)` and `evenvalues(a,b≤a-4)` error.
- **B18**: `diff` on N=0 errors.
- **B19**: adjoint/outer products are ambiguous.
- **B20**: `FixedVector` `elsize` references an undefined `A` (SV/FixedVector.jl:72).
- **B21**: `_setindex!(a::AbstractVector,value,::Val,ind)` references an undefined `ind_size` (SV/indexing.jl:269).
- **B22**: `_setindex!_scalar` assigns at generation time (SV/indexing.jl:27-30); unreachable.

Fix them all in Lean; they are total there by construction. Only generate goldens for the non-buggy domains.

`normalize` multiplies by the reciprocal: **replicate bitwise** (`x * (1/‖a‖)`).

`norm` has no overflow scaling: **replicate** `sqrt (Σ x²)`. Optionally add `normStable`.

`a / s` is true division; `s * a` keeps multiplication order (important for non-commutative α).

Result container follows the first argument (Values/Variables distinction). In Lean both are one type, so this is moot.

Element promotion (`Values(1, 2.0)` becomes Float) has no Lean analog. Require a homogeneous α and coerce explicitly.

`Values(1,"b")` producing `Values{2,Any}` has no analog; skip it.

`sum` over `Bool` gives `Int` (`reduce_first`), while `sum` over `Int8` does not widen and `cumsum` over `Int8` widens (`add_sum`). None of this is relevant in Lean.

Julia `max`/`min` on floats propagate NaN and order `-0.0 < 0.0`. Lean's `max` on `Float` is `if a ≤ b then b else a`, which differs on NaN and signed zeros. **Implement `juliaMax`/`juliaMin` explicitly**:
- `max`: `if isNaN a || isNaN b then NaN else if a == b then (if signbit a then b else a) else …`
- `min`: symmetric

`dot` conjugates the **left** argument per element.

`Values(...)` equality is elementwise; different lengths give `false` (in Lean this is a type error; provide `beqDyn` if needed).

`FixedVector` aliasing has no Lean analog. `Vector` is persistent, and in-place updates happen only when the reference is unique.

**Floating-point parity:**
- `+ - * / sqrt` are IEEE correctly rounded in both languages. **Bitwise match is expected** when the evaluation order matches (§4.1).
- `^` (`Float64^Float64` and `Float64^Int`), `exp`, `log`, `sin`, `cos`, `cosh`, … use Julia's own pure-Julia libm, while Lean calls the platform libm. Allow **≤ 2 ulp** (tests should report ulp distance).
- `muladd` may fuse to FMA in Julia. Use non-fused ops in Lean and allow 1 ulp there.
- **Lean core lacks `expm1`, `log1p`, `hypot`, `sinpi`/`cospi`, `fma`.**
  - Implement `expm1`/`log1p` either via FFI to C (`@[extern "expm1"]` in a small C shim compiled by Lake, which works in compiled code) or in pure Lean with Kahan's trick: `expm1 x = let u := exp x; if u == 1 then x else if u - 1 == -1 then -1 else (u - 1) * x / log u`.
  - Note that AT's `exp t = one + expm1 t` uses Grassmann's `expm1`, not the scalar one, so the scalar function matters only for scalar paths.
- Julia's integer types are fixed-width (Int64 wraps). Use Lean `Int` (arbitrary precision) for coefficients and counts, and accept overflow divergence.

### 8.5 Julia-specific machinery to skip or redesign

| Julia | Lean |
|---|---|
| `@pure`, `@generated`, `@inline`, `@_inline_meta`, `@propagate_inbounds`, `@inbounds` | `@[inline]`, `@[specialize]`, `Fin`-indexed access (unchecked `Array.get`/`FloatArray.get` with proofs), `uget` with `USize` in tight loops |
| `STATICJL` env switch | drop |
| pointer / `unsafe_convert` / `cconvert` / `dataids` / `elsize` / `strides` | drop |
| `Variables` unsafe pointer mutation | Same type as `Values`. Mutate with `Vector.set`/`modify`: in place when the reference is unique (FBIP). Keep accumulators linear, never shared. |
| `FixedVector` wrapper, `SizedVector` | drop (`Vector α n` already is an array with a static size) |
| `SOneTo{n}` | `Fin n`, `List.finRange n`, or `[0:n]` ranges |
| `similar`, `similar_type`, `default_similar_type`, `promote_rule` | drop: static result types |
| `BroadcastStyle`, `Broadcasted`, `_broadcast`, `copyto!` | explicit `map`, `zipWith`, `zipWith3`, plus scalar-broadcast helpers `mapConst` |
| `TupleIndexing`, `to_indices`, multidim `_getindex` | drop, keep only 1-D gather/scatter |
| `Base.rest`, `tvcollect` (generators) | `Vector.ofFn`, `#v[...]` (Lean core literal), `Values.ofList! n l` (checked) |
| `TV[...]`, `TV_F32`, `TV_F64` | `#v[...]` with type ascription |
| `rand`/`randn`/`randexp` | test utilities only (a small splitmix/xoshiro PRNG); Julia RNG streams cannot be reproduced anyway |
| `Base.count(a::Int,b::Int)` piracy | drop, use `countvalues` |
| `Expr`/`Symbol` coefficient hooks (`norm(::Expr)`, `signbit(::Expr)`, `≈` on Expr, `-(::Symbol)`, `*(::Expr, ::TupleVector)`, `∏`/`∑` indirection) | Redesign: coefficients are any `α` with algebra classes. A future `SymExpr` coefficient type implements `Add`/`Mul`/`Neg`/…, so `∏`/`∑` are just `foldl (· * ·)`/`foldl (· + ·)`. Skip symbolic mode in v1. |
| `Postfix{Op}` struct and `*(t, ::Postfix)` | `postfix` notation |
| `@co f(x…)`, `@pseudo f(x…)` | a combinator `co (f : X → X) := complementLeft ∘ f ∘ complementRight` (and n-ary variants), plus an optional command macro `co_def f` that emits `cof` |
| `AbstractArray` aliases (`FloatVector`, `RealArray`, …) | drop |

### 8.6 Performance: how Julia is fast here, and the Lean plan

How Julia gets its speed:
1. `Values{N,T}` is an isbits NTuple: no heap allocation, SROA into registers, LLVM SLP vectorization.
2. `@generated` bodies are **fully unrolled** per `N` (map, fold, dot, norm, broadcast, vcat, diff, indexing).
3. `@pure` and constant propagation of `N` and `V` fold `binomial`, `1<<n`, and index tables at compile time.
4. Method specialization on `V` makes Grassmann's product tables compile-time constants.
5. `@inbounds` removes bounds checks.

Hot paths used downstream:
- `Values` `+ - scalar*` (every Chain/Multivector add)
- `zeros(Variables{N,T})` followed by `out[i] += …` accumulation in generated product code (Grassmann `products.jl:1078` `generate_mutators`, Leibniz `utilities.jl:63-67`)
- `Values(out)` freezing
- `norm(value(t))` (in `iszero`, `isapprox`, `norm`)
- `evens(1,N+1)` grade loops (at generation time in Julia, at runtime in Lean)
- `_diff` (Cartan finite differences)
- `countvalues` (MeshTopology index lists)

Lean plan:
- **Storage abstraction from day one.** Every consumer touches coefficients only through a narrow `Values` API: `ofFn`, `get`, `set`, `map`, `zipWith`, `foldl`, `replicate`, `append`, `cast`.
- Two backends:
  - generic `Vector α n` (boxed elements for `Float`)
  - `FValues n := { data : FloatArray // data.size = n }`, unboxed Float64. `FloatArray` has only `get`/`set`/`push`/`foldl` in core; write `map`/`zipWith` as index loops with `set!`, which is in place when unique.
- Select the backend with an associated-type class:
  ```lean
  class Store (α : Type) where
    Arr : Nat → Type
    get : Arr n → Fin n → α
    ofFn : (Fin n → α) → Arr n
    set : Arr n → Fin n → α → Arr n
    ...
  ```
  - a default `instance (priority := low) : Store α := ⟨Vector α, …⟩`
  - `instance : Store Float := ⟨FValues, …⟩`
  - a separate `LawfulStore` with `get_ofFn`, `get_set`, …, so proofs stay backend-agnostic
- If that is judged too heavy for v1, start with `Vector` only, but **keep the API boundary** so the swap is local.
- `Array.map`/`Vector.map` reuse the buffer when unique (`Array.mapMUnsafe`), so `map` on a fresh intermediate costs no allocation. `zipWith` allocates one result.
- Mark small combinators `@[inline]` and higher-order ones `@[specialize]` so `f` is monomorphized, which recovers much of Julia's unrolling benefit without codegen.
- For N ≤ 8 hot kernels, add an optional unrolling macro later, only if benchmarks demand it.
- Accumulators: `let mut out := Values.replicate n 0` followed by `out := out.modify i (· + x)` in a `for` loop. The compiler keeps `out` unique.
- Grade loops `for g in evens(1,N+1)` become `for g in [1:N+2:2]`. The legacy Nat `Std.Range` syntax `[start:stop:step]` (still in `Init/Data/Range/Basic.lean:69-72`) has an **exclusive** stop, so `stop = b+1`.
- Julia's inclusive `a:b` (what `countvalues` materializes) corresponds to the new polymorphic range `a...b` (`Init/Data/Range/Polymorphic/PRange.lean`, closed, works for `Int`). `a...<b` is the half-open form. The polymorphic ranges have no step syntax, so stepped loops use the legacy form or `evenvalues`.
- Julia's 1-based grade index `g` in `evens(1,N+1)` enumerates grades `0,2,4,…` shifted by +1. In Lean, iterate `grade ∈ [0:N+1:2]` directly and **do not** carry the +1.

### 8.7 Suggested Lean module decomposition

Namespace `Chakravala`. Rough LOC is implementation plus proofs, excluding tests unless noted.

| Module | Contents | LOC |
|---|---|---|
| `Chakravala/Util/JuliaShow.lean` | Julia-compatible `Float` shortest round-trip printer (Ryu or Grisu-exact) with Julia exponent rules (`1.0e10`, `1.0e-5`, `NaN`, `Inf`), `:compact` 6-significant-digit mode, `Int`/`Rat`/`Complex` printers (`1 + 2im`, `1//2`) | 350 |
| `Chakravala/Util/Complex.lean` | computable `Complex α` with `re`, `im`, ring ops, `conj`, `abs`, `abs2`, `inv`, `div`, `exp`, `log`, `sqrt` (for Float) | 200 |
| `Chakravala/Util/FloatExt.lean` | `expm1`, `log1p` (C shim or Kahan), `juliaMax`/`juliaMin`, `rtoldefault`, `isapprox` (Julia rule), ulp distance | 150 |
| `Chakravala/AbstractLattices.lean` | `Wedge`/`Vee` classes, the `Bool` instance, identities `wedge0 = 1`, `vee0 = I` | 40 |
| `Chakravala/StaticVectors/Store.lean` | `Store`/`LawfulStore` classes, `Vector` and `FloatArray` backends | 250 |
| `Chakravala/StaticVectors/Values.lean` | `Values n α` API: `ofFn`, `get`, `set`, `modify`, `replicate`, `zeros`, `ones`, `fill`, `map`, `zipWith`, `zipWith3`, `foldl`, `append` (vcat), `reverse`, gather/scatter by `Values m (Fin n)`, `countvalues`, `evenvalues`, `cast` | 350 |
| `Chakravala/StaticVectors/Arith.lean` | `Add`, `Sub`, `Neg`, `HMul α (Values n α)`, `HMul (Values n α) α`, `HDiv`, `SMul`, `muladd`, `BEq`/`DecidableEq`/`Hashable`/`Ord` (lexicographic) | 150 |
| `Chakravala/StaticVectors/Reduce.lean` | `sum`, `prod`, `maximum`, `minimum` (Julia semantics), `any`, `all`, `count`, `contains`, `isZero`, `accumulate`, `cumsum`, `cumprod`, `diff` | 180 |
| `Chakravala/StaticVectors/LinAlg.lean` | `dot` (conj-left), `bilinearDot`, `normSq`, `norm`, `normP` (1, 2, ∞, general p), `normalize` (multiply by reciprocal), `cross3` | 130 |
| `Chakravala/StaticVectors/Show.lean` | compact `[a, b]` and text/plain display | 100 |
| `Chakravala/StaticVectors/Lemmas.lean` | `get_ofFn`, `get_map`, `get_zipWith`, `get_append_left/right`, `get_reverse`, `reverse_reverse`, `get_diff`, `get_countvalues` (`= a + i`), `get_evenvalues` (`= a + 2i`), `sum_append`, `dot_comm` (commutative ring), `size` lemmas. Use `grind`/`omega` heavily. | 250 |
| `Chakravala/AbstractTensors/Dims.lean` | `mdims`, `tdims`, fast `gdims`; theorems `gdims_eq_choose`, `sum_gdims = tdims` (Mathlib `Nat.sum_range_choose`), `gdims_symm` (for complement casts) | 120 |
| `Chakravala/AbstractTensors/Classes.lean` | kind/parameter classes, operation classes (§8.2), `TensorRing` homogeneous bundle | 250 |
| `Chakravala/AbstractTensors/Notation.lean` | scoped notations with the precedence table (§8.3), postfix `ǂ ₊ ₋ ˣ` | 120 |
| `Chakravala/AbstractTensors/UniformScaling.lean` | `UScale`, `I`, scalar↔pseudoscalar complement, lifting instances for the UniformScaling op list | 120 |
| `Chakravala/AbstractTensors/Scalar.lean` | scalar instances (`Float`, `Int`, `Rat`, `Complex`) of the interface | 120 |
| `Chakravala/AbstractTensors/Derived.lean` | contraction variants (`⨼ ⨽ << >> ∗ ⊛`), `cross`, `abs`, `abs2`, `unit`, `counit`, `unitnorm`, `geomabs`, `metric`, `cometric`, sandwich variants | 200 |
| `Chakravala/AbstractTensors/Transcendental.lean` | generic `(mul, logm, prims)` kernel; plain and metric instantiations of the §2.1.9 table; `logBase` (fixed B1) | 220 |
| `Chakravala/AbstractTensors/Co.lean` | `co`/`pseudo` combinators, the 26 named functions, `co_def` command macro | 100 |
| `Chakravala/AbstractTensors/Interop.lean` | `interop`, `interform`, embedding class | 80 |
| `Chakravala/AbstractTensors/Approx.lean` | `isapprox` (both variants), `iszero`, `isone`, `isnull` | 90 |
| `Tests/Oracle/StaticVectors.lean`, `Tests/Oracle/AbstractTensors.lean` | JSON golden readers and comparators (hex floats, ulp tolerance) | 350 |

Total is about **3,000 LOC** without tests and about 3,400 with them.

### 8.8 Proofs that pay for themselves (development velocity)

- Size bookkeeping is free from the types. The first proofs to write are `get_*` simp lemmas so `simp`/`grind` can normalize any `Values` expression to pointwise form.
- Spec theorems as executable documentation, checkable by `decide` on small n:
  - `(countvalues a b).get i = a + i`
  - `(evenvalues a b).get i = a + 2*i`
  - `diff`'s pointwise spec
  - `reverse ∘ reverse = id`
  - `sum (a ++ b) = sum a + sum b`
  - `dot a b = sum (zipWith (conj · * ·) a b)`
  - `normalize a = (1/‖a‖) • a`
- AbstractTensors:
  - `Σ gdims n g = 2^n`
  - `gdims n g = gdims n (n-g)`
  - postfix laws for scalars: `x₊ + x₋ = x`, `involute (involute x) = x`
  - `co (co f) = f` given `complementLeft ∘ complementRight = id` (holds in Euclidean signatures)
  - these let Grassmann's complement casts be `Vector.cast (gdims_symm …)` at zero cost.

---

## 9. Oracle test plan

A skeleton has been run and produced 549 cases. It is at `/private/tmp/claude-502/-Users-alokbeniwal-Grassmann/c6cc2308-bfca-4b9a-ad33-d89b110132a8/scratchpad/probe/oracle_skeleton.jl`, with output `probe/oracle_sample.json`. Run it with:

```
julia --startup-file=no --project=<juliaenv> oracle.jl
```

### 9.1 Encoding (exactness first)

- `Float64` is encoded as the IEEE bit pattern string `"f64:3ff0000000000000"` (and `f32:` for Float32). This handles NaN, ±Inf and −0.0 exactly. Store `repr` alongside for humans.
- `Int` is a decimal **string** (avoids JSON double rounding).
- `Complex` is `{"re":…,"im":…}`.
- `Rational` is `{"num","den"}`.
- A `Values` value is `{"kind":"Values","N":n,"T":"Float64","v":[…]}`.
- `UniformScaling` is `{"kind":"UniformScaling","λ":enc(λ)}`. The skeleton lacks this encoder, which is why its `postfix_complement` cases show a MethodError coming from the encoder, not from AT.
- Errors are `{"error":"DimensionMismatch","msg":"<first line>"}`. The Lean side only checks that it *rejects* the case (type error, `none`, or exception) and ignores the message.
- Grassmann-carried tensors: `{"V":"⟨111⟩","n":3,"basis":["1","v1","v2","v3","v12","v13","v23","v123"],"v":[…2^n f64…],"repr":string(x)}`. Dump `value(Multivector(x))` so every result is dense in Grassmann's grade-major, lexicographic-within-grade order (the order visible in its printing).

Each case record:
```json
{"suite":"…","op":"…","T":"…","N":…,"args":[…],"out":{"ok":…,"repr":"…"}|{"error":…},"tol":{"ulps":0}}
```
Header fields: `julia`, `pkg` versions, `seed`.

### 9.2 Suites and input distributions

| Suite | Functions | Inputs | Tolerance |
|---|---|---|---|
| `sv.arith` | `+ - neg`, `s*a`, `a*s`, `a/s`, `s\a`, `muladd` | N ∈ {0,1,2,3,4,5,8,16,32}; T ∈ {Int64, Float64, ComplexF64}. Ints uniform in −9..9 (and ±2^40 for overflow-free large ones). Floats `round(20rand-10, digits=3)`, plus `randn`, plus an **edge set** {0.0, −0.0, 1e-300, 1e300, 5e-324, NaN, Inf, −Inf}. Scalars s ∈ {2, 3, 0.1, −0.5}. | exact (bitwise). `muladd`: 1 ulp. |
| `sv.reduce` | `sum`, `prod`, `maximum`, `minimum`, `cumsum`, `cumprod`, `accumulate(-)`, `foldl(-; init)`, `reduce(+; init)`, `iszero`, `in`, `any`, `all`, `count` | same | exact. Include NaN/±0 cases for max/min. |
| `sv.linalg` | `dot`, `bilinear_vecdot`, `norm`, `norm(a,1)`, `norm(a,Inf)`, `norm(a,3)`, `norm(a,2.5)`, `normalize`, `normalize(a,1)` | same, N ≥ 1 (norm of empty is bug B9) | exact except `norm(a,p∉{1,2,Inf})` (≤ 2 ulp, `^`). Also include `norm(Values(1e200,1e200)) == Inf`. |
| `sv.struct` | `diff`, `reverse`, `vcat`, gather `a[idx]` (idx random `Values` of length 1..2N), scatter on a copy | N ≥ 1 for diff | exact |
| `sv.ranges` | `countvalues(a,b)`, `evenvalues(a,b)` | a, b ∈ −6..6 (all 169 pairs). Record errors: they document B17. | exact |
| `sv.ctor` | `Values{N}(vec)` length errors, generator too short/long, `Values{N,Int}(2.5)` InexactError, `zeros`/`ones`/`fill` | fixed list | reject/accept + exact |
| `sv.show` | `print`/`repr`/text-plain strings for the §5 element-type list and random Float64 vectors (to stress the shortest-repr printer: random bits, values straddling the exponent switchovers at 1e-4 and 1e6, powers of ten 1e-8…1e20, subnormals, plus `:compact` renderings) | ~300 values | exact string |
| `at.dims` | `mdims(n)`, `tdims(n)`, `gdims(n,g)` | n ∈ 0..20, g ∈ −1..n+1 | exact |
| `at.scalar` | postfix `⁻¹ ǂ ₊ ₋ ˣ`; `!x`; `!(λI)`; `hodge`; `unit`; `wedgedot`/`contraction` (+`_metric`); `metric`; 3-arg pass-throughs; `∑`/`∏`/`SUB`; `wedge`/`vee` on Bool | x ∈ {Int, Float64 random, ComplexF64 random, Rational}. Record MethodError where Julia has none (Complex for even/odd/involute; B5). | exact |
| `at.grassmann.products` | `contraction ⨼ ⨽ < > << >> ∗ ⊛ ∘ × cross / \ ⊘ >>> ! ⋆ ~ ǂ ₊ ₋ involute`, `x±I`, `x*I`, `I*x`, `x/I`, `I/x`, `metric` | V ∈ {`basis"2"`, `basis"3"`, `basis"4"`, `ℝ^(1,3)` Minkowski}. Random `Single` of each grade, random `Chain` of each grade, random `Multivector`; coefficients uniform in [−2,2] (Float64). | 1e-12 relative |
| `at.grassmann.transcendental` | `cos sin tan cot sec csc tanh coth sech csch asinh acosh atanh acoth asin acos atan acot sinc cosc exp2 exp10 log2 log10`, `b^t` | Carriers: `Single` blades of each grade and `Couple`-type inputs (`a + b·blade`). Scale ∈ {0.1, 0.25, 0.5, 1.0}, because Grassmann's series precision is ~1e-11 and degrades with magnitude. For inverse functions restrict \|t\| < 0.9, and `acosh` scalar part ≥ 1.1. **Include scalar-grade inputs in n = 1..5** to pin the B2 behavior. Record errors (acos/acot of vectors, acoth DomainError). | 1e-9 relative (≥ 1e-12 absolute) |
| `at.grassmann.norms` | `abs`, `abs2` (both graded and mixed), `norm`, `unit`, `coabs`, `geomabs`, `unitize`, `unitnorm`, `iszero`, `isone`, `isapprox` (atol/rtol grid: {0, 1e-12, 1e-6} × {default, 1e-9, 1e-6}, perturbations 10^k for k = −15…−3; graded rank-mismatch cases with zero and nonzero values) | as above | 1e-12 relative; isapprox Boolean exact |
| `at.co` | the 26 co/pseudo functions, `cosandwich`, `antisandwich` | pseudoscalar-grade and vector inputs in `basis"3"` | 1e-9 relative |
| **Excluded** | `log(b::Real, t)` (B1), `cometric` on Singles (B4), every StaticVectors B8-B22 path, Grassmann `cos` on `Multivector` (Grassmann-side UndefVarError `op`) | | |

### 9.3 Comparator rules (Lean side)

- Exact suites compare IEEE bit patterns. Treat all NaNs as equal; **distinguish ±0**.
- ulp suites: `|bits(a) - bits(b)| ≤ k` on the same-sign ordered-integer mapping.
- Relative suites: `‖a − b‖₂ ≤ rtol·max(‖a‖,‖b‖) + atol` on coefficient vectors, i.e. the Julia `isapprox` rule.
- Error cases: Lean must reject. Statically ill-typed cases (length mismatch) are recorded as "type-rejected" and skipped at runtime, with a comment linking the golden.

### 9.4 Julia oracle script outline

This extends the run-verified skeleton.

```julia
using StaticVectors, AbstractTensors, Grassmann, LinearAlgebra, JSON, Random
const SV = StaticVectors; const AT = AbstractTensors
enc(x::Float64) = "f64:" * string(reinterpret(UInt64, x), base=16, pad=16)
enc(x::Integer) = string(x); enc(x::Bool) = x
enc(x::Complex) = Dict("re"=>enc(real(x)), "im"=>enc(imag(x)))
enc(x::Rational) = Dict("num"=>string(numerator(x)), "den"=>string(denominator(x)))
enc(J::UniformScaling) = Dict("kind"=>"UniformScaling", "λ"=>enc(J.λ))
enc(v::SV.TupleVector) = Dict("kind"=>string(nameof(typeof(v))), "N"=>length(v), "T"=>string(eltype(v)), "v"=>enc.(collect(v)))
enc(t::AT.TensorAlgebra) = (m = Multivector(t); Dict("kind"=>"MV", "V"=>string(Manifold(t)), "n"=>mdims(t),
                           "v"=>enc.(collect(value(m))), "repr"=>string(t)))
enc(x::Real) = enc(Float64(x))
run(f, args...) = try r = f(args...); Dict("ok"=>enc(r), "repr"=>repr(r))
                  catch e; Dict("error"=>string(nameof(typeof(e))), "msg"=>first(split(sprint(showerror,e),'\n'))) end
# write one JSON file per suite: {"julia":..., "pkg":{...}, "seed":..., "cases":[...]}
# NOTE: postfix ops must be written *(t, ⁻¹) or (t)⁻¹ — `t*⁻¹` is a parse error (operator suffix).
```

Store goldens under the Lean repository, e.g. `test/goldens/{sv,at}/*.json`, and check in the generating script so the goldens are reproducible (fixed `Xoshiro` seed).
