# Grassmann.jl `src/algebra.jl` (and the algebra core around it): Lean 4 porting spec

Scope owner: Grassmann.jl `src/algebra.jl` COMPLETELY, plus every piece of arithmetic that
`algebra.jl` depends on or that the task explicitly listed (+, -, scalar `*`, `/`, `==`,
`isapprox`, involutions, complements/Hodge, grade projections, norms/`abs`/`abs2`/`metric`,
`inv`, generated-code patterns, promotion). Those listed topics physically live in
`products.jl`, `parity.jl`, `multivectors.jl` (Grassmann), `operations.jl`/`generic.jl`/`DirectSum.jl`
(DirectSum), `generic.jl`/`utilities.jl`/`indices.jl` (Leibniz) and `AbstractTensors.jl`; they are
specified here at the level of exact semantics with citations, so an implementer does not
have to open the Julia.

Notation: `A.jl:L` means `/Users/alokbeniwal/chakravala/<Pkg>.jl/src/A.jl` line L.
Abbreviations: `alg` = Grassmann `algebra.jl`, `prod` = Grassmann `products.jl`,
`par` = Grassmann `parity.jl`, `mv` = Grassmann `multivectors.jl`, `G.jl` = Grassmann `Grassmann.jl`,
`comp` = Grassmann `composite.jl`, `forms` = Grassmann `forms.jl`,
`DS` = DirectSum `DirectSum.jl`, `DSgen` = DirectSum `generic.jl`, `DSop` = DirectSum `operations.jl`,
`DSbasis` = DirectSum `basis.jl`, `Lgen` = Leibniz `generic.jl`, `Lutil` = Leibniz `utilities.jl`,
`Lidx` = Leibniz `indices.jl`, `L.jl` = Leibniz `Leibniz.jl`, `AT` = AbstractTensors `AbstractTensors.jl`.

---------------------------------------------------------------------------------------------

## 0. Provenance and how this spec was verified

* Source: `chakravala/Grassmann.jl` master `4f79a7fd` (2026-08-09, Project version 0.8.47).
  AbstractTensors 0.8.12, DirectSum 0.8.21, Leibniz 0.3.1 clones.
* Oracle: Julia 1.13 env at `scratchpad/juliaenv` (registered Grassmann 0.8.46, AbstractTensors
  0.8.11, DirectSum 0.8.21, Leibniz 0.3.0). I diffed the registered sources against the clones:
  `algebra.jl`, `products.jl`, `parity.jl`, `multivectors.jl` are byte-identical; DirectSum identical;
  Leibniz differs by one import; AbstractTensors differs by two `angle(t,g)` methods. The oracle is
  therefore authoritative for this scope.
* Everything marked "(verified)" was checked by running Julia. Artifacts (all under
  `/private/tmp/claude-502/-Users-alokbeniwal-Grassmann/c6cc2308-bfca-4b9a-ad33-d89b110132a8/scratchpad/notes/oracle/grassmann_algebra/`):
  * `algebra_oracle.jl` - golden dumper (JSON lines). Full run: ~5 min, 79,156 records, 33 MB
    (`out/algebra_goldens.jsonl`); `couple_only.jl` adds 3,456 Couple/PseudoCouple records
    (`out/couple_goldens.jsonl`).
  * `ref_check.py` - a ~200-line clean-room reference implementation of the semantics in section 4
    (bitmask kernels, dense arrays, no Julia logic). It reproduces **all 76,912 non-error,
    non-conformal golden records** and all non-bug Couple records exactly (integer/rational exact,
    floats to 1e-9 relative). It is the executable form of this spec; port it first.
  * `conformal_check.py` / `conformal_comp.py` - prove the conformal (`S"∞∅++"`) algebra equals the
    orthogonal algebra conjugated by the null-basis change of basis of section 4.9 (all 1,024 conformal
    product records pass; complements/Hodge match by hand-table).

---------------------------------------------------------------------------------------------

## 1. Purpose and scope

`algebra.jl` (1,889 lines) is the **product engine** of Grassmann.jl:

1. Basis-blade products on `Submanifold` (unit blades) and `Single` (scaled blades):
   geometric `⟑`/`*`, exterior `∧`, regressive `∨`, interior `contraction` (alg:31-277), plus the
   `_metric` variants taking an explicit metric object `g`.
2. Derived products: sandwich `⊘` and `>>>` (alg:311-387), `veedot`/`⟇`, `antidot`
   (alg:389-397), parallel test `∥` (alg:401), symmetrization `⊙`/`⊠` (alg:287-309, broken), `⊗`
   (alg:149-152).
3. Powers (`^`, `literal_pow`, alg:403-469), inverses and division for every element type
   (`inv`, `/`, `//`, alg:471-715), including a metric-weighted port of Julia's robust complex
   division for `Couple` (alg:553-698).
4. The **code generators** ("Algebra Constructors", alg:717-1889) used by `@generated` methods in
   `products.jl`: `adder*` (sum of two terms / term + chain / term + multivector -> promoted result
   type), `product` / `product_contraction` / `product_∧` / `product_∨` (graded x chain and
   graded x multivector/spinor), `product_sandwich`, and `generate_loop_*` (mixed x mixed). These
   emit fully unrolled straight-line code for small dimensions and runtime loops otherwise.

The Lean port target is: the element types, the four fundamental products and everything derived
from them, with Julia's exact sign conventions, orderings, result-type narrowing (where desirable),
and display strings, on diagonal metrics (Euclidean, `Signature`, `DiagonalForm`, projective
`∞`/`∅`, conformal `∞∅`). Out of scope for a first port (documented for completeness): tangent /
Leibniz derivation algebras (`diffvars≠0`), dyadic/mixed `V⊕V'` spaces, non-diagonal
`MetricTensor`, field-valued metric `g`, symbolic coefficient fields (`Expr`/`Symbol`/Reduce/SymPy).

---------------------------------------------------------------------------------------------

## 2. Public API inventory

### 2.1 Operator families (the aliases are the same function object unless noted)

| Concept | Unicode | ASCII / other names | Definition site | Semantics (section 4 has details) |
|---|---|---|---|---|
| geometric product | `⟑`, `⊖` | `*`, `wedgedot`, `times` | AT:294-296,314,350; alg:38-93; prod:1122-1131,1156-1302 | Clifford product |
| n-ary geometric | `⟑(a,b,c...)` | `*(a,b,c...)` | alg:40-41 | left fold `⟑(a⟑b,c...)` |
| exterior | `∧` | `wedge` (AbstractLattices) | alg:108-147, prod:1171-1184,1185-1302 | outer product |
| n-ary exterior | `∧(a,b,c...)`, `∧(::Values)`, `∧(::FixedVector)` | | alg:111-114,123,125 | left fold; `∧()` of empty `Values{0,<:Chain{V}}` = `One(V)`; AT:273 `∧()=1` |
| exterior of vector list | `∧(t::Chain{V,1,<:Chain{W}})` | | alg:115-121 | if `mdims(V)>mdims(W)`: `map(Real,compound(t,Val(min)))` (composite.jl) else `∧(value(t))` |
| regressive | `∨` | `vee`, `&` (alg:192-194) | alg:156-190, prod:1303-1322 | meet, DeMorgan dual of `∧` |
| n-ary regressive | `∨(a,b,c...)`, `∨(::Values)` | | alg:185-190 | left fold; `∨()` of empty = `Submanifold(V)` (pseudoscalar I); AT:274 `∨()=I` |
| quirk | `∨(t::Chain{V,1,<:Chain})` | | alg:189 | returns `∧(value(t))` (wedge, not vee) - Julia quirk |
| right contraction | `⨽`, `⋅` | `contraction`, `dot`, `|` (binary), `>` | AT:264-265,297,351,447; alg:209-271 | `a⋅b = <(~b) a>_{|a|-|b|}` (verified) |
| left contraction | `⨼` | `<` | AT:259,262 | `a⨼b = a<b = contraction(b,a)` |
| conventional left | | `<<` | AT:260 | `a<<b = contraction(b, ~a)` |
| conventional right | | `>>` | AT:261 | `a>>b = contraction(~a, b)` |
| reversed product | `∗` | | AT:257 (doc alg:95-99) | `a∗b = (~a)⟑b` |
| scalar product | `⊛` | | AT:258 | `scalar(contraction(a,b))` |
| cross product | `×` | `cross` | AT:349 | `hodge(a∧b)` |
| anti-geometric | `⟇` (Julia>=1.10) | `veedot` | alg:391, AT:628-631 | `complementleft(complementright(a)*complementright(b))` |
| anti-dot | | `antidot` = `expansion` = `codot` = `pseudodot`, `∘` | alg:396, AT:314,337 | `complementleft(contraction(complementright(a),complementright(b)))` |
| sandwich | `⊘` | `sandwich` | alg:313-341, AT:313 | `x⊘y = reverse(y)*x*involute(y)` (+ grade projection, 4.12) |
| traditional sandwich | | `>>>` | alg:351-379 | `y>>>x = y*x*clifford(y)` (+ projection) |
| co-sandwich | | `cosandwich` = `pseudosandwich` | AT:559-561 | `complementleft(sandwich(complementright(x),complementright(R)))` |
| anti-sandwich | | `antisandwich` | AT:568-569 | `complementleft(complementright(R)>>>complementright(x))` |
| tensor | `⊗` | | alg:150-152, AT:333-336 | `Dyadic(a,b)` (forms.jl) for graded; if either side grade 0 or a plain number: `a*b` |
| symmetrize | `⊙` | | alg:294 | BROKEN: `permutations` not imported (verified UndefVarError) |
| antisymmetrize | `⊠` | | alg:301-309 | BROKEN, same reason |
| parallel | `∥` | | alg:401 | `iszero(a∧b)` -> `Bool` |
| perpendicular | `⟂` | | alg:23 | exported but never defined (UndefVarError) |
| division | | `/`, `\` | alg:477-480, AT:320-325 | `a/b = a⟑inv(b)`, `a\b = inv(a)⟑b` |
| rational division | | `//` | alg:475-480 | `a//b = a*inv_rat(b)` (`inv_rat` uses `//`) |
| inverse | `⁻¹` (postfix, AT:578) | `inv` | alg:481-551,607-637 | per type (4.10) |
| power | | `^`, `literal_pow` | alg:408-469, AT:326-328 | per type (4.11); `number^t = exp(t*log(number))` |
| metric-explicit variants | | `wedgedot_metric(a,b,g)`, `contraction_metric(a,b,g)`, `veedot_metric`, `antidot_metric`, `^(a,n,g)`, `/(a,b,g)`, `inv(a,g)`, `⊘(a,b,g)`, `>>>(a,b,g)` | alg:39,64,84-93,225,262,322-341,360-379,392,397,421-551 | same semantics with metric object `g`; if `isinduced(g)` (forms:1698-1704: `InducedMetric`, `TensorBundle`, or non-basis `Submanifold`) they delegate to the plain version. `antidot_metric(a,b)` (alg:397) references an undefined `g` (bug). |

Postfix operators (AT:573-582): `t*⁻¹ = inv(t)`, `t*ǂ = conj(t)`, `t*₊ = even(t)`, `t*₋ = odd(t)`,
`t*ˣ = involute(t)` (they are `Postfix{op}` singletons with `*(t,op)=op(t)`).

`UniformScaling` interop (AT:287-292): for all binary ops above, `op(a, I)` = `op(a, Manifold(a)(I))`
where `V(λI)` is `λ` times the pseudoscalar of `V` (DS:533-536: `V(I)` = pseudoscalar
`Submanifold`, `V(λ*I)` = `Single(λ, I)`). Unary `!(λ::Real)` / `complementrighthodge(λ)` return
`UniformScaling(λ)` (AT:303-307); `!(I)` returns `1` for `Bool` (AT:316).

Different-manifold interop (AT:244-256): `interop(op,a,b)` for `Manifold(a)≠Manifold(b)` maps both
into `Manifold(a)∪Manifold(b)` and retries. Same manifold: calls `op(a,b)` directly. (Port: require
same `V`, provide explicit embedding.)

### 2.2 Unary algebra (involutions, complements, parts)

| Function | Aliases | Defined (types) | Semantics per basis blade of grade G in N dims |
|---|---|---|---|
| `reverse` | `~` (DSgen:187 `~b = conj(b)`), `conj` | DSgen:220-233 (Submanifold, Single); prod:1816-1976 (Couple, PseudoCouple, Phasor, Chain, Multivector, Spinor, CoSpinor); DS:618-620 Zero/Infinity identity | `(-1)^{G(G-1)/2}` (`parityreverse`, Lgen:139). NOTE `conj` = `parityconj` = `parityreverse` (Lgen:142): **coefficients are NOT complex-conjugated** (verified) |
| `involute` | postfix `ˣ` | same sites | `(-1)^G` |
| `clifford` | | same sites | `(-1)^{G(G+1)/2}` = reverse∘involute |
| `antireverse` | `pseudoreverse` | DSgen:220-234 (Submanifold/Single), prod:1816 (`:antireverse` uses `pseudograde`/`antigrade`) | `(-1)^{P(P-1)/2}` with `P = N-G` (pseudograde) |
| `pseudoinvolute`,`pseudoclifford` (`antiinvolute`,`anticlifford`) | | DSgen:220-234 only (Submanifold, Single) | `(-1)^P`, `(-1)^{P(P+1)/2}` |
| `adjoint` | postfix `'` | prod:943-1070 (Chain/Multivector/Spinor/CoSpinor), prod:1113, DS:527 (Single) | maps to the dual space `V'` (labels `w¹²`) and applies complex `conj` to coefficients; for dyadic `V` also relabels bits via `dual(V,B,M)` |
| `complementright` | `!`, `complement` | AT:309-310; DSop:339-356 (Submanifold/Single); prod:1324-1487 (Chain, Multivector, Spinor, CoSpinor, Couple, PseudoCouple, Phasor) | Euclidean right complement, 4.7 |
| `complementleft` | | same | Euclidean left complement = inverse of `!` |
| `complementrighthodge` | `⋆`, `hodge`, unary `|` (AT:315) | same | `⋆a = (~a)⟑I` (verified); conjugates complex coefficients |
| `complementlefthodge` | | same | `I⟑(~a)` (verified); conjugates complex coefficients |
| `complementrightanti`, `complementleftanti` | | DSop:333-334 | `complementright(antimetric(t))`, `complementleft(antimetric(t))` |
| `metric` | | DSop:358-381 (Submanifold/Single), prod:1630-1815 (others) | lowering by diagonal metric, 4.8 |
| `antimetric` | `cometric`, `pseudometric` (AT:551) | same | metric product over the complement indices, 4.8 |
| `even` | postfix `₊` | DSop:388 (graded), par:485-501, prod:1488-1522 | keep even grades (`Spinor` result) |
| `odd` | postfix `₋` | DSop:387, par:492-501, prod:1488-1522 | keep odd grades (`CoSpinor` result) |
| `real` | | DSop:402, par:503-526, prod:1523-1629 | keep grades with `(-1)^{G(G-1)/2}=+1` (G mod 4 in {0,1}) |
| `imag` | | DSop:395, par:503-526, prod:1523-1629 | keep grades with G mod 4 in {2,3} |
| `scalar`,`vector`,`bivector`,`trivector`,`volume`(=`pseudoscalar`) | | AT:183-206, DSgen:94-103, mv:1107-1135 | grade 0/1/2/3/N part |
| `imaginary` | | mv:1136-1139 | Couple: `Single(imagvalue, B)`; PseudoCouple: `Single(realvalue, B)`; Quaternion: bivector; AntiQuaternion: vector |
| grade projection | `t(G)`, `t(Val(G))`, `grade(t,G)`, `t[G]` (Multivector/Spinor: raw `Values`) | mv:300-316,325-329,509-559,670,697,723-726; DSgen:26-29,109-113 | Chain of grade G (Zero for Spinor odd / CoSpinor even); `pseudograde(t,G) = grade(t, grade(V)-G)` |
| `isscalar`,`isvector`,`isbivector`,`istrivector`,`isvolume` | | mv:1140-1154 | `norm(t) ≈ norm(part(t))` |
| `iseven`,`isodd` | | par:465-478 | per type (Zero is both) |

### 2.3 Arithmetic, comparison, norms

| Function | Sites | Semantics |
|---|---|---|
| `+(a,b)` / `-(a,b)` | AT:294-295 -> `plus`/`minus`; prod:379-477 (Zero/Infinity), 504-703 (Couples), 852-941 (dispatch), alg:717-1151 (`adder` codegen) | coefficientwise; result type promoted (4.4) |
| `+/-` with plain numbers | prod:852-859 (`NSE = Union{Symbol,Expr,Real,Complex}`, alg:740), prod:445-448 | `a + n = iszero(n) ? a : a + n*One(V)`; `n - a = iszero(n) ? -a : n*One - a` |
| unary `-` | prod:514-520, prod:1121 (Single) | negate all coefficients; `-Submanifold` gives `Single(-1,b)`; `-Zero(V)` has NO method in Julia (MethodError, verified) - port as identity |
| scalar `*` | prod:830-851 (Real/Complex x every type), DS:519-529, prod:1093-1112 (other fields) | coefficientwise; `n*Submanifold = Single(n,b)` |
| `/(t, n::Real/Complex)` | alg:700-715 (`generate_inverses`) | `t * (1/n)` (so Int/Int -> Float64); `//` -> `t*(1//n)` |
| `==` | AT:298 -> `equal` (interop); DS:510, L.jl:89-96, mv:118-129,181-193,358-375,449-453,620-647,771-820,941-957; DS:606-613,665-673 (Zero/Infinity) | exact, basis-aware (4.13) |
| `isapprox` / `≈` | AT:229-240 (generic), mv:122-129,188-193,772-774,785-820,942-957,1103-1105; DS:512-517 | mixed element-wise / norm-based (4.13) |
| `iszero`,`isone` | AT:445-446; DS:598-599,657-658; DSgen:104-106 | `norm(t) ≈ 0`; `norm(t) ≈ value(scalar(t)) ≈ 1` |
| `abs2` | AT:437-440, mv:669,689-696,876-883, DS:622,681 | graded: `contraction(t,t)`; mixed: `(~t)⟑t` then `scalar` if `isscalar`; Couple/PseudoCouple special (4.8) |
| `abs` | AT:435-436, DSgen:89-90 | `sqrt(abs2(t))` (sqrt of scalar -> `Single`, comp:436-449) |
| `norm` | AT:443-444, Lutil:32 | Euclidean 2-norm of the raw coefficient vector (metric-blind), returns a plain number |
| `unit`, `unitize`=`counit`, `unitnorm`, `geomabs` | AT:450-480 | `t/abs(t)`, `t/value(coabs(t))`, `t/norm(geomabs(t))`, `abs(t)+coabs(t)` |
| `coabs`,`coabs2`,`coinv`,... (`co*`, `pseudo*`) | AT:532-551 | `complementleft(f(complementright(t)))` |
| `metric(a,b)`, `cometric(a,b)` | AT:368-379 | `abs(a-b)`, `pseudoabs(a-b)` |
| `norm(a,b)` | AT:366-367 | `norm(a-b)` |

### 2.4 Types (constructors relevant to this scope; full definitions in section 3)

`Submanifold{V,G,B}` (DS:252), `One{V} = Submanifold{V,0,0x0}` (DS:552), `Zero{V}` (DS:563),
`Infinity{V}` (DS:636), `Single{V,G,B,T}` (DS:457), `Chain{V,G,T}` (mv:68), `Multivector{V,T}` (mv:229),
`Spinor{V,T}` / `CoSpinor{V,T}` (= `AntiSpinor`, mv:420-456), `Couple{V,B,T}` (mv:656),
`PseudoCouple{V,B,T}` (mv:677), `Phasor{V,B,T}` (mv:852). Aliases: `Scalar{V,T}`, `GradedVector`,
`Bivector`, `Trivector` (AT:80-101), `Imaginary{V,T}=Spinor{V,T,2}`, `Quaternion{V,T}=Spinor{V,T,4}`,
`AntiQuaternion{V,T}=CoSpinor{V,T,4}`, `LipschitzInteger`, `GaussianInteger{V,B,T<:Integer}=Couple{V,B,T}`
(mv:971-975), `AbstractReal`/`AbstractComplex`/... unions (mv:979-987), `Simplex{V,T,N}=Chain{V,1,T,N}`
(mv:94), `Multiplex` (mv:277).

### 2.5 Internal (non-exported) functions defined in `algebra.jl`

| Name | Line | Role |
|---|---|---|
| `mul(a::Submanifold,b::Submanifold,der)` | alg:43-60 | basis geometric product (diag fast path / `paritygeometric` for non-diag & conformal) |
| `mul_metric(a,b,g,der)` (`@generated`) | alg:64-72 | same with metric object; emits `+(Single{V}((bits,coef))...)` via `mul_term` (alg:62) |
| `wedges(x,i)` | alg:125 | builds left-nested `∧` call expression for n-ary wedge |
| `abs2_inv(::Submanifold{V,G,B})` | alg:473 | `abs2(getbasis(V, grade_basis(V,B)))` = `<~e e>_0 = g(B)` of the blade with tangent bits stripped |
| `inv_rat` | alg:475-551 | `inv` but using `//` |
| `robust_cinv`, `robust_cinv_rev`, `cdiv`, `scaling_cdiv`, `robust_cdiv1_rev`, `robust_cdiv2_rev`, new methods of `Base.robust_cdiv1`/`Base.robust_cdiv2` with a `Val{e}` metric factor | alg:640-698 | metric-weighted robust complex division (4.10.5) |
| `generate_inverses(Mod,T)` | alg:700-715 | `/(graded_or_mixed, x::Mod.T) = a*(1/x)`, `inv(Single{..,Mod.T})`; instantiated for `Base.Real`, `Base.Complex` (alg:713-715) and external fields (G.jl:371-389) |
| `addvec`,`subvec`,`subvecs`,`conjvec`,`mulvec`,`mulvecs`,`isfixed` | alg:719-738 | choose op symbols and storage kind for codegen (4.14) |
| `NSE`, `swapper` | alg:740-742 | helpers |
| `adder(a,b,op)` + 8 typed methods, `adderspin`, `adderanti`, `addermulti` | alg:744-1071 | codegen for `+`/`-` with type promotion (4.4) |
| `product(a,b,swap,field)` | alg:1152-1225 | codegen graded x `Chain` geometric product |
| `product_contraction(a,b,swap,field,contr)` | alg:1226-1324 | codegen graded x `Chain` contraction (also `contraction2` with plain `*`, prod:1150-1155) |
| `product_∧`, `product_∨` | alg:1327-1446 | codegen graded x `Chain` exterior/regressive, incl. `V`/`V'` mixing |
| `product`, `product_∧`, `product_∨`, `product_contraction` for `Multivector`/`Spinor`/`CoSpinor` second argument | alg:1448-1558 | codegen graded x mixed with grade-window shortcuts |
| `product_sandwich` (4 families) | alg:1560-1790 | codegen for `⊘`/`>>>` with graded left side, output projected to that grade |
| `outsym`, `leftrightsym`, `product_loop`, `generate_loop_{spinor,s_m,m_s,anti,a_m,m_a,multivector,s_a,a_s}` | alg:1792-1889 | codegen mixed x mixed (Multivector/Spinor/CoSpinor pairs) |

---------------------------------------------------------------------------------------------

## 3. Data representations

### 3.1 The manifold / metric parameter `V`

Every element carries its algebra `V` as a **type parameter** (compile time). Encodings:

| Kind | Julia type | Parameters | Notes |
|---|---|---|---|
| Euclidean n-space | `Int` n, normalized to `Submanifold{n,n,2^n-1}` | n | printed `⟨111⟩`; all `e_i^2 = +1` |
| Signature | `Signature{N,M,S,F,D,L}` (DS:131) | N dims; M options; S metric bitmask (bit i-1 set ⇔ `e_i^2 = -1`); F `diffvars`; D `diffmode`; L name index | `S"-+++"` = `Signature{4,0,0x1,0,0,1}`. String parser DS:142-150 replaces `∞`->`+` and `∅`->`-` in the metric string, so `S"∅+++"` has `e_∅^2=-1` and `S"∞∅++"` = `Signature{4,3,0x2}` (∞ slot +, ∅ slot -) |
| DiagonalForm | `DiagonalForm{N,M,S,F,D,L}` (DS:193) | S = index into the global `diagonalform_cache` (DS:207-217) holding the diagonal `Values` | `D"1,2,3"`; values may be any numbers |
| MetricTensor | forms:1603 | non-diagonal | out of scope |
| Subspace | `Submanifold{V,G,B}` with non-full B used as a manifold | | e.g. `V(1,4)` printed `⟨1__1⟩` |

Options word M (DSgen:37-40): `hasinf = M%16 ∈ {1,3,5,7,9,11}`, `hasorigin = M%16 ∈ {2,3,6,7,10,11}`,
`dyadmode = -1 if M%16∈8:11, +1 if ∈4:7, else 0`, `polymode = (M&16)==0`. `hasconformal = hasinf && hasorigin`
(Lgen:53). `isdiag(Signature) = !hasconformal` (DSgen:66), `isdiag(DiagonalForm) = true`.
Projective basis vectors occupy the first slots: `∞` is index 1 when present, `∅` is index 1
(or 2 if `∞` present). Element types always store `V` normalized by `DirectSum.submanifold(V)`
(mv:70,231,424; DS:392-394), i.e. as a `Submanifold` wrapping the bundle.

Metric access used by the kernels: `V[i]` (DS:152-155 Signature -> `Bool` "is negative";
DS:219-224 DiagonalForm -> value; DS:283-300 Submanifold -> `±1` for Signature, value for DiagonalForm,
`1` for Int). `signbool(b::Bool) = b ? -1 : 1`, `signbool(x)=x` (DSop:336-337).

### 3.2 Element types

| Type | Compile-time params | Runtime payload | Length | Meaning / invariants |
|---|---|---|---|---|
| `Zero{V}` (DS:563) | V | none | 0 | additive/absorbing zero; `TensorTerm{V,0,Int}`; `value = 0` |
| `Infinity{V}` (DS:636) | V | none | 0 | absorbing infinity; `TensorTerm{V,0,Float64}`; `value = Inf` |
| `Submanifold{V,G,B}` (DS:252) | V, G, B::UInt | none | 0 | unit basis blade `e_B`, `G = popcount(B)`; `valuetype = Int`, `value = 1` |
| `One{V}` (DS:552) | alias `Submanifold{V,0,0x0}` | | | scalar unit, prints `v` |
| `Single{V,G,B,T}` (DS:457) | V, G, B (the *basis Submanifold instance*), T | `v::T` | 1 | `v * e_B`. Constructor `Single{V,G}(v,b)` returns `Zero(V)` iff `order(v)+order(b) > diffmode(V)` (tangent only). Zero values are allowed (`0v₁` prints) but `reverse/involute/...` of a zero `Single` returns `Zero` (DSgen:227) |
| `Chain{V,G,T}` (mv:68-71) | V, G, T (+ computed N = C(n,G)) | `v::Values{C(n,G),T}` | C(n,G) | homogeneous grade-G element; `v[k]` is the coefficient of `indexbasis(n,G)[k]` |
| `Multivector{V,T}` (mv:229-232) | V, T | `v::Values{2^n,T}` | 2^n | full element, grade-major layout (3.3) |
| `Spinor{V,T}` (mv:420-426) | V, T | `v::Values{2^(n-1),T}` | 2^(n-1) | even subalgebra (grades 0,2,4,...) |
| `CoSpinor{V,T}` = `AntiSpinor` (mv:420-456) | V, T | `v::Values{2^(n-1),T}` | 2^(n-1) | odd part (grades 1,3,5,...) |
| `Couple{V,B,T}` (mv:656-659) | V, B (basis Submanifold), T | `v::Values{2,T}` = (`realvalue` = scalar coefficient, `imagvalue` = coefficient of `B`) | 2 | "complex number" `re + im*B` |
| `PseudoCouple{V,B,T}` (mv:677-680) | V, B, T | `v::Values{2,T}` = (`realvalue` = coefficient of `B`, `imagvalue` = coefficient of pseudoscalar `I`) | 2 | `re*B + im*I` |
| `Phasor{V,B,T}` (mv:852-856) | V, B (angle type), T (amplitude type) | `v::T` amplitude, `ω::B` angle | | polar form; arithmetic converts via `complexify` (out of this file's core) |

`Values{N,T}` (StaticVectors) is an immutable tuple-backed vector (stack allocated); `Variables`
is its mutable twin; `FixedVector` a heap-mutable variant used for "fixed" (Big/symbolic) types.
`@computed struct` (ComputedFieldTypes) lets `Chain`'s field length be a function of `V,G`.

Julia aliases worth porting as names: `Quaternion{V,T} = Spinor{V,T,4}` (n=3),
`Imaginary = Spinor{V,T,2}` (n=2), `AntiQuaternion = CoSpinor{V,T,4}`,
`GaussianInteger{V,B,T<:Integer} = Couple{V,B,T}`. Julia prints these alias names in types
(e.g. `Quaternion{⟨111⟩, Int64}`) - cosmetic.

### 3.3 Index ordering conventions (critical)

* Basis vector `e_i` (1-based `i`) ↔ bit `i-1` of a `UInt` mask `B`. A blade is the OR of its bits;
  its canonical orientation is increasing index order `e_{i1} ∧ e_{i2} ∧ ...` with `i1<i2<...`.
* **Within a grade** blades are ordered **lexicographically by their sorted index tuples**
  (Combinatorics `combinations(1:N,G)`, Lutil:109-133,221-223), NOT by numeric mask value.
  `indexbasis(N,G)` (Lutil:225-244) is that ordered list of masks; `indexbasis(N,0) = [0]`.
  Example N=4, G=2: `v₁₂(0b0011), v₁₃(0b0101), v₁₄(0b1001), v₂₃(0b0110), v₂₄(0b1010), v₃₄(0b1100)`
  (verified: `Chain{V,2}(1,2,3,4,5,6)` prints `1v₁₂ + 2v₁₃ + 3v₁₄ + 4v₂₃ + 5v₂₄ + 6v₃₄`).
* `bladeindex(N,B)` (Lutil:181-219) = 1-based rank of `B` inside `indexbasis(N,popcount(B))`,
  `bladeindex(N,0)=1`. Closed form (0-based) for sorted indices `c_1<...<c_G`, `c_0=0`:
  `rank = Σ_{j=1..G} Σ_{t=c_{j-1}+1}^{c_j-1} C(N-t, G-j)`.
* Offsets (Lutil:135-179), all as 0-based starting offsets:
  * `binomsum(N,G) = Σ_{g<G} C(N,g)` - grade-G block start in a `Multivector`.
  * `spinsum(N,G)  = Σ_{g<G, g even} C(N,g)` - grade-G block start in a `Spinor` (G even).
  * `antisum(N,G)  = Σ_{g<G, g odd} C(N,g)` - grade-G block start in a `CoSpinor` (G odd).
  * `*_cumsum(N)` / `*_set(N)` return the vector of all these offsets (length N+2, first 0).
* Positions: `basisindex(N,B) = binomsum(N,|B|) + bladeindex(N,B)` (1-based index into
  `Multivector.v`); `spinindex = spinsum(N,|B|)+bladeindex`; `antiindex = antisum(N,|B|)+bladeindex`.
* Examples. N=3 Multivector: `[1, v₁, v₂, v₃, v₁₂, v₁₃, v₂₃, v₁₂₃]` (masks `0,1,2,4,3,5,6,7`).
  N=3 Spinor (Quaternion): `[1, v₁₂, v₁₃, v₂₃]`; CoSpinor: `[v₁, v₂, v₃, v₁₂₃]`.
  N=4 Spinor: `[1, v₁₂, v₁₃, v₁₄, v₂₃, v₂₄, v₃₄, v₁₂₃₄]`; CoSpinor: `[v₁,v₂,v₃,v₄, v₁₂₃, v₁₂₄, v₁₃₄, v₂₃₄]`.
* Couple: `v = (scalar, B)`; PseudoCouple: `v = (B, I)`.
* Caches (all global, lazily grown): `indexbasis` up to `sparse_limit=22`; `bladeindex`/
  `basisindex`/`spinindex`/`antiindex` dense up to `cache_limit=12` then per-dimension arrays up
  to `index_limit=20` then computed on demand; `binomsum` etc. up to 22; `digits_fast` up to 20;
  parity cache `parity_cache[n][s][a+1][b+1]` (Bool) for n ≤ 22, dictionary beyond (par:325-353);
  regressive/interior caches `construct_cache(:Signature/:DiagonalForm)` (par:373-439) keyed by
  `(n, metric S, options m, a, b)`.

### 3.4 Compile-time vs runtime (Julia) and what that buys

Compile time (type parameters): `V` (dimension, metric bits, projective options, tangent order),
grade `G`, basis mask `B` for `Submanifold`/`Single`/`Couple`/`PseudoCouple`, scalar type `T`,
and the *kind* of the element (Chain vs Spinor vs ...). Runtime: coefficients only.
Consequence: every product/complement method is an `@generated` function that, for small
algebras, emits one straight-line expression per output coefficient (signs, metric factors and
target indices constant-folded, some structurally-zero terms dropped). See 4.14.

### 3.5 Scalar field `T`

Any `Number` (Int, Float64, Rational, Complex, BigFloat, BigInt, Bool, GaloisFields...) or `Any`
(symbolic `Expr`/`Symbol`, Reduce/SymPy/Symbolics via extensions, G.jl:360-389). Mixed-type
operations use `promote_type(valuetype(a),valuetype(b))` (Leibniz `insert_expr` `:t`, Lutil:78).
`value(m,T)` converts the payload when `T` differs (mv:1093-1101). Division by an integer
promotes to Float64 (`1/b`). For the port: a coefficient type class (ring ops + `conj` + `isnull`)
with instances Int, Rat, Float, Complex.

---------------------------------------------------------------------------------------------

## 4. Algorithms (exact math, signs, orderings, edge cases)

Conventions for this section: `n = mdims(V)`; blades are masks `A,B ⊆ {1..n}`; `|A|` = popcount;
`g_i` = diagonal metric entry of `e_i` (`±1` for Euclidean/Signature, the stored value for
DiagonalForm; for `S"∞..."` the ∞ slot is `+1`, for `S"∅..."` the ∅ slot is `-1`);
`g(A) = Π_{i∈A} g_i` (empty product 1); `rev(G) = (-1)^{G(G-1)/2}`, `inv(G) = (-1)^G`,
`cliff(G) = (-1)^{G(G+1)/2}`; `I = e_{1..n}` (mask `2^n-1`); `<x>_k` = grade-k projection.
Everything is linear/bilinear: an operation on general elements is the (bi)linear extension of the
basis-blade kernel over coefficients, followed by Julia's result-type narrowing (4.3). Unless noted,
tangent (`diffvars≠0`) and dyadic branches are omitted (they are identity/no-ops when not tangent:
`derive_mul(V,A,B,a,b,*) = a*b`, prod:47-50; `symmetricmask(V,a,b) = (a, b, 0, 0)`, Lgen:92-97;
`diffcheck = false` except the conformal "null" check below).

### 4.1 Reordering sign (the only sign primitive)

`ε(A,B) = (-1)^{ #{(i,j) : i∈A, j∈B, j<i} }` (par:32-35 `parityjoin(N,a,b) =
isodd(sum(digits(a,N) .* cumsum(digits(b<<1,N))))`). Metric-signed variant used by `parity`
(par:33-35,327-360): `isodd(... + popcount(a & b & S))` with `S` the Signature negative mask.
Implementation (standard, O(n); Lean-flavoured):
```lean
def reorderSign (a b : UInt64) : Int := Id.run do   -- +1 / -1
  let mut s := 0; let mut x := a >>> 1
  while x != 0 do
    s := s + popcount (x &&& b); x := x >>> 1
  return if s % 2 == 0 then 1 else -1
```

### 4.2 The four basis kernels (diagonal, non-conformal metrics) - identities verified on every basis pair for ℝ2-ℝ5, `S"-"`, `S"--"`, `S"-+++"`, `S"+---"`, `S"++-"`, `D"1,2,3"`, `D"-1,2,1,1"`, `S"∞+++"`, `S"∅+++"`

1. **Geometric product** (alg:43-60; `parityinner` par:138-153):
   `e_A ⟑ e_B = ε(A,B) · g(A∩B) · e_{A⊕B}`.
   Julia return types (element manifolds are `Submanifold`-wrapped): disjoint blades (`A∩B=∅`) give the
   `Submanifold` `e_{A⊕B}` when `ε=+1` and `Single{V}(-1, e_{A⊕B})` otherwise; overlapping blades always
   give `Single{V}(coef, e_{A⊕B})` even when `coef = +1` (`v1*v1 = 1v`). For DiagonalForm with overlap the coefficient is
   `sign · |Π g|` where the sign comes from `parity(Signature(V),A,B)` (Signature(V) maps each diagonal
   entry to its sign bit), which equals `ε(A,B)·g(A∩B)`.
2. **Exterior product** (alg:127-147): `A∩B≠∅ -> 0`, else `ε(A,B) · e_{A∪B}`. Metric-free.
3. **Regressive product** (alg:156-175 -> `regressive` cache -> `parityregressivenum`/
   `_parityregressive`, par:41-63). Julia formula: with `α = ~A`, `β = ~B` (bit complements in n bits),
   if `α∩β ≠ ∅` the result is 0; else `C = α⊕β`, `L=|A|+|B|`, blade `e_{~C}` (= `e_{A∩B}`), sign
   `(-1)^{ L(L-n) + pr(A) + pr(B) + pr(C) + [ε(α,β)=-1] }` where `pr(X) = Σ_{i∈X} i + |X|(|X|+1)/2`.
   **Clean equivalent (verified):** `a ∨ b = complementleft( complementright(a) ∧ complementright(b) )`.
   Nonzero iff `A∪B = {1..n}`; result grade `|A|+|B|-n`. Metric-free.
4. **Contraction** `a⋅b` (alg:209-260 -> `interior` -> `parityinterior`, par:65-131). Julia computes
   `a ∨ ⋆b`. **Clean equivalent (verified):**
   `contraction(e_A, e_B) = [B⊆A] · rev(|B|) · ε(B,A) · g(B) · e_{A∖B}`, i.e.
   `a⋅b = < (~b) ⟑ a >_{|a|-|b|}` (zero when `|b|>|a|`). Note this is Hestenes' *left* contraction of
   the reversed right operand into the left operand; Grassmann calls it the right contraction
   (docs algebra.md:505-513; the docs' table formula `<η̃ ω>` has the roles swapped - trust the code).
   ℝ3 examples (verified): `v12⋅v1 = v₂`, `v12⋅v2 = -1v₁`, `v123⋅v12 = v₃`, `v123⋅v13 = -1v₂`,
   `v1⋅v12 = 𝟎`, `v12⋅v12 = v` (One), `v1⋅v1 = v`.
   In `S"-+++"`: `v1⋅v1 = -1v`, `v12⋅v12 = -1v`.

Degenerate metric entries (`g_i = 0`, e.g. `D"1,1,1,0"`) simply produce 0 coefficients (kept as
`Single(0,·)` in Julia).

### 4.3 Result-type narrowing (Julia) - what type a product returns

Value semantics are fully determined by 4.2; Julia additionally narrows the container type.
Verified tables (ℝ3/ℝ4/ℝ5, `probe p11`). Let `a,b` be Chains of grades `g,h` (`Chain{0}` means a
`Chain{V,0}`):

* `Chain{g} * Chain{h}`: `g=0` or `h=0` -> `Chain` of the other grade (scaled); `h=n` (b pseudoscalar)
  -> `Chain{g'}` via `⋆(~a)*b[1]` (alg:1163-1164), `g=n` -> via `complementlefthodge(~b)*a[1]`
  (alg:1165-1166); otherwise `Spinor` if `g+h` even, `CoSpinor` if odd (alg:1155-1156,1191).
  Examples ℝ3: `1*1→Spinor, 1*2→CoSpinor, 1*3→Chain{2}, 3*3→Chain{0}`.
* `Chain{g} ∧ Chain{h}`: `Chain{g+h}`; `Zero` if `g+h>n`; when both operands have grade 0 or n the
  result is a `Single` (`0∧0→Single{0}`, `0∧n→Single{n}`, `n∧0→Single{n}`), otherwise a Chain
  (`0∧1→Chain{1}`) (alg:1337-1341).
* `Chain{g} ∨ Chain{h}`: `Chain{g+h-n}`; `Zero` if `g+h<n`; `Single` when both operands have grade 0
  or n (`0∨n→Single{0}`, `n∨n→Single{n}`), otherwise a Chain (`1∨n→Chain{1}`).
* `Chain{g} ⋅ Chain{h}`: `Chain{g-h}`; `Zero` if `h>g`; grade-0 left: `Single{0}` only for `0⋅0`;
  `n⋅0→Single{n}`, `n⋅n→Single{0}` (alg:1229-1233).
* With `Multivector` on either side -> `Multivector`, except shortcuts that detect only one or two
  grades can contribute (alg:1465-1491): e.g. `M∨v₁ → Couple` (only grades n and n-1 of M
  contribute), `v₁⋅M → Couple`.
* `Spinor*Spinor→Spinor`, `Spinor*CoSpinor→CoSpinor`, `CoSpinor*CoSpinor→Spinor`, `Spinor*vector→CoSpinor`
  etc. (parity algebra; alg:1454-1456, prod:1234-1302). `∨` on spinors: parity flips when n is odd
  (prod:1303-1322). `∧` and `⋅` keep the parity rule except short-cut cases.
* Basis-level (`Submanifold`/`Single`) results stay `Submanifold`/`Single`/`Zero`.
* Conformal contraction/`abs2` of Chains returns a `Multivector` (alg:1238 `μ = istangent|hasconformal`).
Recommendation: port the value semantics exactly; port narrowing only as a typed API layer
(section 8) and compare goldens on dense coefficients (the oracle stores both the dense vector and
the Julia type name).

### 4.4 Addition / subtraction and type promotion (alg:717-1151, prod:852-941)

Coefficientwise sum; the interesting part is the **result type**. Let `a` have grade L (a term:
`Submanifold`/`Single`), `b` grade G. Conditions "plain" = `!istangent(V) && !hasconformal(V)`.

`term ± term` (alg:747-780):
1. same basis blade -> `Single{V,L}(a ± b)` (coefficient op; `Submanifold` has coefficient 1).
2. plain and `L==0` -> `Couple{V,basis(b)}(value(a), ±value(b))`.
3. plain and `G==0` -> `Couple{V,basis(a)}(±value(b), value(a))`.
4. plain and `L==grade(V)` -> `PseudoCouple{V,basis(b)}(±value(b), value(a))`.
5. plain and `G==grade(V)` -> `PseudoCouple{V,basis(a)}(value(a), ±value(b))`.
6. `L==G` -> `Chain{V,L}` with both coefficients placed.
7. both even -> `Spinor`; both odd -> `CoSpinor`; else -> `Multivector` (`adderspin/anti/multi`).

`term ± Chain{G}` same grade (alg:831-855): `Chain{V,G}` with the term's slot updated.
`term{L} ± Chain{G}` (alg:856-952): `L==0 && G==n` -> `Couple{V,I}`; `G==0` -> `Couple{V,basis(a)}`;
`G==grade(V)` -> `PseudoCouple{V,basis(a)}`; both even -> `Spinor`; both odd -> `CoSpinor`; else `Multivector`.
`term ± Multivector` -> `Multivector`; `term ± Spinor` -> `Spinor` if the term is even else
`Multivector`; `term ± CoSpinor` -> `CoSpinor` if odd else `Multivector` (alg:953-1040).
`Chain{G} ± Chain{G}` -> `Chain{G}` (alg:1056-1059). `Chain{G} ± Chain{L}`, `G≠L` (prod:880-886): if
either grade is 0 or n it is first converted to a `Single` (then term rules); if same parity ->
`multispin` of both (`Spinor`/`CoSpinor`); else `Multivector`. Same-kind mixed types add
coefficientwise; `Spinor±CoSpinor` -> `Multivector`; `Chain±Spinor` -> `Spinor` if even else
`Multivector` (prod:899-934). Couple/PseudoCouple sums (prod:530-569, 632-703): same `B` ->
componentwise; otherwise decompose into scalar/imaginary/volume parts and re-add.
Scalars: `t ± n` for `n::Union{Real,Complex,Symbol,Expr}` -> `iszero(n) ? t : t ± n*One(V)`
(prod:852-859), so `v1 + 2.5 = 2.5 + 1.0v₁ ::Couple`. Zero/Infinity (prod:379-462): `Zero` is the
identity (`Zero - x = -x`); `x + Infinity = Infinity`, `x - Infinity = Infinity` (not -∞).
Element type = `promote_type` of the operands.

`multispin(t)` (mv:999-1014): Multivector/Spinor/CoSpinor -> itself; graded -> `Spinor` if even
grade else `CoSpinor`; `Couple{B}` -> `Spinor` if `B` even else `Multivector`; `PseudoCouple{B}` ->
`Spinor` if `grade(V)` and `grade(B)` both even, `CoSpinor` if both odd, else `Multivector`.

Examples (verified): `v1+v2 = 1v₁ + 1v₂ + 0v₃ ::Chain`, `1+v12 = 1 + 1v₁₂ ::Couple`,
`v1+v12 = 0 + 1v₁ + 1v₁₂ ::Multivector`, `1+v123 = 1 + 1v₁₂₃ ::Couple{V,v₁₂₃}`,
`v1+v123 = 1v₁ + 1v₁₂₃ ::PseudoCouple{V,v₁}`, ℝ4: `1+v12+v34 ::Spinor`, `v1+v234 ::CoSpinor`,
`v12+v1234 ::PseudoCouple{V,v₁₂}`, `Chain{V,2}+Chain{V,1} ::Multivector`,
`Chain{V,1}(1,2,3,4)+Chain{V,3}(7,8,9,10) ::CoSpinor`.

### 4.5 Scalar multiplication and scalar division

`n * t`, `t * n` for `n::Real/Complex` (prod:830-851, DS:519-529): scale every coefficient
(`Submanifold` -> `Single(n,b)`; Couple scales both). `t / n` (alg:700-715): `t * (1/n)`;
`t // n`: `t * (1//n)`. `Zero * n = Zero`; `Infinity * n = Infinity`. `Chain{V,0}*t` / `t*Chain{V,0}`
with `t` a `Multivector/Spinor/CoSpinor` ERRORS in Julia (UndefVarError `input`, alg:1483 - see 4.16).
Contraction with a plain number is plain scaling on both sides (`2⋅v1 = v1⋅2 = 2v₁`, verified) unlike
contraction with the scalar blade (`v⋅v1 = 𝟎`).

### 4.6 Involutions (per blade sign; linear)

| op | factor on grade G | sites |
|---|---|---|
| `reverse` = `~` = `conj` | `rev(G)` (G mod 4 ∈ {2,3} negate) | DSgen:220-233, prod:1816-1976 |
| `involute` | `(-1)^G` | same |
| `clifford` | `cliff(G)` (G mod 4 ∈ {1,2} negate) | same |
| `antireverse` (`pseudoreverse`) | `rev(n-G)` | DSgen:220-234; prod:1816 (`antigrade`) |
| `pseudoinvolute`, `pseudoclifford` | `(-1)^{n-G}`, `cliff(n-G)` | DSgen only (basis types) |
| `adjoint` `'` | complex-conj coefficients, move to dual space `V'` | prod:943-1070 |

Couple: `Couple(re, p(grade B) ? -im : im)`; PseudoCouple: `(p(grade B) ? -re : re, p(n) ? -im : im)`
(prod:1820-1825); Phasor negates the angle when `p(grade(basis(angle)))`. `conj` never conjugates
complex coefficients (verified `conj(Chain{2}(1+2im,3,4)) = (-1-2im)v₁₂ + ...`). A Chain whose grade
has factor +1 is returned unchanged (same object). Zero/Infinity are fixed points (DS:618-620,677-679).

### 4.7 Complements and Hodge star

Right complement (`!`, `complementright`, DSop:339-356 basis; prod:1324-1487 containers):
`!e_B = s_R(B) · e_{~B}`, `s_R(B) = (-1)^{Σ_{i∈B} i + |B|(|B|+1)/2}` (`parityright`, Lgen:204,213;
DSop:295-298). Left complement: `complementleft(e_B) = (-1)^{|B|(n-|B|)} · !e_B`
(`parityleft = (odd(G) && even(n)) ⊻ parityright`, Lgen:205). They are mutual inverses:
`complementleft(!x) = x = !(complementleft(x))`, and `!!x = (-1)^{G(n-G)} x` (verified all bases).
ℝ3: `!v1=1v₂₃, !v2=-1v₁₃, !v3=1v₁₂, !v12=1v₃, !v13=-1v₂, !v23=1v₁, !v123=1v, !v=1v₁₂₃`.
ℝ4: `!v1=v₂₃₄, !v2=-v₁₃₄, !v3=v₁₂₄, !v4=-v₁₂₃, !v12=v₃₄, !v13=-v₂₄, !v14=v₂₃, !v23=v₁₄,
!v24=-v₁₃, !v34=v₁₂, !v123=v₄, !v124=-v₃, !v134=v₂, !v234=-v₁, !v1234=v`; `complementleft` flips the
odd-grade ones. Metric-independent (the "Euclidean" complement).

Hodge (`⋆`, `hodge`, `complementrighthodge`): `⋆e_B = g(B) · s_R(B) · e_{~B}`
(`parityrighthodge`, DSop:299-304) **= (~e_B) ⟑ I (verified in every signature including ∞/∅)**.
Left Hodge `complementlefthodge(e_B) = I ⟑ (~e_B) = (-1)^{G(n-G)} ⋆e_B`. Equivalently
`⋆ = complementright ∘ metric`, `⋆_left = complementleft ∘ metric` for Euclidean/Signature/DiagonalForm
(fails only on projective blades because `metric` zeroes them, see 4.8). For non-diagonal metrics or
explicit metric objects Julia uses `reverse(b)*V(I)` (DSop:347).
Complex coefficients: Hodge versions apply `conj` to coefficients (DSop:344,353; prod:1330,1350)
- plain complements do not (verified `⋆((1+2im)v1) = (1 - 2im)v₂₃`, `!` keeps `1+2im`).
Container rules (prod:1324-1487): Chain{G} -> Chain{n-G}; Multivector -> Multivector; Spinor ->
CoSpinor if n odd else Spinor; CoSpinor -> Spinor if n odd else CoSpinor; `Couple` ->
`realvalue*I + c(imaginary)` (NOTE: the scalar part is not conjugated even for Hodge);
`PseudoCouple` -> `c(volume)+c(imaginary)`; Phasor via `complexify`. Dyadic V -> error;
tangent Chain -> via Multivector.

Doc examples (verified): ℝ3 `!Multivector(1..8) = 8 + 7v₁ - 6v₂ + 5v₃ + 4v₁₂ - 3v₁₃ + 2v₂₃ + 1v₁₂₃`
(same for `complementleft`, `⋆`, `complementlefthodge` since n=3 is odd and Euclidean);
`S"++-"`: `hodge(Multivector{V}(1,…,8)) = -8 - 7v₁ + 6v₂ + 5v₃ - 4v₁₂ - 3v₁₃ + 2v₂₃ + 1v₁₂₃`.

### 4.8 Metric, antimetric, norms

* `metric(e_B)` (DSop:358-369): `g(B) · e_B` (as `Single`, even when `+1`) except: projective
  blades containing exactly one of `∞`,`∅` -> `Zero` (in `S"∞+++"`, `metric(v∞)=𝟎`); conformal or
  non-diagonal -> `complementleft(⋆b)`. Container `metric` (prod:1630-1815): coefficient `conj(c)·g(B)`
  per blade (**conjugates complex coefficients; does NOT zero projective blades** - inconsistent with
  the basis version, verified `metric(Chain{S"∞+++",1}(1,2,3,4)) = 1v∞ + 2v₁ + 3v₂ + 4v₃`); non-diagonal
  -> `contraction(metrictensor(V,G), b)`.
* `antimetric(e_B)` = `cometric` = `pseudometric`: `g(~B) · e_B` (DSop:318-320, 371-378; prod:1630);
  conformal/non-diagonal basis case calls the undefined `antimetric_term` (UndefVarError, verified).
* `abs2` (AT:437-440 and overrides):
  * graded (`Submanifold`,`Single`,`Chain`): `contraction(t,t) = <~t ⟑ t>_0` (Hermitian for complex
    coefficients: `abs2(Chain(1im,2,0)) = 5`). Returns `One`/`Single{0}`/`Chain{V,0}` (`abs2(v1+v2) = 2v ::Chain{V,0}`).
  * mixed (`Multivector`,`Spinor`,`CoSpinor`): `a = (~t)⟑t`; returns `scalar(a)` if `isscalar(a)`
    (norm-based test) else the full `a` (e.g. ℝ3 `abs2(Multivector(1..8)) = 204 + 38v₁ - 126v₂ + 154v₃`).
  * `Couple{B}` (mv:669): `re² + im²·abs2(e_B)` = `<~z z>_0` (drops the non-scalar cross term that
    appears when `B² = +1`).
  * `PseudoCouple{B}` (mv:689-696): `re²·abs2(B) + im²·abs2(I)`, plus `2·⋆B·re·im` when
    `(~B)⟑I == (~I)⟑B`; this equals the full `(~z)⟑z`.
  * `Zero -> Zero`, `Infinity -> Infinity`.
* `abs(t) = sqrt(abs2(t))`; sqrt of a scalar-graded value -> `Single(sqrt(value))` (comp:436-449),
  DomainError for negative Float; of a non-scalar -> `exp(log(t)/2)` (often errors, verified for
  `abs(Multivector(1..8))`).
* `norm(t) = norm(value(t))`: Euclidean norm of the raw coefficient vector (metric-blind); plain number.
* `abs2_inv(e_B)` (alg:473) = `abs2(e_B)` with tangent bits removed `= rev(|B|)·ε(B,B)·g(B) = g(B)`
  (because `ε(B,B) = rev(|B|)`); verified: `S"-+++"` `abs2(v1)=-1v`, `abs2(v12)=-1v`, `abs2(v23)=v`; `D"1,2,3"`
  `abs2(v12)=2v`, `abs2(v123)=6v`. Note `e_B⟑e_B = rev(|B|)·g(B)`.

### 4.9 Conformal `S"∞∅…"` (and non-diagonal) semantics

Julia treats `hasconformal(V)` as non-diagonal: products go through `paritygeometric` (par:166-254)
which splits bases into metric-coupled blocks and expands via interior products; complements use
the `P=hasinf+hasorigin` special complement and the `2`/`½` "null" factors (Lgen:215-224,233-237).
**Verified clean model:** let the stored coordinates be in the null basis `n∞ = v∞`, `n∅ = v∅`
(slots 1,2), and let `e₊,e₋` be the orthogonal basis of the underlying `Signature{…,S=0b10}` (`e₊²=+1`
slot 1, `e₋²=-1` slot 2). Define the outermorphism `T` by `n∞ ↦ e₊ + e₋`, `n∅ ↦ (e₋ - e₊)/2`, identity
on other vectors (`n∞∧n∅ ↦ e₊∧e₋`, `det T = 1`). Then for `op ∈ {⟑, ∧, ∨, ⋅}`:
`op_conf(x,y) = T⁻¹( op_orth(Tx, Ty) )` (all 1,024 basis pairs pass), and for basis blades
`!_conf = T⁻¹∘!_orth∘T`, `⋆_conf x = (~x)⟑I`, `⋆left_conf x = I⟑(~x)` (all 16 match). Concretely `T` acts
blade-wise: blades containing neither or both of `∞,∅` are fixed; for a blade `X` without `∞,∅`,
null coefficients `(a, b)` of `(n∞X, n∅X)` map to orthogonal coefficients `(a - b/2, a + b/2)` of
`(e₊X, e₋X)`; inverse `(c₊,c₋) ↦ ((c₊+c₋)/2, c₋-c₊)`.
Consequences: `v∞²=v∅²=0`, `v∞⋅v∅ = -1`, `v∞∅² = 1`, `v∞⟑v∅ = -1 + v∞∅`, `v∅⟑v∞ = -1 - v∞∅`
(tests, verified). Julia inconsistencies in conformal (do not replicate / exclude from goldens):
container `!` omits the 2/½ factors (`!Chain(1,2,3,4) ≠ Σ cᵢ !eᵢ`), container `metric` uses the Gram
lowering while basis `metric` uses `cl∘⋆`, `antimetric` errors, contraction/abs2 of Chains returns a
`Multivector` type.

### 4.10 Inverse and division

Generic: `a / b = a ⟑ inv(b)`, `a \ b = inv(a) ⟑ b` (alg:477-478; AT:320-325). `//` uses `inv_rat`
(same algorithms with `//`).

4.10.1 Basis/term (alg:536-546): `inv(One)=One`; `inv(e_B) = (rev(G)/abs2_inv(e_B)) · e_B = (rev(G)/g(B))·e_B`
(the `/` makes it Float for Int input: `inv(v12) = -1.0v₁₂`, DiagonalForm `inv(v2)=0.5v₂`,
`S"-+++"` `inv(v1) = -1.0v₁`, conformal null `inv(v∞) = Inf*v∞`); `inv(Single{V,0}) = Single(inv(v))`;
`inv(c·e_B) = (rev(G) / (abs2(e_B)·c)) · e_B`.

4.10.2 Chain (alg:482-485): `inv(a) = (~a) / value(scalar(abs2(a)))` = `~a / <~a a>_0`. Valid for
blades/versors of one grade; for a non-blade Chain the result is just `~a/|a|²` (no check).
Null vectors give `Inf`/`NaN` coefficients (verified `inv(Chain{S"-++"}(1.0,1,0)) = Inf*v₁ + Inf*v₂ + NaN*v₃`).
Complex coefficients use the Hermitian `abs2`, so `a*inv(a) ≠ 1` in general (verified).

4.10.3 Multivector / Spinor / CoSpinor (alg:486-532):
```
inv(m):
  rm = ~m ; d = rm ⟑ m ; fd = norm(d)          # Euclidean coefficient norm
  if norm(scalar(d)) ≈ fd:  return rm / scalar(d)          # d is (numerically) a scalar
  for k in grades:                                          # 1..n (Multivector), 2,4,.. (Spinor/CoSpinor)
      if norm(d[k]) ≈ fd:  return rm / d(k)                 # d is a single grade k -> Chain inverse
  error("inv($m) is undefined")
```
`≈` is `Base.isapprox` with default `rtol = sqrt(eps)`, `atol = 0`. For symbolic `T=Any` the test is
exact symbolic equality of sums of squares. Examples (verified): ℝ3
`inv(Multivector(1.0,0,0,0,0,0,0,2)) = 0.2 - 0.4v₁₂₃`; `inv(Multivector(1..8))` and
`inv(Multivector(1.0,2,0,…))` -> error "inv(...) is undefined"; ℝ4
`inv(Spinor(1.0,2,0,…)) = 0.2 - 0.4v₁₂ - 0.0v₁₃ …`, `inv(Spinor(1,0,…,0.5))` -> error (d = 1.25 + v₁₂₃₄).

4.10.4 PseudoCouple (alg:481): `inv(z) = (~z) / abs2(z)`. Phasor (alg:547-549): amplitude inverted,
angle negated. `Zero -> Infinity`, `Infinity -> Zero` (prod:405,417); `Zero / x = Zero` (NaN Single when
`x` zero), `One / Zero = Infinity`.

4.10.5 Couple (alg:553-638): scalar/Couple and Couple/scalar as expected. Let `f = abs2(e_B)` (as
Float). Generic real `T` (alg:556-577, Smith's algorithm with `f`):
```
div((a,b),(c,d)):                              # (a + bB)/(c + dB)
  if |c| <= |d|: r = (isinf(c)&&isinf(d)) ? sign(c)/sign(d) : c/d
                 den = d*f + r*c ;  return ((a*r + b*f)/den, (b*r - a)/den)
  else:          r = (isinf(c)&&isinf(d)) ? sign(d)/sign(c) : d/c
                 den = c + (r*d)*f ; return ((a + (b*r)*f)/den, (b - a*r)/den)
inv((c,d)) generic (alg:607-612):  if isinf(c)|isinf(d): return (copysign(0,c), flipsign(-0,d))
                 e = c*c + d*d*f ; return (c/e, rev(|B|) ? -d/e : d/e)
```
`Float64` (alg:591-605, 615-637, 640-698) ports Julia Base's robust complex division
(Baudin-Smith, arXiv:1210.4539) with the metric factor `f` spliced in:
```
div64((a,b),(c,d)):
  ab = max(|a|,|b|); cd = max(|c|,|d|)
  halfov = 0.5*floatmax; twounϵ = floatmin*2/eps; f = Float64(abs2(e_B))
  if ab>=halfov || ab<=twounϵ || cd>=halfov || cd<=twounϵ:
      (a,b,c,d,s) = Base.scaleargs_cdiv(a,b,c,d,ab,cd); (p,q) = cdiv(a,b,c,d,f); return (p*s,q*s)
  return cdiv(a,b,c,d,f)
cdiv(a,b,c,d,f): if |d|<=|c|: (p,q) = cdiv1(a,b,c,d,f)
                 else (p,q) = cdiv1rev(b,a,d,c,f); q = -q
cdiv1(a,b,c,d,f):    r=d/c; t=1/(c+(d*r)*f); p=cdiv2(a,b,c,d,r,t,f); q=cdiv2b(b,-a,c,d,r,t)
cdiv1rev(a,b,c,d,f): r=d/c; t=1/(c*f+d*r); p=cdiv2rev(a,b,c,d,r,t,f); q=cdiv2b(b,-a,c,d,r,t)
cdiv2(a,b,c,d,r,t,e):    r≠0 ? (b*r≠0 ? (a+(b*r)*e)*t : a*t+((b*t)*r)*e) : (a+(d*(b/c))*e)*t
cdiv2rev(a,b,c,d,r,t,e): r≠0 ? (b*r≠0 ? (a*e+b*r)*t : (a*t)*e+(b*t)*r) : (a*e+d*(b/c))*t
cdiv2b(a,b,c,d,r,t):     r≠0 ? (b*r≠0 ? (a+b*r)*t : a*t+(b*t)*r) : (a+d*(b/c))*t      # Base.robust_cdiv2
Base.scaleargs_cdiv (julia base/complex.jl:429-449): bs=2/eps^2; s=1
  if ab>=halfov: a*=0.5;b*=0.5;s*=2  elif ab<=twounϵ: a*=bs;b*=bs;s/=bs
  if cd>=halfov: c*=0.5;d*=0.5;s*=0.5 elif cd<=twounϵ: c*=bs;d*=bs;s*=bs
inv64((c,d)):  if isinf(c)|isinf(d): return Complex(copysign(0.0,c), flipsign(-0.0,d))   # BUG: returns Base.Complex
  cd = max(|c|,|d|); s=1
  if cd >= floatmax/2: c*=0.5; d*=0.5; s=0.5   elif cd <= 2floatmin/eps: c*=bs; d*=bs; s=bs
  if |d| <= |c|: (p,q) = cinv(c,d,f) else (q,p) = cinvrev(-d,-c,f)
  return (p*s, q*s)
cinv(c,d,f):    r=d/c; p=1/muladd(d, r*f, c); q=-r*p
cinvrev(c,d,f): r=d/c; p=1/muladd(d, r, c*f); q=-r*p
```
Integer Couples are converted to Float (alg:613). Float16/Float32 go through `widen`, which is
broken (`widen(re, widen(im))`, mv:831) -> MethodError (verified).
**Correctness caveat (verified):** these formulas compute `(c - dB)/(c² + f d²)`, the true inverse
only when `B² = -f`, i.e. `rev(|B|) = -1` (grades ≡ 2,3 mod 4). For `B` with `B² = +f`
(grade ≡ 0,1 mod 4, e.g. `1+2v1` in ℝ3, `1+2v1234` in ℝ4, `1+2v1` in `S"-+++"`) Julia's `inv` and
`/` are WRONG (`(1+2v1)*inv(1+2v1) = -0.6`). The correct general formula is
`inv(c + dB) = (c - dB)/(c² - d²·B²)` with `B² = value(e_B⟑e_B)`; `⟑` on Couples is correct
(prod:573-575 uses `value(B⟑B)`).

4.10.6 `generate_inverses` (alg:700-715): for each registered field type `T` (Real, Complex, plus any
`generate_algebra` extension): `a / b::T = a * (1/b)`, `a // b::T = a*(1//b)`,
`inv(Single{V,G,B,T})` as 4.10.1.

### 4.11 Powers

* `literal_pow` (alg:408-419, used when the exponent is a literal): `x^0 = one(x)`, `x^1 = x`,
  `x^2 = x*x`, `x^3 = x*x*x`, `x^-1 = inv(x)`, `x^-2 = (i=inv(x); i*i)`; for Float scalars
  (`Scalar{V,<:AbstractFloat}`, `Chain{V,0,<:AbstractFloat}`) other literal `p` use `x^p` on the value.
* Term (alg:424-438): `i==0 -> getbasis(V,0)` (One); `i==1 -> v`; else `j = (i-1) % 4`,
  `out = e_B^{j+1}` by repeated `⟑`, times `value(v)^i` for `Single`. **Bug:** the period-4 shortcut is
  only valid when `e_B² = ±1`; wrong for DiagonalForm (`D"1,2,3"`: `v2^5 = v₂`, true `4v₂`) and null
  vectors (`v∞^5 = v∞`, true 0) (verified). Negative runtime exponents: `j<0` -> `out = nothing`
  (verified `v12^(-1)` returns `nothing`); Int value with negative power -> DomainError.
* General `TensorAlgebra` (alg:440-469): `isone(i) -> v`. If `v::Chain` and `n ≤ 3` (non-tangent):
  `sq = contraction2(~v, v)` (a contraction with plain `*`, prod:1150-1152; equals `v⟑v` for vectors,
  bivectors and trivectors in ≤3D), `d = i ÷ 2`, `val = d==1 ? sq : sq^d`, return
  `i%2==0 ? val : val*v`. If `Couple` with `value(B⟑B) == -1`: `Couple(Complex(v)^i)` (Complex power).
  Else `out = One(V)`; if `i < 8`: multiply `i` times; else binary exponentiation over the bits of
  `i` (`indices(UInt(i))`). **Bugs:** `i ≤ 0` returns `One(V)` (`m^0` ok but `m^-1 = One`), and the
  Chain path returns `v` for `i=-1` (verified `Chain(1,2,3)^n` with `n=-1` gives `1v₁ + 2v₂ + 3v₃`).
  Port: `x^n = n≥0 ? repeated/binary product : inv(x)^(-n)`.
* `Phasor^n` (alg:422-423): amplitude^n, angle*n. `number^t = exp(t*log(number))` (AT:326).
* Zero/Infinity powers (prod:463-477): `x^Zero = One`; `Zero^0 = One`, `Zero^n = Zero` for n>0,
  `Infinity` for n<0; `Infinity^n` mirrors; `|s|^∞` -> `One/Zero/∞` by `|s|` vs 1.

### 4.12 Sandwich products

Generic (alg:313-316,351-354): `x ⊘ y = reverse(y) ⟑ x ⟑ involute(y)`; `y >>> x = y ⟑ x ⟑ clifford(y)`;
Couple/PseudoCouple on the "sandwiched" side are split into parts and each part sandwiched.
Generated (`product_sandwich`, alg:317-341,355-379,1560-1790) when the sandwiched element `x` is
`TensorGraded{V,G}` and the versor `y` is `Spinor`, `CoSpinor`, `Couple`, `PseudoCouple` or
`TensorGraded` (but not when both are basis terms - `⊘(::TensorTerm,::TensorTerm)` is more specific
and generic): computes the same product as `clifford(y)⟑x⟑y` for `⊘` (equal to
`reverse(y)⟑x⟑involute(y)` for homogeneous-parity `y`) or `y⟑x⟑clifford(y)` for `>>>`, then
**returns only the grade-G part as `Chain{V,G}`** (alg:1614-1615,1730-1731,1785-1786). No
normalization: `v1 ⊘ (v1+v2) = 0v₁ - 2v₂ + 0v₃`. `x::Chain` with `y::Multivector` is generic (full,
unprojected). N ≥ 12: generated sandwich returns `nothing` (the large-N branch is commented out).
Couple versor with odd `B` (or PseudoCouple with `grade(B)` parity ≠ n parity) -> converted by
`multispin` first (alg:1748-1752). All generic vs projected cases above pass `ref_check.py`.
Examples (verified ℝ3): `v1 ⊘ v2 = 1v₁`, `(v1+v2) ⊘ v12 = -1v₁ - 1v₂ + 0v₃`, `v12 >>> v1 = -1v₁`,
`Chain(1,2,3) ⊘ (1.0+1.0v12) = -4.0v₁ + 2.0v₂ + 6.0v₃`, `(1.0+1.0v12) >>> Chain(1,2,3) = 4.0v₁ - 2.0v₂ + 6.0v₃`,
`Chain(1,2,3) ⊘ Chain(0,1,1) = 2v₁ - 6v₂ - 4v₃`, `Chain(1,2,3) ⊘ CoSpinor(1.0,2.0,3.0,4.0) = -30.0v₁ - 60.0v₂ - 90.0v₃`,
`exp(π/4*v12) >>> v1 = 2.22045e-16v₁ - 1.0v₂ + 0.0v₃`.

### 4.13 Equality and approximate equality

* `a == b` (AT:298) -> `equal`, basis-aware and exact:
  * same-grade terms (DS:510): same blade -> values equal; different blades -> both values zero;
    different grades (L.jl:96): `0 == value(a) == value(b)`.
  * `Chain == Chain` same grade (mv:126): elementwise `==`; different grades: both all-zero (mv:127).
  * `Chain == term` (mv:181-186): matching slot equal and every other slot zero; `term == Chain` symmetric.
  * `Multivector == Multivector`: elementwise; `Multivector == Chain`: embedded (mv:358-364).
  * `Multivector == term` (mv:365-368) indexes `2<<n` -> out-of-bounds crash (process abort with
    `@inbounds`, verified) - bug; correct bound is `1<<n`.
  * Spinor/CoSpinor comparisons (mv:449-453,620-639); with Multivector via conversion.
  * Couple: same `B` componentwise; different `B`: real parts equal and both imag zero (mv:771,787);
    with terms/containers via `multispin` (mv:785-820).
  * Numbers (L.jl:89-96, mv:118-125,370-375,640-647,776-783): `n == t` iff scalar part equals `n`
    and the rest is zero. `Multivector == Number` errors (UndefVarError `V`, mv:372 - bug).
  * `Zero == x` iff `iszero(x)`; `Infinity == x` iff `isinf(norm(x))` (DS:606-613,665-673).
* `isapprox` (≈):
  * generic `TensorAlgebra` (AT:229-232): `norm(a-b) ≤ max(atol, rtol*max(norm(a),norm(b)))`,
    finite norms required, `rtol = rtoldefault(valuetype)` (sqrt(eps) floats, 0 ints).
  * `TensorGraded` pair (AT:233-240): same manifold required; same rank -> as above; different rank
    -> both `isnull`.
  * Chain/Chain same grade (mv:128): **elementwise** `≈` (so `0 ≈ 1e-20` is false); different grades:
    all ≈ 0. Chain vs term (mv:188-193): slot ≈ and exact zeros elsewhere; `term ≈ Chain` is exact `==`.
  * Multivector/Spinor/CoSpinor pairs (mv:1103-1105): same manifold and vector `≈` (norm-based).
  * Couple/PseudoCouple (mv:772-774,785-820): componentwise; PseudoCouple different-B version has a
    typo (`realvalue(a)≈imagvalue(b)≈0`).
  * With plain numbers (DS:512-517): convert the number to `Single{V}` then generic.
* `iszero(t) = norm(t) ≈ 0` (effectively exact zero for floats), `isone(t) = norm(t) ≈ value(scalar(t)) ≈ 1`.

### 4.14 Code generation patterns (how Julia gets its speed) - alg:717-1889, prod:15-358

1. **Everything algebraic is decided at compile time.** `@generated` methods receive types only;
   the generator (`adder`, `product`, `product_contraction`, `product_∧/∨`, `product_sandwich`,
   `generate_loop_*`) runs the combinatorics (blade lists, signs, metric factors, target indices) and
   returns a Julia expression.
2. **Small algebras are fully unrolled.** The generator allocates `out = FixedVector{K,Any}` filled
   with zeros, then for every pair of basis blades calls a `*_pre` mutator (prod:150-358:
   `geomaddmulti!_pre`, `geomaddspin!_pre`, `geomaddanti!_pre`, `skewaddblade!_pre`,
   `exteraddblade!_pre`, `meetaddblade!_pre`, `joinadd*_pre`, `setblade!_pre`, ...), which does NOT
   compute; it appends the symbolic term `MUL(sign*metric, a_i*b_j)` to the expression in output slot
   `k` (`pre_val`, prod:137: first term creates `∑(term)`, later ones `push!` into its args). Where the
   generator can see a structural zero (e.g. `isnull` checks at par:109, alg:1602,1713) the term is
   skipped; otherwise zero coefficients are simply multiplied. The returned code is
   `Chain{V,G}(Values{K,t}(∑(...), ∑(...), ...))`: straight-line, SIMD-friendly, no branches, no loops.
3. **Thresholds** (`cache_limit = 12`, Lutil:106):
   * graded x Chain products/contractions: unroll iff `C(n,G)·(left is Chain ? C(n,L) : 1) < 4096`
     (alg:1167,1235,1342).
   * graded x Multivector/Spinor/CoSpinor: unroll iff `n < 12` (alg:1492).
   * mixed x mixed (`generate_loop_*`, prod:1202-1300): unroll iff `n < 6` (`cache_limit/2`, alg:1846,1829).
   * adders: Chain `C(n,G) < 4096`, spin/anti `n-1 < 12`, multi `n < 12`; complements/involutions:
     Chain `C(n,G) < 4096`, others `n < 12`.
   * `product_sandwich`: only the unrolled branch exists (n < 12).
4. **Large algebras use runtime loops** over the same kernels with mutable `Variables` (`mvec`) and
   cached parity tables; `if coefficient ≠ 0` skipping gives sparse-input speedups; for tangent
   algebras a `Bool` return from the mutator signals promotion of the accumulator to `Any`
   (`insert_expr((:out,);mv=:out)` converts `out` to `FixedVector{Any}`), otherwise ignored.
5. **Grade-window shortcuts** before generating (alg:1465-1491,1158-1166,1229-1233,1337-1341):
   results that are provably zero return `Zero(V)` at compile time; one or two contributing grades
   are dispatched to the smaller Chain kernels; pseudoscalar operands use `⋆`/`complementlefthodge`
   identities (`a⟑(βI) = β·⋆(~a)`... see 4.3).
6. **Storage selection** (alg:719-738): `isfixed(T)` true for BigFloat, BigInt, Rational{BigInt},
   Complex{Big*}, and non-`Number` types -> `svec` (`FixedVector`, heap) and symbolic `∑/∏/-` ops;
   otherwise `mvec` (`Variables`, stack) and native `+ * -`. `mulvec(a,b,:contraction)` uses `dot`
   (conjugating) instead of `*` for contractions of graded operands (alg:727-730); the mixed x mixed
   loops always use `*` (prod:1204) - hence Multivector⋅Multivector does NOT conjugate complex
   coefficients while graded⋅graded does (verified).
7. **Parity/metric caches** (par:325-439) are global mutable tables indexed by `(n, metric bits, a, b)`
   filled on first use (the generators consult them at compile time; runtime loops at run time).
8. **Metric-object variants** (`field=true`): the generator emits `value(value(g))[i]` lookups
   instead of constant metric factors (par:90-106,141-145) so `g` may vary at runtime.

### 4.15 Complex-coefficient policy (summary, verified)

`⟑`, `∧`, `∨`, `!`, `complementleft`, `reverse`/`conj`/`involute`/`clifford`: bilinear/linear, no
conjugation. `⋆`, `complementlefthodge`, `metric` (containers), `adjoint`: conjugate coefficients.
`contraction` on graded operands (Single/Chain, graded x mixed): conjugates the LEFT coefficient
(`dot(x,y) = conj(x)*y`; `contraction(1im*v1, v1) = (0 - 1im)v`), mixed x mixed: no conjugation.
`abs2` of graded: Hermitian. `inv(Chain)` with complex coefficients is therefore not a true inverse.

### 4.16 Known upstream bugs / quirks (do not replicate; exclude from goldens or mark)

| # | Site | Symptom (verified unless noted) | Correct behavior for the port |
|---|---|---|---|
| 1 | alg:294,301 | `⊙`, `⊠` -> UndefVarError `permutations` | symmetrize / antisymmetrize over `S_k` with sign `indexparity!` |
| 2 | alg:23 | `⟂` exported, undefined | omit or define as `iszero(a⋅b)` (decide) |
| 3 | alg:397 | `antidot_metric(a,b)` uses undefined `g` | take `g` argument |
| 4 | alg:424-438 | term powers via period 4: wrong for `|g|≠1`, null; negative -> `nothing` | `e^n = (e²)^{⌊n/2⌋} e^{n mod 2}`, negatives via `inv` |
| 5 | alg:440-469 | `m^n`, n ≤ 0 -> One; Chain `^(-1)` -> itself | `inv(m)^(-n)` |
| 6 | alg:553-637 | Couple `inv`, `/` wrong when `B² = +abs2(B)` (grades ≡ 0,1 mod 4) | `(c-dB)/(c²-d²B²)` |
| 7 | alg:579-583, mv:831 | Float16/32 Couple inv/div -> MethodError (`widen`) | compute in Float64, round |
| 8 | alg:617 | `inv(Couple(Inf,·))` returns `Base.Complex` | return Couple |
| 9 | alg:1483 | `Chain{V,0} ⟑ Multivector/Spinor/CoSpinor` (both orders) -> UndefVarError `input`; also breaks `veedot` of grade-n chains with mixed types and some sandwiches | scalar multiply |
| 10 | alg:1616-1654,1732,1787 | generated sandwich for n ≥ 12 returns `nothing` | generic formula |
| 11 | alg:189 | `∨(::Chain{V,1,<:Chain})` computes `∧` | decide (probably intended `∨` of the list) |
| 12 | prod:558 | `PseudoCouple ± PseudoCouple` real part uses `imagvalue(b)` | componentwise |
| 13 | prod:778-783 | `Couple ∨ term` drops `scalar(a) ∨ I` | full bilinear |
| 14 | prod:767-768 | `∨(::TensorTerm{V,0},::Couple)` references undefined `B` | fix |
| 15 | prod:618 | `contractn` typo in `contraction(::Couple,::PseudoCouple)` | `contraction` |
| 16 | prod:651 | `Subamnifold` typo in `plus(::TensorTerm,::PseudoCouple)` (pseudoscalar branch) | fix |
| 17 | prod:400-402 | `Zero / n::Int` ambiguous MethodError | `Zero` |
| 18 | DS (no method) | `-Zero(V)` MethodError | identity |
| 19 | mv:367 | `Multivector == term` out-of-bounds (`2<<n`) crash | `1<<n` |
| 20 | mv:372 | `Multivector == Number` UndefVarError `V` | fix |
| 21 | mv:405 | `Multivector[e_B]` uses grade getter -> BoundsError | index by `basisindex` |
| 22 | mv:774 | PseudoCouple ≈ typo | componentwise |
| 23 | mv:1124 | `trivector(::Couple)` calls undefined `imaginarya` | `imaginary` |
| 24 | DSop:372 | `antimetric` on conformal/non-diag basis: `antimetric_term` undefined | define |
| 25 | prod:1324-1487 vs DSop | conformal container `!`/`metric` disagree with basis versions (4.9) | use the T-conjugated model everywhere |
| 26 | n=1 | generated sandwich and `Multivector(CoSpinor)` crash for n=1 (`@inbounds` OOB) | handle n=1 |
| 27 | mv:300-305 vs 544 | `Spinor(G)` for odd G returns a zero `Chain`, `Spinor(Val(G))` returns `Zero` | pick one |
| 28 | 4.13 | Chain ≈ is elementwise with atol=0; Multivector ≈ is norm-based | decide (recommend norm-based everywhere) |
| 29 | alg:918,1037 | `addpseudo` referenced but undefined (CoSpinor adder, n ≥ 13 loop path) (not run) | `addanti!` |

---------------------------------------------------------------------------------------------

## 5. Display / printing rules (exact)

Building blocks (Leibniz `Lidx:139-203`, `L.jl:63-73`, Grassmann `mv:34-58`, DirectSum `DS:175-189,
226-243,325-356,488,604,663`):

* **Blade label** `printindices(io,V,B)`: prefix `"v"` (vectors; `"w"` for dual/covector spaces,
  `"∂"`, `"ϵ"` for tangent) followed by one character per index (after `shift_indices`). The scalar
  blade prints as just `v`. Index characters for prefix `v`: `i=1..9 -> ₁…₉`, `10 -> ₀`,
  `11..36 -> a..z` (from `"1234567890abcdefghijklmnopqrstuvwxyzABC…"[i]`), `i>36 -> ` superscript table
  at `i-26`; dual prefix `w` uses superscripts `¹²³…⁰` then letters. Projective shift
  (`Lidx:122-132`): with `∞` present, index 1 prints `∞`; with `∅` present, the next index prints
  `∅`; remaining indices are shifted down by `hasinf+hasorigin`. Examples (verified): ℝ12 blade of
  all indices `v₁₂₃₄₅₆₇₈₉₀ab`; `e₁₀` alone `v₀`; `S"∞∅++"` blades `v∞, v∅, v₁, v₂, v∞∅, v∞₁, …, v∞∅₁₂`.
* **`showvalue(io,V,B,x)`** (Lidx:195-203): if `showparens(typeof(x))` (x is `Complex`, `Rational`,
  `Expr`, or a non-term `TensorAlgebra`; Lidx:185, L.jl:63-73) print `"(" x ")"`, else `show(io,x)`
  followed by `showstar`: `"⊗"` if `x` is a `TensorAlgebra`, `"*"` unless `x` is a non-Bool `Integer`
  or a finite `AbstractFloat`; then the blade label. So `2v₁`, `-1v₁₂`, `2.5v₁`, `(1//2)v₁`,
  `(1 + 2im)v₁₂`, `true*v₁`, `NaN*v₁`, `Inf*v∞`, `-0.0v₁`.
* **`showterm(io,V,B,x,compact)`** (mv:46-58): if `x::Real`, `signbit(x)` and not NaN:
  print `" - "` (`"-"` if compact) then `showvalue` of `-x` (with `typemin(Int)` widened);
  otherwise `" + "` (`"+"`) then `showvalue(x)`. Complex never takes the minus branch.
* **Compact numbers**: containers print their coefficients through `compactio(io) =
  IOContext(io, :compact=>true)` (mv:39-44, toggle `compact()` default true), but the separators
  use the *original* io's `:compact` (so `repr` gives `" + "` with spaces; inside a `Vector` display
  `"+"`/`"-"` without spaces, e.g. `1v₁-2v₂+3v₃`). Julia compact Float64 = shortest round-trip rounded
  to 6 significant digits, scientific when the decimal exponent is < -4 or ≥ 6 after rounding
  (verified table):

  | value | full `show` | compact |
  |---|---|---|
  | 0.1+0.2 | `0.30000000000000004` | `0.3` |
  | 1/3 | `0.3333333333333333` | `0.333333` |
  | 2/3 | `0.6666666666666666` | `0.666667` |
  | 12345.6789 | `12345.6789` | `12345.7` |
  | 99999.5 | `99999.5` | `99999.5` |
  | 123456.0 | `123456.0` | `123456.0` |
  | 123456.789 | `123456.789` | `1.23457e5` |
  | 1e5 / 1e6 | `100000.0` / `1.0e6` | `100000.0` / `1.0e6` |
  | 1e15 / 1e16 / 1e20 | `1.0e15` / `1.0e16` / `1.0e20` | same |
  | 1e-4 / 1.234e-5 / 1e-7 | `0.0001` / `1.234e-5` / `1.0e-7` | same |
  | 3.14159265 / sqrt(2) | `3.14159265` / `1.4142135623730951` | `3.14159` / `1.41421` |
  | 2.220446049250313e-16 | | `2.22045e-16` |
  | 5.0e-301, Inf, -Inf, NaN, -0.0 | same | same |
  | 1//2, -3//4 | `1//2`, `-3//4` | same |
  | 1+2im, 1.5-2.5im | `1 + 2im`, `1.5 - 2.5im` | `1+2im`, `1.5-2.5im` |
* **Per type**:
  * `Submanifold` basis: label only (`v₁₂`, `v`). As a manifold: `⟨111⟩` (Euclidean), `⟨-+++⟩`,
    `⟨1,2,3⟩` (DiagonalForm), `⟨∞∅++⟩`, subspace `⟨1__1⟩`; dual adds `'`, dyadic `*`, tangent prefix
    `T¹⟨…⟩`. `Λ(V)` prints `DirectSum.Basis{⟨111⟩,8}(v, v₁, v₂, v₃, v₁₂, v₁₃, v₂₃, v₁₂₃)`.
  * `Zero` -> `𝟎` (U+1D7CE); `Infinity` -> `∞`; `One` -> `v`.
  * `Single` (DS:488): `showvalue` with the non-compact io: `-1v₁₂`, `1.123456789v₁`, `0.16666666666666666v₂₃`,
    `(1 + 2im)v₁₂`, `(-1//2)v₁`, scalar blade `2v`, `1.0v`.
  * `Chain` (mv:109-116): first coefficient via `showvalue` (sign kept, e.g. `-1v₁`), the rest via
    `showterm`; **all** `C(n,G)` coefficients are printed including zeros:
    `1v₁ + 2v₂ + 0v₃`, `-1v₁ + 2v₂ - 3v₃`, `0.0714286v₁ + 0.142857v₂ + 0.214286v₃`, `(1+2im)v₁ + (0-3im)v₂`,
    `(-1//2)v₁ + (1//3)v₂`, `true*v₁ + false*v₂ + true*v₃`, `-0.0v₁ + 1.0v₂ + NaN*v₃`, `-1.0v₁ + Inf*v₂ - Inf*v₃`,
    `-9223372036854775808v₁ + 2v₂`, scalar chain `14v`.
  * `Multivector` (mv:340-356): `print(io, v[1])` (bare scalar, compact, no label), then only the
    **nonzero** (`!isnull`) basis coefficients via `showterm`; if none: `showstar(v[1])` then `v⃖`
    (`v` + U+20D6). E.g. `1 + 2v₁ + 3v₂ + …`, `0 + 1v₁ + 1v₁₂`, `-1 + 2v₁₂`, `0v⃖`, `1.0v⃖`, `-1v⃖`,
    `1+1im*v⃖`, `1//2 + (1//1)v₁ + …`, `1.0 - 2.5v₃`.
  * `Spinor` (mv:589-600): bare scalar then **all** even-grade (≥2) coefficients via `showterm`:
    `1 + 2v₁₂ + 3v₁₃ + 4v₂₃`, `1.0 + 0.0v₁₂ + 0.0v₁₃ + 0.0v₂₃`, `-1 + 0v₁₂ + 2v₁₃ + 0v₂₃`.
  * `CoSpinor` (mv:601-615): first coefficient via `showvalue`, the rest via `showterm`, all printed:
    `2v₁ + 3v₂ + 4v₃ + 8v₁₂₃`, `0v₁ - 1v₂ + 2v₃ + 0v₁₂₃`, `-1v₁ + 0v₂ + 0v₃ + 0v₁₂₃`.
  * `Couple` (mv:757-761): `show(io, re)` (non-compact) + `showterm(io,V,B,im)`: `3.0 + 4.0v₁₂`,
    `1 + 1v₁₂`, `-1 - 2v₁₂`, `-0.0 - 0.0v₁₂`, `1.4142135623730951 + 1.0v₁₄`.
  * `PseudoCouple` (mv:762-766): `showvalue(re at B)` + `showterm(im at I)`: `1v₁ + 1v₁₂₃`,
    `-1v₁₂ - 2v₁₂₃`, `-1.5v₁ - 2.5v₁₂₃`.
  * `Phasor` (mv:931-934): `amplitude ∠ angle` (`∠` without spaces when compact).
  * Julia type strings (for the oracle `type` field only): `Chain{⟨111⟩, 1, Int64, 3}`,
    `Quaternion{⟨111⟩, Int64}`, `GaussianInteger{⟨111⟩, v₁₂, Int64}`, `Multivector{⟨111⟩, Int64, 8}`.
* Product results that are `+1` on disjoint blades are `Submanifold` (print `v₁₂`), while overlapping
  blades always produce a `Single` (print `1v`, `1v₂`) even when the coefficient is +1 (alg:49-53).
  Contraction with coefficient +1 returns the `Submanifold` (`v12⋅v12 = v`, `v12⋅v1 = v₂`).

---------------------------------------------------------------------------------------------

## 6. Golden examples (verbatim; all re-run on the oracle)

### 6.1 From the Grassmann test suite (`test/runtests.jl`, `test/issuestests.jl`, `test/generictests.jl`)

The whole suite passes on the oracle env (verified: every testset green, 19,061 assertions incl.
18,998 generic-law checks over `[3, V"+++", S"∞+", S"∅+", V"-+++", S"∞∅+"]`).

```julia
@basis "++++" s e;  e124 * e23 == e134            # prints 1v₁₃₄
[Λ(3).v32^2, Λ(3).v13^2, Λ(3).v21^2] == [-1Λ(3).v for j∈1:3]   # Λ(3).v32 == -1v₂₃, Λ(3).v21 == -1v₁₂
@basis "++++"; (v1*v1, v1⋅v1, v1∧v1) == (1,1,0)
@basis "-+++"; (v1*v1, v1⋅v1, v1∧v1) == (-1,-1,0); (v2*v2, v2⋅v2, v2∧v2) == (1,1,0)
basis"-+++"; h = 1v1+2v2; h⋅h == 3v                # 3v ::Chain{⟨-+++⟩,0}
Λ(62).v32a87Ng == -1Λ(62).v2378agN                  # label parsing / reorder sign at n=62
# Issue 19 (S"∞∅++"): (v∞^2, v∅^2, v1^2, v2^2) == (0v, 0v, v, v); v∞⋅v∅ == -1v; v∞∅^2 == v
#   (v∞∅*v∞, v∞∅*v∅) == (-1v∞, v∅); (v∞*v∅, v∅*v∞) == (-1 + 1v∞∅, -1 - 1v∞∅)
# Issue 20 (S"∞∅+"): v∅*v∞ == -1 - v∞∅; v∅*(-v∞) == 1 + v∞∅
# Issue 17 (basis"2"): a = v + v1 - v1; a == v; typeof(a) <: Couple; a == 1; a - 1 == 0
# Issue 16: A = 2v1 + v2; B = v1 + v2; A + B == 3v1 + 2v2; v1 + A == 3v1 + 1v2
# Issue 14 (basis"+++"): (v1+v2) + (v1+v2)*(v1+v2) == 2 + 1v1 + 1v2
# Issue 22 (basis"++"): typeof(v1+v2) <: Chain; Multivector(v1+v2) == v1 + v2; Chain(v) == v
# generictests: for G in [3, V"+++", S"∞+", S"∅+", V"-+++", S"∞∅+"] and random Float64 multivectors:
#   e*A == A == A*e; a^2 ≈ scalar(a^2)*basis[1] (vectors); associativity; distributivity;
#   a⋅b == 0.5(ab+ba); a∧b == 0.5(ab-ba); ab == a⋅b + a∧b; ab == 2a⋅b - ba; aa == a⋅a  (vectors a,b)
# isapprox tests (basis"2"): v ≈ v, v1 + v2 ≈ v1 + v2, !(v ≈ v1), !(2v ≈ v1+v12), !(v1+v2 ≈ v+v1+v12) ...
# scalar tests: scalar(v) == 1v; scalar(2v) == 2v; scalar(v1) == 0v; scalar(-v+v1) == -1v; scalar(v1+v2) == 0v
```

### 6.2 From the docs (`docs/src/algebra.md`), re-verified

```
Chain(1,2,3)*Chain(4,5,6)            => 32 - 3v₁₂ - 6v₁₃ - 3v₂₃          ::Quaternion{⟨111⟩, Int64}
wedge(Chain(1,2,3),Chain(4,5,6))     => -3v₁₂ - 6v₁₃ - 3v₂₃              ::Chain{⟨111⟩, 2, Int64, 3}
G4 = Λ(Submanifold(4)); G4.v12 + 2G4.v14 => 1v₁₂ + 0v₁₃ + 2v₁₄ + 0v₂₃ + 0v₂₄ + 0v₃₄
sqrt(2) + Λ(V(1,4)).v14              => 1.4142135623730951 + 1.0v₁₄       ::Couple{⟨1__1⟩, v₁₄, Float64}
Spinor{Submanifold(3)}(1,2,3,4)      => 1 + 2v₁₂ + 3v₁₃ + 4v₂₃
basis"3"; 1 + v12 - v13              => 1 + 1v₁₂ - 1v₁₃ + 0v₂₃            ::Quaternion{⟨111⟩, Int64}
wedge(!v12,!v23)                     => -1v₁₃
!vee(v12,v23)                        => -1v₁₃
wedge(v12,!v12)                      => 1v₁₂₃
complementright(Multivector(1,…,8))  => 8 + 7v₁ - 6v₂ + 5v₃ + 4v₁₂ - 3v₁₃ + 2v₂₃ + 1v₁₂₃
complementleft / complementrighthodge of the same => identical output (n=3, Euclidean)
@basis S"++-"; hodge(Multivector{V}(1,…,8)) => -8 - 7v₁ + 6v₂ + 5v₃ - 4v₁₂ - 3v₁₃ + 2v₂₃ + 1v₁₂₃
vee(Chain{V}(1,2,3),hodge(Chain{V}(4,5,6))) => -4v ; Chain{V}(1,2,3)⋅Chain{V}(4,5,6) => -4v
complexify(Chain(1,2)) => 1 + 2v₁₂ ; vectorize(Couple(1,2)) => 1v₁ + 2v₂
```

### 6.3 Basis tables (verified; `v`=One, `𝟎`=Zero, `1v₂`=Single, `v₂`=Submanifold)

`⟨111⟩` ⟑:

| ⟑ | v | v₁ | v₂ | v₃ | v₁₂ | v₁₃ | v₂₃ | v₁₂₃ |
|---|---|---|---|---|---|---|---|---|
| **v** | v | v₁ | v₂ | v₃ | v₁₂ | v₁₃ | v₂₃ | v₁₂₃ |
| **v₁** | v₁ | 1v | v₁₂ | v₁₃ | 1v₂ | 1v₃ | v₁₂₃ | 1v₂₃ |
| **v₂** | v₂ | -1v₁₂ | 1v | v₂₃ | -1v₁ | -1v₁₂₃ | 1v₃ | -1v₁₃ |
| **v₃** | v₃ | -1v₁₃ | -1v₂₃ | 1v | v₁₂₃ | -1v₁ | -1v₂ | 1v₁₂ |
| **v₁₂** | v₁₂ | -1v₂ | 1v₁ | v₁₂₃ | -1v | -1v₂₃ | 1v₁₃ | -1v₃ |
| **v₁₃** | v₁₃ | -1v₃ | -1v₁₂₃ | 1v₁ | 1v₂₃ | -1v | -1v₁₂ | 1v₂ |
| **v₂₃** | v₂₃ | v₁₂₃ | -1v₃ | 1v₂ | -1v₁₃ | 1v₁₂ | -1v | -1v₁ |
| **v₁₂₃** | v₁₂₃ | 1v₂₃ | -1v₁₃ | 1v₁₂ | -1v₃ | 1v₂ | -1v₁ | -1v |

`⟨111⟩` ⋅:

| ⋅ | v | v₁ | v₂ | v₃ | v₁₂ | v₁₃ | v₂₃ | v₁₂₃ |
|---|---|---|---|---|---|---|---|---|
| **v** | v | 𝟎 | 𝟎 | 𝟎 | 𝟎 | 𝟎 | 𝟎 | 𝟎 |
| **v₁** | v₁ | v | 𝟎 | 𝟎 | 𝟎 | 𝟎 | 𝟎 | 𝟎 |
| **v₂** | v₂ | 𝟎 | v | 𝟎 | 𝟎 | 𝟎 | 𝟎 | 𝟎 |
| **v₃** | v₃ | 𝟎 | 𝟎 | v | 𝟎 | 𝟎 | 𝟎 | 𝟎 |
| **v₁₂** | v₁₂ | v₂ | -1v₁ | 𝟎 | v | 𝟎 | 𝟎 | 𝟎 |
| **v₁₃** | v₁₃ | v₃ | 𝟎 | -1v₁ | 𝟎 | v | 𝟎 | 𝟎 |
| **v₂₃** | v₂₃ | 𝟎 | v₃ | -1v₂ | 𝟎 | 𝟎 | v | 𝟎 |
| **v₁₂₃** | v₁₂₃ | v₂₃ | -1v₁₃ | v₁₂ | v₃ | -1v₂ | v₁ | v |

`⟨111⟩` ∨:

| ∨ | v | v₁ | v₂ | v₃ | v₁₂ | v₁₃ | v₂₃ | v₁₂₃ |
|---|---|---|---|---|---|---|---|---|
| **v** | 𝟎 | 𝟎 | 𝟎 | 𝟎 | 𝟎 | 𝟎 | 𝟎 | v |
| **v₁** | 𝟎 | 𝟎 | 𝟎 | 𝟎 | 𝟎 | 𝟎 | v | v₁ |
| **v₂** | 𝟎 | 𝟎 | 𝟎 | 𝟎 | 𝟎 | -1v | 𝟎 | v₂ |
| **v₃** | 𝟎 | 𝟎 | 𝟎 | 𝟎 | v | 𝟎 | 𝟎 | v₃ |
| **v₁₂** | 𝟎 | 𝟎 | 𝟎 | v | 𝟎 | v₁ | v₂ | v₁₂ |
| **v₁₃** | 𝟎 | 𝟎 | -1v | 𝟎 | -1v₁ | 𝟎 | v₃ | v₁₃ |
| **v₂₃** | 𝟎 | v | 𝟎 | 𝟎 | -1v₂ | -1v₃ | 𝟎 | v₂₃ |
| **v₁₂₃** | v | v₁ | v₂ | v₃ | v₁₂ | v₁₃ | v₂₃ | v₁₂₃ |

`⟨-+++⟩` ⟑:

| ⟑ | v | v₁ | v₂ | v₃ | v₄ | v₁₂ | v₁₃ | v₁₄ | v₂₃ | v₂₄ | v₃₄ | v₁₂₃ | v₁₂₄ | v₁₃₄ | v₂₃₄ | v₁₂₃₄ |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| **v** | v | v₁ | v₂ | v₃ | v₄ | v₁₂ | v₁₃ | v₁₄ | v₂₃ | v₂₄ | v₃₄ | v₁₂₃ | v₁₂₄ | v₁₃₄ | v₂₃₄ | v₁₂₃₄ |
| **v₁** | v₁ | -1v | v₁₂ | v₁₃ | v₁₄ | -1v₂ | -1v₃ | -1v₄ | v₁₂₃ | v₁₂₄ | v₁₃₄ | -1v₂₃ | -1v₂₄ | -1v₃₄ | v₁₂₃₄ | -1v₂₃₄ |
| **v₂** | v₂ | -1v₁₂ | 1v | v₂₃ | v₂₄ | -1v₁ | -1v₁₂₃ | -1v₁₂₄ | 1v₃ | 1v₄ | v₂₃₄ | -1v₁₃ | -1v₁₄ | -1v₁₂₃₄ | 1v₃₄ | -1v₁₃₄ |
| **v₃** | v₃ | -1v₁₃ | -1v₂₃ | 1v | v₃₄ | v₁₂₃ | -1v₁ | -1v₁₃₄ | -1v₂ | -1v₂₃₄ | 1v₄ | 1v₁₂ | v₁₂₃₄ | -1v₁₄ | -1v₂₄ | 1v₁₂₄ |
| **v₄** | v₄ | -1v₁₄ | -1v₂₄ | -1v₃₄ | 1v | v₁₂₄ | v₁₃₄ | -1v₁ | v₂₃₄ | -1v₂ | -1v₃ | -1v₁₂₃₄ | 1v₁₂ | 1v₁₃ | 1v₂₃ | -1v₁₂₃ |
| **v₁₂** | v₁₂ | 1v₂ | 1v₁ | v₁₂₃ | v₁₂₄ | 1v | 1v₂₃ | 1v₂₄ | 1v₁₃ | 1v₁₄ | v₁₂₃₄ | 1v₃ | 1v₄ | 1v₂₃₄ | 1v₁₃₄ | 1v₃₄ |
| **v₁₃** | v₁₃ | 1v₃ | -1v₁₂₃ | 1v₁ | v₁₃₄ | -1v₂₃ | 1v | 1v₃₄ | -1v₁₂ | -1v₁₂₃₄ | 1v₁₄ | -1v₂ | -1v₂₃₄ | 1v₄ | -1v₁₂₄ | -1v₂₄ |
| **v₁₄** | v₁₄ | 1v₄ | -1v₁₂₄ | -1v₁₃₄ | 1v₁ | -1v₂₄ | -1v₃₄ | 1v | v₁₂₃₄ | -1v₁₂ | -1v₁₃ | 1v₂₃₄ | -1v₂ | -1v₃ | 1v₁₂₃ | 1v₂₃ |
| **v₂₃** | v₂₃ | v₁₂₃ | -1v₃ | 1v₂ | v₂₃₄ | -1v₁₃ | 1v₁₂ | v₁₂₃₄ | -1v | -1v₃₄ | 1v₂₄ | -1v₁ | -1v₁₃₄ | 1v₁₂₄ | -1v₄ | -1v₁₄ |
| **v₂₄** | v₂₄ | v₁₂₄ | -1v₄ | -1v₂₃₄ | 1v₂ | -1v₁₄ | -1v₁₂₃₄ | 1v₁₂ | 1v₃₄ | -1v | -1v₂₃ | 1v₁₃₄ | -1v₁ | -1v₁₂₃ | 1v₃ | 1v₁₃ |
| **v₃₄** | v₃₄ | v₁₃₄ | v₂₃₄ | -1v₄ | 1v₃ | v₁₂₃₄ | -1v₁₄ | 1v₁₃ | -1v₂₄ | 1v₂₃ | -1v | -1v₁₂₄ | 1v₁₂₃ | -1v₁ | -1v₂ | -1v₁₂ |
| **v₁₂₃** | v₁₂₃ | -1v₂₃ | -1v₁₃ | 1v₁₂ | v₁₂₃₄ | 1v₃ | -1v₂ | -1v₂₃₄ | -1v₁ | -1v₁₃₄ | 1v₁₂₄ | 1v | 1v₃₄ | -1v₂₄ | -1v₁₄ | 1v₄ |
| **v₁₂₄** | v₁₂₄ | -1v₂₄ | -1v₁₄ | -1v₁₂₃₄ | 1v₁₂ | 1v₄ | 1v₂₃₄ | -1v₂ | 1v₁₃₄ | -1v₁ | -1v₁₂₃ | -1v₃₄ | 1v | 1v₂₃ | 1v₁₃ | -1v₃ |
| **v₁₃₄** | v₁₃₄ | -1v₃₄ | v₁₂₃₄ | -1v₁₄ | 1v₁₃ | -1v₂₃₄ | 1v₄ | -1v₃ | -1v₁₂₄ | 1v₁₂₃ | -1v₁ | 1v₂₄ | -1v₂₃ | 1v | -1v₁₂ | 1v₂ |
| **v₂₃₄** | v₂₃₄ | -1v₁₂₃₄ | 1v₃₄ | -1v₂₄ | 1v₂₃ | -1v₁₃₄ | 1v₁₂₄ | -1v₁₂₃ | -1v₄ | 1v₃ | -1v₂ | 1v₁₄ | -1v₁₃ | 1v₁₂ | -1v | 1v₁ |
| **v₁₂₃₄** | v₁₂₃₄ | 1v₂₃₄ | 1v₁₃₄ | -1v₁₂₄ | 1v₁₂₃ | 1v₃₄ | -1v₂₄ | 1v₂₃ | -1v₁₄ | 1v₁₃ | -1v₁₂ | -1v₄ | 1v₃ | -1v₂ | -1v₁ | -1v |

`⟨+-⟩` ⋅:

| ⋅ | v | v₁ | v₂ | v₁₂ |
|---|---|---|---|---|
| **v** | v | 𝟎 | 𝟎 | 𝟎 |
| **v₁** | v₁ | v | 𝟎 | 𝟎 |
| **v₂** | v₂ | 𝟎 | -1v | 𝟎 |
| **v₁₂** | v₁₂ | v₂ | v₁ | -1v |

### 6.4 Unary tables on basis blades (verified; `!`=complementright, `cl`=complementleft, `⋆`=hodge, `⋆l`=complementlefthodge)

`S"-+++"`:
```
v : b*b=v abs2=v !=1v₁₂₃₄ cl=1v₁₂₃₄ ⋆=1v₁₂₃₄ ⋆l=1v₁₂₃₄ ~=v metric=1v anti=-1v inv=v
v₁ : b*b=-1v abs2=-1v !=1v₂₃₄ cl=-1v₂₃₄ ⋆=-1v₂₃₄ ⋆l=1v₂₃₄ ~=v₁ metric=-1v₁ anti=1v₁ inv=-1.0v₁
v₂ : b*b=1v abs2=v !=-1v₁₃₄ cl=1v₁₃₄ ⋆=-1v₁₃₄ ⋆l=1v₁₃₄ ~=v₂ metric=1v₂ anti=-1v₂ inv=1.0v₂
v₁₂ : b*b=1v abs2=-1v !=1v₃₄ cl=1v₃₄ ⋆=-1v₃₄ ⋆l=-1v₃₄ ~=-1v₁₂ metric=-1v₁₂ anti=1v₁₂ inv=1.0v₁₂
v₂₃ : b*b=-1v abs2=v !=1v₁₄ cl=1v₁₄ ⋆=1v₁₄ ⋆l=1v₁₄ ~=-1v₂₃ metric=1v₂₃ anti=-1v₂₃ inv=-1.0v₂₃
v₁₂₃ : b*b=1v abs2=-1v !=1v₄ cl=-1v₄ ⋆=-1v₄ ⋆l=1v₄ ~=-1v₁₂₃ metric=-1v₁₂₃ anti=1v₁₂₃ inv=1.0v₁₂₃
v₂₃₄ : b*b=-1v abs2=v !=-1v₁ cl=1v₁ ⋆=-1v₁ ⋆l=1v₁ ~=-1v₂₃₄ metric=1v₂₃₄ anti=-1v₂₃₄ inv=-1.0v₂₃₄
v₁₂₃₄ : b*b=-1v abs2=-1v !=1v cl=1v ⋆=-1v ⋆l=-1v ~=v₁₂₃₄ metric=-1v₁₂₃₄ anti=1v₁₂₃₄ inv=-1.0v₁₂₃₄
```
`D"1,2,3"`:
```
v₁ : b*b=1v abs2=v !=1v₂₃ cl=1v₂₃ ⋆=1v₂₃ ⋆l=1v₂₃ ~=v₁ metric=1v₁ anti=6v₁ inv=1.0v₁
v₂ : b*b=2v abs2=2v !=-1v₁₃ cl=-1v₁₃ ⋆=-2v₁₃ ⋆l=-2v₁₃ ~=v₂ metric=2v₂ anti=3v₂ inv=0.5v₂
v₃ : b*b=3v abs2=3v !=1v₁₂ cl=1v₁₂ ⋆=3v₁₂ ⋆l=3v₁₂ ~=v₃ metric=3v₃ anti=2v₃ inv=0.3333333333333333v₃
v₁₂ : b*b=-2v abs2=2v !=1v₃ cl=1v₃ ⋆=2v₃ ⋆l=2v₃ ~=-1v₁₂ metric=2v₁₂ anti=3v₁₂ inv=-0.5v₁₂
v₂₃ : b*b=-6v abs2=6v !=1v₁ cl=1v₁ ⋆=6v₁ ⋆l=6v₁ ~=-1v₂₃ metric=6v₂₃ anti=1v₂₃ inv=-0.16666666666666666v₂₃
v₁₂₃ : b*b=-6v abs2=6v !=1v cl=1v ⋆=6v ⋆l=6v ~=-1v₁₂₃ metric=6v₁₂₃ anti=1v₁₂₃ inv=-0.16666666666666666v₁₂₃
```
`S"∞+++"` (∞ slot is metric +1; `metric` zeroes blades with ∞):
```
v∞ : b*b=1v abs2=v !=1v₁₂₃ cl=-1v₁₂₃ ⋆=1v₁₂₃ ⋆l=-1v₁₂₃ ~=v∞ metric=𝟎 anti=𝟎 inv=1.0v∞
v₁ : b*b=1v abs2=v !=-1v∞₂₃ cl=1v∞₂₃ ⋆=-1v∞₂₃ ⋆l=1v∞₂₃ ~=v₁ metric=1v₁ anti=1v₁ inv=1.0v₁
v∞₁ : b*b=-1v abs2=v !=1v₂₃ cl=1v₂₃ ⋆=1v₂₃ ⋆l=1v₂₃ ~=-1v∞₁ metric=𝟎 anti=𝟎 inv=-1.0v∞₁
v₁₂₃ : b*b=-1v abs2=v !=-1v∞ cl=1v∞ ⋆=-1v∞ ⋆l=1v∞ ~=-1v₁₂₃ metric=1v₁₂₃ anti=1v₁₂₃ inv=-1.0v₁₂₃
```
`S"∅+++"` (∅ slot is metric -1):
```
v∅ : b*b=-1v abs2=-1v !=1v₁₂₃ cl=-1v₁₂₃ ⋆=-1v₁₂₃ ⋆l=1v₁₂₃ ~=v∅ metric=𝟎 anti=𝟎 inv=-1.0v∅
v∅₁ : b*b=1v abs2=-1v !=1v₂₃ cl=1v₂₃ ⋆=-1v₂₃ ⋆l=-1v₂₃ ~=-1v∅₁ metric=𝟎 anti=𝟎 inv=1.0v∅₁
v∅₁₂₃ : b*b=-1v abs2=-1v !=1v cl=1v ⋆=-1v ⋆l=-1v ~=v∅₁₂₃ metric=𝟎 anti=𝟎 inv=-1.0v∅₁₂₃
```
`S"∞∅++"` conformal (basis level; matches the T-model of 4.9):
```
v∞  b*b=𝟎 abs2=𝟎 !=2v∅₁₂ cl=-2v∅₁₂ ⋆=1v∞₁₂ ⋆l=-1v∞₁₂ ~=v∞ metric=-2v∅ inv=Inf*v∞
v∅  b*b=𝟎 abs2=𝟎 !=-0.5v∞₁₂ cl=0.5v∞₁₂ ⋆=-1v∅₁₂ ⋆l=1v∅₁₂ ~=v∅ metric=-0.5v∞ inv=Inf*v∅
v₁  b*b=1v abs2=v !=1v∞∅₂ cl=-1v∞∅₂ ⋆=1v∞∅₂ ⋆l=-1v∞∅₂ ~=v₁ metric=1v₁ inv=1.0v₁
v∞∅ b*b=1v abs2=-1v !=1v₁₂ cl=1v₁₂ ⋆=-1v₁₂ ⋆l=-1v₁₂ ~=-1v∞∅ metric=-1v∞∅ inv=1.0v∞∅
v∞₁ b*b=𝟎 abs2=𝟎 !=-2v∅₂ cl=-2v∅₂ ⋆=-1v∞₂ ⋆l=-1v∞₂ ~=-1v∞₁ metric=-2v∅₁ inv=-Inf*v∞₁
v∅₁ b*b=𝟎 abs2=𝟎 !=0.5v∞₂ cl=0.5v∞₂ ⋆=1v∅₂ ⋆l=1v∅₂ ~=-1v∅₁ metric=-0.5v∞₁ inv=-Inf*v∅₁
v∞∅₁₂ b*b=-1v abs2=-1v !=1v cl=1v ⋆=-1v ⋆l=-1v ~=v∞∅₁₂ metric=-1v∞∅₁₂ inv=-1.0v∞∅₁₂
products: v∞*v∅ = -1 + 1v∞∅ + 0v∞₁ + … (Spinor); v∅*v∞ = -1 - 1v∞∅ + …; v∞⋅v∅ = -1v; v∞∧v∅ = v∞∅;
          v∅∧v∞ = -1v∞∅; v₁*v∞ = -1v∞₁
```

### 6.5 Mixed-element goldens (ℝ3 unless stated; verified)

```
Multivector(1,2,3,4,5,6,7,8)               => 1 + 2v₁ + 3v₂ + 4v₃ + 5v₁₂ + 6v₁₃ + 7v₂₃ + 8v₁₂₃
~M        => 1 + 2v₁ + 3v₂ + 4v₃ - 5v₁₂ - 6v₁₃ - 7v₂₃ - 8v₁₂₃            (= reverse = conj)
involute  => 1 - 2v₁ - 3v₂ - 4v₃ + 5v₁₂ + 6v₁₃ + 7v₂₃ - 8v₁₂₃
clifford  => 1 - 2v₁ - 3v₂ - 4v₃ - 5v₁₂ - 6v₁₃ - 7v₂₃ + 8v₁₂₃
antireverse => -1 - 2v₁ - 3v₂ - 4v₃ + 5v₁₂ + 6v₁₃ + 7v₂₃ + 8v₁₂₃
M'        => 1 + 2w¹ + 3w² + 4w³ + 5w¹² + 6w¹³ + 7w²³ + 8w¹²³   ::Multivector{⟨---⟩', Int64, 8}
M(2) => 5v₁₂ + 6v₁₃ + 7v₂₃ (Chain) ; M[2] => [5, 6, 7] (Values) ; scalar(M) => 1v ; vector(M) => 2v₁ + 3v₂ + 4v₃
even(M) => 1 + 5v₁₂ + 6v₁₃ + 7v₂₃ (Quaternion) ; odd(M) => 2v₁ + 3v₂ + 4v₃ + 8v₁₂₃ (CoSpinor)
real(M) => 1 + 2v₁ + 3v₂ + 4v₃ ; imag(M) => 0 + 5v₁₂ + 6v₁₃ + 7v₂₃ + 8v₁₂₃
abs2(M) => 204 + 38v₁ - 126v₂ + 154v₃ ; norm(M) => 14.2828568570857 ; abs(M) -> error ; inv(M) -> error "inv(...) is undefined"
M*N (N = Multivector(8,7,…,1)) => 0 + 36v₁ + 60v₂ - 72v₃ + 88v₁₂ - 36v₁₃ + 116v₂₃ + 114v₁₂₃
M∧N => 8 + 23v₁ + 30v₂ + 37v₃ + 35v₁₂ + 33v₁₃ + 49v₂₃ + 114v₁₂₃
M∨N => 114 + 49v₁ + 33v₂ + 35v₃ + 37v₁₂ + 30v₁₃ + 23v₂₃ + 8v₁₂₃
M⋅N => 120 - 28v₁ + 148v₃ + 80v₁₂ + 112v₂₃ + 64v₁₂₃
M+N => 9 + 9v₁ + … + 9v₁₂₃ ; M - v12 => 1 + 2v₁ + 3v₂ + 4v₃ + 4v₁₂ + 6v₁₃ + 7v₂₃ + 8v₁₂₃
3 - M => 2 - 2v₁ - 3v₂ - 4v₃ - 5v₁₂ - 6v₁₃ - 7v₂₃ - 8v₁₂₃ ; M/2 => 0.5 + 1.0v₁ + 1.5v₂ + … + 4.0v₁₂₃
M//2 => 1//2 + (1//1)v₁ + (3//2)v₂ + (2//1)v₃ + (5//2)v₁₂ + (3//1)v₁₃ + (7//2)v₂₃ + (4//1)v₁₂₃
M*M = M^2 => -144 - 108v₁ + 102v₂ - 72v₃ + 74v₁₂ - 36v₁₃ + 46v₂₃ + 48v₁₂₃
M^8 => 1242432016 + 685358592v₁ - 2447359488v₂ - 524954112v₃ - 2815151616v₁₂ - 1735266816v₁₃ - 3182943744v₂₃ - 3984486912v₁₂₃
M^9 => 71815114768 + 56525180960v₁ - 36509119440v₂ + 46888421440v₃ - 16740572080v₁₂ + 37251661920v₁₃ + 3027975280v₂₃ + 10391172224v₁₂₃
inv(Multivector(1.0,0,0,0,0,0,0,2)) => 0.2 - 0.4v₁₂₃ ; M₂*inv(M₂) => 1.0v⃖
S"-++" M = Multivector{V}(1..8): M*N => 64 + 36v₁ + 54v₂ + 74v₃ + 88v₁₂ - 36v₁₃ - 18v₂₃ + 114v₁₂₃
   M⋅N => 0 - 28v₁ - 22v₂ + 80v₁₂ + 64v₁₂₃ ; M∨N and M∧N identical to ℝ3 (metric-free)
   ⋆M => -8 + 7v₁ + 6v₂ - 5v₃ + 4v₁₂ - 3v₁₃ - 2v₂₃ + 1v₁₂₃ (= complementlefthodge(M), n odd)
   metric(M) => 1 - 2v₁ + 3v₂ + 4v₃ - 5v₁₂ - 6v₁₃ + 7v₂₃ - 8v₁₂₃ ; abs2(M) => -54 + 38v₁ + 26v₂ - 54v₃
ℝ4 Spinor S=Spinor{V}(1..8), T=Spinor{V}(8..1), C=CoSpinor{V}(8..1):
   S*T => -88 + 36v₁₂ + 60v₁₃ - 72v₁₄ + 18v₂₃ + 102v₂₄ + 18v₃₄ + 114v₁₂₃₄
   S*C => 0v₁ + 84v₂ - 36v₃ - 96v₄ + 88v₁₂₃ - 36v₁₂₄ + 116v₁₃₄ - 36v₂₃₄
   ~S => 1 - 2v₁₂ - 3v₁₃ - 4v₁₄ - 5v₂₃ - 6v₂₄ - 7v₃₄ + 8v₁₂₃₄ ; !S => 8 + 7v₁₂ - 6v₁₃ + 5v₁₄ + 4v₂₃ - 3v₂₄ + 2v₃₄ + 1v₁₂₃₄
   S + v1 => 1 + 1v₁ + 2v₁₂ + … (Multivector) ; S + v12 => 1 + 3v₁₂ + 3v₁₃ + … (Spinor)
   inv(Spinor(1.0,2,0,0,0,0,0,0)) => 0.2 - 0.4v₁₂ - 0.0v₁₃ - 0.0v₁₄ - 0.0v₂₃ - 0.0v₂₄ - 0.0v₃₄ + 0.0v₁₂₃₄
```

### 6.6 Chains, powers, inverses (ℝ3 unless stated; verified)

```
Chain(1,2,3)^2 => 14v (Chain{0}) ; ^3 => 14v₁ + 28v₂ + 42v₃ ; ^5 => 196v₁ + 392v₂ + 588v₃ ; ^9 => 38416v₁ + 76832v₂ + 115248v₃
Chain(1,2,3)^-1 (literal) => 0.0714286v₁ + 0.142857v₂ + 0.214286v₃ ; ^-2 (literal) => 0.0714286v
Chain{V,2}(1,2,3)^2 => -14v ; ^3 => -14v₁₂ - 28v₁₃ - 42v₂₃ ; Chain{V,2}(1,2,3)*Chain{V,2}(1,2,3) => -14 + 0v₁₂ + 0v₁₃ + 0v₂₃ (Quaternion)
(2v12)^5 => 32v₁₂ ; (2v12)^9 => 512v₁₂ ; v12^3 => -1v₁₂
(1+v12)^2 => 0 + 2v₁₂ ; (1+2v12)^9 => -1199 - 718v₁₂ ; (1+2v12)^0 => 1 + 0v₁₂
(v1+v2)^2 => 2v ; (v1+v2+v3)^3 => 3v₁ + 3v₂ + 3v₃
inv(v12) => -1.0v₁₂ ; inv(2v12) => -0.5v₁₂ ; inv(v1+v2) => 0.5v₁ + 0.5v₂ + 0.0v₃ ; inv(v) => v ; inv(2.0v) => 0.5v
inv(Chain{V,2}(1.0,2.0,3.0)) => -0.0714286v₁₂ - 0.142857v₁₃ - 0.214286v₂₃ ; inv(Chain{V,3}(2.0)) => -0.5v₁₂₃
Chain(1.0,2.0,3.0)/Chain(1.0,0.0,0.0) => 1.0 - 2.0v₁₂ - 3.0v₁₃ + 0.0v₂₃ ; v1/v2 => 1.0v₁₂ ; v1\v2 => 1.0v₁₂
2/v12 => -2.0v₁₂ ; v12/2 => 0.5v₁₂ ; v12//2 => (1//2)v₁₂ ; Grassmann.inv_rat(Chain(1,2,3)) => (1//14)v₁ + (1//7)v₂ + (3//14)v₃
abs2(Chain{V,2}(1,2,3)) => 14v ; abs(Chain{V,2}(1.0,2,3)) => 3.7416573867739413v ; norm(-2v12) => 2.0 ; abs2(v12) => v
abs2(Spinor{V}(1,2,3,4)) => 30v ; abs2(CoSpinor{V}(1,2,3,4)) => 30v
S"-++": abs2(Chain{V,1}(1,2,3)) => 12v ; inv(Chain{V,1}(1.0,2,3)) => 0.0833333v₁ + 0.166667v₂ + 0.25v₃
products: v1*v2 => v₁₂ ; v2*v1 => -1v₁₂ ; v12*v12 => -1v ; v123*v123 => -1v ; v12∨v23 => v₂
v1 × v2 => 1v₃ ; (v1+2v2) × (v2+v3) => 2v₁ - 1v₂ + 1v₃ ; v12 & v23 => v₂ ; veedot(v12,v23) => 1v₂ ; antidot(v12,v23) => 𝟎
veedot(v12,v13) => 1v₁ ; antidot(v12,v12) => 1v₁₂₃ ; antidot(v1,v12) => 1v₁₃ ; ∨(v12,v23,v13) => -1v
v1 ⨼ v12 => v₂ ; v12 ⨽ v1 => v₂ ; v1 << v12 => v₂ ; v1 >> v12 => 𝟎 ; v1 < v12 => v₂ ; v12 | v1 => v₂ ; v1 ∗ v12 => 1v₂
v12 ⊛ v12 => v ; (v1+v2) ⊛ (v1+3v2) => 4v ; ∥(v1,2v1) => true ; ∥(v1,v2) => false
⋆Chain(1,2,3) => 3v₁₂ - 2v₁₃ + 1v₂₃ (= ! = complementleft = hodge = |) ; S"-++": ⋆Chain{V,1}(1,2,3) => 3v₁₂ - 2v₁₃ - 1v₂₃
S"-++": ⋆Chain{V,2}(1,2,3) => 3v₁ + 2v₂ - 1v₃ ; metric(Chain{V,1}(1,2,3)) => -1v₁ + 2v₂ + 3v₃
complex: ⋆Chain(1+2im,3,4) => (4+0im)v₁₂ + (-3+0im)v₁₃ + (1-2im)v₂₃ ; !Chain(1+2im,3,4) => (4+0im)v₁₂ + (-3+0im)v₁₃ + (1+2im)v₂₃
   Chain(1+2im,3,4)' => (1-2im)w¹ + (3+0im)w² + (4+0im)w³ ; contraction(1im*v1, v1) => (0 - 1im)v
ℝ4: v12⊘exp(π/4*v12) => 1.0v₁₂ + 0.0v₁₃ + … ; S"-+++": inv(Chain{V,1}(1.0,1,0)) (null) … Inf/NaN
D"1,2,3": B.v2^2 => 2v ; B.v2^5 => v₂ (BUG; true 4v₂) ; (3B.v2)^5 => 243v₂ (BUG, true 243·4v₂)
```

### 6.7 Couple / PseudoCouple (verified)

```
ℝ3 z = 3.0 + 4.0v12, w = 1.0 - 2.0v12:
z*w => 11.0 - 2.0v₁₂ ; z/w => -1.0 + 2.0v₁₂ ; inv(z) => 0.12 - 0.16v₁₂ ; z*inv(z) => 1.0 + 0.0v₁₂
abs2(z) => 25.0v ; abs(z) => 5.0v ; ~z = clifford(z) = conj(z) => 3.0 - 4.0v₁₂ ; involute(z) => 3.0 + 4.0v₁₂
z^2 => -7.0 + 24.0v₁₂ ; z^3 => -117.0 + 44.0v₁₂ ; z^10 => -9.653287e6 + 1.476984e6v₁₂ ; (3+4v12)^2 => -7 + 24v₁₂
z∧w => 3.0 - 2.0v₁₂ ; z∨w => 𝟎 ; z⋅w => -5.0 + 4.0v₁₂ ; z+w => 4.0 + 2.0v₁₂ ; z-w => 2.0 + 6.0v₁₂
z+v1 => 3.0 + 1.0v₁ + 4.0v₁₂ (Multivector) ; z+v12 => 3.0 + 5.0v₁₂ ; z+1 => 4.0 + 4.0v₁₂ ; 2z => 6.0 + 8.0v₁₂
z/2 => 1.5 + 2.0v₁₂ ; 2.0/z => 0.24 - 0.32v₁₂ ; Complex(z) => 3.0 + 4.0im
Couple{V,v12}(1e300,1e300)/Couple{V,v12}(1e-300,1e300) => 1.0 - 1.0v₁₂ ; inv(Couple{V,v12}(1e300,1e300)) => 5.0e-301 - 5.0e-301v₁₂
!(3.0 + 4.0v12) => 4.0v₃ + 3.0v₁₂₃ (PseudoCouple) ; (3.0+4.0v12)(0) => 3.0v ; (3.0+4.0v12)(2) => 4.0v₁₂
(1.0+2.0v1)*(3.0+4.0v1) => 11.0 + 10.0v₁ (correct) ; (1.0+2.0v1)^3 => 13.0 + 14.0v₁ (correct)
(1.0+2.0v1)/(3.0+4.0v1) => 0.44 + 0.08v₁ (BUG: hyperbolic B, true -5/7 + 2/7 v₁) ; inv(1.0+2.0v1) => 0.2 - 0.4v₁ (BUG)
(1.0+2.0v123)*(3.0+4.0v123) => -5.0 + 10.0v₁₂₃ ; (1.0+2.0v123)/(3.0+4.0v123) => 0.44 + 0.08v₁₂₃ (correct, v₁₂₃²=-1)
p = 2.0v1 + 3.0v123 (PseudoCouple): p*(1.0v1 + 5.0v123) => -13.0 + 13.0v₂₃ ; abs2(p) => 13.0v
  inv(p) => 0.15384615384615385v₁ - 0.23076923076923078v₁₂₃ ; ~p => 2.0v₁ - 3.0v₁₂₃ ; p∧q => 𝟎
  p⋅(1.0v1 + 5.0v123) => 17.0 + 3.0v₂₃ ; !p => 3.0 + 2.0v₂₃ (Couple)
ℝ4: a = 2.0v12 + 3.0v1234: abs2(a) => 13.0v ; ~a*a => 13.0 + 0.0v₃₄ ; inv(a) => -0.15384615384615385v₁₂ + 0.23076923076923078v₁₂₃₄
S"-+++": g = 1.0+2.0v12 (v₁₂²=+1, abs2(v₁₂)=-1): inv(g) => -0.3333333333333333 + 0.6666666666666666v₁₂ (correct)
         e = 1.0+2.0v1: inv(e) => -0.3333333333333333 + 0.6666666666666666v₁ (BUG; e*inv(e) = -1.6666666666666665)
```

### 6.8 Addition type-promotion goldens (verified)

```
ℝ3: v1+v2 => 1v₁ + 1v₂ + 0v₃ (Chain) ; 1+v12 => 1 + 1v₁₂ (Couple) ; v1+v12 => 0 + 1v₁ + 1v₁₂ (Multivector)
    v12+v13 => 1v₁₂ + 1v₁₃ + 0v₂₃ ; 1+v123 => 1 + 1v₁₂₃ (Couple) ; v1+v123 => 1v₁ + 1v₁₂₃ (PseudoCouple)
    2v1+3v2 => 2v₁ + 3v₂ + 0v₃ ; v1-v2 => 1v₁ - 1v₂ + 0v₃ ; v1 + 2.5 => 2.5 + 1.0v₁ ; 2.5 - v12 => 2.5 - 1.0v₁₂
    Chain(1,2,3)+1 => 1 + 1v₁ + 2v₂ + 3v₃ (Multivector) ; Chain(1,2,3)+v1 => 2v₁ + 2v₂ + 3v₃ ; v1-Chain(1,2,3) => 0v₁ - 2v₂ - 3v₃
    Chain(1,2,3)+v12 => 0 + 1v₁ + 2v₂ + 3v₃ + 1v₁₂ ; Chain(1,2,3)+v123 => 1v₁ + 2v₂ + 3v₃ + 1v₁₂₃ (CoSpinor)
    Chain{V,2}(1,2,3)+5 => 5 + 1v₁₂ + 2v₁₃ + 3v₂₃ (Quaternion) ; Chain{V,3}(7)+5 => 5 + 7v₁₂₃ (Couple)
    Chain{V,0}(7)+v1 => 7 + 1v₁ (Couple) ; v2 + Chain{V,3}(7) => 1v₂ + 7v₁₂₃ (PseudoCouple)
    Zero+v1 => v₁ ; Zero-v1 => -1v₁ ; Zero+3 => 3v ; Inf+v1 => ∞ ; v1-Inf => ∞
ℝ4: 1+v12+v34 => 1 + 1v₁₂ + 0v₁₃ + 0v₁₄ + 0v₂₃ + 0v₂₄ + 1v₃₄ + 0v₁₂₃₄ (Spinor)
    v1+v234 => 1v₁ + 0v₂ + 0v₃ + 0v₄ + 0v₁₂₃ + 0v₁₂₄ + 0v₁₃₄ + 1v₂₃₄ (CoSpinor) ; v12+v1234 => 1v₁₂ + 1v₁₂₃₄ (PseudoCouple)
    Chain{V,2}(1..6)+Chain{V,1}(1..4) => 0 + 1v₁ + 2v₂ + 3v₃ + 4v₄ + 1v₁₂ + … + 6v₃₄ (Multivector)
    Chain{V,2}(1..6)+Chain{V,0}(7) => 7 + 1v₁₂ + … + 6v₃₄ + 0v₁₂₃₄ (Spinor) ; +Chain{V,4}(7) => 0 + 1v₁₂ + … + 7v₁₂₃₄ (Spinor)
```

### 6.9 Sandwich goldens: see 4.12 (all verified).


---------------------------------------------------------------------------------------------

## 7. Dependencies on other chakravala packages (symbols used by this scope)

| Package | Symbols used (where) | Port note |
|---|---|---|
| **AbstractTensors** | type lattice `TensorAlgebra{V,T} <: Number`, `Manifold`, `TensorGraded{V,G,T}`, `TensorTerm`, `TensorMixed`, `Scalar/GradedVector/Bivector/Trivector` (AT:32-124); `TAG` (alg:192); operator objects `∧ ∨ ⟑ ⊖ ⊘ ⊗ ⊛ ⊙ ⊠ ⨼ ⨽ ⋆ ∗ ⟇`, `plus minus times contraction equal wedgedot veedot wedgedot_metric contraction_metric log_metric`, `pseudosandwich antisandwich cosandwich antidot codot expansion`, `interop`, `hodge`, `complement(left/right)(hodge/anti)`, `value valuetype scalar vector bivector trivector volume pseudoscalar involute clifford even odd unit`, `abs/abs2/norm/iszero/isone` defaults, postfix ops, `@co/@pseudo` (alg:15-18, G.jl:24,39-41); `Sym`=`:AbstractTensors` for symbolic `∑ ∏ - / // conj dot` (alg:21,500,545,702; prod:133-139); `SUB`, `rem`, `div` | port as the Lean class/operator layer (another agent covers AbstractTensors) |
| **DirectSum** | `Submanifold`, `Single`, `Signature`, `DiagonalForm`, `Zero`, `One`, `Infinity`, `Basis`/`Λ`, `getbasis`, `getalgebra`, `dual`, `signbool`, `metric`, `metrichash`, `antimetric`, `cometric`, `paritymetric`, `parityanti`, `parityright/left(hodge)` for Submanifold, `complementleft/right(hodge/anti)` on basis, `reverse/involute/clifford/conj` on basis, `antireverse/antiinvolute/anticlifford`, `isdiag`, `hasconformal`, `supermanifold`, `submanifold`, `mixed`, `combine`, `⊕`, `∪` (G.jl:33,37; par:17-18) | port as the manifold/basis layer (shared with the DirectSum spec) |
| **Leibniz** | `diffcheck diffmode symmetricsplit loworder isnull Field ExprField` (alg:19-20); `parityreverse parityinvolute parityconj parityclifford parityright parityleft parityrighthodge paritylefthodge complement grade_basis` (par:15-16); caches `binomial binomsum spinsum antisum *cumsum/_set indexbasis indexbasis_set bladeindex basisindex spinindex antiindex gdimsall`, `insert_expr`, `mvec svec mvecs svecs`, `cache_limit sparse_limit algebra_limit fill_limit`, `intlog promote_type digits_fast indices indexsplit`, `symmetricmask diffmask diffvars hasinf hasorigin dyadmode`, printing `showvalue printindices indexstring` (G.jl:34-49) | index/cache layer -> Lean `Grassmann/Basis/Index.lean` |
| **StaticVectors** | `Values`, `Variables`, `FixedVector`, `evens` (=`evenvalues`), `countvalues`, `∑ ∏` | Lean `Vector`/`FloatArray`/generated structs |
| **AbstractLattices** | `∧ ∨ wedge vee` generic functions | notation only |
| ComputedFieldTypes, Combinatorics, LinearAlgebra | `@computed`; `combinations` (via Leibniz `combo`); `UniformScaling`, `I`, `dot`, `cross`, `norm`, `det`, `rank` | not needed in Lean |

Internal Grassmann cross-file symbols used by `algebra.jl`: from `parity.jl`: `parity`,
`parityinner`, `paritygeometric`, `regressive`, `interior`, `parityinterior`, `fieldneg/fieldprod`;
from `products.jl`: `tvec/tvecs`, `derive_mul/derive_pre/derive_post`, `bcast`, `set_val/pre_val/add_val`,
all mutators `{set,add}{multi,blade,spin,anti}!` and `_pre` variants and their `join/geom/meet/skew/exter`
wrappers, `contraction2`, `generate_products`; from `multivectors.jl`: all types, `multispin`,
`maxgrade/mingrade/nextmaxgrade/nextmingrade/maxpseudograde/nextmaxpseudograde` (mv:1156-1197),
`realvalue/imagvalue/imaginary`, `value(m,T)`, `value_diff`, `numtype`; from `forms.jl`:
`isinduced`, `metrictensor`, `metricextensor`, `Dyadic`; from `composite.jl`: `compound`, `sqrt`,
`exp`, `log`. Note `addpseudo` (alg:918,1037) is referenced but never defined anywhere (latent bug in
the n ≥ 13 CoSpinor adder path).

---------------------------------------------------------------------------------------------

## 8. Lean 4 porting notes

### 8.1 Strategy (three layers, each testable against the oracle)

1. **Spec kernel** (port `ref_check.py` 1:1): dense coefficient arrays in Julia canonical order, bitmask
   kernels of 4.1-4.2, complements 4.7, conformal via `T` 4.9, inverses 4.10. Slow but obviously
   correct; passes all goldens (it already does in Python). Everything else is differentially tested
   against it.
2. **Typed fast layer**: `Chain V G α`, `Multivector`, `Spinor`, `CoSpinor`, `Couple`, `PseudoCouple`,
   `Single` with precomputed per-signature tables and specialized loops; result kinds follow 4.3/4.4.
3. **Codegen layer** (the `@generated` analog): a Lean command elaborator that, for a concrete
   small signature, emits straight-line kernels over unboxed-`Float` structures. Only for hot
   signatures (ℝ2, ℝ3, ℝ4, PGA `S"∅+++"`-style, CGA `S"∞∅+++"`, STA `S"-+++"`), gated by benchmarks.

### 8.2 What becomes a dependent index (erased, zero cost) vs runtime data

| Julia type parameter | Lean | Runtime cost |
|---|---|---|
| dimension n | index `n : Nat` of `Sig n` | erased |
| grade G of `Chain`/`Single` | type index `G : Nat` | erased; lengths via `binom n G` in `Vector α (binom n G)` |
| element kind (Chain/Spinor/CoSpinor/Couple/...) | distinct structures | none |
| metric (negative mask / diagonal / ∞∅ flags) | `V : Sig n` appears in every type (prevents mixing algebras) **and** is available at runtime (kernels read it) - put it in an `[Algebra V]` instance holding precomputed tables | one pointer; `@[specialize]` on the instance lets the compiler specialize per concrete algebra |
| blade mask `B` of `Single`/`Submanifold`/`Couple`/`PseudoCouple` | **runtime** `UInt64` field + `grade` proof/check | 8 bytes. Making `B` a type index gives no Lean speedup (Lean does not monomorphize on values) and makes sums/containers awkward |
| scalar type `T` | type parameter `α` with a small class (`Add Mul Neg Sub OfNat Div`, `conj`, `isZero`) | `@[specialize]`; Float gets dedicated `FloatArray` backends |

Truncated-subtraction caveat: `vee : Chain V a α → Chain V b α → Chain V (a+b-n) α` and
`contraction : Chain V a α → Chain V b α → Chain V (a-b) α` must return the zero element when
`a+b<n` / `b>a` (Nat subtraction saturates to grade 0, which has one slot). `wedge` to grade `a+b>n`
is naturally empty because `binom n (a+b) = 0` - an elegant analog of Julia returning `Zero`.
Provide a result sum type for the dynamic API:
```lean
inductive TA {n : Nat} (V : Sig n) (α : Type) where
  | zero
  | single   (G : Nat) (s : Single V G α)
  | chain    (G : Nat) (c : Chain V G α)
  | couple   (z : Couple V α)          -- scalar + blade
  | pseudo   (z : PseudoCouple V α)    -- blade + pseudoscalar
  | spinor   (s : Spinor V α)
  | cospinor (s : CoSpinor V α)
  | multi    (m : Multivector V α)
```
whose `+`/`*` implement the narrowing tables (4.3, 4.4). The typed API (no `TA`) is the fast path.

### 8.3 Suggested core types (sketch; avoid Mathlib in the core library so `binom` is local)

```lean
inductive MetricKind where
  | euclid                          -- `Int n`: all +1
  | signature (neg : UInt64)        -- bit i ↔ e_{i+1}^2 = -1   (∅ slot is negative, ∞ slot positive)
  | diagonal  (g : Array Float)     -- DiagonalForm (make generic in α if exact diag needed)
deriving Repr, BEq, Hashable

structure Sig (n : Nat) where
  kind      : MetricKind
  hasInf    : Bool := false         -- ∞ occupies slot 1
  hasOrigin : Bool := false         -- ∅ occupies slot 1, or 2 if hasInf
deriving Repr, BEq, Hashable

def binom : Nat → Nat → Nat         -- local Pascal; @[simp] lemmas: binom n k = 0 for k > n, Σ_k = 2^n
structure Chain {n} (V : Sig n) (G : Nat) (α : Type) where
  c : Vector α (binom n G)          -- k-th slot ↔ indexbasis n G [k] (lexicographic)
structure Multivector {n} (V : Sig n) (α : Type) where c : Vector α (2^n)
structure Spinor   {n} (V : Sig n) (α : Type) where c : Vector α (2^(n-1))   -- even grades
structure CoSpinor {n} (V : Sig n) (α : Type) where c : Vector α (2^(n-1))   -- odd grades
structure Single {n} (V : Sig n) (G : Nat) (α : Type) where
  blade : UInt64 ; coeff : α        -- invariant popcount blade = G, blade < 2^n
structure Couple {n} (V : Sig n) (α : Type) where blade : UInt64 ; re im : α
structure PseudoCouple {n} (V : Sig n) (α : Type) where blade : UInt64 ; re im : α
```
For `Float` use `FloatArray`-backed twins (`{a : FloatArray // a.size = k}`): `Array Float` boxes every
element. For n ≤ 4 the codegen layer can use plain structures with `Float` fields (stored unboxed in
the constructor's scalar area), the closest analog of Julia's `Values` tuples.

### 8.4 Per-algebra tables (the analog of Julia's global caches)

Build once per `V` (in the `Algebra V` instance, or a memo keyed by `Sig` via `IO.Ref`/`initialize`
for common algebras):
* `order : Array UInt64` canonical position -> mask; `pos : Array UInt32` mask -> position
  (inverse permutation); `gradeOff[g]` = `binomsum n g`, `spinOff`, `antiOff`.
* `gsign : Array Int8`/`gcoef : FloatArray` of size `4^n` for `n ≤ 8` holding
  `ε(A,B)·g(A∩B)` (geometric), and `wsign`, `csign` (contraction), `vsign` (regressive) - or compute
  on the fly with `reorderSign` (a handful of popcounts; also fine).
* Product "plans" for `Chain G × Chain H` (list of `(i,j,k,coef)` with nonzero coef) memoized per
  `(G,H,op)`; the dense multivector product becomes a flat loop over a plan array.
* Complement permutation + sign tables per grade.
Kernel shape (dense geometric product, canonical storage):
```
for i in 0..2^n: let ai := a[i]; if ai ≠ 0 then
  for j in 0..2^n: let bj := b[j]; if bj ≠ 0 then
    let k := pos[order[i] ^^^ order[j]]; out[k] += gcoef[i*2^n+j] * ai * bj
```
Spinor×Spinor, Chain×Chain etc. iterate only their blades and write into the narrower output.

### 8.5 How Julia gets its speed and the Lean equivalents

| Julia mechanism (4.14) | Lean equivalent |
|---|---|
| `@generated` + `_pre` mutators emit per-coefficient `∑(± a_i b_j)` expressions | `elab`/`macro` command `#gen_ga_kernels R3` that runs the spec kernel at elaboration time and emits `@[inline] def` with straight-line code over a `structure MV_R3 where s e1 e2 e3 e12 e13 e23 e123 : Float` |
| type-level `V`, `G` (constant folding) | `[Algebra V]` + `@[specialize]` (dictionary removal), plus codegen for hot signatures |
| `Values` stack tuples | unboxed-Float structures (small n) / `FloatArray` (large n) |
| parity/index caches | tables in the instance; `initialize` for globals |
| type narrowing (Spinor half size, Chain `C(n,G)` size) | same via distinct types; this is where most of Julia's speed comes from - keep it |
| grade-window shortcuts (pseudoscalar via Hodge, zero by grade) | type-level: `binom n k = 0`, special-case `G=0`/`G=n` in typed ops |
Benchmark targets (to measure against Julia `@btime` on the same machine): ℝ3 Multivector⟑Multivector,
ℝ3 rotor sandwich `R⊘x`, CGA ℝ4,1 Multivector product, ℝ5 Chain{2}⟑Chain{2}, n=8 Multivector product
(loop path), `inv` of a versor.

### 8.6 Tricky semantics checklist (all in section 4)

1. Lexicographic blade order within grades (3.3) - not numeric mask order.
2. Contraction is `<(~b) a>_{|a|-|b|}` (right operand reversed), `<`/`⨼` swap, `<<`/`>>` reverse the
   left operand.
3. Regressive and complements are metric-free; Hodge = `(~a)⟑I`; left versions differ by `(-1)^{G(n-G)}`.
4. `∅` slot has metric -1, `∞` slot +1; `metric` zeroes projective blades only at basis level.
5. Conformal: implement via the `T` change of basis (4.9); do not replicate Julia's container
   inconsistencies.
6. `conj` = reverse (no complex conjugation); Hodge/metric/adjoint conjugate; graded contraction
   conjugates the left coefficient (4.15). Decide whether the port follows this (fidelity) or offers
   an explicit Hermitian variant; most users are real-valued.
7. `abs2`: scalar for graded & Couple, full `~t t` for mixed.
8. `inv` for mixed types uses the homogeneous-norm test with `rtol = sqrt(eps)`; errors otherwise.
9. Generated sandwich projects to the input grade; generic does not.
10. `Chain ≈` is elementwise (atol 0) while `Multivector ≈` is norm-based.
11. Display: containers compact-print numbers, Single/Couple print full precision; Chain/Spinor/CoSpinor
    print zeros, Multivector hides them; scalar blade label `v`; `𝟎`, `v⃖`.
12. Result types: `+1` products on disjoint blades stay `Submanifold`, overlapping ones become `Single`.

### 8.7 Julia-specific things to skip or redesign

`@pure`, `@generated`, `@computed`; global mutable caches; cross-manifold `interop` (replace by explicit
`embed`); `Values`/`Variables`/`FixedVector` distinction and `isfixed`; symbolic `Any`/`Expr` fields and
`generate_algebra`/`generate_products` for external rings (a Lean coefficient class covers this);
tangent/`Derivation` algebras (`diffvars`, `derive_mul`, `symmetricmask` Q/Z bits); dyadic `V⊕V'` and
`adjoint` space flipping (keep only coefficient-conjugating `adjoint` if needed); `field=true` metric
objects; `UniformScaling` sugar (optional); `Phasor` (optional, belongs with `composite.jl`);
`literal_pow` (Lean: just `HPow`); postfix `⁻¹ ǂ ₊ ₋ ˣ` (use notation); the 28 bugs of 4.16.

### 8.8 Proofs worth weaving in (cheap, high leverage)

* `reorderSign` as a GF(2) bilinear form `τ(a,b) = Σ_{i>j} a_i b_j`: prove bilinearity in each argument
  (`τ(a⊕a',b) = τ(a,b)+τ(a',b)`), from which the **cocycle** `τ(a,b)+τ(a⊕b,c) = τ(a,b⊕c)+τ(b,c)`
  follows in two lines; with the metric identity `g(a∩b)·g((a⊕b)∩c) = g(a∩(b⊕c))·g(b∩c)` (exact for
  any diagonal `g`: both sides are the product over the elements lying in at least two of `a,b,c`,
  each counted once - check the 8 membership patterns) this gives associativity of the blade product
  for all n.
  For concrete small n, `native_decide`/`decide` over all triples is also viable (n ≤ 4: 4096 triples).
* `bv_decide` for mask identities on `BitVec 64` (complement involution, `A⊕B` grade parity).
* `omega`/`grind` for index arithmetic (`gradeOff g + rank < gradeOff (g+1)`, spinor offsets,
  `binom` bounds), and `Vector` size obligations (all erased at runtime).
* Complement laws: `cl (cr x) = x`, `cr (cr x) = (-1)^{G(n-G)} x`, `a ∨ b = cl(cr a ∧ cr b)`,
  `⋆a = (~a)⟑I` - state as theorems on the spec kernel; check by `decide` for n ≤ 4 and by property
  tests (Plausible) above.
* Differential theorems: `fastMul = specMul` for the codegen'd algebras (by `decide`/`native_decide`
  on symbolic coefficients is not possible; instead prove the plan generator correct once, or test).

### 8.9 Module decomposition (rough LOC)

| Module | Content | LOC |
|---|---|---|
| `Grassmann/Basis/Bits.lean` | popcount (SWAR or `@[extern]` shim), `reorderSign`, masks, complement masks, projective/conformal slot helpers, lemmas | 250 |
| `Grassmann/Basis/Index.lean` | `binom`, lexicographic combination order/rank, `indexbasis`, `bladeindex`, `basisindex/spinindex/antiindex`, offsets, bijection lemmas | 350 |
| `Grassmann/Manifold.lean` | `Sig n`, metric access `g i`, ∞/∅ options, parsing `S"…"`/`D"…"`, printing `⟨…⟩` (shared with DirectSum spec) | 300 |
| `Grassmann/Coeff.lean` | coefficient class; Int, Rat, Float, Complex instances; `conj`, `isZero`, Julia-style `≈` | 150 |
| `Grassmann/Types.lean` | Single, Chain, Multivector, Spinor, CoSpinor, Couple, PseudoCouple, Zero/One/Infinity, conversions to/from dense, `TA` sum type | 500 |
| `Grassmann/Algebra/Spec.lean` | spec kernel (port of `ref_check.py`) | 300 |
| `Grassmann/Algebra/Tables.lean` | per-`V` tables and product plans, `Algebra V` instance | 300 |
| `Grassmann/Algebra/Products.lean` | ⟑ ∧ ∨ ⋅ < << >> ∗ ⊛ × ⟇ antidot on all type pairs, narrowing | 800 |
| `Grassmann/Algebra/Add.lean` | + - scalar ops, promotion tables (4.4) | 350 |
| `Grassmann/Algebra/Involutions.lean` | reverse, involute, clifford, antireverse, even/odd/real/imag, grade projections | 200 |
| `Grassmann/Algebra/Complements.lean` | !, complementleft, ⋆, left Hodge, metric, antimetric | 250 |
| `Grassmann/Algebra/Conformal.lean` | T / T⁻¹ outermorphism, conformal wrappers | 150 |
| `Grassmann/Algebra/Norms.lean` | abs2, abs, norm, isapprox, ==, iszero/isone | 200 |
| `Grassmann/Algebra/Inverse.lean` | inv (blade, chain, mixed algorithm), Couple robust division (4.10.5), `/ \ //`, powers | 400 |
| `Grassmann/Algebra/Sandwich.lean` | ⊘, >>>, co/anti sandwiches, projected variants | 150 |
| `Grassmann/CodeGen.lean` | `#gen_ga_kernels` elaborator + generated struct types | 500 |
| `Grassmann/Show.lean` | labels, subscripts, compact/full float printing (Ryu-shortest + 6-digit compact), per-type `Repr`/`ToString` | 400 |
| `Grassmann/Proofs/*.lean` | cocycle/associativity, complement laws, index bijections | 600 |
| `test/Golden.lean` + `test/Laws.lean` | JSONL loader (`Lean.Json`), comparators, property tests | 400 |
| **Total** | | **~6,500** |

---------------------------------------------------------------------------------------------

## 9. Oracle test plan

### 9.1 Record format (what `algebra_oracle.jl` writes; one JSON object per line)

```json
{"sig": {"name":"⟨-+++⟩","n":4,"kind":"Signature","negmask":1,"hasinf":false,"hasorigin":false},
 "op": "mul",
 "args": [{"type":"Chain","grade":1,"B":null,"dense":[0,1,2,3,4,0,0,0,0,0,0,0,0,0,0,0]}, {...}],
 "result": {"type":"Spinor","grade":null,"B":null,"dense":[...16 coefficients...],"repr":"-13 + ... "}}
```
* `kind ∈ {Euclidean, Signature, DiagonalForm}`; DiagonalForm carries `"diag":[...]`.
* `dense` is always the full `2^n` coefficient vector in **Multivector canonical order** (3.3);
  ints stay ints, floats are numbers or the strings `"Inf" "-Inf" "NaN"`, rationals `[num,den]`.
* `type` is the Julia container kind (`Zero Submanifold Single Chain Couple PseudoCouple Spinor CoSpinor
  Multivector Number Bool`), `grade` for graded types, `B` the blade mask for Couple/PseudoCouple.
* Failing Julia calls are recorded as `{"error": "<message>"}` instead of `result` (1,220 records:
  the `Chain{0}×mixed` bug, `abs` of negative-norm elements); the port should either skip or assert
  the documented correct behavior.

### 9.2 Coverage (what the provided scripts dump)

| Block | Signatures | Inputs | Ops |
|---|---|---|---|
| Cayley (exhaustive) | ℝ1…ℝ5, `S"-"`, `S"--"`, `S"-+++"`, `S"+---"`, `S"++-"`, `D"1,2,3"`, `D"-1,2,1,1"`, `S"∞+++"`, `S"∅+++"` | every basis blade / pair | mul wedge vee contraction lcontraction shl shr revmul scalarprod veedot antidot; neg reverse tilde involute clifford conj complementright complementleft hodge lefthodge metric even odd real imag abs2 norm scalar vector bivector antireverse; inv |
| Random containers | the above with 2 ≤ n ≤ 4, 3 reps | integer coefficients uniform in −5..5: one `Chain` per grade, a dense and a 50%-sparse `Multivector`, `Spinor`, `CoSpinor` | all unary ops, `pow0`…`pow5`, all 15 binary ops incl. add sub sandwich tsandwich on all pairs |
| Float/invertible | n ≥ 2 | random vectors (3 decimals), 2-blades `v₁∧v₂`, versors `v₁v₂`, `v₁v₂v₃` | inv, abs, div, ldiv, sandwich, tsandwich |
| Conformal | `S"∞∅++"` | every basis pair | mul wedge vee contraction |
| Couple/PseudoCouple (`couple_only.jl`) | ℝ2, ℝ3, ℝ4, `S"-+++"`, `S"++-"`, `D"1,2,3"` | random ints per blade B; floats for inv/div only when `rev(|B|) = -1` | mul add sub wedge vee contraction (with Couple and with I), reverse involute clifford complementright complementleft hodge abs2 neg pow3, inv, div |

Current dump: 79,156 + 3,456 records (~34 MB), ~5.5 min total (dominated by Julia generated-function
compilation; parallelize per signature for speed).

### 9.3 Additional goldens to add (not yet dumped)

1. **Threshold crossings**: n = 6 (mixed×mixed switches from unrolled to loops, 4.14), n = 7..8 random
   Multivector products, `Chain` products with `C(n,G)·C(n,L) ≥ 4096` (e.g. n=13, G=L=6 sparse inputs),
   n = 12/13 for adders. Values must be identical across the thresholds.
2. **Display**: `repr` for each container with Int, negative Int, `typemin(Int)`, Float needing compact
   rounding (table in section 5), `-0.0`, `NaN`, `±Inf`, Rational (positive/negative), Complex, Bool,
   BigFloat; blade labels for n up to 40 (index chars `₀ a…z` and beyond 36), dual `w` labels, projective
   and conformal labels, manifold strings (`⟨111⟩ ⟨-+++⟩ ⟨1,2,3⟩ ⟨∞∅++⟩ ⟨1__1⟩`), `Λ(V)`.
3. **Robust Couple division edge cases** (Float64, B with `rev = -1`): operands scaled by 1e±300,
   subnormals, `Inf` components, signed zeros; compare bitwise (these follow Julia Base exactly).
4. **Powers**: `pow6…pow12` (binary exponentiation branch for `i ≥ 8`), Couple complex-power branch
   (`B²=-1`), Chain `n ≤ 3` `contraction2` branch.
5. **Equality/approx**: pairs differing by 1e-12, 1e-20, exact zeros; mixed container pairs; numbers.
6. **Algebraic-law property tests** (no oracle needed; run in Lean on random Float/Int inputs):
   associativity & distributivity of ⟑ (all signatures), `a⋅b = (ab+ba)/2`, `a∧b = (ab-ba)/2`,
   `ab = a⋅b + a∧b` (vectors), `aa = a⋅a`, `a ∨ b = cl(cr a ∧ cr b)`, `a⋅b = <(~b)a>`,
   `⋆a = (~a)⟑I`, `cl∘cr = id`, `cr∘cr = (-1)^{G(n-G)}`, `inv(x)⟑x = 1` for versors,
   rotor sandwiches preserve grade and norm, conformal `T`-model agreement.

### 9.4 Exclusions / expected divergences (from 4.16)

Skip or flip-to-correct: every `error` record; Couple `inv`/`div` with `rev(|B|) = +1`;
`PseudoCouple ± PseudoCouple`; `Couple ∨ non-Couple`; conformal container `!`/`metric`/`antimetric`;
term powers `^n` for n ≥ 3 on `DiagonalForm` blades with `|g|≠1` or null blades; negative runtime
powers; complex-coefficient `inv`; n = 1 spinors. The oracle script already avoids dumping Couple
`inv`/`div` for `rev(|B|) = +1`, n = 1 spinors and conformal complements; `ref_check.py` flags
`PseudoCouple ± PseudoCouple` and `Couple ∨ non-Couple` records via `known_bug(rec)`.

### 9.6 How to (re)run

```
D=/private/tmp/claude-502/-Users-alokbeniwal-Grassmann/c6cc2308-bfca-4b9a-ad33-d89b110132a8/scratchpad
cd $D/notes/oracle/grassmann_algebra
julia --startup-file=no --project=$D/juliaenv algebra_oracle.jl out 5     # ~5 min -> out/algebra_goldens.jsonl
julia --startup-file=no --project=$D/juliaenv couple_only.jl out          # ~30 s  -> out/couple_goldens.jsonl
python3 ref_check.py out/algebra_goldens.jsonl                             # expect only pass:* plus error/conformal-skip counts
python3 ref_check.py out/couple_goldens.jsonl                              # expect pass:* plus knownbug:*
python3 conformal_check.py                                                 # expect mul/wedge/vee/contraction all pass
```
`ref_check.py`'s `Alg` class (≈150 lines) is the recommended blueprint for the Lean spec kernel.

### 9.5 Comparison rules for the Lean harness

Exact for Int and Rational coefficients; Float: `|x-y| ≤ 1e-9·max(1,|x|,|y|)` (tighten to bitwise for
the robust-division block); `NaN` matches `NaN`; `Inf` strings. Compare `type` only for the typed
narrowing layer; compare `repr` only in the display suite.
