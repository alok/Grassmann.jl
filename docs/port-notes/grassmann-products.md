# Grassmann.jl products layer: porting spec for Lean 4

Scope: `Grassmann.jl/src/products.jl` in full (1976 lines), plus the product generators in `algebra.jl` and the parity kernels in `parity.jl` that products.jl calls. Without those two files the products cannot be implemented.

Source: `/Users/alokbeniwal/chakravala/Grassmann.jl` at commit `4f79a7f` (2026-08-09, Project.toml `version = "0.8.47"`).
Oracle: registered Grassmann 0.8.46 / AbstractTensors 0.8.11 on Julia 1.13, in `scratchpad/juliaenv`. Every behaviour cited as "probe" below was observed in that environment.

File references are relative to `/Users/alokbeniwal/chakravala/`. In this spec, `P:` means `Grassmann.jl/src/products.jl`, `A:` means `Grassmann.jl/src/algebra.jl`, `Y:` means `Grassmann.jl/src/parity.jl`, `M:` means `Grassmann.jl/src/multivectors.jl`, `AT:` means `AbstractTensors.jl/src/AbstractTensors.jl`, `L:` means `Leibniz.jl/src/`, and `DS:` means `DirectSum.jl/src/`.

Companion artifacts, all copied into `scratchpad/notes/grassmann-products-data/` (working copies are in `scratchpad/prodprobe/`). Each was run and checked against the oracle:

| path | what |
|---|---|
| `ref.py` | Independent Python implementation of every basis-level formula in §4.1 for diagonal metrics. It reproduces Julia's Cayley tables for `*`, `∧`, `∨`, `⋅`, `<<`, `⋆`, `!`, `complementleft`, `complementlefthodge`, `reverse`, `metric` and `antimetric` exactly: **0 mismatches** over ℝ2, ℝ3, ℝ4, S"-+++", S"+-" and DiagonalForm(2,3,-1). |
| `ref_gram.py` | Chevalley-recursion reference for arbitrary Gram matrices (§4.2). **0 mismatches** against Julia for `*`, `∧`, `∨`, `⋅`, `<<` and `⋆` on S"∞∅++", S"∞∅+++", S"∞++" and S"∅++". Also 0 mismatches for `!`, `complementleft` and `metric` on Multivector inputs. |
| `tables.txt`, `cga.txt` | The raw Julia Cayley dumps used for the checks above. |
| `types_{R3,R4,CGA4}.tsv` | Julia's exact **result type** for every (op ∈ `* ∧ ∨ ⋅ +`) × (lhs kind/grade) × (rhs kind/grade). See §4.5. |
| `oracle_products.jl` (+ `products_golden.json`) | Ready-to-run JSON golden generator (§9). |
| `sweep.jl` | Randomized check of each type-combination dispatch path against the bilinear extension of the basis tables. It is how the bugs in Appendix A were found. |

---

## 0. Key facts for the implementer

1. **All binary products are bilinear extensions of a basis-blade table.** A basis blade is a bitmask `B::UInt`, with bit `k-1` set iff basis vector `e_k` is present. The whole difficulty of products.jl is (a) choosing the result container type and (b) generating unrolled code that is fast in Julia. The mathematics is §4.1 and §4.2, and both were validated.
2. **Storage order is not bitmask order.** Grade-major; within a grade, the lexicographic order of the sorted index tuple. For ℝ4, grade 2 is `e12, e13, e14, e23, e24, e34` (bitmasks 3,5,9,6,10,12). See §3.2.
3. `*` = `⟑` = `⊖` = `wedgedot` = `times` are **one function** (`AT:296,314`). `⋅` = `dot` = `⨽` = `|` = `>` = `contraction`. `antidot` = `codot` = `pseudodot` = `expansion` = `∘`. `⟇` = `veedot`. `⊘` = `sandwich`. `~` = `Base.conj` = `reverse`: this is grade reversal only and never conjugates complex coefficients.
4. **Contraction convention** (validated in every signature tested, including null-basis CGA). Here `⌋` and `⌊` are the Dorst left/right contractions:
   - `contraction(a,b) = a⋅b = a ∨ ⋆b = (~b) ⌋ a`, with result grade `grade(a) - grade(b)`. So `e12⋅e1 = +e2`, `e12⋅e2 = -e1`, and `e12⋅e12 = +1` in Euclidean space.
   - `a ⨼ b = a < b = contraction(b,a) = (~a) ⌋ b`
   - `a << b = contraction(b,~a) = a ⌋ b` (exactly Dorst's left contraction)
   - `a >> b = contraction(~a,b) = ~(a ⌊ b)`
5. `∨` is the regressive product, defined by De Morgan: `!(a∨b) == (!a)∧(!b)`. `!` is the metric-free right complement, and `complementleft` is its inverse. `⋆x == (~x)*I` and `complementlefthodge(x) == I*(~x)` hold in every tested signature, conformal included.
6. **Result-type rules are compile-time functions of (types, grades, N, metric flags).** Summary: Chain×Chain under `*` gives a Spinor or CoSpinor (by parity of G+L). There are early-outs when a factor is a scalar or pseudoscalar Chain. `∧` gives `Chain{G+L}` or `Zero`. `∨` gives `Chain{G+L-N}` or `Zero`. `⋅` gives `Chain{L-G}` or `Zero`, but a Multivector when the metric is conformal. Full rules are in §4.5, and the tables list every grade combination.
7. **Sandwich products** `x ⊘ y = ~y * x * involute(y)` and `y >>> x = y * x * clifford(y)`. When `x` is graded and `y` is a Spinor, CoSpinor, Couple, PseudoCouple or Chain, the result is **projected to grade(x)** and returned as a `Chain` (§4.6).
8. The **Couple/PseudoCouple section of products.jl contains many real bugs**: wrong formulas and undefined variables. See Appendix A. Port the *correct* mathematics. §4.7 gives both the intended and the Julia formulas. When comparing against the oracle, use `dense_mv`, which the golden generator computes via Multivector conversion.
9. Julia's speed comes from `@generated` functions. They emit fully unrolled, branch-free code with the signs folded in when the problem is small: fewer than 4096 blade pairs for graded products, `N < 12` for graded×multivector, `N < 6` for multivector×multivector. Larger cases fall back to runtime loops with memoized parity caches. The Lean equivalent is a precomputed **product plan** (a list of `(i,j,k,coef)` entries per signature, op and shape), evaluated once as a closed term. Hot signatures can additionally get **metaprogrammed straight-line kernels** (§8).
10. Skip in v1: tangent/derivation spaces (`diffvars≠0`, `derive_mul`, the Q/Z masks), dyadic mixed spaces `V⊕V'`, symbolic scalar fields, the runtime-metric `_metric` variants, and cross-manifold `interop`. Each is Julia-specific or can be deferred (§8.6).

---

## 1. Purpose and scope

`products.jl` is the **product dispatch layer** of Grassmann.jl. It defines:

- the **accumulation kernels** ("mutators") that generated code uses to add one blade-pair contribution into an output coefficient vector (`P:141-368`)
- the algebra of **special elements** `Zero`, `Infinity`, `One`, `Phasor`, `Couple` and `PseudoCouple` for `+`, `-`, `*`/`⟑`, `∧`, `∨`, `contraction`, `/` and `^` (`P:372-826`)
- **scalar-field multiplication** for every container (`P:830-851`, plus `generate_products`, `P:1074-1142`)
- **`+`/`-` dispatch** to the `adder` code generators in algebra.jl (`P:852-941`)
- `adjoint` (`'`) for Chain, Multivector, Spinor and CoSpinor (`P:943-1070`)
- the **method table of the generated products**: `⟑`, `∧`, `∨`, `contraction` and their `_metric` variants over the pairs Chain/TensorTerm/TensorGraded × Chain/Multivector/Spinor/CoSpinor (`P:1146-1322`)
- **unary linear maps** on containers:
  - complements left/right and Hodge (`P:1324-1487`)
  - `even`/`odd` (`P:1488-1522`) and `real`/`imag` (`P:1523-1629`)
  - `metric`/`antimetric` (`P:1630-1815`)
  - `reverse`/`involute`/`conj`/`clifford`/`antireverse` (`P:1816-1976`)

The generators it calls live elsewhere. `product`, `product_contraction`, `product_∧`, `product_∨`, `product_sandwich`, `generate_loop_*` and `adder` are in `A:744-1889`. The basis-level `mul`, `∧`, `∨` and `contraction` on `Submanifold`/`Single` are in `A:38-277`. The parity and sign kernels (`parityinner`, `paritygeometric`, `parityregressive`, `parityinterior`, the caches) are in `Y:32-439`. The user-facing operator names come from AbstractTensors (`AT:244-351`). This spec covers all of these as far as products need them.

Out of scope, except where this spec needs to reference them: the type definitions and show methods (`multivectors.jl`), `inv`/`/`/`^`/`exp`/`log` beyond the product-related parts (`algebra.jl`, `composite.jl`), and operators and forms (`forms.jl`).

---

## 2. Public API inventory

### 2.1 Binary products

| Unicode | ASCII / function alias | Definition (exact) | Defined at |
|---|---|---|---|
| `*` | `⟑`, `⊖`, `wedgedot`, `times` (same function) | Geometric (Clifford) product. `Base.:*(a::TensorAlgebra,b::TensorAlgebra)=times(a,b)` | `AT:296,314`; basis `A:38-91`; generated `P:1156-1302`; Single×Single `P:1122-1126` |
| `*(a,b,c...)` | | left fold `(a*b)*c...` | `A:40-41` |
| `∧` | `wedge` (AbstractLattices `const ∧ = wedge`) | Exterior product: `Σ_{r,s} <a_r b_s>_{r+s}` | `A:103-147`; generated `P:1171-1233,1234-1301` |
| `∧(t::Values)` | | n-ary fold `((t1∧t2)∧t3)...`; `∧()` over an empty Values of Chain gives `One(V)` | `A:111-123` |
| `∨` | `vee`, `&` (for TAG types) | Regressive product: `!(a∨b) = !a ∧ !b` | `A:156-196`; generated `P:1171-1184,1185-1233,1303-1322` |
| `∨(t::Values)` | | n-ary fold; `∨()` over empty gives `Submanifold(V)` (the pseudoscalar I) | `A:185-190` |
| `contraction` | `⋅`, `dot`, `⨽`, `|`, `>` (`LinearAlgebra.dot`) | `a ∨ ⋆b = (~b)⌋a` | `A:203-270`; generated `P:1156-1170,1185-1302` |
| `⨼` | `<` | `contraction(b,a)` | `AT:259,262` |
| `<<` | | `contraction(b,~a)` = Dorst `a⌋b` | `AT:260` |
| `>>` | | `contraction(~a,b)` | `AT:261` |
| `∗` | | `(~a)*b` (reversed geometric product) | `AT:257` |
| `⊛` | | `scalar(contraction(a,b))` | `AT:258` |
| `×` | `cross` | `⋆(a∧b)` (`hodge(∧(a,b))`) | `AT:349` |
| `⊗` | | TensorGraded⊗TensorGraded gives `Dyadic(a,b)`; if either side is grade 0 it is `a*b`; Real/Complex ⊗ x is `a*x` | `A:150-152`, `AT:333-336` |
| `⊘` | `sandwich` | `reverse(y)*x*involute(y)`; graded `x` gives a grade-projected Chain (§4.6) | `A:313-345`, `AT:313` |
| `>>>` | | `y*x*clifford(y)` (note the argument order: `y>>>x`) | `A:351-385` |
| `veedot` | `⟇` | `complementleft(complementright(a)*complementright(b))` | `A:391`, `AT:629` |
| `veedot_metric(a,b,g)` | | same with `wedgedot_metric` | `A:392` |
| `antidot` | `codot`, `pseudodot`, `expansion`, `∘` | `complementleft(contraction(!a,!b))` | `A:396`, `AT:314,337` |
| `antidot_metric(a,b)` | | **BUG**: uses unbound `g` | `A:397` |
| `cosandwich` | `pseudosandwich` | `complementleft(sandwich(!x,!R))` | `AT:559-561` |
| `antisandwich(R,x)` | | `complementleft((!R) >>> (!x))` | `AT:568-569` |
| `wedgedot_metric(a,b,g)` | | geometric product using a runtime metric `g`; if `isinduced(g)` it is `a*b` | `A:39,64-91`, `P:1127-1131,1156-1302` |
| `contraction_metric(a,b,g)` | | contraction using runtime `g` | `A:225-277`, `P:1156-1302` |
| `contraction2(a,b)` / `contraction2_metric` | (internal) | `product_contraction` with plain `*` (no conj), used by `^` | `P:1150-1155` |
| `⊙(x...)` | | symmetrization `Σ_σ ∏ x_σ / K!`. **Broken**: `permutations` is not imported (probe: UndefVarError) | `A:294` |
| `⊠(x...)` | | anti-symmetrization. **Broken** for the same reason | `A:301-309` |
| `∥(a,b)` | | `iszero(a∧b)` | `A:401` |
| `⟂` | | exported (`A:23`) but **never defined** | — |
| `/`, `\` | | `a*inv(b)`, `inv(a)*b` | `AT:320-321`, `A:475-555` |
| `^` | | integer power (repeated squaring for i≥8; Chain with N≤3 uses `contraction2(~v,v)`) | `A:405-470`, `P:463-477` |
| `+`, `-` | `plus`, `minus` | module addition with type promotion (§4.10) | `AT:294-295`, `P:504-941` |

`UniformScaling` interop: every op `op(a::TensorAlgebra, I)` becomes `op(a, Manifold(a)(I))`. `V(λI)` is `λ` times the pseudoscalar (`AT:287-291`, `P:374-377`, `A:108-109,182-183`).

### 2.2 Unary maps defined (or given methods) in products.jl

| Name | Alias | Semantics | Container methods |
|---|---|---|---|
| `complementright` | `!`, `complement` | metric-free right complement (§4.1) | `P:1324-1487` (Chain, Multivector, Spinor, CoSpinor, Couple, PseudoCouple, Phasor) |
| `complementleft` | | left complement, the inverse of `!` | same |
| `complementrighthodge` | `⋆`, `hodge`, `|x` (unary `|`) | `(~x)*I` = `!(metric(x))` | same; Chain uses `conj` on the coefficients |
| `complementlefthodge` | | `I*(~x)` | same |
| `complementrightanti` / `complementleftanti` | | `!(antimetric(t))` / `complementleft(antimetric(t))` | `DS:operations.jl:333-334` |
| `metric` | | outermorphism of the Gram matrix; diagonal case: `e_B ↦ (∏_{i∈B} g_i) e_B`, values `conj`'d | `P:1630-1815` |
| `antimetric` | `cometric`, `pseudometric` | diagonal case: `e_B ↦ (∏_{i∉B} g_i) e_B`. **Errors** on conformal spaces (probe) | `P:1630-1815` |
| `reverse` | `~`, `conj` | grade k scaled by `(-1)^{k(k-1)/2}` | `P:1816-1976` |
| `involute` | postfix `ˣ` | `(-1)^k` | same |
| `clifford` | | `involute∘reverse`: `(-1)^{k(k+1)/2}` | same |
| `antireverse` | `pseudoreverse` | `(-1)^{m(m-1)/2}` with `m = N-k` | same (Couple version is inconsistent, Appendix A #9) |
| `even` / `odd` | postfix `₊` / `₋` | Multivector gives Spinor / CoSpinor of its even / odd part | `P:1488-1522`; others in `Y:465-477`, `DS:operations.jl:387-388` |
| `real` / `imag` | | keep grades with `(-1)^{k(k-1)/2} = +1` / `-1`; same container type | `P:1523-1629` |
| `adjoint` | postfix `'` | move to the dual space `V'` and `conj` the coefficients | `P:943-1070` |
| unary `-` | | negate all coefficients | `P:514-520,1121` |

### 2.3 Internal functions whose semantics the port must reproduce

| Function | Role | Where |
|---|---|---|
| `mul(a::Submanifold,b::Submanifold)` | basis geometric product | `A:43-60` |
| `parity(n,s,a,b)` / `parityjoin` | reorder sign plus negative-metric overlap | `Y:32-35,326-360` |
| `parityinner(V,a,b)` | diagonal geometric coefficient: `±\|∏g\|` | `Y:131-153` |
| `paritygeometric(V,A,B)` | non-diagonal geometric product as a list of `(blade,coef)` | `Y:165-313` |
| `parityregressive(V,a,b,skew)` | regressive sign and blade | `Y:41-67` |
| `parityinterior(V,a,b,lim,field)` | contraction list (diagonal or Gram) | `Y:69-129` |
| `regressive`, `interior` | cached wrappers | `Y:364-439` |
| `joinaddmulti!` etc. | accumulation kernels (§4.3) | `P:180-358` |
| `exterbits`, `exteradd*!` | `∧` guard `A&B==0` | `P:360-368` |
| `product`, `product_contraction`, `product_∧`, `product_∨`, `product_sandwich`, `generate_loop_*`, `product_loop` | code generators (§4.4) | `A:1152-1889` |
| `adder`, `adderspin`, `adderanti`, `addermulti` | `+`/`-` generators (§4.10) | `A:744-1140` |
| `mulvec`, `subvec`, `conjvec`, `isfixed`, `swapper` | choose scalar ops and storage | `A:719-742` |
| `multispin`, `value_diff`, `mingrade`/`maxgrade`/`nextmingrade`/`nextmaxgrade`/`maxpseudograde` | container helpers | `M:999-1011,1100-1101,1156-1195` |

### 2.4 Exports touching products

- `A:23-28`: `∗, ⊛, ⊖, ∧, ∨, ⟑, wedgedot, veedot, ⊗, ⨼, ⨽, ⊙, ⊠, ⟂, ∥, ⊘, sandwich, pseudosandwich, antisandwich, cosandwich, ⟇`
- `Grassmann.jl:29`: `hodge, wedge, vee, complement, dot, antidot`
- `M:26-27`: `⋅, cross, ×, contraction`
- `Y:21-28`: `complementleft, complementright, ⋆, complementlefthodge, complementrighthodge, complementleftanti, complementrightanti, involute, clifford, pseudoreverse, antireverse, odd, even, angular, radial, ₊, ₋, ǂ`

---

## 3. Data representations

### 3.1 Type parameters, split into compile-time and runtime

| Type | Julia parameters (all compile-time) | Runtime fields | Notes |
|---|---|---|---|
| `Submanifold{V,G,B}` (basis blade; `One{V}` = grade 0) | V manifold, G grade, B `UInt` bitmask | none | the value is implicitly 1 |
| `Single{V,G,B,T}` | V, G, B = a `Submanifold` value, T field | `v::T` | a scaled basis blade |
| `Zero{V}`, `Infinity{V}` (DirectSum) | V | none | absorbing elements |
| `Chain{V,G,T,X}` | V, G, T; X = binomial(N,G) is computed | `v::Values{X,T}` | a full grade-G vector |
| `Multivector{V,T,X}` | V, T; X = 2^N | `v::Values{2^N,T}` | full algebra, grade-major (§3.2) |
| `Spinor{V,T,X}` | V, T; X = 2^(N-1) | `v::Values` | even grades 0,2,4,… concatenated |
| `CoSpinor{V,T,X}` (alias `AntiSpinor`) | same | `v` | odd grades 1,3,5,… concatenated |
| `Couple{V,B,T}` | V; B = basis `Submanifold`; T | `v::Values{2,T}` = (`realvalue`, `imagvalue`) | `z = re + im·B` (`M:656-660`) |
| `PseudoCouple{V,B,T}` | V, B, T | `v::Values{2,T}` | `z = re·B + im·I`. `realvalue` is the B coefficient and `imagvalue` the pseudoscalar coefficient (`M:677-681,1133-1134`) |
| `Phasor{V,B,T}` | V; B = angle type; T = amplitude type | `v::T` (amplitude), `ω::B` (angle) | `complexify(z) = amplitude*exp(angle)` for scalar-like types, otherwise `amplitude ⊘ exp(angle/2)` (`M:852-858,1031-1045`) |

Aliases: `Quaternion{V,T} = Spinor{V,T,4}`, `Imaginary = Spinor{…,2}`, `AntiQuaternion = CoSpinor{…,4}`, `GaussianInteger{V,B,T<:Integer} = Couple{V,B,T}` (`M:971-975`). Probe display uses these names, for example `Quaternion{⟨111⟩, Int64}`.

Manifold `V`. In practice every element's `V` is a `Submanifold` of a `Signature`, `DiagonalForm` or metric tensor bundle; for example `ℝ3 :: Submanifold{3,3,0x07}`. Properties the product layer reads:

- `mdims(V)` (N)
- `grade(V)` = N − diffvars
- `metric(V)`: the Signature bitmask of negative squares
- `V[i]`: the diagonal entries
- `metrictensor(V)`: the Gram matrix
- `isdiag(V)`: false for conformal ∞∅ and for general metric tensors (`DS:generic.jl:66-68`)
- `hasconformal`, `hasinf`, `hasorigin`
- `istangent`/`diffvars`/`diffmode`, `isdyadic`, `isdual`, `dual(V)`

### 3.2 Index and ordering conventions (critical)

- **Blade bitmask**: bit `k-1` stands for basis vector `k` (LSB = e1). In `S"∞∅+++"`, bit 0 is `v∞`, bit 1 is `v∅`, and `v1` is bit 2. Tangent (derivation) indices occupy the top `D` bits: `diffmask = ((1<<D)-1)<<(N-D)` (`L:generic.jl:68-80`).
- **`indexbasis(N,G)`** (`L:utilities.jl:225-243`) lists all G-subsets of {1..N} in `Combinatorics.combinations(1:N,G)` order, which is **lexicographic on the sorted index tuple**, converted to bitmasks.
  - ℝ4 G=2: `[0b0011, 0b0101, 0b1001, 0b0110, 0b1010, 0b1100]` = e12, e13, e14, e23, e24, e34.
  - This is **not** increasing bitmask order: bitmask order would be e12, e13, e23, e14, e24, e34.
- **`bladeindex(N,B)`**: 1-based position of B inside `indexbasis(N, popcount B)`. `bladeindex(N,0) = 1` (`L:utilities.jl:181-220`).
- **`basisindex(N,B)`** = `binomsum(N,G) + bladeindex(N,B)` with `binomsum(N,G) = Σ_{q<G} C(N,q)`. This is the Multivector index, 1-based.
- **`spinindex(N,B)`** = `spinsum(N,G) + bladeindex` with `spinsum(N,G) = Σ_{q<G, q even} C(N,q)`. This is the Spinor index.
- **`antiindex(N,B)`** = `antisum(N,G) + bladeindex` with `antisum(N,G) = Σ_{q<G, q odd} C(N,q)`. This is the CoSpinor index. `binomsum_set`, `spinsum_set` and `antisum_set` are the cumulative arrays of length N+2 (`L:utilities.jl:135-179`).
- Full orders:
  - ℝ3 Multivector: `[1, e1, e2, e3, e12, e13, e23, e123]`
  - ℝ4 Spinor: `[1, e12, e13, e14, e23, e24, e34, e1234]`
  - ℝ4 CoSpinor: `[e1, e2, e3, e4, e123, e124, e134, e234]`
  - ℝ3 Spinor (Quaternion): `[1, e12, e13, e23]`
  - ℝ3 CoSpinor: `[e1, e2, e3, e123]`
- Loops in generated code iterate the **1-based "grade slot" g** from 1 to N+1, meaning grade `g-1`. `evens(1,N+1)` = 1,3,5,… are the even grades 0,2,4; `evens(2,N+1)` are the odd grades.
- The display of indices uses subscripts `v₁₂₃`. Dual space elements use `w¹²` (§5).

Julia typing gotcha: `TensorAlgebra <: Number` (AbstractTensors). Every Grassmann element `isa Number`, and methods written for `Number` or `Real` interact with tensor dispatch. That is why products.jl lists `Fields`/`Real`/`Complex` explicitly (`P:830-851`, `P:445-461`). Lean has no such subtyping: write scalar⊗tensor instances explicitly (`HSMul`/`HMul α (Chain V G α)` …).

### 3.3 Invariants

- `Chain{V,G}` requires `0 ≤ G ≤ N`, and `length(v) == C(N,G)`.
- A Spinor holds even grades only and a CoSpinor odd grades only. Both have length 2^(N-1) for N ≥ 1.
- A `Couple{V,B}` is only created by `+` when `!istangent(V) && !hasconformal(V)` (`A:751-758`). In conformal spaces `1 + v12` becomes a Spinor.
- `One{V}` is `Submanifold{V,0,0x0}` and prints `v`.

---

## 4. Algorithms

### 4.1 Basis-blade primitives (diagonal metric, non-tangent)

Notation:

- `N = mdims(V)`; `F = (1<<N)-1`
- `|X| = popcount X`
- `idx(X)` = 1-based indices of the set bits
- `Σidx(X)` = sum of `idx(X)`
- `g_i` = diagonal metric entry: ±1 for a Signature, arbitrary numbers for a DiagonalForm, 0 allowed (degenerate)
- `g(X) = ∏_{i∈X} g_i`, with `g(∅)=1`

Every formula below was checked, blade pair by blade pair, against the Julia oracle (`ref.py`).

```
reorderNeg(a,b)  := parity of  Σ_{i∈a} |{ j∈b : j < i }|
    # Grassmann: parityjoin Y:32-35 = isodd(sum(digits(a) .* cumsum(digits(b<<1))))
    # bit trick: s=0; a>>=1; while a≠0: s += popcount(a & b); a >>= 1
    # Signature version adds popcount(a & b & negmask) (Y:33-35, Y:350-355)

geom(a,b)        := (-1)^reorderNeg(a,b) · g(a&b) · e_{a xor b}
    # Julia: A:43-60 (mul); Y:137-153 (parityinner = ±|g(a&b)|, sign from parity incl. neg bits)
    # For a Signature: g(a&b) = (-1)^{popcount(a&b&negmask)}.
    # Degenerate (g_i = 0): coefficient 0, still returned as a Single with value 0 (probe: v1*v1 = 0v).

wedge(a,b)       := 0                                   if a&b ≠ 0
                    (-1)^reorderNeg(a,b) · e_{a|b}      otherwise        (A:127-134)

ρ(X)             := parity of ( Σidx(X) + |X|(|X|+1)/2 )          # Leibniz parityright (L:generic.jl:204)
!e_X             := (-1)^ρ(X) · e_{F&~X}                            # complementright
complementleft(e_X) := (-1)^{ρ(X) + [|X| odd ∧ N even]} · e_{F&~X}    # L:generic.jl:205; DS docs "(-1)^{m(n-1)}"
⋆e_X             := g(X) · (-1)^ρ(X) · e_{F&~X}                    # complementrighthodge  (= (~e_X)*I)
complementlefthodge(e_X) := g(X)·(-1)^{ρ(X)+[|X| odd ∧ N even]} · e_{F&~X}   (= I*(~e_X))

regressive(a,b)  :  α = F&~a, β = F&~b
                    if α&β ≠ 0  → 0                   (the blades do not span V)
                    C = α xor β ; L = |a|+|b|
                    s = [L(L−N) odd] ⊕ ρ(a) ⊕ ρ(b) ⊕ ρ(C) ⊕ reorderNeg(α,β)
                    result = (-1)^s · e_{F&~C}          (F&~C == a&b)
    # Y:41-67 (_parityregressive). G in the formula is grade(V) = N for non-tangent V.
    # "skew" flag: when a=b=0 the basis is forced to 0 unless skew (irrelevant for N≥1).

contraction(a,b) := if g(b) = 0 → 0 (Julia returns Zero)
                    r = regressive_skew(a, F&~b)          # skew=true
                    if r = 0 → 0
                    (-1)^{ρ(b)} · g(b) · r               # = e_a ∨ ⋆e_b      (Y:69-129 diag branch)
a << b           := (-1)^{|a|(|a|-1)/2} · contraction(b, a)     # = a ⌋ b
metric(e_X)      := g(X) e_X                   antimetric(e_X) := g(F&~X) e_X
reverse(e_X)     := (-1)^{|X|(|X|-1)/2} e_X    involute: (-1)^{|X|}    clifford: (-1)^{|X|(|X|+1)/2}
antireverse(e_X) := (-1)^{m(m-1)/2} e_X, m = N−|X|
```

Grade selection facts that follow (all verified):
- `e_a ∨ e_b ≠ 0` only if `a|b = F`; the result blade is `a&b` with grade `|a|+|b|−N`.
- `contraction(e_a,e_b) ≠ 0` only if `b ⊆ a`; the result is `e_{a−b}` with grade `|a|−|b|`.
- Two worked examples: `e12∨e23 = +e2` and `e12⋅e2 = −e1` in ℝ3.

Julia return **types** at the basis level:
- `Submanifold × Submanifold`:
  - `*` returns a `Submanifold` when the sign is + and the path is "Signature or disjoint"; otherwise it returns a `Single` (for example `v1*v1 :: Single{…,0}` "1v" when V is a Submanifold) or `Zero`. It returns a sum of Singles when the metric is non-diagonal.
  - `∧`, `∨` and `contraction` return `Submanifold`, `Single` or `Zero`.
- `Single × Single` (`P:1122-1126`) returns `v*mul(ba,bb,v)` with `v = a.v*b.v`.
- `∧`/`∨`/`contraction` on TensorTerms return `Single{V}(sign*prod, blade)` or `Zero` (`A:136-176,238-260`). For `contraction` the coefficient product is `dot(a.v,b.v) = conj(a.v)*b.v` (§4.12).

### 4.2 Non-diagonal metrics: conformal null basis and general Gram

`isdiag(V)` is false for conformal `S"∞∅…"`, which uses the Gram block `g(∞,∞)=g(∅,∅)=0` and `g(∞,∅)=−1`, and for general `MetricTensor` bundles.

The basis is the **wedge basis**: `v∞∅ = v∞∧v∅`, and `v∞*v∅ = −1 + v∞∅`.

**Grassmann's algorithm** is `paritygeometric` (`Y:165-313`):
1. `splitbasis` partitions the indices into metric-connected blocks (groups of indices joined by non-zero off-diagonal Gram entries).
2. It factorizes each blade by block and iterates the rule `a_i ⊖ B = a_i∧B + a_i<~B` (docs `algebra.md:520-530`).
3. It uses `parityinterior` with the grade-G Gram compound matrix `metrictensor(V,G)` for the contraction parts.
4. `combinebasis`/`combinegeometric` merge the terms.

**Recommended port (validated, 0 mismatches):** Chevalley recursion on the wedge basis with an arbitrary symmetric Gram matrix `G`.

```
vec_lc(i, e_B) = Σ_{k-th set bit j of B, k=0,1,…} (−1)^k · G[i][j] · e_{B \ j}          # e_i ⌋ e_B
vec_mul(i, X)  = vec_lc(i, X) + e_i ∧ X                                                   # e_i X
blade_mul(A, X):                     # e_A X,  e_A = e_{a1}∧e_{A'} (a1 = lowest set bit)
   if A = 0: return X
   return vec_mul(a1, blade_mul(A', X)) − blade_mul(vec_lc(a1, e_{A'}), X)
contraction(a,b) = (−1)^{|b|(|b|−1)/2} · < e_b e_a >_{|a|−|b|}      (0 if |b|>|a|)
a << b           = < e_a e_b >_{|b|−|a|}                            (0 if |a|>|b|)
⋆x = (~x)*I ;  complementlefthodge(x) = I*(~x)
∧, ∨, !, complementleft: metric-independent, as in §4.1
metric(e_X) = (G e_{x1}) ∧ (G e_{x2}) ∧ …   (outermorphism of the Gram matrix)
```

Conformal behaviour to reproduce (from probes and `test/issuestests.jl`):

```
v∞^2 = v∅^2 = 0,  v∞⋅v∅ = −1,  v∞∅^2 = 1
v∞∅*v∞ = −v∞,     v∞∅*v∅ = v∅
v∞*v∅ = −1 + v∞∅, v∅*v∞ = −1 − v∞∅
```

Julia also skips blade pairs up front using `diffcheck(V,A,B)` (`L:generic.jl:99-105`): a pair is dropped when both contain ∞ and neither contains ∅, or vice versa. This is an optimisation that is correct for null vectors.

`S"∞++"` (Riemann sphere) is **diagonal** with `v∞² = +1`. `S"∅++"` is diagonal with `v∅² = −1`.

### 4.3 Accumulation kernels (`P:141-368`)

`generate_mutators(M,F,set_val,SUB,MUL)` (`P:180-358`) is evaluated inside `generate_products`. For each op ∈ {add, set} and storage ∈ {multi, blade, spin, anti} (index functions basisindex, bladeindex, spinindex, antiindex) it defines:

- `$s(out,val,i::UInt,::Val{N})`: `out[index(N,i)] (+)= val` (`P:156-163`). The variants without `Val` use `intlog(length(out))` as N. That is only correct for multi storage and is unused elsewhere.
- `$s_pre(...)`: the same, but it builds a Julia `Expr`. For `add` it either creates `Expr(:call, ∑, val)` or pushes onto an existing sum's args (`P:137`). This is how unrolled code is assembled.
- `joinadd…!(V,m,a,b,v)`: if `v≠0` and `!diffcheck`, then `out[(A⊻B)|Q] += parityinner(grade(V),A,B)*v`, i.e. the pure reorder sign (`P:199-222`). It is guarded by `exterbits` (`A&B==0`) in `exteradd…!` (`P:360-368`).
- `geomadd…!`: diagonal: `out[A⊻B] += parityinner(V,A,B)*v`; otherwise loop over `paritygeometric(V,A,B)` (`P:223-260`).
- `meetadd…!`: `(g,C,t) = regressive(V,A,B)`; if `t`, `out[C] += g*v` (`P:270-296`).
- `skewadd…!`: diagonal: `interior(V,A,B)`; otherwise loop over `parityinterior(V,A,B,Val(true))` (`P:297-350`).

Tangent-space branches multiply by `getbasis(loworder(V),Z)`, drop terms whose order exceeds `diffmode`, and return `true` to request promotion to `Any` storage. Skip these in v1.

Return value: `false` normally. `true` means "the output needs to be retyped to Any; redo". Only tangent spaces return true.

### 4.4 How the generated products are built

All generators are `@noinline` functions from **types** to `Expr`. They are called from `@generated` methods, so they run once per concrete type signature. Variables `N`, `t`, `ib`, `bn`, `bs`, `rs`, `ps` and `μ` are bound by `insert_expr` (`L:utilities.jl:74-96`): `t` = promoted value type, `ib = indexbasis(N,G)`, `bn = gdimsall(N)`, `bs = binomcumsum`, `rs = spincumsum`, `ps = anticumsum`, `μ = istangent(V)`.

**`product(a::Type{S<:TensorGraded{V,L}}, b::Type{<:Chain{V,G}}, swap, field)`** (`A:1152-1225`). This backs `⟑` (Chain×TensorTerm with swap, TensorGraded×Chain) and `wedgedot_metric`.

```
MUL = ∏ (or * for bits types); anti = isodd(L) ≠ isodd(G); outT = anti ? CoSpinor : Spinor
if S is Zero/Infinity            → return a
if G == 0 (b scalar Chain)       → S<:Chain ? Chain{V,L}(a.v .* b[1]) : (swap ? Single(b)⟑a : a⟑Single(b))
elif S<:Chain && L == 0          → Chain{V,G}(a[1] .* b.v)
elif (swap ? L : G) == N         → right factor is the pseudoscalar:  X*I = ⋆(~X)   (scaled by the coefficient)
elif (swap ? G : L) == N         → left factor is the pseudoscalar:   I*X = complementlefthodge(~X)
elif C(N,G)·(S<:Chain ? C(N,L) : 1) < 4096:  unrolled
     for each blade i of a (or the single blade U of a TensorTerm), each blade j of b:
         geomadd{anti|spin}!_pre(out, A_i, B_j, MUL(a_i, b_j))    # (B_j, U) order when swap
     return outT{V}(Values(out...))
else runtime loop, same accumulation, skipping zero a_i.
```

**`product_contraction(a::S grade L, b::Chain{V,G}, swap, field, contr)`** (`A:1226-1325`):

```
MUL = dot (conj of the first argument) for contraction; * for contraction2
if (swap ? G<L : L<G) && !tangent → Zero(V)        # left grade must be ≥ right grade
if S Zero/Infinity → a
if (G==0 || G==N) && !tangent → contraction with Single(b) (keeping the order)
GL = swap ? G−L : L−G ; μ = istangent(V) | hasconformal(V)
accumulate skewadd{multi|blade}!(out, A, B, MUL(...)) over all blade pairs
return μ ? Multivector{V} : value_diff(Chain{V,GL})       # value_diff unwraps Chain{V,0} only if its value is a tensor
```

This is why `a⋅b` for two vectors gives `Chain{V,0}` (displayed "32v"). In conformal spaces it gives a Multivector.

**`product_∧` / `product_∨`** (`A:1327-1446`):

```
w,W = swap ? (R,Q) : (Q,R);  V = w==W ? w : (w==dual(W) ? (dyadmode(w)≠0 ? W⊕w : w⊕W) : interop)
∧: G+L > N → Zero ;  ∨: G+L < N → Zero        (non-tangent)
if S Zero/Infinity → a
if (L==0 || L==N) → op(a, Single(b)) (keeping the order)
result grade GL = G+L (∧) or G+L−N (∨); accumulate exteradd / meetadd over blade pairs
return Chain{V,GL}   (Multivector if tangent)
```

When dual spaces are mixed, blade indices are mapped with `dual(V,ib,M)`. Skip this.

**Graded × Multivector/Spinor/CoSpinor** (`A:1448-1546`). This is one generator per (input ∈ {Multivector, Spinor, CoSpinor}) × (op ∈ {∧, *, ∨, contraction}):

```
outT: Multivector input → Multivector
      Spinor input,  op ∈ {∧,*,⋅}: isodd(G) ? CoSpinor : Spinor
      CoSpinor input, op ∈ {∧,*,⋅}: iseven(G) ? CoSpinor : Spinor
      Spinor input,  ∨: isodd(G)⊻isodd(N) ? CoSpinor : Spinor
      CoSpinor input, ∨: isodd(G)⊻isodd(N) ? Spinor : CoSpinor
early outs (non-tangent):
  ∧:  G+mingrade(b) > N → Zero; == N → a∧b(mingrade); G+nextmingrade(b)==N → a∧b(min)+a∧b(nextmin)
  ∨:  G+maxgrade(b) < N → Zero; == N → a∨b(maxgrade); G+nextmaxgrade(b)==N → two terms
  ⋅ (a graded on the left):   G < mingrade(b) → Zero; G == mingrade → a⋅b(min); G == nextmingrade → two terms
  ⋅ (swap, b on the left): maxgrade(b) < G → Zero; == G → b(max)⋅a; nextmaxgrade == G → two terms
  *:  S<:Chain && G==0 → BUG (UndefVarError `input`, A:1483: `$input` must be `$$input`)
      G == N (a is the pseudoscalar) → swap ? ⋆(~b)(·coef) : complementlefthodge(~b)(·coef)
main: for each grade slot g of b's storage, each blade i in it, each blade j of a:
      preproduct!(out, swapper(ib[j], ia[i]), MUL(a_j, b_gi))       (unrolled when N < 12)
```

`mingrade`/`maxgrade`: Multivector 0/N; Spinor 0/(N odd ? N−1 : N); CoSpinor 1/(N odd ? N : N−1). `nextgrade` is 2 for spinors and 1 for Multivector (`M:1156-1195`). The `b(Val(k))` grade projection returns a Chain. The early-outs therefore change the **result type**: `v1⋅m` in ℝ3 returns `Couple` "2 + 1v₁", and `v12∧m` returns a `PseudoCouple`.

**Multivector/Spinor pairs** (`P:1185-1322`, `A:1792-1889`):

| lhs × rhs | ops | kernel loop | result |
|---|---|---|---|
| Multivector × Multivector | `∧ * ∨ ⋅` (+metric) | `generate_loop_multivector` | Multivector |
| Spinor × Multivector, Multivector × Spinor | same | `s_m`, `m_s` | Multivector |
| CoSpinor × Multivector, Multivector × CoSpinor | same | `a_m`, `m_a` | Multivector |
| Spinor × Spinor | `∧ * ⋅` | `spinor` | Spinor |
| CoSpinor × CoSpinor | `∧ * ⋅` | `anti` | Spinor |
| Spinor × CoSpinor, CoSpinor × Spinor | `∧ * ⋅` | `s_a`, `a_s` | CoSpinor |
| Spinor ∨ Spinor | `∨` | `spinor` + meetadd{anti if N odd} | N odd ? CoSpinor : Spinor |
| CoSpinor ∨ CoSpinor | `∨` | | N odd ? CoSpinor : Spinor |
| Spinor ∨ CoSpinor, CoSpinor ∨ Spinor | `∨` | | N odd ? Spinor : CoSpinor |

`generate_loop_*` (`A:1838-1889`) enumerates the left grade slots × the right grade slots × their blades and calls `preproduct!(V,out,Xi,Yj,MUL(a[i],b[j]))`. With `N < cache_limit/2 = 6` it returns a fully unrolled `Values(...)` constructor. Otherwise it returns a runtime loop that skips zero coefficients. `product_loop` (`A:1828-1836`) wraps the result as `type{V}(…)` or `type{V,t}(out)`. **MUL is plain `*` for all these loops, including contraction** (`P:1204`: `mulvec(a,b)` with no op argument), so there is no complex conjugation here.

**Chain and TensorTerm dispatch table** (`P:1156-1184`):
- `⟑`, `contraction`, `wedgedot_metric`, `contraction_metric`: `(b::Chain, a::TensorTerm)` uses swap=true; `(a::TensorGraded, b::Chain)` uses swap=false.
- `∧` and `∨`: `(Chain,Chain)`, `(Chain,TensorTerm)` with swap, and `(TensorTerm,Chain)`.
- The `_metric` variants return early with `isinduced(g) && return :(op(a,b))`.

### 4.5 Result-type rules

The full tables are in `types_{R3,R4,CGA4}.tsv`. Extracted rules, where N = mdims:

**`*` (geometric):**

| a \ b | Chain{L} (general) |
|---|---|
| Chain{0} | `Chain{L}` (scaling) |
| Chain{G}, 0<G<N | `Spinor` if G+L even, else `CoSpinor`; `Chain{N−G}` if L==N (via `⋆(~a)`) |
| Chain{N} | `Chain{N−L}` (via `complementlefthodge(~b)`); `Chain{0}` if L==N |
| Single{G} × Chain{L} | G=0 → `Chain{L}`; L=0 → `Single{G}`; G=N → `Chain{N−L}`, or `Single{0}` if L=N; L=N → `Single{N−G}`; otherwise Spinor/CoSpinor by the parity of G+L. Chain{G} × Single{L} is the mirror image (the TSV has every case) |

Other cases:
- Basis×Basis and Single×Single give `Single`/`Submanifold` (or a sum of Singles for non-diagonal metrics).
- Graded × Spinor/CoSpinor gives a Spinor or CoSpinor by parity (above). Graded × Multivector gives a Multivector. Pseudoscalar × Spinor gives CoSpinor if N is odd.
- Multivector × anything gives a Multivector. **`Chain{0}` × Multivector/Spinor/CoSpinor errors** (bug).

**`∧`:** `Chain{G}∧Chain{L}` gives `Chain{G+L}` if G+L≤N, else `Zero`. If either factor is `Chain{0}`, or the other is `Chain{N}`, the result goes via `Single(b)` and is `Single`/`Chain`. For example `Chain0∧Chain0 → Single0` and `Chain0∧ChainN → SingleN`. Graded∧Spinor gives a Spinor/CoSpinor, or a single `Chain`/`Single` through the early-outs (for example ℝ3 `Chain2∧CoSpinor → Chain3`).

**`∨`:** `Chain{G}∨Chain{L}` gives `Chain{G+L−N}` if G+L≥N, else `Zero`. `Chain{N}∨Chain{N} → Single{N}`, and `Chain0∨ChainN → Single0`.

**`⋅`:** `Chain{L}⋅Chain{G}` gives `Chain{L−G}` if L≥G, else `Zero`. Equal grades give `Chain{0}`. `ChainN⋅Chain0 → SingleN` and `ChainN⋅ChainN → Single0`. **Conformal:** Chain⋅Chain gives a `Multivector` whenever both grades are ≥1.

**`+`:** see §4.10. Examples: `Chain0+Chain2 → Spinor`, `Chain0+ChainN → Couple[N]`, `Chain1+Chain3 → CoSpinor` (in both ℝ3 and ℝ4), `Chain1+Chain2 → Multivector`.

Porting guidance: encode the *generic* rules as type-level functions (below). Treat the early-out shortcuts (scalar or pseudoscalar factors, next-grade projections) as optional specialisations: they are purely performance and type details. Numerical equality in dense form is what the oracle checks.

### 4.6 Sandwich products (`A:313-385,1560-1790`)

The generic definitions are `x⊘y = ~y * x * involute(y)` and `y>>>x = y * x * clifford(y)`. Both are verified in every signature.

`product_sandwich(a::TensorGraded{V,G}, b, swap)`:
1. **First pass:** `out = b' * a` where `b' = clifford(b)` (for ⊘) or `b` (for >>>). It uses the correct geometric kernel for the parity of `b`.
2. **Second pass:** `out2 = out * b''` where `b'' = b` (for ⊘) or `clifford(b)` (for >>>).
3. **Return `Chain{V,G}(out2[grade-G slice])`**: the result is projected onto grade G.

For an even `b`, `clifford(b) = reverse(b)` and `involute(b) = b`. For odd `b` there are sign identities, so the formulas agree with the generic ones.

- **Couple / PseudoCouple b** (`A:1737-1790`): a two-term version with the blades `B` and `1`/`I`. If `b` is not homogeneous in parity (Couple with odd `B`, or PseudoCouple with `isodd(grade B) ≠ isodd(N)`), it falls back to `⊘(a, multispin(b))`, and the result may be a Multivector (probe `a⊘p`).
- **Chain b** (`A:1658-1735`): the same structure with `par = parityclifford(L)`.
- Only the unrolled branch (`N < 12`) is implemented. **For `N ≥ 12` the generator returns `nothing`** (the loop branch is commented out). This is a bug in high dimensions.
- The Multivector/Couple-left methods go through the generic three-product formula: `⊘(x::Couple,y) = (scalar(x)⊘y) + (imaginary(x)⊘y)`, and similarly for PseudoCouple, Couple-right `>>>` and PseudoCouple-right `>>>`.

Semantics note: the projection is exact for versors. For a generic non-versor `b` in high dimension, the dropped grades could be non-zero. This does not happen for a vector `a` with even `b` in N ≤ 5, by reverse symmetry.

### 4.7 Couple / PseudoCouple / Phasor algebra (`P:479-826`)

Notation: `z = r + i·B` (Couple), `p = r·B + i·I` (PseudoCouple). `B2 = value(B*B)` or `value(wedgedot_metric(B,B,g))`. `κ(X) = value(abs2_inv(X)) = contraction(e_X,e_X)`; for example +1 for the Euclidean e12 (`A:473`).

Same-B formulas (Julia is correct unless flagged):

| op | Couple × Couple (same B) | PseudoCouple × PseudoCouple (same B) |
|---|---|---|
| `*` | `Couple{B}(r1r2 + i1i2·B2, r1i2 + i1r2)` (`P:573-575`) | `out = i-part cross terms = (r1B)(i2I) + (i1I)(r2B)`; `Couple{V,basis(out)}(r1r2·B2 + value(I*I)·i1i2, value(out))` (`P:576-579`) |
| `∧` | `Couple{B}(r1r2, r1i2 + i1r2)` (`P:590-592`) | `grade(B)==0 ? PseudoCouple{B}(r1r2, r1i2+i1r2) : Zero` (`P:593-595`) |
| `∨` | `grade(B)==N ? Couple{B}(r1i2+i1r2, i1i2) : Zero` (`P:598-600`) | `PseudoCouple{B}(r1i2+i1r2, i1i2)` (`P:601-603`) |
| `⋅` | `Couple{B}(r1r2 + i1i2·κ(B), i1r2)` (`P:608-610`) | `Couple{V,basis(o)}(r1r2κ(B) + i1i2κ(V), value(o))` with `o = contraction(volume(a), imaginary(b))` (`P:611-614`) |
| `+`/`-` | componentwise (`P:557`) | **BUG** `P:558`: real part uses `imagvalue(b)`; correct is componentwise |

Mixed cases (different B, or a Couple with other types) distribute over the parts, `op(a, scalar(b)) + op(a, imaginary(b))` etc. (`P:583-586,623-630,705-826`). Correct intended semantics: **bilinear extension** of the basis tables applied to `{r·1, i·B}` or `{r·B, i·I}`. Implement exactly that in Lean, for example by converting to the two-term sparse form. Julia deviations are in Appendix A #1–#8.

Scalar (TensorTerm{V,0}) with a Couple (`P:721-724`): `Couple{B}(s·r, s·i)`; the same for PseudoCouple (including under `∧`, `P:738-739`).

Phasor (`P:479-502,559-561,571-588,596,604,615`):
- `Phasor*Phasor = Phasor(amp1*amp2, angle1+angle2)`
- `Phasor/Phasor = Phasor(amp1/amp2, angle1−angle2)`
- `-Phasor = Phasor(−amp, angle)`
- `Phasor ± Phasor = polarize(complexify ± complexify)`
- Mixed with other TensorAlgebra: `complexify` first
- `∧`/`∨` of phasors: `Phasor(complexify ∧/∨ complexify)`
- `contraction`: `polarize(contraction(complexify, complexify))`

Low priority for the port.

### 4.8 Zero, Infinity and One (`P:379-477`)

Semantics are extended-real absorbing rules:

- Zero op Zero gives Zero for `+ - ⟑ ∧ ∨ contraction contraction_metric wedgedot_metric`. Infinity op Infinity gives Infinity for `⟑ ∧ ∨ contraction` (`P:379-393`).
- `x ± Zero = x`, `Zero + x = x`, `Zero − x = −x` (`P:395-398`). `x ± Infinity = Infinity` (note that `x − Infinity` is `+Infinity`; `P:407-410`). `Number ± Zero{V} = Single{V}(±a)` (`P:445-448`).
- `⟑` and `wedgedot_metric` of TensorTerm/Couple/PseudoCouple with Zero or Infinity return the special element (`P:419-428`), and likewise for `∧ ∨ contraction` (`P:430-443`). Chains and Multivectors return the special element through the `S<:Zero || S<:Infinity → return a` guards in the generators. Real or Complex `*` Zero/Infinity gives the special element (`P:449-461`).
- Division and inverse:
  - `inv(Zero)=Infinity`, `inv(Infinity)=Zero`, `One/Zero = Infinity` (`P:404-417`)
  - `Zero/b`: NaN-Single if `b` is zero, else Zero. **BUG** `P:400`: unbound `V`; also, probe `Zero(ℝ3)/0` gives an ambiguous method.
  - `Infinity/b`: NaN if `b` is infinite, else Infinity.
- Powers (`P:463-477`):
  - `x^Zero = One`; `Zero^Zero = One`; `Infinity^Zero = One`
  - `Zero^s`: `s==0 → One`, `s<0 → Infinity`, otherwise `Zero`
  - `Zero^Infinity = Zero`; `Infinity^Infinity = Infinity`
  - `s^Infinity` (s a scalar Single): `|s|==1 → One`, `|s|<1 → Zero`, otherwise Infinity
  - `Infinity^s`: `s==0 → One`, `s<0 → Zero`, otherwise Infinity
  - **BUG** `P:473`: `Number^Infinity` builds a range (`isless(c,1) : Zero(V) : b`), probe MethodError
- **Scalar Single/Submanifold × Chain shortcuts** (`P:521-528`): `Single{V,0}⟑Chain = Chain(a.v*b.v)`; `One⟑x = x` (grade-0 Submanifold, even across `V≠W`).

### 4.9 Unary maps on containers (`P:1324-1976`)

**Complements** (`P:1324-1487`):

```
Chain{V,G} b:  isdyadic → error;  istangent → c(Multivector(b))
     hodge variants: (!isdiag(V) || (field && !isinduced(g))) → complement{left|right}(metric(b,g))
     out[complement(N,B,D)] = p(V,B) · adj(b[B])       # p = parityright/left or parityright/lefthodge; adj = conj for hodge
     return Chain{V,N−G}
Multivector m: same, per blade → Multivector
Spinor m:   → (N odd ? CoSpinor : Spinor);   CoSpinor m: → (N odd ? Spinor : CoSpinor)
Couple z:   c(z) = Single{V,N,I}(r) + c(imaginary(z))      → PseudoCouple (probe ⋆(2+3v12) = 3v₃ + 2v₁₂₃)
PseudoCouple z: c(volume(z)) + c(imaginary(z))
Phasor: c(complexify(z))
```

`parityrighthodge(V,B)` for a DiagonalForm/Submanifold returns `±g(B)` as an Int or other number (`DS:operations.jl:293-310`). In Chain code it is applied with `MUL(par, val)`.

Chain-level `complement(N,B,D)` always uses `P=0`, which gives the plain bit complement. **The basis-level (Submanifold) complements in DirectSum differ in conformal spaces** (`DS:operations.jl:339-356`):
- the non-Hodge `!` multiplies by 2 or ½ when exactly one of ∞/∅ is present (`parityrightnull`, `L:generic.jl:215-222`), and
- Hodge uses `complement(...,P=hasinf+hasorigin)`.

Probe: `!v∞ = 2v∅₁₂₃` but `!(1.0v∞ + 0v₁) = 1.0v∅₁₂₃`. **Port the Chain/Multivector behaviour** (plain complement, validated) and treat the basis-level quirk as a DirectSum inconsistency.

**`metric` / `antimetric`** (`P:1630-1815`):
- Diagonal: `out[B] = paritymetric(V,B) · conj(b[B])` or `parityanti(V,B) · conj(b[B])`. A Bool parity means negate.
- Non-diagonal: `contraction(metrictensor(V,G), b)` (Chain), `contraction(metricextensor(V), m)` (Multivector), or `metriceven`/`metricodd`. The `anti` versions use `antitensor`/`antiextensor`/`antieven`/`antiodd`, **which error in conformal spaces** (probe).
- Field variant: `contraction(g, b)`.
- Couple: `scalar(z) + metric(imaginary(z))`.

**Reverse family** (`P:1816-1976`), for p ∈ {parityreverse, parityinvolute, parityconj=parityreverse, parityclifford} and the grade function `grade` (or `antigrade = N − grade` for antireverse):
- Chain: if D==0 and there is no sign flip, return `b`; otherwise negate everything.
- Multivector/Spinor/CoSpinor: flip the sign per grade slot.
- Couple: flip only the imaginary part by `p(g(B))` (Appendix A #9 for antireverse).
- PseudoCouple: flip the real part by `p(g(B))` and the imaginary part by `p(g(V))`.
- Phasor: flip the angle.
- `conj(m::Multivector)` is **identical to reverse** and does not conjugate coefficients (probe).

**even/odd** (`P:1488-1522`): Multivector → `Spinor` (even grades) or `CoSpinor` (odd grades).
**real/imag** (`P:1523-1629`): keep grade k iff `!parityreverse(k)` (real: k mod 4 ∈ {0,1}) or `parityreverse(k)` (imag: k mod 4 ∈ {2,3}). Same container type.

**adjoint** (`P:943-1070`):
- Non-dyadic: `Chain{dual(V),G}(conj.(v))`; the same for Multivector, Spinor and CoSpinor.
- Dyadic: permutes coefficients with `dual(V,ib,M)`.
- **BUG** `P:1024`: `$VECS` is undefined in the N≥12 dyadic Spinor branch.
- Probe: `m'` has type `Multivector{⟨---⟩'}` and displays with `w¹…` names.

### 4.10 `+`/`-` type promotion (`P:504-569,630-703,852-941`; `A:744-1140`)

| a | b | result |
|---|---|---|
| TensorTerm{L} | TensorTerm{G} with the same basis | `Single{V,L}(a±b)` |
| grade-0 TensorTerm | other TensorTerm | `Couple{V,basis(b)}(a, ±b)` (only when non-tangent and non-conformal) |
| TensorTerm | grade-0 TensorTerm | `Couple{V,basis(a)}(±b, a)` |
| TensorTerm{N} (pseudoscalar) | TensorTerm | `PseudoCouple{V,basis(b)}(±b, a)` |
| TensorTerm | TensorTerm{N} | `PseudoCouple{V,basis(a)}(a, ±b)` |
| TensorTerm{G} | TensorTerm{G}, different basis | `Chain{V,G}` |
| both even grades | | `Spinor`; both odd → `CoSpinor`; otherwise `Multivector` |
| TensorTerm{L} | Chain{G} | same grade → `Chain`; `L==0 && G==N` → `Couple{V,I}`; `G==0` → `Couple{V,basis(a)}`; `G==N` → `PseudoCouple{V,basis(a)}`; same parity → `Spinor`/`CoSpinor`; otherwise `Multivector` |
| TensorTerm{G} | Spinor | even G → `Spinor`, odd → `Multivector` |
| TensorTerm{G} | CoSpinor | odd G → `CoSpinor`, even → `Multivector` |
| Chain{G} | Chain{L} (G≠L) | if either grade is 0 or N → via `Single(chain)`; same parity → `multispin` (Spinor/CoSpinor); otherwise `Multivector` (`P:880-886`) |
| Chain{G} | Spinor / CoSpinor | same-parity container, otherwise Multivector (`P:919-934`) |
| Spinor | CoSpinor | Multivector (`P:566-567`) |
| Multivector | anything | Multivector |
| Couple{B} | Couple{B} | Couple; different B → through the parts |
| Couple | TensorTerm | Couple if b is scalar or has basis B; otherwise `multispin(a) ± b` |
| TensorAlgebra | Number/Symbol/Expr (NSE) | `a ± b*One(V)` (`P:852-859`) |

`multispin(Couple{B})` is a Spinor if grade(B) is even, otherwise a Multivector. `multispin(PseudoCouple)` is a Spinor if N and grade(B) are both even, a CoSpinor if both are odd, otherwise a Multivector (`M:999-1011`).

### 4.11 Scalar-field multiplication (`P:830-851`, `P:1093-1112`)

For F ∈ {Real, Complex} and every container X, `F*X` and `X*F` return the same container with scaled values. `F*Submanifold` gives `Single`. `Single` uses the symbolic-safe `∏`. For symbolic or unknown fields, `generate_products(Field,…)` also defines `-Single`, `Single⟑Single`, `∨(Field,Field)=0`, `∧(Field,Field)=a*b` and `∧(F,TensorTerm) = Single`. `generate_products` is instantiated for Real, Complex, Rational{BigInt}, BigFloat, BigInt, Complex{Big*} and SymField (`Grassmann.jl:361-367`).

### 4.12 Complex coefficients

Probe-verified quirks. Recommendation: Float-only first, and document these.

- `contraction` on Single/Chain uses `dot(x,y) = conj(x)*y`. Examples: `(1im*v1)⋅v1 = −1im`, and `a⋅b` for complex Chains is sesquilinear, so `abs2(chain)` is real.
- Multivector/Spinor contraction loops use plain `*` (no conj).
- Chain⋅Single (the swap path) passes the Single's coefficient as the first `dot` argument. Chain⋅Submanifold and Submanifold⋅Chain do not conjugate.
- `⋆`, `complementlefthodge`, `metric`, `antimetric` and `adjoint` conj the coefficients. `!`, `complementleft`, `~`/`reverse`/`conj` do not.

### 4.13 Powers, abs2 and inverse (product consumers in algebra.jl, summarised)

- `literal_pow`: `x^0 = one(x)`, `x^1 = x`, `x^2 = x*x`, `x^3 = x*x*x`, `x^-1 = inv(x)`, `x^-2 = (i=inv(x); i*i)` (`A:408-418`).
- `^(v::TensorTerm, i::Integer)` (`A:424-438`): `i==0` gives `getbasis(V,0)`; `i==1` gives `v`. Otherwise `j=(i-1)%4` and the result is the basis raised to the power `j+1` by repeated `*` (the basis-power cycle has period 4). It is then scaled by `value(v)^i`. Probe: `v12^3 = -1v₁₂`, `(2v12)^3 = -8v₁₂`.
- `^(v::TensorAlgebra, i::Integer)` (`A:440-470`):
  - For a Chain with `N ≤ 3` and no tangent: `sq = contraction2(~v,v)` (a scalar Chain{0}); the result is `sq^(i÷2)`, times `v` if `i` is odd. Probe: `a^2 = 14v :: Chain{V,0}`, `B^2 = -14v`.
  - A Couple whose `B*B == -1` goes through `Complex^i`.
  - Otherwise, for `i < 8`, repeated `out *= v` starting from `One(V)`. For `i ≥ 8`, binary exponentiation over the bits of `i` from LSB up.
- `abs2(t::TensorGraded) = contraction(t,t)`; `abs2(t) = (~t)*t`, reduced to a scalar if `isscalar` (`AT:437-440`).
- `inv` (Chain): `~a / value(scalar(abs2(a)))`.
- `inv` (Multivector/Spinor): `rm = ~m; d = rm*m`. If `d` is scalar-normed, return `rm/scalar(d)`; else if `d` is a single grade k, return `rm/d(k)`; otherwise throw "inv(m) is undefined". Probe: a generic ℝ3 Multivector throws (`A:475-535`, Multivector at `A:486`).
- Couple `inv` and `/` use robust complex division with `B² = abs2_inv(B)` (`A:553-698`).

### 4.14 Tangent and dyadic spaces (skip in v1)

`derive_mul` (`P:29-75`), `derive_pre`/`derive_post` (`P:77-131`) and `derive` (`P:25-26`) are active only when `istangent(V) && isdyadic(V)`. Otherwise `derive_mul(V,A,B,a,b,op) = op(a,b)` and `derive_mul(V,A,B,v,x) = v`. For tangent spaces, `symmetricmask(V,a,b) = (a&~D, b&~D, (a|b)&D, a&b&D)` (`L:generic.jl:92-97`) splits the Grassmann bits from the symmetric (derivation) bits. It multiplies by `getbasis(loworder(V),Z)` and truncates by `order > diffmode`.

---

## 5. Display (strings observed in probes; the full rules belong to the multivectors.jl spec)

- `Submanifold`: `v₁₂`; `One`: `v`; `Zero`: `𝟎`; `Infinity`: `∞`.
- `Single`: `-1v₁₂`, `1v₃`, `2v` (grade 0). Complex: `(0 + 1im)v`.
- `Chain`: all components shown, including zeros: `1v₁ + 1v₂ + 0v₃`, `-3v₁₂ - 6v₁₃ - 3v₂₃`. Grade 0: `32v`. Complex: `(0+1im)v`.
- `Spinor` / `Quaternion`: the scalar has no `v`, and zeros are shown: `32 - 3v₁₂ - 6v₁₃ - 3v₂₃`, `-14 + 0v₁₂ + 0v₁₃ + 0v₂₃`.
- `CoSpinor`: `-8v₁ - 8v₂ + 8v₃ + 2v₁₂₃`.
- `Multivector`: the scalar is always printed; **zero non-scalar components are omitted**: `0 + 1v₁ + 1v₁₂`, `0 + 4v₁₂₃`.
- `Couple`: `2 + 3v₁₂`; `PseudoCouple`: `2v₁₂ + 3v₁₂₃`, `-1v₁₂ + 0v₁₂₃`.
- Dual space: `1.0 + 2.0w¹ + …`, with signature `⟨---⟩'`.
- Conformal: `v∞`, `v∅`, `v∞∅`, `v∞₁₂₃`.
- Types print with aliases: `Quaternion{⟨111⟩, Int64}`, `GaussianInteger{⟨111⟩, v₁₂, Int64}`.

---

## 6. Golden examples (verbatim)

### 6.1 From the test suite

From `test/runtests.jl`:

```julia
@basis "++++" s e; e124 * e23 == e134
[Λ(3).v32^2, Λ(3).v13^2, Λ(3).v21^2] == [-1Λ(3).v for j∈1:3]
@basis "++++"; (v1*v1, v1⋅v1, v1∧v1) == (1,1,0)
@basis "-+++"; (v1*v1, v1⋅v1, v1∧v1) == (-1,-1,0) ; (v2*v2,v2⋅v2,v2∧v2) == (1,1,0)
basis"-+++"; h = 1v1+2v2; h⋅h == 3v
Λ(62).v32a87Ng == -1Λ(62).v2378agN
```

From `test/issuestests.jl`:

```julia
@basis S"∞∅++": (v∞^2, v∅^2, v1^2, v2^2) == (0v, 0v, v, v); v∞ ⋅ v∅ == -1v; v∞∅^2 == v
                (v∞∅ * v∞, v∞∅ * v∅) == (-1v∞, v∅); (v∞*v∅, v∅*v∞) == (-1 + 1v∞∅, -1 - 1v∞∅)
basis"2": a = v + v1 - v1; a == v; typeof(a) <: Couple; a == 1
basis"+++": (v1+v2) + (v1+v2)*(v1+v2) == 2 + 1v1 + 1v2
@basis S"∞∅+": v∅*v∞ == -1 - v∞∅ ; v∅*(-v∞) == 1 + v∞∅
```

From `test/generictests.jl`, holding for V ∈ {3, V"+++", S"∞+", S"∅+", V"-+++", S"∞∅+"}:
- associativity and distributivity of `*`
- for vectors: `a⋅b == 0.5(a*b+b*a)`, `a∧b == 0.5(a*b−b*a)`, `a*b == a⋅b + a∧b`, `a*b == 2a⋅b − b*a`, `a*a == a⋅a`

### 6.2 From the docs

From `docs/src/algebra.md`:

```julia
julia> wedge(Chain(1,2,3),Chain(4,5,6))          # -3v₁₂ - 6v₁₃ - 3v₂₃
julia> Chain(1,2,3)*Chain(4,5,6)                  # 32 - 3v₁₂ - 6v₁₃ - 3v₂₃
julia> complementright(Multivector(1,2,3,4,5,6,7,8))   # 8 + 7v₁ - 6v₂ + 5v₃ + 4v₁₂ - 3v₁₃ + 2v₂₃ + 1v₁₂₃
julia> complementleft(Multivector(1,2,3,4,5,6,7,8))    # same as above (N=3 odd)
julia> @basis S"++-"; hodge(Multivector{V}(1,2,3,4,5,6,7,8))  # -8 - 7v₁ + 6v₂ + 5v₃ - 4v₁₂ - 3v₁₃ + 2v₂₃ + 1v₁₂₃
julia> vee(Chain{V}(1,2,3),hodge(Chain{V}(4,5,6)))    # -4v   (S"++-")
julia> basis"3"; wedge(!v12,!v23)                  # -1v₁₃
julia> !vee(v12,v23)                               # -1v₁₃
julia> wedge(v12,!v12)                             # 1v₁₂₃
julia> 1 + v12 - v13                               # 1 + 1v₁₂ - 1v₁₃ + 0v₂₃  :: Quaternion
julia> sqrt(2) + G42.v14                           # Couple{⟨1__1⟩, v₁₄, Float64}
```

Docs caveats. The docs claim `η << ω = η < ~ω` (`algebra.md:508`). The code (`AT:260`) is `contraction(ω,~η)`, which is Dorst `η⌋ω`. The contraction table at `algebra.md:616-620` gives "Grassmann right `<η>_r > <ω>_s = <~η ω>_{r−s}`". That disagrees with the code whenever r−s ≡ 2,3 (mod 4): for example `contraction(e123,e3) = +e12`, but `<~e123 e3>_2 = −e12`. **Follow the code.** The verified identities are in §0 item 4.

### 6.3 Probe goldens: ℝ3

Set-up: `@basis ℝ3; a=1v1+2v2+3v3; b=4v1+5v2+6v3; B=1v12+2v13+3v23; s=1+B; c=a+7v123; m=Multivector{ℝ3}(1,…,8)`.

```
v2*v1 = -1v₁₂        v12*v12 = -1v      v123*v123 = -1v   v1∧v1 = 𝟎
v12∨v23 = v₂         v1∨v23 = v         v1∨v2 = 𝟎
contraction(v12,v2) = -1v₁   contraction(v12,v1) = v₂   contraction(v1,v12) = 𝟎
v1⨼v12 = v₂   v1×v2 = 1v₃   ⋆v1 = 1v₂₃   ⋆v12 = 1v₃
a*b = 32 - 3v₁₂ - 6v₁₃ - 3v₂₃ (Spinor)   a⋅b = 32v (Chain{0})   a×b = -3v₁ + 6v₂ - 3v₃
a∨(a∧b) = 0v (Chain{0})    a∨b = 𝟎
a*B = -8v₁ - 8v₂ + 8v₃ + 2v₁₂₃ (CoSpinor)    B*a = 8v₁ + 8v₂ - 8v₃ + 2v₁₂₃
B*B = -14 + 0v₁₂ + 0v₁₃ + 0v₂₃   a∧B = 2v₁₂₃   B⋅a = -8v₁ - 8v₂ + 8v₃   a⋅B = 𝟎
(1+B)*(1+B) = -13 + 2v₁₂ + 4v₁₃ + 6v₂₃   (a+B)*(a+B) = 0 + 4v₁₂₃
(1+v12)*(1+v12) = 0 + 2v₁₂ (Couple)
a>>>B = 2v₁₂ + 36v₁₃ + 38v₂₃   (1+B)>>>a = 15v₁ - 18v₂ - 51v₃   a⊘(1+B) = -17v₁ - 50v₂ - 19v₃
v1⊘v2 = 1v₁   v1>>>v2 = 1v₂   a∗b = 32 - 3v₁₂ - 6v₁₃ - 3v₂₃   B∗B = 14 + 0v₁₂ + 0v₁₃ + 0v₂₃
a⊛b = 32v   veedot(a,b) = 3v₁ - 6v₂ + 3v₃ - 32v₁₂₃   antidot(a,b) = 32v₁₂₃
a<<B = -8v₁ - 8v₂ + 8v₃   a>>B = 𝟎
s*c = -12v₁ + 24v₂ - 12v₃ + 9v₁₂₃   c*s = -28v₁ + 8v₂ + 4v₃ + 9v₁₂₃   c*c = -35 + 42v₁₂ - 28v₁₃ + 14v₂₃
s∨s = 0v₁+0v₂+0v₃+0v₁₂₃ (CoSpinor)   c∨c = 14v₁ + 28v₂ + 42v₃ + 49v₁₂₃   s∨c = 9 + 7v₁₂ + 14v₁₃ + 21v₂₃
contraction(s,s) = 15 + 1v₁₂ + 2v₁₃ + 3v₂₃   contraction(c,c) = 63 + 21v₁₂ - 14v₁₃ + 7v₂₃
a∨s = 2v (Chain{0})   contraction(s,a) = -8v₁ - 8v₂ + 8v₃ + 0v₁₂₃
m*m = -144.0 - 108.0v₁ + 102.0v₂ - 72.0v₃ + 74.0v₁₂ - 36.0v₁₃ + 46.0v₂₃ + 48.0v₁₂₃
m∧m = 1.0 + 4.0v₁ + 6.0v₂ + 8.0v₃ + 10.0v₁₂ + 12.0v₁₃ + 14.0v₂₃ + 48.0v₁₂₃
m∨m = 48.0 + 32.0v₁ + 48.0v₂ + 64.0v₃ + 80.0v₁₂ + 96.0v₁₃ + 112.0v₂₃ + 64.0v₁₂₃
contraction(m,m) = 204.0 + 19.0v₁ - 63.0v₂ + 77.0v₃ + 37.0v₁₂ - 18.0v₁₃ + 23.0v₂₃ + 8.0v₁₂₃
⋆m = 8.0 + 7.0v₁ - 6.0v₂ + 5.0v₃ + 4.0v₁₂ - 3.0v₁₃ + 2.0v₂₃ + 1.0v₁₂₃
antireverse(m) = -1.0 - 2.0v₁ - 3.0v₂ - 4.0v₃ + 5.0v₁₂ + 6.0v₁₃ + 7.0v₂₃ + 8.0v₁₂₃
real(m) = 1.0 + 2.0v₁ + 3.0v₂ + 4.0v₃     imag(m) = 0.0 + 5.0v₁₂ + 6.0v₁₃ + 7.0v₂₃ + 8.0v₁₂₃
v1⋅m = 2 + 1v₁ (Couple!)   v1∧m = 0 + 1v₁ + 3v₁₂ + 4v₁₃ + 7v₁₂₃   v12∨m = 4 + 6v₁ + 7v₂ + 8v₁₂
z=2+3v12, w=5-1v12: z*w = 13 + 13v₁₂   z∧w = 10 + 13v₁₂   contraction(z,w) = 7 + 15v₁₂   z∨w = 𝟎
⋆z = 3v₃ + 2v₁₂₃ (PseudoCouple)   p=2v12+3v123: p*p = -13 - 12v₃ (Couple{v₃})  contraction(p,p) = 13 + 6v₃
a^2 = 14v   a^3 = 14v₁ + 28v₂ + 42v₃   B^2 = -14v   s^9 = 139441 - 36839v₁₂ - 73678v₁₃ - 110517v₂₃
```

### 6.4 Probe goldens: other signatures

Minkowski `S"-+++"`, with a=v1+2v2+3v3+4v4 and b=2v1−v2+5v3+v4:

```
contraction(v12,v12) = -1v   ⋆v1 = -1v₂₃₄   complementleft(v1) = -1v₂₃₄   !v1 = 1v₂₃₄
a*b = 15 - 5v₁₂ - 1v₁₃ - 7v₁₄ + 13v₂₃ + 6v₂₄ - 17v₃₄ + 0v₁₂₃₄   a⋅b = 15v
(a∧b)⋅a = 41v₁ - 58v₂ + 95v₃ - 32v₄   a×b = -17v₁₂ - 6v₁₃ + 13v₁₄ + 7v₂₃ - 1v₂₄ + 5v₃₄
metric(v12) = -1v₁₂   antimetric(v12) = 1v₁₂
```

DiagonalForm(2,3,−1):

```
e1*e1 = 2v   e12*e12 = -6v   e12*e2 = 3v₁   contraction(e12,e2) = -3v₁   ⋆e1 = 2v₂₃   !e1 = 1v₂₃
x=1e1+2e2+3e3: x*x = 5 + 0v₁₂ + 0v₁₃ + 0v₂₃   ⋆x = -3v₁₂ - 6v₁₃ + 2v₂₃
```

DiagonalForm(0,1,1,1), degenerate:

```
v1*v1 = 0v  v12*v1 = 0v₂  contraction(v12,v1) = 𝟎  ⋆v1 = 0v₂₃₄  antimetric(v234) = 0v₂₃₄
```

Conformal:
- `S"∞∅+++"`: `⋆v∞ = 1v∞₁₂₃`, `⋆v∅ = −1v∅₁₂₃` (basis level). `C.v1*C.v∞ = −1v∞₁`. `(v∞+v1)*(v∅+v1) = 0 + 1v∞∅ + 1v∞₁ − 1v∅₁` (Spinor).
- `S"∞∅++"`: `paritygeometric(V,0b0101,0b0110) = [(0b0011,−1),(0,1)]`, i.e. `(v∞₁)(v∅₁) = 1 − v∞∅`.

ℝ4 with `s = 1+2v12+3v34+4v1234` and `c = v1+v234`:

```
s∨s = 20 + 16v₁₂ + … + 24v₃₄ + 16v₁₂₃₄      s∨c = 4v₁ + 2v₂ + … + 4v₂₃₄
(v1+v2)*v1234 = 0v₁₂₃ + 0v₁₂₄ - 1v₁₃₄ + 1v₂₃₄ (Chain{3})   v1234*(v1+v2) = … + 1v₁₃₄ - 1v₂₃₄
contraction(v1234, s) = 4 + 3v₁₂ + 2v₃₄ + 1v₁₂₃₄
a=v1+2v2+3v3+4v4, s=1+2v12+3v34+v13 (Float): a⊘s = 15v₁ + 6v₂ - 45v₃ + 12v₄   s>>>a = 43v₁ - 2v₂ - 1v₃ - 24v₄
```

---

## 7. Dependencies on other chakravala packages (symbols used by the products layer)

- **Leibniz**:
  - parity: `parityreverse`, `parityinvolute`, `parityclifford`, `parityconj`, `parityright`, `parityleft`, `parityrighthodge`, `paritylefthodge`, `parityrightnull`/`parityleftnull` (+`pre`)
  - masks and complements: `complement(N,B,D,P)`, `symmetricmask`, `symmetricsplit`, `diffcheck`, `diffmask`, `diffvars`, `diffmode`, `loworder`, `grade_basis`, `grade(V,B)`, `pseudograde`
  - indices and sizes: `indices`, `digits_fast`, `bit2int`, `indexbits`, `binomial` (=`gdims`), `gdimsall`, `binomsum`, `spinsum`, `antisum`, their `_set`/`cumsum`, `bladeindex`, `basisindex`, `spinindex`, `antiindex`, `indexbasis`, `lowerbits`, `expandbits`, `intlog`
  - code generation: `insert_expr`, `mvec`, `svec`, `mvecs`, `svecs`, `promote_type`
  - limits: `cache_limit=12`, `sparse_limit=22`, `algebra_limit=8`
  - fields: `Field=Real`, `Fields=(Real,Complex)`, `ExprField`, `check_field`, `extend_field`, `isnull`
  - `indexsplit`, `Derivation`, `derive`
- **DirectSum**:
  - types: `Submanifold`, `Signature`, `DiagonalForm`, `Single`, `Zero`, `One`, `Infinity`, `Basis`/`Λ`
  - basis access and metric: `getbasis`, `isdiag`, `hasconformal`, `hasinf`, `hasorigin`, `istangent`, `isdyadic`, `isdual`, `dual`, `dyadmode`, `metric`, `metrictensor`, `metricextensor`, `paritymetric`, `parityanti`, `signbool`
  - complements and involutions: complement/metric/antimetric methods on `Submanifold` (`DS:operations.jl:339-380`), `antireverse = pseudoreverse` (`DS:generic.jl:234`), `Base.:~ = conj` (`DS:generic.jl:187`)
  - `⊕`, `options`, `mdims`, `rank`, `grade`
- **AbstractTensors**:
  - types: `TensorAlgebra`, `TensorGraded`, `TensorTerm`, `TensorMixed`, `TAG`
  - operator aliases: `wedgedot`/`⟑`/`⊖`/`times`, `∗`, `⊛`, `⨼`, `⨽`, `<<`, `>>`, `<`, `>`, `|`, `dot→contraction`, `cross`, `⊗`, `∘→expansion`, `sandwich`/`⊘`, `cosandwich`, `antisandwich`, `veedot`/`⟇`, `interop`
  - symbolic arithmetic: `∑`, `∏`, `SUB`, `-`, `conj`, `dot`
  - `abs2` definitions (`AT:437-440`), `complementright=!`, `hodge=⋆`
- **StaticVectors**: `Values`, `Variables`, `FixedVector`, `evens`, `countvalues`, `evenvalues`, `list`
- **AbstractLattices**: `∧ = wedge`, `∨ = vee`
- **External**: Combinatorics (combination order via Leibniz), LinearAlgebra (`dot`, `cross`, `I`, `UniformScaling`, `isdiag`)

---

## 8. Lean 4 porting notes

### 8.1 Compile-time indices versus runtime values

| Julia | Lean recommendation | Cost |
|---|---|---|
| `V` (manifold) | explicit index `(V : Sig)`. `Sig` is a structure: `n : Nat`, metric kind (euclid, sign mask, diagonal values, conformal flags, general Gram). Make common spaces `abbrev`s (`R3`, `STA`, `CGA3`, `PGA3`) so products over them become closed terms | zero |
| `G` (grade of Chain) | index `(G : Nat)`; storage `FVec (binom V.n G)`. **`binom n k = 0` for k>n, so `Chain V (G+L)` beyond N is automatically the empty Zero** | zero |
| Spinor/CoSpinor | one type `Half V (odd : Bool) α` of length `2^(n-1)`; `Spinor := Half V false`, `CoSpinor := Half V true` | zero; parity arithmetic becomes `Bool.xor` at type level |
| `B` (blade of Submanifold/Single/Couple/PseudoCouple) | type-level `BitVec V.n` or `UInt64` literal index, as in Julia. The sign of `Single V B₁ * Single V B₂` is then a closed term over literals. Result type `Single V (B₁ ^^^ B₂)` for diagonal non-degenerate metrics | zero |
| `T` (field) | type parameter `α` with a class `Coeff α` (Float first, then Int/Rat) | – |
| `X` (length) | derived; never stored | – |
| result-type rules (§4.5) | `HMul`/`HAnd`-style instances with an `outParam` result, e.g. `instance : HMul (Chain V G α) (Chain V L α) (Half V ((G+L)%2==1) α)`. `∨` needs `if G+L ≥ V.n then Chain V (G+L-V.n) α else ZeroT V` (a type-level `if` on decidable Nat; it reduces on literals). Contraction: `if L ≥ G then Chain V (L-G) α else ZeroT V` | zero |
| Julia early-out shortcuts (scalar or pseudoscalar factors, next-grade Couple results) | **optional**. Implement as fast paths inside kernels, not as different result types, unless a literal-grade instance with higher priority is wanted. The oracle compares dense values | zero |
| coefficients | runtime `FloatArray`-backed `FVec n` (structure `data : FloatArray`, `h : data.size = n`). **Avoid `Vector Float n`/`Array Float` for hot data: elements are boxed** | – |

Sketch of the core types and one kernel (illustrative Lean 4 v4.35 style; not compiled):

```lean
structure FVec (n : Nat) where
  data : FloatArray
  size_eq : data.size = n

inductive MetricKind | euclid | sign (neg : UInt64) | diag (g : Array Float) | gram (G : Array (Array Float))
structure Sig where
  n : Nat
  kind : MetricKind
  conformal : Bool := false        -- ∞∅ null pair at bits 0,1 (gram kind)

structure Chain (V : Sig) (G : Nat) where v : FVec (binom V.n G)
structure MV    (V : Sig)          where v : FVec (2 ^ V.n)
structure Half  (V : Sig) (odd : Bool) where v : FVec (2 ^ (V.n - 1))
abbrev Spinor V := Half V false
abbrev CoSpinor V := Half V true
structure Single (V : Sig) (B : UInt64) where c : Float           -- grade = popcount B (type level)
structure Couple (V : Sig) (B : UInt64) where re : Float; im : Float
structure PseudoCouple (V : Sig) (B : UInt64) where re : Float; im : Float

@[inline] def reorderNeg (a b : UInt64) : Bool := Id.run do
  let mut a := a >>> 1; let mut s : UInt64 := 0
  while a != 0 do s := s + (a &&& b).popCount; a := a >>> 1   -- UInt64.popCount (or a local popcount)
  return s % 2 == 1

structure Plan where           -- one entry per non-zero (i,j) → k contribution
  ia : Array UInt16
  ib : Array UInt16
  ic : Array UInt16
  coef : FloatArray

@[noinline] def mulPlan (V : Sig) (sa sb : Shape) : Plan := ...   -- closed term when V is an abbrev

@[specialize] def runPlan (p : Plan) (a b : FloatArray) (out : FloatArray) : FloatArray := Id.run do
  let mut o := out
  for t in [0:p.coef.size] do
    let k := p.ic[t]!.toNat
    o := o.set! k (o[k]! + p.coef[t]! * a[p.ia[t]!.toNat]! * b[p.ib[t]!.toNat]!)
  return o

instance : HMul (Chain V G) (Chain V L) (Half V ((G + L) % 2 == 1)) := ⟨fun a b => ...⟩
```

`Nat.choose` is Mathlib. To avoid a Mathlib dependency, define `Grassmann.binom` by structural recursion with `@[simp]` lemmas. Decide-reduction works for small literals. Proving `binom n (n-g) = binom n g` needs `g ≤ n`, so give `Chain` a `Fact (G ≤ V.n)` or an erased proof field for complements.

### 8.2 Hot paths and how Julia gets its speed

1. **`@generated` unrolling.** When a product is small, the generator enumerates all blade pairs at compile time and emits straight-line code `out_k = ∑(∏(±g, a_i*b_j), …)` with signs and metric factors as literals (probe: `Grassmann.product(typeof(a),typeof(b))` prints this expression). Thresholds:
   - C(N,G)·C(N,L) < 4096 for Chain×Chain and Chain×Term (`product*`)
   - N < 12 for graded×Multivector/Spinor and for complement/reverse loops on Multivectors
   - N < 6 (`cache_limit/2`) for Multivector×Multivector (`product_loop`, `generate_loop_*`)
   - C(N,G) < 4096 for unary Chain maps
2. **Memoized parity caches** above those thresholds: `parity_cache[n][metric][a][b]` (`Y:325-360`), the regressive/interior caches keyed by (n, metric, options, a, b) (`Y:373-439`), and the Leibniz caches for index/basis/bladeindex.
3. **Stack-allocated immutable tuples** (`Values`/SVector), and dispatch on type parameters so that there is no runtime branching on V, G or B.

Lean equivalents, in order of effort:

- **(a) Product plan tables.**
  - `def plan (V : Sig) (op : Op) (sa sb : Shape) : Plan`, where `Plan` holds `ia ib ic : Array UInt16` and `coef : FloatArray` (sign × metric), with zero contributions removed.
  - Evaluation is `for t in [0:plan.size]: out[ic[t]] += coef[t]*a[ia[t]]*b[ib[t]]`.
  - If `V` is a closed `abbrev`, `plan R3 .mul (.chain 1) (.chain 1)` is a **closed term**: Lean's compiler extracts it and evaluates it once at initialization. Use `@[noinline]` on `plan` so it is not re-inlined.
  - This reproduces Julia's unrolled arithmetic apart from interpretation overhead of about 1–2 ns per term.
- **(b) Metaprogrammed kernels**: a `gen_products R3` command elaborator that emits `@[inline] def mulMV_R3 (a b : FVec 8) : FVec 8 := ⟨#[...]⟩` with literal signs. This mirrors `@generated` for the handful of signatures that matter: ℝ2, ℝ3, ℝ4, STA `-+++`, PGA `0+++`, CGA `∞∅+++`.
- **(c) Runtime bit kernels** for large N (> 8): `reorderSign` via popcount (`UInt64` popcount is available), metric overlap via `popcount (a &&& b &&& neg)`, and precomputed `indexBasis`/`bladeIndex` arrays per n, cached as closed terms per `n`.
- The storage-order permutation between bitmask and grade-lexicographic order must be table-driven, with `toBits : Array UInt64` and `fromBits : Array UInt32` per n.

### 8.3 Tricky semantics checklist

1. Contraction conventions (§0 item 4). `⋅` on equal-grade Chains returns `Chain V 0`, not a scalar.
2. Regressive and complement sign formulas (§4.1), including `complementleft`'s extra `(-1)^{[G odd ∧ N even]}`.
3. Orderings (§3.2).
4. The sandwich grade projection (§4.6).
5. Couple creation rules and their bugs (§4.7, Appendix A).
6. Zero/Infinity absorbing semantics (§4.8).
7. Complex conjugation rules (§4.12).
8. Conformal null basis: use the Gram path (§4.2), and do not replicate DirectSum's basis-level ½/2 complement factors.
9. In a degenerate diagonal metric, products give zero-valued Singles but contraction gives `Zero`. Harmless numerically.
10. `conj` = `~` = reverse (no complex conjugation); `'` is the adjoint, which conjugates and dualizes.
11. `x − Infinity = Infinity` (not −∞).
12. `Chain{0} × Multivector/Spinor/CoSpinor` errors in Julia. Implement it as scaling.

### 8.4 Proofs that speed up development (cheap, high value)

- Bit-level lemmas proved by `bv_decide`/`decide` over `BitVec 8`:
  - `reorderSign a b ⊕ reorderSign b a = (|a||b| − |a∧b|) mod 2`
  - `geom` sign antisymmetry for disjoint vectors
  - `complement (complement x) = x`
- For every blade of the common signatures up to n=5, by `decide` (or `native_decide` if slow): associativity `(ab)c = a(bc)`; `cl(!x) = x`; `⋆x = (~x)·I`; De Morgan `!(a∨b) = !a ∧ !b`; `contraction(a,b) = (~b)⌋a`; `a·b = a⌋b + a∧b` for vectors. These catch sign-table bugs immediately.
- Index roundtrips: `bladeIndex n (indexBasis n g)[i] = i`, and the sizes `Σ_g binom n g = 2^n` and `Σ_{g even} = 2^(n-1)` (n ≥ 1). These are needed to cast storage lengths, so prove them with `omega`/`simp` once.
- Type-level grade facts: `binom n k = 0` for `k > n` (Zero by construction); `(G+L)%2` parity algebra via `decide`.

### 8.5 Suggested module decomposition (products-related part only, about 5.2k LOC)

| Module | Content | LOC |
|---|---|---|
| `Grassmann/Basis/Bits.lean` | popcount, reorderSign, complement index, ρ, grade sign functions | 200 |
| `Grassmann/Basis/Index.lean` | binom, indexBasis, bladeIndex/basisIndex/spinIndex/antiIndex tables, roundtrip lemmas | 300 |
| `Grassmann/Metric.lean` | `Sig` kinds, `g(X)`, Gram access, isDiag/conformal flags (shared with the DirectSum port) | 150 |
| `Grassmann/Parity.lean` | geom (diagonal), wedge, regressive, interior, complement parities, Chevalley geom for a Gram | 400 |
| `Grassmann/Kernel/Plan.lean` | product plans per (sig, op, shapes), closed-term caching | 300 |
| `Grassmann/Kernel/Dense.lean` | evaluation of plans over `FVec`, grade-sparse iteration | 250 |
| `Grassmann/Kernel/Codegen.lean` | command elaborator emitting unrolled kernels for chosen signatures | 400 |
| `Grassmann/Product/Term.lean` | Submanifold/Single × Submanifold/Single for all ops | 250 |
| `Grassmann/Product/Graded.lean` | Chain×Chain / Term×Chain for `* ∧ ∨ ⋅` with fast paths | 400 |
| `Grassmann/Product/Mixed.lean` | Multivector/Half × everything | 300 |
| `Grassmann/Product/Couple.lean` | Couple/PseudoCouple (correct formulas), Phasor minimal | 350 |
| `Grassmann/Product/Special.lean` | Zero/One/Infinity rules, scalar multiplication, powers | 150 |
| `Grassmann/Product/Derived.lean` | `⨼ << >> ∗ ⊛ × veedot antidot ⊘ >>> cosandwich antisandwich ∥`, integer powers | 300 |
| `Grassmann/Unary/Complement.lean` | `! complementleft ⋆ complementlefthodge metric antimetric` | 250 |
| `Grassmann/Unary/Involution.lean` | `reverse involute clifford antireverse even odd real imag adjoint` | 200 |
| `Grassmann/Sum.lean` | `+`/`-` promotion table (§4.10) | 300 |
| `Grassmann/Proofs/Tables.lean` | decide-based identity checks for small signatures | 350 |
| `Grassmann/Test/Golden.lean` | JSON loader, dense comparison, known-bug skip list | 250 |

### 8.6 Julia-specific parts to skip or redesign

- `Expr`-building `_pre` mutators and `insert_expr`: replace with plans and codegen.
- `Values`, `Variables` and `FixedVector`: use one storage class.
- `isfixed`/`svec` paths for BigFloat and symbolic fields, `SymField`, and `generate_products` per field: use `Coeff α`.
- `@pure`: pure functions with closed-term caches.
- `interop`/`∪` of manifolds, and dual/dyadic `V⊕V'` mixing: defer; require the same `V`.
- Tangent and derivation spaces (`diffvars`, `derive_*`, Q/Z masks): defer.
- `_metric` variants with a runtime metric field `g`: later, as "Gram passed at runtime", reusing §4.2.
- `⊙`/`⊠`: broken upstream. Reimplement from the definition if needed.
- `⟂`: undefined upstream; skip.
- Phasor: low priority.

---

## 9. Oracle test plan

Generator: `notes/grassmann-products-data/oracle_products.jl`. Run it as `julia --startup-file=no --project=<juliaenv> oracle_products.jl <outdir> [ncases]`.

It writes `products_golden.json` with the following fields:

- `signatures[]`: `name`, `ctor` (Julia constructor string), `n`, `blades` (Julia storage order, as bitmasks), `gram` (n×n), `diag`, `conformal`. The set is R2, R3, R4, R5, M13 (`-+++`), `+-`, `++-`, D(2,3,−1), PGA3 (D(0,1,1,1)), CGA4 (`∞∅++`), CGA5 (`∞∅+++`), INF3 (`∞++`), ORG3 (`∅++`).
- `cayley[]`: for each signature and binary op in `* ∧ ∨ ⋅ ⨼ << >> ∗ ⊛ × veedot antidot ⊘ >>>`, a 2^n × 2^n table of dense results.
  - `basis`: Submanifold inputs.
  - `multivector`: inputs converted to Multivector first, which exercises the container generators.
  - `null` marks a Julia error.
- `unary_tables[]`: per blade dense results for `~ involute clifford conj antireverse ⋆ ! complementleft complementlefthodge metric antimetric even odd real imag neg`, at both levels.
- `cases[]`: for every signature with n ≤ 4, every binary op above plus `+ −`, and every ordered pair of element kinds:
  - element kinds: Submanifold{g}, Single{g}, Chain{g} for all g, Spinor, CoSpinor, Multivector, and (non-conformal only) Couple{g}, PseudoCouple{g}
  - coefficients drawn from {±1, ±2, ±3}, so every result is exactly representable
  - each case records inputs (`type`, `grade`, `blade`, native `coeffs`, `dense`), and either the output (`type`, native `coeffs`, `dense`) or `error`
  - `dense_mv` is the same op on Multivector-converted inputs; `inconsistent: true` when `dense ≠ dense_mv`
  - unary cases per kind

Lean test policy:

1. **Tables first.** Verify the basis-level Plan tables against `cayley[*].multivector`. This is the bilinear ground truth, and every entry is exact.
2. **Typed cases.** Compare Lean's dense output with `out.dense` when `inconsistent` is false. When it is true, or the case has `error`, compare against `dense_mv` and record the case in a `known_julia_bug` list. That covers Appendix A #1–#8 and the `Chain{0}×Multivector` errors.
3. **Type tags.** Optionally compare Lean's result kind with `out.type` for the generic rules in §4.5. The TSVs give every grade combination.
4. **Tolerance.** Integer-valued inputs make every product exact, so use exact equality. For Float-valued inputs, if added, use relative tolerance 1e-12.
5. **Distributions to add later:**
   - Float coefficients in [−1,1] for n ≤ 6
   - sparse Chains with 1–2 non-zero entries, to hit the zero-skipping paths
   - high-N spot checks for n = 8 and 10: random Chain pairs for `∧`, `∨`, `⋅`, and `*` on grade-1/2
   - complex coefficients for the §4.12 conjugation quirks, marked "informational"
6. **Property tests without the oracle, run in Lean:**
   - associativity and distributivity of `*`
   - `a*b = a⋅b + a∧b` for vectors
   - `!(a∨b) = !a∧!b`
   - `⋆x = (~x)*I`
   - `contraction(a,b) = (~b)⌋a`
   - `a⊘b = ~b*a*involute(b)` for versor `b`
   - on random elements in every signature above

---

## Appendix A: Julia bugs and inconsistencies

Each item was confirmed by probe unless marked "by reading".

| # | Location | Symptom | Correct behaviour |
|---|---|---|---|
| 1 | `P:558` | `PseudoCouple + PseudoCouple` with the same B: real part = `ra ± ib`. Probe `p+p = 5v₁₂ + 6v₁₂₃` for p = 2v12+3v123 | componentwise |
| 2 | `P:584` | `PseudoCouple*PseudoCouple` with different B: last term is `volume(b)*imaginary(a)`. Probe `p*q = -12 - 2v₂ - 16v₃`; correct is `-12 - 2v₂ - 8v₃ + 3v₂₃` | `volume(a)*imaginary(b)` |
| 3 | `P:618` | `contraction(Couple, PseudoCouple)`: `contractn` is undefined → UndefVarError | `contraction(scalar(a), imaginary(b)) + …` |
| 4 | `P:651` | `plus(TensorTerm, PseudoCouple)` with basis ≠ B: `Subamnifold` typo → UndefVarError. Cascades into `∨`/`∧` of PseudoCouples with Multivector/Spinor | `Submanifold(V)` |
| 5 | `P:767-768` | `∨(TensorTerm{V,0}, Couple)` and the reverse: `B` unbound → UndefVarError | bilinear |
| 6 | `P:771-783` | `I ∨ Couple` and `Couple ∨ I` drop the scalar term: `(2+3v12)∨v123 = 3v₁₂`, correct is `2 + 3v₁₂` | include `a∨scalar(b)` whenever `a` is the pseudoscalar |
| 7 | `P:627` | `Couple ∨ Couple` with different B: `imaginary(a)∨imaginary(b)` only. ℝ4 `(1+3I)∨(−1+3v124)` gives `9v₁₂₄`; correct is `−3 + 9v₁₂₄` | bilinear |
| 8 | `P:585-586` via #1 | Couple×PseudoCouple and PseudoCouple×Couple are wrong because they sum through the buggy #1 | bilinear |
| 9 | `P:1820-1822` | `antireverse(Couple)` flips only the imaginary part. `antireverse(2+3v12) = 2+3v₁₂` in ℝ3, but the Multivector gives `−2+3v₁₂` | flip the scalar by `parityreverse(N)` too |
| 10 | `A:1483` | `Chain{V,0} * Multivector/Spinor/CoSpinor` (and the reverse): `$input` should be `$$input` → UndefVarError | scaling |
| 11 | `P:400` | `Zero / Number`: `V` unbound (probe: ambiguous method) | NaN Single / Zero |
| 12 | `P:473` | `Number ^ Infinity` builds a range → MethodError | `\|c\|==1 → One`, `\|c\|<1 → Zero`, otherwise Infinity |
| 13 | `A:397` | `antidot_metric(a,b)` uses unbound `g` (by reading) | take `g` as a parameter |
| 14 | `A:294,301` | `⊙`/`⊠`: `permutations` is not imported | import Combinatorics |
| 15 | `A:23` | `⟂` exported but undefined | – |
| 16 | `A:1560-1790` | `product_sandwich` returns `nothing` for N ≥ 12 (loop branch commented out; by reading) | implement a loop |
| 17 | `P:1024,1057,1921,1958` | `$VECS` is undefined in the N≥12 branches of adjoint (dyadic Spinor/CoSpinor) and of the reverse family on Spinor/CoSpinor. Reverse of a Spinor with N ≥ 12 therefore throws (by reading) | use `mvecs`/`svecs` |
| 18 | `A:1422,1434` | `product_∧/∨` non-cached TensorTerm branch: `A,B = (X,x) : (x,X)` range typo, and `$pro` is undefined. Only reached when C(N,L) ≥ 4096 (by reading) | swapper |
| 19 | `DS:operations.jl:339-356` vs `P:1338-1370` | Conformal: basis-level `!`/`complementleft` apply the ½/2 null factor; Chain-level does not. Basis-level `metric(v∞)` in `S"∞++"` returns Zero while the Multivector level returns v∞ | follow the Chain/Multivector level |
| 20 | `P:1630-1815` + `DS` | `antimetric` errors on every conformal space (probe, both levels) | Gram-complement outermorphism |
| 21 | `M:1127` | `trivector(::Couple)` calls `imaginarya` (typo, by reading) | `imaginary` |
| 22 | `AT:260` vs docs `algebra.md:512` | the docs claim `η<<ω = η<~ω`; the code is `contraction(ω,~η)` | follow the code |
| 23 | complex (§4.12) | inconsistent conjugation between Chain/Single and Multivector contraction paths | pick one policy and document it |
