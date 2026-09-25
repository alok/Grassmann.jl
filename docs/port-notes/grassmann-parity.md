# Grassmann.jl `src/parity.jl` — Porting Spec: every basis-blade sign rule

Scope owner: `Grassmann.jl/src/parity.jl` (595 lines) **plus every helper it calls** in Leibniz.jl / DirectSum.jl /
AbstractTensors.jl and every call site in `algebra.jl` / `products.jl` / `forms.jl` that turns these parities into
products. Everything below was read from source **and checked against the Julia oracle** (see §0).

Source revisions read:

| package | clone path | commit / version | oracle env version | diff vs oracle |
|---|---|---|---|---|
| Grassmann.jl | `/Users/alokbeniwal/chakravala/Grassmann.jl` | `4f79a7f` (2026-08-09), v0.8.47 | v0.8.46 | `parity.jl` byte-identical |
| DirectSum.jl | `/Users/alokbeniwal/chakravala/DirectSum.jl` | `7b964d8`, v0.8.21 | v0.8.21 | identical `src/` |
| Leibniz.jl | `/Users/alokbeniwal/chakravala/Leibniz.jl` | `a319d27`, v0.3.1 | v0.3.0 | only an extra `pseudoscalar` import |
| AbstractTensors.jl | `/Users/alokbeniwal/chakravala/AbstractTensors.jl` | v0.8.12 | v0.8.11 | not parity-relevant |

Notation: `file:line` paths are relative to `/Users/alokbeniwal/chakravala/`. `G.` = `Grassmann.jl/src/`,
`DS.` = `DirectSum.jl/src/`, `L.` = `Leibniz.jl/src/`, `AT.` = `AbstractTensors.jl/src/AbstractTensors.jl`.

---

## 0. Verification status (read this first)

All pseudocode in §4 was re-implemented in Python (`ref.py`) and compared term-by-term against a Julia oracle dump of
**every ordered pair of basis blades** in 20 spaces (products `*`, `∧`, `∨`, `contraction`, `×`; unary `~`, `involute`,
`clifford`, `conj`, `antireverse`, `!`, `complementleft`, `⋆`, `complementlefthodge`, Chain complements, `x*x`).

Artifacts (scratchpad `/private/tmp/claude-502/-Users-alokbeniwal-Grassmann/c6cc2308-bfca-4b9a-ad33-d89b110132a8/scratchpad/parity_probe/`):

| file | purpose |
|---|---|
| `dump.jl` | Julia oracle dumper (JSONL; `OUT=... julia dump.jl [space names]`) |
| `dump_all.jsonl` | full dump, 20 spaces, 4192 records (one process) |
| `dump_small.jsonl` | tangent spaces dumped in a **fresh** process (see §4.13 cache-collision defect) |
| `ref.py` | the reference implementation of this spec (≈450 lines, typed Python) |
| `compare.py` | ref vs oracle comparator |
| `truth.py` | independent Chevalley-recursion Clifford product (ground truth for arbitrary bilinear forms) |

Results:

* `compare.py dump_all.jsonl`: **21 178 checks pass, 322 fail**, and every failure is a documented oracle defect
  (Julia throws, or Julia's cache returns a value computed for a *different* space). No failure is a spec error.
* `compare.py dump_small.jsonl` (tangent spaces, fresh process): `mul/wedge/vee/dot/cross` **0 failures**
  (tan21: 48 each, tan22: 144 each, tanM: 48 each).
* `truth.py`: the Julia geometric product equals the true Clifford product for E3, M4, S4, I4, D3, D3deg, D4,
  P4inf, P4orig, P3infneg, **C3 (64/64), C5 (1024/1024)**. It is **wrong** for `C4neg` (56/256: the `-` on a Euclidean
  conformal basis vector is ignored) and for the general `MetricTensor` MT3 (2/64: middle-grade terms dropped).

Space names used throughout: `E3=S"+++"`, `M4=S"-+++"`, `S4=S"+-+-"`, `I4=4` (Int manifold), `C3=S"∞∅+"`,
`C5=S"∞∅+++"`, `C4neg=S"∞∅+-"`, `P4inf=S"∞+++"`, `P4orig=S"∅+++"`, `P3infneg=S"∞-+"`, `D3=D"1,2,-3"`,
`D3deg=D"1,1,0"`, `D4=D"2,-1,3,-4"`, `dual2=S"++"'`, `dual3=S"+-+"'`, `mixed2=S"++"⊕S"++"'`,
`tan21=tangent(S"++")`, `tan22=tangent(S"++",2,2)`, `tanM=tangent(S"-+",2,1)`, `MT3=MetricTensor([1 .5 0;.5 1 .5;0 .5 1])`.

---

## 1. Purpose & scope

`parity.jl` is the **sign/metric kernel** of Grassmann: given two basis blades encoded as bitmasks, it decides

* the sign (and metric factor) of the geometric product, exterior product, regressive product, interior
  (contraction) product, and their "metric field" (runtime metric) variants;
* the sign of Grassmann/Hodge complements (imported from Leibniz/DirectSum, re-exported here);
* grade-involution parities (reverse, involute, Clifford conjugate, pseudo/anti versions);
* the non-diagonal geometric product expansion (conformal null basis, general `MetricTensor`) via
  "split into metric-connected groups, then contract + wedge" (`paritygeometric*`);
* memoization caches (`parity_cache`, `regressive_cache`, `interior_*_cache`) — Julia-specific perf plumbing;
* `even/odd/real/imag/iseven/isodd/signbit` element-level predicates on the composite types.

It does **not** contain the coefficient loops (those are `products.jl` generated functions) or display
(multivectors.jl / Leibniz `indices.jl`). Those consumers are summarized where they change semantics.

---

## 2. Public API inventory

### 2.1 Exports declared in `G.parity.jl`

| symbol | defined in | signature | semantics | ASCII / alias |
|---|---|---|---|---|
| `complementleft` | `DS.operations.jl:339-356`; Chain/Multivector/Spinor kernels `G.products.jl:1324-1487` | `complementleft(t)` | Euclidean left Grassmann complement (§4.9) | — |
| `complementright` | same | `complementright(t)` | Euclidean right complement | `!t` (`AT:309-310`) |
| `⋆` | `AT:311` | `⋆(t) = complementrighthodge(t)` | Hodge right complement | `hodge(t)`, unary `|t` (`AT:312,315`) |
| `complementlefthodge` | `DS.operations.jl:339-356` | `complementlefthodge(t[,g])` | Hodge left complement | — |
| `complementrighthodge` | same | `complementrighthodge(t[,g])` | Hodge right complement `≈ ~t*I` | `⋆`, `hodge` |
| `complementleftanti` | `DS.operations.jl:334` | `complementleft(antimetric(t))` | | — |
| `complementrightanti` | `DS.operations.jl:333` | `complementright(antimetric(t))` | | — |
| `involute` | `DS.generic.jl:220-233` (+ Chain kernels `G.products.jl:1816-1976`) | `involute(t)` | grade-k part × (-1)^k | postfix `AbstractTensors.ˣ` (`AT:582`; **not** re-exported by Grassmann) |
| `clifford` | same | `clifford(t)` | involute∘reverse | — |
| `pseudoreverse` | `DS.generic.jl:228-231` | | reverse by pseudograde | `antireverse` (`DS.generic.jl:234`) |
| `antireverse` | const alias | | same | — |
| `odd` | `DS.operations.jl:387`, `G.parity.jl:492-501`, Multivector kernel `G.products.jl:1488-1522` | `odd(t)` | odd-grade part | postfix `t * ₋` (`AT:581`) |
| `even` | `DS.operations.jl:388`, `G.parity.jl:485-500` | `even(t)` | even-grade part | postfix `t * ₊` (`AT:580`) |
| `angular`, `radial` | **nowhere** (definitions commented out `G.parity.jl:447-463`) | — | exported but undefined → `UndefVarError` | — |
| `₊`, `₋`, `ǂ` | `AT:573-582` | `Postfix{op}` objects, applied as `t * op` (`Base.:*(t,op::Postfix)=op(t)`). **Spaces are mandatory**: `t*₊` lexes as a new suffixed operator `*₊` (ParseError). Oracle: `v12 * ǂ = -1v₁₂`, `(v1+v12) * ₊ = 0 + 1v₁₂ + 0v₁₃ + 0v₂₃` | even / odd / conj(=reverse) | — |

Also imported into `Base` and extended here: `reverse, conj, ~, signbit, imag, real` (`G.parity.jl:27`).

### 2.2 Internal (non-exported) parity API — all must exist in the port

| function | file:line | returns |
|---|---|---|
| `parityjoin(N,a,b)` | `G.parity.jl:32` | `Bool`: reorder parity of `e_a e_b` (Euclidean) |
| `parityjoin(N,S,a,b)` | `G.parity.jl:33-35` | `Bool`: reorder parity + #shared negative-metric indices |
| `paritycomplementinverse(N,G)` | `G.parity.jl:37-39` | `Bool` (unused anywhere in the ecosystem) |
| `parityregressive(V::Int,a,b,skew)` / `(V::Signature,…)` | `G.parity.jl:41,56` | `(Bool, UInt, Bool, UInt)` |
| `_parityregressive(V,a,b,Val{skew})` | `G.parity.jl:42-54` | same |
| `parityregressivenum(V,A,B)` | `G.parity.jl:57-60` | `(±1, C, t, Z)` |
| `parityregressive(V::Manifold,A,B)` | `G.parity.jl:61-63` | `parityregressivenum(Signature(V),A,B)` |
| `parityinterior(V::Int,a,b)` | `G.parity.jl:65-70` | `(±1, C, t, Z)` (references undefined `lim`; dead) |
| `diffcheck2(V,A,B)` | `G.parity.jl:79-83` | `Bool` |
| `parityinterior(V::Manifold,a,b,Val{lim},Val{field})` | `G.parity.jl:85-131` | `lim ? (Values{(C,g)},Z) : (g,C,t,Z)` |
| `parityinner(V::Int,a,b)` | `G.parity.jl:133-136` | `±1` |
| `parityinner(V::Manifold,a,b,Val{field})` | `G.parity.jl:138-153` | metric-weighted sign (number or `Expr`) |
| `parityseq(V,B::Tuple)` | `G.parity.jl:155-162` | `±1` |
| `paritygeometric(V,A,B,field)` | `G.parity.jl:166-198` | `Values{(C::UInt, g)}` (list of terms) |
| `paritygeometricright/left` | `G.parity.jl:199-254` | list of states |
| `splitbasis(V,B)` / `splitbasis(V,ind)` | `G.parity.jl:256-293` | tuple of group bitmasks |
| `combinebasis`, `combinegeometric` | `G.parity.jl:295-314` | |
| `fieldprod`, `fieldneg` | `G.parity.jl:316-321` | numeric or `Expr` arithmetic |
| `parity(n,s,a,b)` (cached) | `G.parity.jl:327-353` | `Bool` |
| `parity(V::Signature|Int|Manifold, a, b)`, `parity(a::Submanifold,b::Submanifold)` | `G.parity.jl:354-361` | `Bool` |
| `interior(...)` dispatchers | `G.parity.jl:365-370` | |
| `regressive(a::Submanifold,b::Submanifold)` | `G.parity.jl:371` | |
| `regressive(V,a,b)`, `interior(V::Signature|DiagonalForm|MetricTensor,a,b,Val{false},Val{field})` | generated by `construct_cache` `G.parity.jl:373-439`, `G.forms.jl:1627` | cached `(g, C, t, Z)` |
| `signbit(V::Manifold[,G])` | `G.parity.jl:441-446` | `Vector{Bool}` |
| `iseven/isodd` (many types) | `G.parity.jl:465-478` | `Bool` |
| `even/odd/real/imag` (spinor/couple types) | `G.parity.jl:485-526` | projections |

Imported helpers (the port must implement them identically): `parityreverse, parityinvolute, parityclifford,
parityconj, parityright, parityleft, parityrighthodge, paritylefthodge` (`L.generic.jl:139-142, 202-231`),
`paritymetric, parityanti` (`DS.operations.jl:312-324`), `complement` (`L.generic.jl:233-237`),
`symmetricmask, diffmask, diffcheck, hasinf/hasorigin(V,…)` (`L.generic.jl:53-105`), `grade_basis/grade(V,B)`
(`L.generic.jl:146-153`), `digits_fast` (`L.indices.jl:70-98`), `indices` (`L.indices.jl:106-119`).

### 2.3 Operators whose basis-level sign rule lives here (user-facing names)

| operator | definition | rule section |
|---|---|---|
| `a*b`, `⟑`, `⊖`, `wedgedot`, `times` | `AT:296,314`; `G.algebra.jl:38` → `mul` | §4.5 |
| `wedgedot_metric(a,b,g)` | `G.algebra.jl:39,64-72` | §4.5.4 |
| `a∧b`, `wedge` | `G.algebra.jl:108,127-147` | §4.4 |
| `a∨b`, `vee`, `a&b` | `G.algebra.jl:156-194` | §4.6 |
| `contraction(a,b)`, `a⋅b`, `dot`, `a|b`, `a>b`, `a⨽b` | `AT:264-265,297`; `G.algebra.jl:209-271` | §4.7 |
| `a<b`, `a⨼b` | `AT:259,262` = `contraction(b,a)` | §4.7 |
| `a<<b` | `AT:260` = `contraction(b,~a)` | §4.7 |
| `a>>b` | `AT:261` = `contraction(~a,b)` | §4.7 |
| `a∗b` | `AT:257` = `(~a)⟑b` | §4.5 |
| `a⊛b` | `AT:258` = `scalar(contraction(a,b))` | §4.7 |
| `cross(a,b)`, `a×b` | `AT:349` = `hodge(a∧b)` | §4.10 |
| `veedot(a,b)`, `⟇` | `G.algebra.jl:391`, `AT:629` = `complementleft(!a * !b)` | §4.9 |
| `antidot(a,b)` | `G.algebra.jl:396` = `complementleft(contraction(!a,!b))` | §4.9 |
| `~a`, `conj`, `reverse` | `DS.generic.jl:187,220-227` | §4.2 |

---

## 3. Data representations

### 3.1 Blades

* A basis blade is a `UInt` (UInt64) bitmask `B`. **Bit k (0-based) ⇔ generator index k+1 (1-based)**;
  `indices(B)` returns the ascending 1-based list (`L.indices.jl:106-119`). Blade `e_B = e_{i1} ∧ … ∧ e_{ik}` with
  `i1 < … < ik` (the canonical *exterior* ordering; for non-orthogonal metrics this is the outer-product basis, not
  the geometric-product basis).
* Grade of a blade = `count_ones(B)`, except that tangent (diff) bits are excluded where noted (`grade(V,B)`,
  `L.generic.jl:146-148`).
* `Submanifold{V,G,B}` is the Julia type of a basis blade: *everything* (`V`, grade `G`, bits `B`) is a type
  parameter (`DS.DirectSum.jl:252-254`). `Single{V,G,B,T}` = coefficient `v::T` × blade `B`
  (`DS.DirectSum.jl:457-461`). `Zero{V}` prints `𝟎`.
* In practice `V` of a blade is itself the *full-space* `Submanifold{M,N,2^N-1}` wrapping the `TensorBundle` `M`
  (`Single{A,…}` normalizes `A` via `submanifold(A)`, `DS.DirectSum.jl:459`; `Basis{Submanifold{M,…}}`
  `DS.basis.jl:258`). Consequently `typeof(V)<:Signature` tests inside hot paths are **always false** for real
  blades (important for §4.5.1 and §4.9).

### 3.2 Space (`TensorBundle{n,Options,Metrics,Vars,Diff,Name}`)

| field | Julia param | meaning | compile-time? |
|---|---|---|---|
| `n` | `N` | total generators `mdims(V)` including diff vars | yes (type param) |
| `Options` | `M` | bitfield `tensorhash` (below) | yes |
| `Metrics` | `S` | `Signature`: metric bits (bit k set ⇔ `e_{k+1}^2 = -1`); `DiagonalForm`: **index into global `diagonalform_cache`** (`DS.DirectSum.jl:207-217`); `MetricTensor`: index into `metrictensor_cache` (`G.forms.jl:1634-1643`) | yes |
| `Vars` | `F` | `diffvars` ν: number of tangent variables | yes |
| `Diff` | `D` | `diffmode` μ: max total order of Leibniz–Taylor monomials | yes |
| `Name` | `L` | index into `namecache` of prefixes `("v","w","∂","ϵ")` | yes |

`Options` encoding (`DS.DirectSum.jl:83-85`, decoders `DS.generic.jl:37-40`):

```
tensorhash(d,o,c=0,C=0) = (1<<(d-1)) | (1<<(2o-1)) | (c<0 ? 8 : 1<<(3c-1)) | (1<<(5C-1))   # Julia: 1<<(-1) == 0
bit 1  (=1)  hasinf      ∞ present (generator index 1)
bit 2  (=2)  hasorigin   ∅ present (index 2 if hasinf else index 1)
     4       dual (dyadmode = +1)           M%16 ∈ 4:7
     8       dyadic V⊕V' (dyadmode = -1)    M%16 ∈ 8:11
    16       polymode == false
_hasinf(M)    = M%16 ∈ (1,3,5,7,9,11)
_hasorigin(M) = M%16 ∈ (2,3,6,7,10,11)
_dyadmode(M)  = M%16 ∈ 8:11 ? -1 : (M%16 ∈ 4:7 ? 1 : 0)
```

`S"…"` parsing (`DS.DirectSum.jl:139-150`): `∞`→`+`, `∅`→`-` then bit k set iff char k is `-`. So in
`S"∞∅+++"` the metric bits are `0b00010` (**∅ carries a `-` bit**, ∞ a `+`). `hasconformal(V) = hasinf && hasorigin`
(`L.generic.jl:53`).

Derived quantities (port verbatim):

```
isdiag(V)   = Int: true | DiagonalForm: true | MetricTensor: false (G.forms.jl:1672)
              Signature: !hasconformal(V)   (DS.generic.jl:66)     # conformal is NOT diagonal
grade(V)    = N - (dyadic ? 2 : 1) * diffvars              (L.generic.jl:12)
diffmask(V) (L.generic.jl:70-80):
   non-dyadic: ((1<<D)-1) << (N-D)                         # top D bits
   dyadic:     ( ((1<<D)-1) << (N-2D) , ((1<<D)-1) << (N-D) )   # two blocks; callers OR them
loworder(V) = same space with diffmode-1                   (DS.generic.jl:133-137)
```

### 3.3 The *three* metric views (critical — they disagree for conformal spaces)

| view | used by | Int | Signature (non-conf.) | Signature conformal | DiagonalForm | MetricTensor |
|---|---|---|---|---|---|---|
| **A. `Signature(V)` metric bits** (`DS.DirectSum.jl:380-389`, `G.forms.jl:1654`) | `parity(V,a,b)`, `parityregressive` | 0 | `S` | **0** (non-diag ⇒ `UInt(0)`) | `signbit.(diag)` bits | 0 |
| **B. `V[i]` of the full `Submanifold`** (`DS.DirectSum.jl:283-300`) → parent's entries | `parityinner`, `parityrighthodge/lefthodge`, `paritymetric` | 1 | ±1 from `S` | ±1 from `S` (**∅ ⇒ -1**) | diag value | matrix row |
| **C. `metrictensor(V)`** (`G.forms.jl:1582-1593`) | non-diag `parityinterior`, `splitbasis` | I | diag(±1) | **hard-coded**: `g[∞,∅]=g[∅,∞]=-1`, `g[i,i]=+1` for i≥3 **regardless of S** | diag | matrix |

Consequences, all confirmed by the oracle:

* Conformal products use view C ⇒ `C4neg`: `v₂*v₂ = 1v` although the space says `-` (**oracle bug**, §8.6).
* Conformal Hodge uses view B ⇒ the ∅ generator contributes `-1` there (it is `+/-`-agnostic in products).
* `signbit(V)` for conformal V uses view A (metric 0) ⇒ pure reorder parity.

### 3.4 Storage / index ordering conventions (shared with every coefficient container)

* `indexbasis(n,g)` (`L.utilities.jl:221-244`): all `g`-subsets of `{1..n}` in **lexicographic** order of their sorted
  index lists (Combinatorics `combinations(1:n,g)` order), as bitmasks. `indexbasis(n,0)=[0]`. Example n=3:
  `[0] [1,2,4] [3,5,6] [7]` = `v v₁ v₂ v₃ v₁₂ v₁₃ v₂₃ v₁₂₃`.
* `bladeindex(n,B)` (1-based) = rank of `B` in `indexbasis(n,popcount B)`; `bladeindex(n,0)=1`.
  Closed form (verified n≤10): with sorted indices `c1<…<cg`, `c0=0`:
  `rank0 = Σ_{j=1..g} Σ_{t=c_{j-1}+1}^{c_j-1} C(n-t, g-j)`; `bladeindex = rank0+1`. (Lex, **not** colex.)
* `basisindex(n,B) = binomsum(n,popcount B) + bladeindex(n,B)`, `binomsum(n,g) = Σ_{q<g} C(n,q)`
  (`L.utilities.jl:135,185`). `Multivector` stores `2^n` values in this order.
* `spinindex` / `antiindex` (`L.utilities.jl:136-137,186-187`): same but summing only even / only odd `q`.
  `Spinor` (even) and `CoSpinor` (odd) store `2^(n-1)` values in these orders. `Chain{V,G}` stores `C(n,G)` values in
  `bladeindex` order.
* Diff (tangent) generators are the **highest** indices; dyadic covectors occupy the upper half
  (`mixed2`: `v₁=1, v₂=2, w¹=4, w²=8`).

### 3.5 What is compile-time vs runtime in Julia

Everything about the space and the blade bits is compile-time (type parameters); `@pure` + `@generated` make every
basis×basis sign a constant in generated code for `binomial(N,G) < 2^cache_limit (=4096)` / `N < 12`
(`G.products.jl:1343,1375`; `L.utilities.jl:104-107`: `algebra_limit=8, sparse_limit=22, cache_limit=12`,
`index_limit=20` in `L.indices.jl:70`). Beyond that, loops run at runtime and consult the caches of §4.13.
Only coefficients (`T` values) are runtime. The `field=true` ("`_metric`") variants make the **metric** runtime too
(they emit `Expr`s indexing a runtime metric object `g`).

---

## 4. Algorithms (exact, bit-for-bit)

Pseudocode uses: `pc(x)` = popcount; `lowmask(n) = (1<<n)-1` (0 if n≤0); `idx(B)` = ascending 1-based indices;
`⊕` = xor on Bool; `&, |, ^, ~` bitwise on UInt64. **Julia precedence trap:** `<<` binds tighter than `-`, and
`&` (multiplicative level) binds tighter than `|`/`⊻` (additive level); `UInt(1)<<n-1` means `(1<<n)-1`.

### 4.0 Primitive bit functions

```
inv(a, b)            # number of pairs (i∈a, j∈b) with i > j
  = Σ_{k : bit k of a set} pc(b & lowmask(k))

complement(N, B, D=0, P=0) :: UInt        # L.generic.jl:233-237
  UP = (1 << (P==1 ? 0 : P)) - 1          # P = hasinf+hasorigin ∈ {0,1,2}; UP ∈ {0, 3}
  ND = N - D
  C  = ((~B) & (UP ^ lowmask(ND))) | (B & (UP ^ (lowmask(D) << ND)))
  return pc(C & UP) != 1 ? C ^ UP : C
```

`complement` flips all non-diff, non-null bits; keeps diff bits of `B`; with `P=2` (conformal) the two null bits
{∞,∅} are copied then flipped **together** iff zero or both are set (so `{}`↔`{∞,∅}`, and `{∞}`→`{∞}`, `{∅}`→`{∅}`).
With `P∈{0,1}`, `UP=0` and it is the plain complement within the low `ND` bits.

Julia reference of `inv` (`G.parity.jl:32`): `isodd(sum(digits_fast(a,N) .* cumsum(digits_fast(b<<1,N))))`
where `digits_fast(x,N)` = `N+1` little-endian binary digits (`L.indices.jl:73-98`); the `<<1` shifts so the cumsum
at position k counts bits of `b` strictly below k. Only the parity is kept.

### 4.1 `parityjoin` / `parity` (reorder + metric parity)

```
parityjoin(N, a, b)    = odd(inv(a,b))                              # G.parity.jl:32
parityjoin(N, S, a, b) = odd(inv(a,b) + pc(a & b & S))              # G.parity.jl:33-35

parity(n, s, a, b) = parityjoin(n, s, a, b)       # memoized, G.parity.jl:327-353 (cache is pure perf)
parity(V::Signature, a, b):                       # G.parity.jl:354-358
    Dm = diffmask(V) (OR both blocks if dyadic)
    return parity(mdims(V), metric(V), a & ~Dm, b & ~Dm)       # diff bits never contribute a sign
parity(V::Int, a, b)      = parity(V, 0, a, b)                   # :359  (Euclidean)
parity(V::Manifold, a, b) = parity(Signature(V), a, b)           # :360  (metric view A, §3.3)
parity(a::Submanifold{V}, b::Submanifold{V}) = parity(V, UInt(a), UInt(b))   # :361
```

Meaning: `e_a e_b = (-1)^{parityjoin(S,a,b)} e_{a⊕b}` for a Signature metric (without magnitudes).

### 4.2 Grade involutions (reverse / involute / clifford / conj and pseudo-)

```
parityreverse(G)  = odd((G-1)*G/2)          # L.generic.jl:139
parityinvolute(G) = odd(G)                  # :140
parityclifford(G) = parityreverse(G) ⊕ parityinvolute(G)   # :141
parityconj        = parityreverse           # :142  (so conj == ~ == reverse)
grade(V, B)       = pc(B & lowmask(grade(V)))          # L.generic.jl:146-148 (diff bits excluded)
pseudograde(V, B) = grade(V) - grade(V, B)             # :152-153
```

Basis rule (`DS.generic.jl:220-233`), for `r ∈ {reverse, involute, conj, clifford}`:

```
r(b::Submanifold{V,G,B})       = parity_r(grade(V,B))       ? Single{V}(-1, b) : b
pseudo_r(b::Submanifold{V,G,B}) = parity_r(pseudograde(V,B)) ? Single{V}(-1, b) : b   # pseudoreverse/antireverse,
                                                                                     # pseudoinvolute, pseudoclifford
r(b::Single) = value(b) != 0 ? Single(value(b), r(basis(b))) : Zero
```

Chain/Multivector/Spinor kernels (`G.products.jl:1816-1976`): if `diffvars==0` use `parity_r(g)` per grade `g`
(antireverse: `parityreverse(N-g)`), else per blade `parity_r(grade(V,B))` (antireverse: `pseudograde(V,B)`).
Chain early exit: `D==0 && !parity_r(G) ⇒ return b` unchanged.

Couple/PseudoCouple/Phasor (`G.products.jl:1820-1829`): negate the imaginary part iff `parity_r(grade(B))`; the
PseudoCouple's pseudoscalar part iff `parity_r(grade(V))` (antireverse uses `antigrade`).

Verified: E3 `~v₁₂ = -1v₁₂`, `antireverse(v) = -1v` (pseudograde 3), `clifford(v₁₂₃) = v₁₂₃`; M4
`antireverse(v) = v` (pseudograde 4).

### 4.3 Tangent / conformal guards

```
symmetricmask(V, a, b)  (L.generic.jl:92-97):
    D = diffmask(V) (OR blocks if dyadic)
    A = a & ~D ; B = b & ~D ; Q = (a&D) | (b&D) ; Z = (a&D) & (b&D)
    return (A, B, Q, Z)          # A,B exterior parts; Q = union of ∂-bits; Z = repeated ∂-bits

hasorigin_bits(V, X) = hasinf(V) ? (X & 2) == 2 : (X & 1) == 1          # L.generic.jl:61
diffcheck(V, A, B)  (L.generic.jl:99-105):
    v   = diffmask(V) (OR blocks)
    conf= hasconformal(V)
    hi  = conf && odd(A) && odd(B) && !(hasorigin_bits(A) || hasorigin_bits(B))   # ∞ twice, no ∅ anywhere
    ho  = conf && hasorigin_bits(A) && hasorigin_bits(B) && !(odd(A) || odd(B))   # ∅ twice, no ∞ anywhere
    return hi || ho || (diffvars(V) != 0 && pc(A & v) + pc(B & v) > diffmode(V))
diffcheck2(V, A, B) = diffvars(V) != 0 && pc(A&v) + pc(B&v) > diffmode(V)     # G.parity.jl:79-83 (no null test)
```

`hi/ho` implement "a null vector squared is zero" early: if ∞ occurs in both factors and ∅ in neither, the product
is 0. `diffcheck` is called with *raw* (unmasked) `a,b` by `∧` (`G.algebra.jl:130`), `mul`
(`G.algebra.jl:46`, only when `istangent(V)`), and the coefficient kernels (`G.products.jl:200,212,224,243`).

### 4.4 Exterior product `∧` (`G.algebra.jl:127-147`)

```
wedge(V, a, b):
    A,B,Q,Z = symmetricmask(V,a,b)
    if (A & B) != 0 or diffcheck(V,a,b) or derive_mul(V,a,b,1,true) == 0: return Zero
    d = getbasis(V, (A ^ B) | Q)
    if diffvars(V) != 0 and Z != 0: d = Single{V}(getbasis(loworder(V), Z), d)   # tensor-valued coeff, §4.11
    return parity(V, a, b) ? Single{V}(-1, d) : d        # = inv(A,B) since A,B disjoint (metric irrelevant)
```

Result display type: bare `Submanifold` if +, `Single(-1)` if −. The coefficient kernel variant
(`joinaddmulti!`, `G.products.jl:199-222`, used by Chain∧Chain through `exterbits`, `G.products.jl:360-368`) uses
`parityinner(grade(V),A,B)` = `parity(Int)` = Euclidean `inv` sign — identical since A,B disjoint.

### 4.5 Geometric product `*`

#### 4.5.1 Diagonal spaces (`isdiag(V)`: Int, non-conformal Signature, DiagonalForm) — `G.algebra.jl:43-55`

```
mul_diag(V, a, b):
    if istangent(V) and (diffcheck(V,a,b) or derive_mul(...) == 0): return Zero
    A,B,Q,Z = symmetricmask(V,a,b)
    d = getbasis(V, (A ^ B) | Q)
    if typeof(V)<:Signature (never true for real blades, §3.1) or (A & B) == 0:
        out = parity(V,a,b) ? Single{V}(-1,d) : d
    else:
        out = Single{V}(parityinner(V,A,B), d)
    if diffvars(V) != 0 and Z != 0: out = Single{V}(getbasis(loworder(V),Z), out)
    return out

parityinner(V, a, b)   # G.parity.jl:138-153, live branch (isdiag or hasconformal)
    A,B = symmetricmask(V,a,b)[1:2] ; C = A & B
    g = |Π_{i ∈ idx(C)} V[i]|            # view B: ±1 for Signature, diag value for DiagonalForm, 1 for Int; 1 if C empty
    return parity(V, A, B) ? -g : g      # parity uses view A: reorder + shared negative bits
```

Closed form: `e_a e_b = (-1)^{inv(A,B) + pc(A∩B∩S_A)} · Π_{i∈A∩B} |g_ii| · e_{(A⊕B)|Q}` with `S_A` = view-A bits.
Display: disjoint & + → `Submanifold`; disjoint & − → `Single(-1)`; overlapping → always `Single(±g)` (so
`v₁*v₁` prints `1v`, and a degenerate `D"1,1,0"` gives `v₃*v₃ = 0v`, a zero-valued `Single`, **not** `𝟎`).

The non-coefficient kernel `geomaddmulti!` (`G.products.jl:223-241`) uses the same: `isdiag ? [(A⊕B, parityinner(V,A,B))]
: paritygeometric(V,A,B)`, adds each term at `bas|Q`, multiplies by `e_Z` for repeated diff bits.

#### 4.5.2 Non-diagonal spaces (conformal Signature, MetricTensor) — `paritygeometric` (`G.parity.jl:166-314`)

`mul` (`G.algebra.jl:56-59`): `out = paritygeometric(V,a,b)`; `isempty(out) ? Zero : +(Single{V}.(out)...)`
(no `diffcheck`, no `symmetricmask`: non-diag + tangent is not supported). Result is always a `Single` (e.g. `1v∞₁`,
note the explicit `1`) or a sum printed as a full `Spinor`/`CoSpinor`/`Multivector` (zeros shown).

Idea: split each factor into **metric-connected groups** (connected components of the metric's nonzero pattern
restricted to the blade's indices), expand the *other* factor against the groups one at a time using
`X * g = (contraction part) + (wedge part)`, with sign fix-ups.

```
splitbasis(V, B):                                   # G.parity.jl:283-293
    if B == 0: return []
    ind = idx(B)
    if isdiag(V): return [1<<(i-1) for i in ind]
    M  = metric matrix restricted to ind×ind        # view C
    f  = [ [j : M[i][j] != 0] for i in 1..len(ind) ]   # positions within ind (1-based)
    for i: if i ∉ f[i]: f[i].push(i)
    j = 2
    while j <= len(f):                               # greedy union (G.parity.jl:262-279)
        t = false
        for k in 1..j-1:
            for q in f[j]:
                if q ∈ f[k]:
                    t = true
                    for p in f[j]: if p ∉ f[k]: f[k].push(p)
                    remove f[j]; break
            if t: break
        if !t: j += 1
    return [ OR_{p ∈ grp} (1 << (ind[p]-1)) for grp in f ]      # groups ordered by their first member

parityseq(V, bs):                                    # G.parity.jl:155-162
    if isdiag(V) or len(bs) == 1: return 1
    out = false
    for i in 2..len(bs): out ⊕= parityjoin(0, bs[i-1], bs[i])   # ONLY consecutive pairs (see §8.6)
    return out ? -1 : 1

paritygeometric(V, A, B):                            # G.parity.jl:166-176
    a = splitbasis(V,A); b = splitbasis(V,B)
    ga = max(pc.(a), default 0); gb = max(pc.(b), default 0)
    if (ga<=1 and gb<=1) ? pc(A) >= pc(B) : ga >= gb:
        return expand_right(V, A, b)
    else:
        return expand_left(V, a, B)

State = ((E, Eg), (I, Ig))        # represents Eg*Ig * e_{E ∪ I} (canonical order); I = still-contractible part

expand_right(V, A, b):                               # G.parity.jl:177-187, 199-226
    if b empty: vals = [((0,1),(A,1))]
    else:
        vals = step_right(V, ((0, parityseq(V,b)), (A,1)), b[1])
        for grp in b[2..]: vals = concat(step_right(V, s, grp) for s in vals)
    return combinebasis(vals)

step_right(V, ((Ae,Aeg),(Ai,Aig)), B):
    G = pc(B)
    flip = parityclifford(G) ⊕ odd(G * pc(Ai))
    if isdiag(V) or hasconformal(V):
        (g, C, t, _) = interior(V, Ai, B)            # §4.7, = contraction(e_Ai, e_B) = g e_C
        Cg = flip ? -(Aig*g) : Aig*g
        CCg = t ? [((Ae,Aeg),(C,Cg))] : []
    else:                                            # MetricTensor
        (list, _) = parityinterior(V, Ai, B, lim=true)   # [(C_k, g_k)]
        gg = flip ? -(Aig*Aeg) : Aig*Aeg
        CCg = [((Ae, gg), (C_k, g_k)) for (C_k, g_k) in list]
    if (Ai & B) == 0:
        p = parityjoin(0, Ai ^ Ae, B) ? -Aeg : Aeg
        return [((Ae ^ B, p*Aig), (Ai, 1))] ++ CCg    # wedge term first, then contraction term(s)
    return CCg

expand_left(V, a, B):                                # G.parity.jl:188-198, 227-254 (groups consumed last→first)
    if a empty: vals = [((0,1),(B,1))]
    else:
        vals = step_left(V, a[end], ((0, parityseq(V,a)), (B,1)))
        for grp in reverse(a[1..end-1]): vals = concat(step_left(V, grp, s) for s in vals)
    return combinebasis(vals)

step_left(V, A, ((Be,Beg),(Bi,Big))):
    G = pc(A)
    if isdiag(V) or hasconformal(V):
        (g, C, t, _) = interior(V, Bi, A)            # contraction(e_Bi, e_A)
        Cg = parityreverse(G) ? -(Big*g) : Big*g
        CCg = t ? [((Be,Beg),(C,Cg))] : []
    else:
        (list,_) = parityinterior(V, Bi, A, lim=true)
        gg = parityreverse(G) ? -(Big*Beg) : Big*Beg
        CCg = [((Be,gg),(C_k,g_k)) for ...]
    if (A & Bi) == 0:
        p = parityjoin(0, A, Be ^ Bi) ? -Beg : Beg
        return [((A ^ Be, p*Big), (Bi,1))] ++ CCg
    return CCg

combinebasis(vals) = [ (E ^ I, Eg*Ig) for ((E,Eg),(I,Ig)) in vals if (E & I) == 0 ]   # G.parity.jl:295-308
```

Terms are **not merged** by `combinebasis`; `mul` sums the `Single`s, the kernels add them into the output array.

Why the sign fix-ups are right (proof sketch, useful for Lean proofs): with `contraction(X,b) = ⟨~b X⟩` (§4.7) and a
vector `b`, the right contraction is `X⌊b = (-1)^{|X|-1} contraction(X,b)` — this is `flip` for `G=1`
(`parityclifford(1)=true`). For the left side, `a⌋X = contraction(X,a)` for vectors (`parityreverse(1)=false`) and
for a 2-group `E`, `E⌋X = -contraction(X,E)` (`parityreverse(2)=true`). The accumulated `Ae` never needs a sign
because groups are ordered by their lowest index, so every earlier group's indices are below every index being
contracted.

**Exactness.** `X*b = X⌊b + X∧b` is exact only when `b` is a vector. For conformal spaces the only non-vector group
is `E=e∞∧e∅`; the side-selection rule guarantees: if exactly one factor contains `E`, the *other* factor is split
into vectors; if both contain `E`, then `A = ±E∧A'` with `A' ⊥ E`, `A E = ±A' E E = ±A'` (pure contraction). Hence the
conformal product is exact — confirmed 1024/1024 on C5 against `truth.py`. For a general `MetricTensor` with two
multi-vector groups (e.g. MT3 `v₁₂*v₂₃`, all coupled) the middle-grade terms are dropped: oracle gives `-0.25v`,
truth is `-0.25 - 0.5v₁₂ + 1.0v₁₃ - 0.5v₂₃` (§8.6).

#### 4.5.3 Hand-worked conformal example (C5, verified)

`v∞ * v∅` (A=`0b00001`, B=`0b00010`): groups `a=[1]`, `b=[2]`, `ga=gb=1`, `pc(A)=1 ≥ pc(B)=1` ⇒ expand_right,
`parityseq=1`, state `((0,1),(1,1))`. `G=1`, `flip = true ⊕ odd(1) = false`.
Contraction `interior(V,1,2)`: compound row of `∅` has single nonzero `K=∞` with `g=-1`; `A ∨ !K` gives scalar with
sign `+` (details §4.7) ⇒ `(g=-1, C=0, t=true)`, `Cg=-1`. Wedge: `parityjoin(0,1,2)=inv({1},{2})=0` ⇒ `p=+1`,
state `((2,1),(1,1))`. `combinebasis` ⇒ `[(3,+1),(0,-1)]` ⇒ **`-1 + 1v∞∅`**. Reverse order `v∅*v∞`:
contraction sign `neg=true ⊕ pr({2})=true ⇒ +g=-1`, wedge `inv({2},{1})=1 ⇒ -1` ⇒ **`-1 - 1v∞∅`**. (Both are the
`Issue #19/#20` goldens.)

#### 4.5.4 Runtime-metric variant (`wedgedot_metric`, `field=true`)

`mul_metric(a,b,g)` (`G.algebra.jl:64-72`): if `isinduced(g)` (the full-space Submanifold or `InducedMetric`,
`G.forms.jl:1698-1700`) → plain `mul`; else **always** the `paritygeometric(...,Val(true))` path even for diagonal
spaces. With `field=true`, `interior` and `parityinner` return `Expr`s: diag: `value(value(g))[basisindex(N,C)]`
(the runtime metric's blade-norm for blade `C`), non-diag: `value(value(g)[G])[bladeindex][i]` (compound entry)
while structurally-zero entries of the *static* metric are skipped (`G.parity.jl:101-102,109`). `fieldprod(a,b)`
(`G.parity.jl:316-321`) multiplies with constant folding: `±1*Expr` → `Expr` / `-(Expr)`. Port: implement as the same
sign skeleton parameterized by a runtime metric structure; sign decisions stay static.

### 4.6 Regressive product `∨` (`G.parity.jl:41-63`, `G.algebra.jl:156-175`)

```
parityright_raw(sumidx, G)   = odd(sumidx + G*(G+1)/2)                    # L.generic.jl:204
parityright(S::UInt, B, N)   = parityright_raw(Σ idx(B), pc(B))           # L.generic.jl:213 (S ignored!)

_parityregressive(V, a, b, skew=false):          # V here is Signature(V) (view A) or Int
    N = mdims(V); S = metric(V); D = diffvars(V); G = (V isa Int) ? V : grade(V)
    A,B,Q,Z = symmetricmask(V,a,b)
    α = complement(N, A, D) ; β = complement(N, B, D)          # P = 0
    if pc(α & β) == 0 and !diffcheck(V, α, β):
        C = α ^ β ; L = pc(A) + pc(B)
        bas = (skew or A + B != 0) ? complement(N, C, D) : 0
        par = parityright(S,A,N) ⊕ parityright(S,B,N) ⊕ parityright(S,C,N)
        neg = odd(L*(L-G)) ⊕ par ⊕ parityjoin(S, α, β)       # α,β disjoint ⇒ S term vanishes
        return (neg, bas | Q, true, Z)
    return (false, 0, false, Z)

regressive(V, a, b) = (neg ? -1 : 1, C, t, Z)  of  _parityregressive(Signature(V), a, b)   # cached, §4.13
vee(a, b):   (p, C, t, Z) = regressive(V,a,b)
    if !t or derive_mul(...) == 0: return Zero
    d = getbasis(V, C); if istangent(V) and Z != 0: d = Single{V}(getbasis(loworder(V),Z), d)
    return p == 1 ? d : Single{V}(p, d)
```

Semantics: DeMorgan `a ∨ b = (-1)^{L(L-G)} ⋆⁻¹(⋆a ∧ ⋆b)` with the Euclidean right complement (docstring
`G.algebra.jl:154`). Metric-independent. Worked (E3): `v₁₂ ∨ v₂₃`: α=`{3}`, β=`{1}`, C=`{1,3}`, bas=`{2}`,
L=4 (even), `pr({1,2})=6→F`, `pr({2,3})=8→F`, `pr({1,3})=7→T`, `inv({3},{1})=1→T` ⇒ `F⊕T⊕T=F` ⇒ **`v₂`**.
`v₁₂ ∨ v₁₃ = v₁`; I4 `v₁₂₃₄ ∨ v₁₂₃₄ = v₁₂₃₄`; tangent tan22 `∂₁v₁₂ ∨ ∂₁v₁₂ = ∂₁⊗∂₁v₁₂`.
Scalar edge: for `G≥1`, `v ∨ v = 𝟎` (α=β=full overlap).

### 4.7 Interior / contraction product (`G.parity.jl:65-131`, `G.algebra.jl:209-271`)

Grassmann's `contraction(a,b)` (= `⋅`, `|`, `>`, `⨽`, `dot`) is `a ∨ ⋆b`. For a Euclidean diagonal metric this equals
`⟨~b · a⟩_{|a|-|b|}` — i.e. the *left* contraction of `~b` onto `a`, zero if `b ⊄ a` in index support. So
`v₁₂⋅v₂ = -1v₁`, `v₁₂⋅v₁₂ = v` (**+1**, not −1), `v₁₂₃⋅v₁₂ = v₃`, `v₂⋅v₁₂ = 𝟎`, `v₁<v₁₂ = v₂`.

```
parityinterior(V, a, b, lim):            # V = TensorBundle(full Submanifold) (view A for Signature, forms.jl:1674-1688)
    A,B,Q,Z = symmetricmask(V,a,b); N = mdims(V)
    if diffcheck(V, A, B): return lim ? ([], Z) : (1, 0, false, Z)
    G = pc(B)
    if isdiag(V):
        bas = [B] ; gs = [ Π_{i∈idx(B)} V[i] ]            # Signature ±1 (view A == parent for non-conformal),
                                                         # DiagonalForm actual values (signed); 1 if empty
    else:
        bas = indexbasis(grade(V), G)                    # all grade-G blades K
        gs  = [ det(M[idx(B), idx(K)]) for K in bas ]    # row of the G-th compound of metric view C
    gout = 0 ; tout = false ; acc = ordered map CQ -> coef
    for (K, gk) in zip(bas, gs):
        if gk != 0 and !diffcheck2(V, A, K):
            (neg, C, t, _) = _parityregressive(Signature(V), A, complement(N, K, diffvars(V)), skew=true)
            tout |= t
            if t:
                ggg = (neg ⊕ parityright_raw(Σ idx(K), G)) ? -gk : gk
                acc[C|Q] += ggg ; gout += ggg
    if lim: return ([(c, acc[c]) in insertion order], Z)
    if len(acc) > 1: throw("this is a limited variant of interior product")
    return (gout, first key of acc or 0, tout, Z)

contraction(a, b):                       # G.algebra.jl:209-223
    if derive_mul(...) == 0: return Zero
    if isdiag(V) or hasconformal(V):
        (g, C, t, Z) = interior(V, a, b)         # cached, lim=false
        if !t: return Zero
        d = getbasis(V, C); if istangent and Z != 0: d = Single{V}(getbasis(loworder(V),Z), d)
        return g == 1 ? d : Single{V}(g, d)
    else:                                         # MetricTensor
        (list, Z) = parityinterior(V, a, b, lim=true)
        return empty ? Zero : Σ Single{V}(c, C)
```

Details: `gk == 0` entries are **skipped** (not produced as zero terms), so on `D"1,1,0"`, `v₃⋅v₃ = 𝟎` while
`v₃*v₃ = 0v`. Conformal compound rows (view C) have exactly one nonzero: `K = σ(B)` where σ swaps ∞↔∅ if `B`
contains exactly one of them, and `g = -1` iff `B ∩ {∞,∅} ≠ ∅` else `+1` (so `lim=false` never throws there).

Worked (E3, `v₁₂⋅v₂`): diag, `g=1`; `_parityregressive(A=0b011, complement(3,0b010)=0b101, skew)`: α'=`{3}`,
β'=`{2}`, C'=`{2,3}`, bas=`{1}`, L=4 (even), `pr({1,2})=F, pr({1,3})=T, pr({2,3})=F`, `inv({3},{2})=T` ⇒ neg=F;
`ggg = (F ⊕ pr({2}): 2+1 odd=T) ⇒ -1` ⇒ **`-1v₁`**.

Tangent (tan21, fresh process): `v₁⋅∂₁ = ∂₁v₁` (Q carries the ∂ bit; A=`{1}`, B=∅, K=∅).

`parityinterior(V::Int,…)` (`G.parity.jl:65-70`) is the same with `parityright(0,Σidx(B),pc(B))` and no metric; it
references an undefined `lim` in its early return (dead code; `diffcheck` on Int is always false).

### 4.8 `parityinner` (`G.parity.jl:133-153`)

Given in §4.5.1 (live branch). `parityinner(V::Int,a,b) = parity(V,A,B) ? -1 : 1` (Euclidean). The non-diag,
non-conformal branch returns a **Chain row** of the compound metric (not a number) — dead code (only reached from
`isdiag` call sites).

### 4.9 Complements

#### 4.9.1 Parity helpers

```
# Leibniz (L.generic.jl:202-214) — pure index arithmetic, metric ignored:
parityright_raw(s, G)        = odd(s + G(G+1)/2)
parityleft_raw(s, G, N)      = (odd(G) and even(N)) ⊕ parityright_raw(s, G)
parityrighthodge_raw(V::Int, s, G) = odd(V) ⊕ parityright_raw(s,G)     # V = #negative metric bits in B
paritylefthodge_raw(V, s, G, N)    = (odd(G) and even(N)) ⊕ parityrighthodge_raw(V, s, G)

# DirectSum, V = full Submanifold or DiagonalForm (DS.operations.jl:293-306) — these are what blades use:
parityright(V, B, G=pc(B)):   ind = idx(B & lowmask(N-D)); return parityright_raw(Σind, G) ? -1 : 1
parityleft(V, B, G=pc(B)):    ind = …; return parityleft_raw(Σind, G, N-D) ? -1 : 1
parityrighthodge(V, B, G):    ind = idx(B & lowmask(N-D))
                              g   = Π V[ind]         # view B: parent ±1 or diag values; 1 if empty
                              c   = hasconformal(V) and (B & 3) == 2          # ∅ present, ∞ absent
                              return (parityright_raw(Σind, G) ⊕ c) ? -g : g
paritylefthodge(V, B, G):     same with parityleft_raw(Σind, G, N-D)
```

Note `G` defaults to `pc(B)` **including** diff bits while `ind` excludes them (matters for tangent spaces; oracle-consistent).
`parityright_raw(Σidx X, |X|)` = `odd(inv(X, X^c))`, so `e_X ∧ !e_X = I` in the Euclidean metric.

Null scaling (`L.generic.jl:215-219`): `parityrightnull(V,B,v) = parityleftnull(V,B,v) =
(hasconformal(V) and pc(B & 3) == 1) ? (odd(B) ? 2v : v/2) : v`.

#### 4.9.2 Basis-blade complements (`DS.operations.jl:339-356`)

```
complementright(b = e_B):
    isdyadic(V) → throw "Complement for mixed tensors is undefined"
    d = complement(N, B, D, P=0)
    v = parityrightnull(V, B, 1)                 # 2 if B∩{∞,∅}={∞}, 1/2 if ={∅}, else 1 (conformal only)
    return Single{V}(parityright(V,B) * v, d)    # ALWAYS a Single (prints "1v₂₃" even when +1)
complementleft: same with parityleft / parityleftnull
complementrighthodge(b = e_B):
    if (!isdiag(V) and !hasconformal(V)): return reverse(b) * V(I)          # MetricTensor: geometric product with I
    d = complement(N, B, D, P = hasinf(V) + hasorigin(V))
    return Single{V}(parityrighthodge(V, B), d)                              # coefficient ±Π g_ii
complementlefthodge(b):
    if (!isdiag(V) and !hasconformal(V)): return complementleft(metric(b))
    same as right with paritylefthodge
X(b::Single) = adj(value(b)) * X(basis(b))   with adj = identity for complementright/left, conj for the hodge ones
X(Zero) = Zero                               (DS.DirectSum.jl:618-620)
```

The `(h,pg,true)` "field" hodge variants (`args=(:g,)`) always take the metric route:
right → `wedgedot_metric(reverse(b), V(I), g)`, left → `complementleft(metric(b,g))`.

#### 4.9.3 Coefficient-container complements (`G.products.jl:1324-1487`) — differ from blades!

For `Chain`, `Multivector`, `Spinor`, `CoSpinor`:
* dyadic → throw "Complement for dyadic tensors is undefined"; tangent Chain → **`UndefVarError: args`**
  (oracle bug: `$(args...)` spliced at runtime, `G.products.jl:1340`).
* Euclidean complements: coefficient `parityright(V,B)*adj(v)` placed at `complement(N,B,D)` — **no null scaling**.
  So in C3: `!(2v∞ as Chain) = 2.0v∅₁` but `!(2v∞ as Single) = 4v∅₁` (the Single path multiplies by the blade's `2`).
* Hodge: if `!isdiag(V)` (includes **conformal**) or runtime non-induced metric → `complementright(metric(x))`;
  else coefficient `parityrighthodge(V,B)` placed at `complement(N,B,D)` with **P=0** (fine for diag spaces where the
  null-pair logic is off anyway).
* Output container: Chain grade `N-G`; Spinor ↔ CoSpinor swap iff `N` odd.

#### 4.9.4 Metric / antimetric (`DS.operations.jl:312-324,358-381`)

```
paritymetric(V,B) = Π V[idx(B & lowmask(N-D))]            # view B, 1 if empty
parityanti(V,B)   = paritymetric(V, complement(N,B,D,P))
metric(b):  if !isdiag(V) or hasconformal(V): return complementleft(complementrighthodge(b))
            dyadic → throw
            if hasorigin(b) and !hasinf(b): return Zero
            if hasinf(b) and !hasorigin(b): return Zero
            return Single{V}(paritymetric(V,B), b)
antimetric(b): non-diag or conformal → antimetric_term(b)   ← UNDEFINED (UndefVarError; oracle bug)
               else same null guards, Single{V}(parityanti(V,B), b)
hasinf(b::Submanifold)    = hasinf(space) and odd(B)                      (DS.generic.jl:116)
hasorigin(b::Submanifold) = hasorigin(space) and (hasinf(space) ? B&2==2 : odd(B))   (DS.generic.jl:119)
```

So in `S"∅+++"`, `metric(v∅) = 𝟎` while `v∅*v∅ = -1v` (inconsistent null semantics; oracle-confirmed). In C3,
`metric(v∞) = -2v∅` (through the null-scaled `complementleft`).

#### 4.9.5 Worked complement goldens (all oracle-verified)

| space | blade | `!` (cr) | `complementleft` | `⋆` (hr) | `complementlefthodge` |
|---|---|---|---|---|---|
| E3 | `v₂` | `-1v₁₃` | `-1v₁₃` | `-1v₁₃` | `-1v₁₃` |
| E3 | `v₁₂` | `1v₃` | `1v₃` | `1v₃` | `1v₃` |
| M4 | `v₁` | `1v₂₃₄` | `-1v₂₃₄` | `-1v₂₃₄` | `1v₂₃₄` |
| M4 | `v₁₂₃₄` | `1v` | `1v` | `-1v` | `-1v` |
| D3 | `v₂₃` | `1v₁` | `1v₁` | `-6v₁` | `-6v₁` |
| D3deg | `v₃` | `1v₁₂` | `1v₁₂` | `0v₁₂` | `0v₁₂` |
| C3 | `v∞` | `2v∅₁` | `2v∅₁` | `1v∞₁` | `1v∞₁` |
| C3 | `v∅` | `-0.5v∞₁` | `-0.5v∞₁` | `-1v∅₁` | `-1v∅₁` |
| C3 | `v∞∅` | `1v₁` | `1v₁` | `-1v₁` | `-1v₁` |
| C3 | `v∅₁` | `0.5v∞` | `0.5v∞` | `1v∅` | `1v∅` |
| C3 | `v` | `1v∞∅₁` | `1v∞∅₁` | `1v∞∅₁` | `1v∞∅₁` |
| P4orig | `v∅` | `1v₁₂₃` | `-1v₁₂₃` | `-1v₁₂₃` | `1v₁₂₃` |
| tanM | `∂₁` | `-1∂₁v₁₂` | `1∂₁v₁₂` | `-1∂₁v₁₂` | `1∂₁v₁₂` |
| dual3 | `w¹` | `1w²³` | `1w²³` | `-1w²³` | `-1w²³` |

Hand derivation C3 `⋆v∅`: B=`0b010`, ind=`[2]`, g=V[2]=−1 (∅ has the `-` bit), c=true, `parityright_raw(2,1)=odd(3)=T`,
`T⊕T=F` ⇒ coefficient `g=-1`; `complement(3,2,0,P=2)`: UP=3, C=`((~2)&4)|(2&3)=6`, pc(6&3)=1 ⇒ 6=`v∅₁` ⇒ `-1v∅₁`. ✓

### 4.10 Cross product (`AT:349`)

`cross(a,b) = hodge(a ∧ b)` = `complementrighthodge(wedge(a,b))`. Hence always a `Single`/`Zero`; throws in dyadic
spaces. E3: `v₁×v₂ = 1v₃`; C5: `v∞×v∅ = -1v₁₂₃` (hodge of `v∞∅`); dual2: `w¹×w² = 1w`.

### 4.11 Tangent (diff-variable) basis and dyadic/dual spaces

* Diff bits (`∂ᵢ` for vector spaces, `ϵⁱ` for dual) are **symmetric/commuting**: excluded from every parity via
  `symmetricmask`/`parity` masking; the result carries `Q = union` of diff bits.
* Repeated diff bits `Z = a_D ∧ b_D ≠ 0` (i.e. `∂ᵢ∂ᵢ`) turn the coefficient into the blade `e_Z` of `loworder(V)`
  (diffmode−1): `∂₁*∂₁ = ∂₁⊗∂₁` (a `Single` whose value is `Submanifold{T¹⟨…⟩,1,0x4}`), `∂₁v₂*∂₁v₁ = -1∂₁⊗∂₁v₁₂`,
  `∂₁v₁₂ ∨ ∂₁v₁₂ = ∂₁⊗∂₁v₁₂`, `∂₁v₁₂⋅∂₁v₁ = ∂₁⊗∂₁v₂`. `Single` construction returns `Zero` when
  `order(value)+order(blade) > diffmode` (`DS.DirectSum.jl:476-487`), `order(e_B) = pc(B & diffmask)` (`DS.generic.jl:44`).
* Total order limit: `diffcheck` returns true (⇒ `𝟎`) iff `pc(a_D)+pc(b_D) > diffmode`: tan22 `∂₁*∂₁₂ = 𝟎`.
  With `diffmode=1`, `∂₁*∂₁ = 𝟎`.
* **Port recommendation:** represent the diff part as a multi-index (exponent vector, total degree ≤ μ) — `Q`/`Z`
  are exactly its "support" and "overflow" encodings. Julia's nested-Single encoding is an artifact (and triggers
  a `StackOverflowError` via `interop` recursion for some `Single×Single` tangent products — oracle bug).
* `derive_mul` (`G.products.jl:29-75`) only acts when `istangent && isdyadic`; it is **broken** in the oracle
  (`Leibniz.indexsplit(@inbounds (…)[1],mdims(V))` parses as a tuple ⇒ `MethodError`; every product involving `ϵ`
  in `tangent(S"++"⊕S"++"')` throws). Otherwise it returns its input (so `iszero(der)` is false).
* **Dual space** `V'` (`DS.generic.jl:146-162`): options gain the dual bit and **metric bits are flipped**
  (`flipsign(N,S) = (2^N-1) & ~S`, `DS.generic.jl:141`; DiagonalForm negates values, `DS.DirectSum.jl:207`). So
  `S"++"'` shows `⟨--⟩'` and `w¹*w¹ = -1w`. All sign rules are otherwise identical.
* **Dyadic** `V⊕V'` (`DS.operations.jl:36-54`): concatenated bits (`mixed2`: metric `0b1100`), covectors in the upper
  half; products follow the diagonal rules (`v₁*w¹ = v₁w¹`, `w¹*w¹ = -1v`, `v₁w¹*v₁w¹ = 1v`); all complements/hodge/
  cross throw. `diffmask` has two blocks (§3.2).

### 4.12 Element-level predicates and projections (`G.parity.jl:441-526`, `DS.operations.jl:387-402`)

```
signbit(V::Manifold)    = [parity(V, b, b) for b in indexbasis(rank(V))]     # true ⇔ e_b² < 0 (view A!)
signbit(V::Manifold, G) = [parity(V, b, b) for b in indexbasis(rank(V), G)]
signbit(::Chain|Single|AbstractSpinor|Multivector) = false
iseven(Zero)=isodd(Zero)=true
iseven(t::TensorGraded{V,G}) = even(G) or iszero(t);  isodd likewise
iseven(Spinor)=true; isodd(Spinor)=iszero; iseven(CoSpinor)=iszero; isodd(CoSpinor)=true
iseven(Couple{V,B}) = even(grade(B)) or iszero(imaginary)
isodd(Couple{V,B})  = odd(grade(B)) ? iszero(scalar) : iszero(t)
iseven/isodd(PseudoCouple) = both parts even / both parts odd
iseven(Multivector) = norm(t) ≈ norm(even(t))    (approximate!)
odd(TensorGraded{V,G}) = odd(G) ? t : Zero ; even = complement      (DS.operations.jl:387-388)
even(Spinor)=t; odd(CoSpinor)=t; even(CoSpinor)=odd(Spinor)=Zero
even(Couple{V,B}) = even(grade B) ? t : scalar(t);  odd(Couple) = odd(grade B) ? imaginary : Zero
even/odd(PseudoCouple) = even/odd(imaginary) + even/odd(volume)
even(Multivector{V,T,4}) = scalar + volume ; odd(Multivector{V,T,4}) = vector   (2-dim special case)
imag(TensorGraded{V,G}) = parityreverse(G) ? t : Zero ; real = the other      (DS.operations.jl:395-402)
real/imag(TensorTerm{V,G}) same rule (G.parity.jl:503-504)
real(Couple) = scalar + real(imaginary); imag(Couple) = imag(imaginary)
real/imag(PseudoCouple) = sum over volume & imaginary parts
Multivector/Spinor/CoSpinor real/imag: per-grade keep iff !parityreverse(g) (real) / parityreverse(g) (imag)
   (generated kernels G.products.jl:1523-…; special small-N methods G.parity.jl:509-526 e.g.
    imag(Spinor{V,T,8}) = bivector, imag(CoSpinor{V,T,8|16|32}) = trivector, imag(Quaternion)=imaginary)
```

Oracle: `signbit(S"-+++") = [0,1,0,0,0,0,0,0,1,1,1,0,0,0,1,1]`; `signbit(S"-+++",2) = [0,0,0,1,1,1]`;
`signbit(S"∞∅+++")` = grades 2,3 true, others false (metric ignored). E3: `m = 1+2v₁+3v₁₂+4v₁₂₃`:
`real(m) = 1 + 2v₁`, `imag(m) = 0 + 3v₁₂ + 4v₁₂₃`, `even(m) = 1 + 3v₁₂ + 0v₁₃ + 0v₂₃`, `odd(m) = 2v₁ + 0v₂ + 0v₃ + 4v₁₂₃`,
`iseven(m)=isodd(m)=false`; Couple `z = 1+2v₁₂`: `real(z)=1v`, `imag(z)=2v₁₂`; PseudoCouple `2v₁₂+3v₁₂₃`: `even = 2v₁₂`,
`odd = 3v₁₂₃`, `real = 𝟎`.

### 4.13 Caches (Julia-specific; `G.parity.jl:323-439`)

* `parity_cache[n][s][a+1][b+1]::Bool` (Vector-of-Dict-of-Vector, grown lazily up to the requested `a,b`); for
  `n > sparse_limit=22`, `parity_extra[n-22][s][a][b]` nested Dicts; `n==0` uncached. Pure memo of `parityjoin`.
* `construct_cache(:Signature)`, `(:DiagonalForm)` (`G.parity.jl:438-439`), `(:MetricTensor)` (`G.forms.jl:1627`)
  generate `regressive(V,a,b)` (Signature only, via `parityregressivenum(Signature(V),…)`) and
  `interior(V::T,a,b,Val{false},Val{field})` for field ∈ {true,false}, memoized in
  `cache[n][S][options+1][a+1][b+1]::Tuple{Any,UInt,Bool,UInt}` (`n>22`: Dict variant).
* **Defect (oracle correctness hazard):** the key omits `diffvars`, `diffmode` and the concrete space type
  identity beyond `(n, S, options)`. A tangent space and a plain space with equal `(N, S, options)` share entries:
  after evaluating `E3` (`S"+++"`), `tangent(S"++")` (also N=3,S=0,opts=0) returns `v ∨ v₁₂ = 𝟎` instead of `v`
  (fresh process). **Oracle goldens for tangent spaces must be produced in a fresh Julia process per space.**
* Lean replacement: no mutable global caches. Signs are O(N) popcounts (§8.2); optional per-space precomputed tables.

---

## 5. Display / printing rules relevant to parity outputs

Result *type* determines the printed form, so the port must track "bare blade vs coefficient" exactly:

| operation | returns bare `Submanifold` when | otherwise |
|---|---|---|
| `*` diag | factors disjoint and sign + | `Single(-1)`; overlapping ⇒ always `Single(±g)` (`1v`, `0v`) |
| `*` conformal/MetricTensor | never | `Single` (`1v∞₁`) or full `Spinor`/`CoSpinor`/`Multivector` sum |
| `∧` | sign + | `Single(-1)` |
| `∨` | `p == 1` | `Single(-1)` |
| `contraction` (diag/conformal) | `g == 1` | `Single(g)` |
| `~`, `involute`, `clifford`, `conj`, `antireverse` | parity false | `Single(-1)` |
| `!`, `complementleft`, `⋆`, `complementlefthodge`, `×` | never | always `Single` |
| zero result | — | `Zero` prints `𝟎` (`DS.DirectSum.jl:604`) |

`Single` printing (`L.indices.jl:195-203`, `DS.DirectSum.jl:488`): `show(value)` then `"*"` unless the value is a
non-Bool `Integer` or finite `AbstractFloat` (`⊗` if the value is a `TensorAlgebra`, e.g. `∂₁⊗∂₁`), values of type
`Complex/Rational/Expr` are parenthesized; then the blade label. Examples (oracle): `-1v₁₂`, `1v`, `2.0v₃`, `-0.5v∞₁`,
`0v`, `-1∂₁⊗∂₁v₁₂`, `(1//2)v₁`, `(1 + 2im)v₁₂`.

Blade labels (`L.indices.jl:14-48,139-181`, `DS.DirectSum.jl:403-406`): scalar = prefix alone (`v` / `w`); vector
prefix `v` with subscript indices `₁…₉`, `₀` for 10, then `a…z` for 11–36; dual prefix `w` with superscripts `¹²³…`;
∞ generator prints `∞`, ∅ prints `∅`, and remaining indices are shifted down by `hasinf+hasorigin`
(`L.indices.jl:122-132`); diff generators print as `∂ᵢ` (vector) / `ϵⁱ` (dual) and are **printed first**
(`∂₁v₁₂`). Mixed blades concatenate `v…w…` (`v₁w¹²`).

Space show strings (from oracle): `⟨+++⟩`, `⟨-+++⟩`, `⟨1111⟩` (Int 4), `⟨∞∅1⟩` and `⟨∞∅111⟩` (conformal Euclidean
part prints `1`, **not** `+`, because `sig` falls back to `s[k]`), `⟨∞∅1-1⟩` (C4neg), `⟨∞+++⟩`, `⟨∅+++⟩`, `⟨1,2,-3⟩`,
`⟨1,1,0⟩`, `⟨--⟩'` (dual of `++`), `⟨-+-⟩'`, `⟨++--⟩*` (mixed), `T¹⟨++₁⟩`, `T²⟨++₁₂⟩`, `T²⟨-+₁⟩`,
`⟨[1.0, 0.5, 0.0],[0.5, 1.0, 0.5],[0.0, 0.5, 1.0]⟩` (MetricTensor).

Sum printing (multivectors.jl scope, cited for completeness): full containers show every component including
zeros, scalar without label, signs as ` + ` / ` - ` with absolute values: `-1 + 1v∞∅ + 0v∞₁ + 0v∞₂ + …`,
`0.0v₁₂ - 0.0v₁₃ + 2.0v₂₃` (note `-0.0` prints as `- 0.0`).

---

## 6. Golden examples (verbatim; all re-checked against the oracle)

### 6.1 From the test suite (`Grassmann.jl/test/runtests.jl`, `issuestests.jl`)

```julia
@basis "++++" s e;  e124 * e23 == e134                         # runtests.jl:4
[Λ(3).v32^2, Λ(3).v13^2, Λ(3).v21^2] == [-1Λ(3).v for j∈1:3]    # :5 (v32 = -v23 by label parsing)
@basis "++++"; (v1*v1, v1⋅v1, v1∧v1) == (1,1,0)                 # :7
@basis "-+++"; (v1*v1, v1⋅v1, v1∧v1) == (-1,-1,0); (v2*v2,v2⋅v2,v2∧v2) == (1,1,0)   # :8
basis"-+++"; h = 1v1+2v2; h⋅h == 3v                             # :9
Λ(62).v32a87Ng == -1Λ(62).v2378agN                              # :10 (non-Windows)
@basis S"∞∅++"                                                   # issuestests.jl:9-16
  (v∞^2, v∅^2, v1^2, v2^2) == (0v, 0v, v, v)
  v∞ ⋅ v∅ == -1v
  v∞∅^2 == v
  (v∞∅ * v∞, v∞∅ * v∅) == (-1v∞, v∅)
  (v∞ * v∅, v∅ * v∞) == (-1 + 1v∞∅, -1 - 1v∞∅)
@basis S"∞∅+"                                                    # issuestests.jl:60-69
  v∅*v∞ == -1 - v∞∅ ;  v∅*(-v∞) == 1 + v∞∅
basis"+++"; (v1+v2) + (v1+v2)*(v1+v2) == 2 + 1v1 + 1v2          # issuestests.jl:53-56
```

`generictests.jl` property tests (for G ∈ `3, V"+++", S"∞+", S"∅+", V"-+++", S"∞∅+"`): unity, `a²∈𝔽`, associativity,
distributivity, `a⋅b = ½(ab+ba)`, `a∧b = ½(ab−ba)`, `ab = a⋅b + a∧b`, `ab = 2a⋅b − ba`, `aa = a⋅a` — port these as
Lean property tests (they hold for vectors in every space above).

### 6.2 Oracle-harvested basis goldens (string form exactly as Julia prints)

```
E3  v12*v2 = 1v₁      v12⋅v2 = -1v₁     v2⋅v12 = 𝟎      v12∨v13 = v₁     v12∨v23 = v₂
E3  ⋆v2 = -1v₁₃       !v2 = -1v₁₃       v1×v2 = 1v₃     v12⋅v12 = v      v123⋅v1 = v₂₃
E3  v123⋅v12 = v₃     v1⋅v123 = 𝟎       ~v12 = -1v₁₂    v1<v12 = v₂      v12⨽v1 = v₂     v1⨼v12 = v₂
M4  v₁*v₁ = -1v       v₁⋅v₁ = -1v       S4 v₂*v₂ = -1v
I4  v₁₂₃₄*v₁₂₃₄ = 1v  v₁₂₃₄∨v₁₂₃₄ = v₁₂₃₄   v₁₂₃₄⋅v₁₂₃₄ = v
C5  v∞*v∞ = 𝟎         v∞*v∅ = -1 + 1v∞∅ + 0v∞₁ + 0v∞₂ + 0v∞₃ + 0v∅₁ + 0v∅₂ + 0v∅₃ + 0v₁₂ + 0v₁₃ + 0v₂₃ + 0v∞∅₁₂ + 0v∞∅₁₃ + 0v∞∅₂₃ + 0v∞₁₂₃ + 0v∅₁₂₃
C5  v∞∧v∅ = v∞∅       v∞⋅v∅ = -1v       v∞×v∅ = -1v₁₂₃  v∞∅*v∞ = -1v∞   v∞∅*v∅ = 1v∅   v∞∅*v∞∅ = 1v
C5  v∞∅⋅v∞ = v∞       v∞∅⋅v∅ = -1v∅     v∞∅⋅v∞∅ = -1v   v∞₂*v∞₁ = 𝟎     v∞∅₁*v∞₁ = 1v∞
C5  v∞∅₁₂₃*v∞∅₁₂₃ = -1v   v∞∅₁₂₃∨v∞∅₁₂₃ = v∞∅₁₂₃   v∞*v₁ = 1v∞₁   v₁*v∞ = -1v∞₁
C4neg (S"∞∅+-") v₂*v₂ = 1v      ← oracle bug; mathematically -1
P4inf v∞*v∞ = 1v      P4orig v∅*v∅ = -1v    (null only in conformal spaces)
D3  v₂*v₂ = 2v   v₃*v₃ = -3v   v₂⋅v₂ = 2v   ⋆v₂₃ = -6v₁
D3deg v₃*v₃ = 0v  v₃⋅v₃ = 𝟎
dual2 w¹*w¹ = -1w   w¹*w² = w¹²   w¹∨w² = w   w¹×w² = 1w
mixed2 v₁*w¹ = v₁w¹   w¹*v₁ = -1v₁w¹   w¹*w¹ = -1v   v₁w¹*v₁w¹ = 1v   v₁w¹⋅v₁w¹ = -1v
tan21 v₁*∂₁ = ∂₁v₁   ∂₁*v₁ = ∂₁v₁   ∂₁*∂₁ = 𝟎 (diffmode 1)
tan22 ∂₁*∂₁ = ∂₁⊗∂₁   ∂₁*∂₂ = ∂₁₂   ∂₁*∂₁₂ = 𝟎   ∂₁v₂*∂₁v₁ = -1∂₁⊗∂₁v₁₂   ∂₁v₁₂⋅∂₁v₁ = ∂₁⊗∂₁v₂
tanM  ∂₁v₁*∂₁v₁ = -1∂₁⊗∂₁
MT3 v₁₂*v₂₃ = -0.25v   ← oracle drops -0.5v₁₂ + 1.0v₁₃ - 0.5v₂₃
```

The complete tables (every blade pair, every op, 20 spaces) are in `dump_all.jsonl` / `dump_small.jsonl`
(`{"space","a","b","mul":{"s","t","T"},…}`; `t` = `[[bits, coef],…]`, `T` = Julia result type name).

---

## 7. Dependencies on other chakravala packages

| package | symbols used by parity.jl / these rules |
|---|---|
| **Leibniz** (`L.`) | `parityreverse, parityinvolute, parityconj, parityclifford, parityright, parityleft, parityrighthodge, paritylefthodge, parityrightnull, parityleftnull` (generic.jl:139-231); `complement` (:233); `complementleft/right/…hodge, ⋆` docs (:239-269); `symmetricmask, symmetricsplit, diffmask, diffcheck, hasconformal, hasinf/hasorigin(V,A,B), hasinf2, hasorigin2` (:53-105); `grade_basis, grade(V,B), pseudograde(V,B)` (:146-153); `digits_fast/digitsfast, indices, indexsplit, index_limit` (indices.jl:70-119,213); `indexbasis, bladeindex, basisindex, binomsum, sparse_limit, cache_limit, algebra_limit` (utilities.jl); `odd, even, involute, clifford` (re-exported AbstractTensors generics); `printindices/printlabel/showvalue` for display |
| **DirectSum** (`DS.`) | `Signature, DiagonalForm, Submanifold, Single, Zero, One, TensorBundle` types; `metric, options, diffvars, diffmode, dyadmode, isdyadic, isdual, istangent, isdiag, hasinf, hasorigin, mdims, rank, grade(V), loworder, getbasis, Λ/Basis, signbool, paritymetric, parityanti, antireverse (=pseudoreverse), antiinvolute, anticlifford, complementleftanti, complementrightanti, complement functions for Submanifold, metric/antimetric(b)`, `flipsign`, `tensorhash`, `Signature(::Submanifold)` |
| **AbstractTensors** (`AT`) | `TensorAlgebra` (note: `<: Number`), `TensorGraded, TensorTerm, Manifold, Values, Variables`; operator constants `⋆, hodge, complementright(=!), complement, ⊖, ⟑, times, ∗, ⊛, ⨼, ⨽, <, >, <<, >>, |, dot, cross, veedot/⟇, antidot/codot/pseudodot(=expansion)`; `Postfix` `₊ ₋ ǂ ˣ ⁻¹`; `involute, clifford, even, odd, scalar, vector, volume, value` generics |
| **Grassmann itself** | `metrictensor, metricdyad, MetricTensor, compound, isinduced, TensorBundle(::Submanifold)` (forms.jl:1580-1700, composite.jl:714-720); `mul, ∧, ∨, contraction` (algebra.jl); coefficient kernels (products.jl) |

---

## 8. Lean 4 porting notes

### 8.1 Types: what becomes an index vs a runtime value

| Julia | Lean | runtime cost |
|---|---|---|
| `N = mdims(V)` | index `(n : Nat)` on the space / blade types, with `n ≤ 64` | 0 (erased where only used in proofs; small `Nat` otherwise) |
| blade bits `B` (type param) | `structure Blade (n : Nat) where bits : UInt64; lt : bits.toNat < 2^n` | 0 (proof field erased) |
| grade `G` of `Chain{V,G}` | index `(g : Nat)` + `Vector α (Nat.choose n g)` storage | 0 |
| space `V` (options, metric bits, diffvars, diffmode, kind) | `structure Space where n : Nat; kind : Kind; S : UInt64; inf orig : Bool; dyad : Int8; D μ : Nat` passed as an explicit/implicit **value** index: `Multivector (V : Space) α` | a pointer per call; sign math is branch-light |
| `DiagonalForm` values | `Array Float`/generic field in `Space` (or a separate `Metric` structure) | runtime |
| `MetricTensor` | `Matrix` in `Space` | runtime |
| `Submanifold` vs `Single` distinction | keep a `Term` result with `coef : Option α` (None = bare blade) **only in the display/golden layer**; core arithmetic uses plain coefficients | 0 in core |

Keep sign functions total and pure over `UInt64`; prove their specs against `Finset`-level definitions.

### 8.2 Hot paths and how to make them fast

* Julia's speed = every basis×basis sign is constant-folded inside `@generated` kernels for small N; otherwise
  memo caches. In Lean:
  * `inv(a,b)` parity: `par := 0; x := a >>> 1; while x ≠ 0: par ^= pc(x &&& b); x >>>= 1` — O(N) popcounts.
  * Lean core has **no native UInt64 popcount** (only `BitVec.cpop`, a recursive `Nat` fold,
    `~/lean4/src/Init/Data/BitVec/Basic.lean:893-905`). Implement SWAR `popcount64` in pure `UInt64` ops (12 ops) or
    `@[extern "lean_popcount64"]` + `@[implemented_by]` with a reference; prove `swar = (BitVec.cpop …).toNat` by
    `bv_decide`.
  * For N ≤ 8: optional per-space `ByteArray` sign tables (`2^N × 2^N` bits = 8 KiB) built once.
  * Chain×Chain loops: the unrolled-kernel analog of `@generated` is an elaborator/macro that emits straight-line code
    for fixed small `n` (optional, later).
* Conformal/MetricTensor products are cold paths: implement `paritygeometric` literally (lists), or better, the
  Chevalley recursion of `truth.py` (exact for every bilinear form, simpler to prove), and use `paritygeometric`
  only if bug-compatibility for MetricTensor is required.

### 8.3 Suggested policy on oracle defects

Reproduce oracle behavior **except**: (a) where Julia throws (`antimetric` on conformal, tangent Chain complements,
dyadic-tangent `derive_mul`, tangent `StackOverflow`) — define the mathematically obvious value; (b) cache-order
artifacts — follow fresh-process values; (c) `C*neg` conformal signature and MetricTensor dropped terms — implement
the true Clifford product and mark those goldens as known divergences. Keep deterministic quirks that are "API
behavior" (null scaling 2 / ½ on blade complements vs none on Chain complements; `metric(v∅)=𝟎` in `S"∅+++"`; `0v`
vs `𝟎`) behind clearly named functions so the golden suite matches.

### 8.4 Tricky semantics checklist

1. Bit k ⇔ index k+1; lexicographic `indexbasis` (not colex).
2. `S"∞∅…"` sets the ∅ metric bit; conformal products ignore *all* metric bits (view C), hodge uses them (view B).
3. `contraction(a,b) = a ∨ ⋆b = ⟨~b a⟩` (so `v₁₂⋅v₁₂ = +1`); `<`, `⨼` swap args; `<<`, `>>` insert a reverse.
4. Regressive sign includes `(-1)^{L(L-grade V)}` and three `parityright` terms; metric-free.
5. Complement `P=2` swaps/copies the null pair; only hodge uses `P`.
6. Hodge coefficient = ±Π g_ii (DiagonalForm magnitudes appear; degenerate ⇒ `0v`).
7. Dual spaces negate the metric; dyadic spaces forbid complements.
8. Diff bits commute, never contribute sign, repeat ⇒ lower-order coefficient; total order ≤ μ.
9. `symmetricmask` returns `(A,B,Q,Z)`; results are placed at `C | Q`.
10. `parityseq` only XORs consecutive group pairs (correct for sorted/contiguous groups only).
11. `lim=false` interior throws if more than one result blade (non-diag, non-conformal metrics).

### 8.5 Suggested Lean module decomposition (this layer)

| module | contents | est. LOC (code + proofs) |
|---|---|---|
| `Grassmann/Bits/Popcount.lean` | SWAR popcount, `lowmask`, `indices`, `inv`, proofs vs `BitVec.cpop`/`Finset.card` | 120 + 120 |
| `Grassmann/Bits/Index.lean` | `indexbasis` (lex), `bladeindex`, `basisindex`, `spinindex`, `antiindex`, combinatorial-number-system proofs (bijection with `Fin (choose n g)`) | 200 + 200 |
| `Grassmann/Space.lean` | `Space`, options decode/encode (`tensorhash`), `grade`, `diffmask`, `isdiag`, `conformal`, three metric views, dual/dyadic constructors | 220 + 40 |
| `Grassmann/Parity/Core.lean` | `parityjoin`, `parity`, reverse/involute/clifford/conj + pseudo, `symmetricmask`, `diffcheck(2)`; theorems: bilinearity over xor, graded commutativity, reverse = `inv(b,b)` | 150 + 220 |
| `Grassmann/Parity/Complement.lean` | `complement(N,B,D,P)`, right/left/hodge parities, null scaling, `paritymetric/anti`; theorems: `complement` involutive, `e_X ∧ !e_X = I` | 180 + 150 |
| `Grassmann/Parity/Products.lean` | wedge, diag geometric, regressive, interior (diag + compound row), cross, tangent `Q/Z` handling | 300 + 150 |
| `Grassmann/Parity/NonDiag.lean` | `splitbasis`, `paritygeometric` (bug-compatible) and `chevalley` (exact) + equivalence theorem on conformal | 250 + 150 |
| `Grassmann/Parity/Predicates.lean` | `signbit`, even/odd/real/imag grade predicates | 80 |
| `test/ParityGolden.lean` | JSON golden loader + comparator (mirrors `compare.py`) | 200 |

Total ≈ 1.7k code + 1.2k proofs. Good `decide`/`bv_decide` targets for N ≤ 5: associativity of the diagonal sign
cocycle, `complement` involution, regressive/complement DeMorgan identities, `v⋅w = ½(vw+wv)`.

### 8.6 Known oracle defects (do not blindly replicate)

| # | defect | evidence |
|---|---|---|
| 1 | Conformal spaces ignore signature bits beyond ∞/∅ in products (metricdyad hard-codes +1) | C4neg `v₂*v₂ = 1v`; truth.py 56/256 fail |
| 2 | General `MetricTensor` product drops middle-grade terms when both factors have multi-vector metric groups | MT3 `v₁₂*v₂₃ = -0.25v` |
| 3 | `parityseq` XORs only consecutive groups (wrong for ≥3 interleaved groups) | code `G.parity.jl:158-160` |
| 4 | regressive/interior cache key omits diffvars/diffmode → cross-space contamination | `pcache.jl`: tan21 `v∨v₁₂` = `v` fresh, `𝟎` after E3 |
| 5 | `antimetric` on conformal / non-diag calls undefined `antimetric_term` | UndefVarError |
| 6 | Chain/Multivector complements in tangent spaces: `UndefVarError: args` | `G.products.jl:1340` |
| 7 | dyadic+tangent `derive_mul`: `@inbounds (x)[1],mdims(V)` tuple parse → MethodError | `tangent(S"++"⊕S"++"',1,1)`: `v₁*ϵ¹` throws |
| 8 | some tangent `Single×Single` products: `StackOverflowError` (interop recursion on loworder manifold) | dump run |
| 9 | Null scaling (2, ½) applied to blade complements but not Chain complements | C3 `!v∞ = 2v∅₁`, `!(2.0v∞ Chain) = 2.0v∅₁` |
| 10 | `metric(b)` treats ∞/∅ blades as zero in ∞-only/∅-only spaces, products treat them as ±1 | P4orig `metric(v∅)=𝟎`, `v∅*v∅=-1v` |
| 11 | `angular`, `radial` exported but undefined | `G.parity.jl:28,447-463` |
| 12 | `parityinterior(V::Int,…)` references undefined `lim`; non-diag `parityinner` returns a Chain | dead code |
| 13 | `DiagonalForm` sign uses `signbit` ⇒ a `-0.0` entry counts as negative | `DS.DirectSum.jl:384-389` |

---

## 9. Oracle test plan

Generator: extend `dump.jl` (already emits JSONL with `s` = printed string, `t` = `[[bits,coef]]`, `T` = type).
Rules: one fresh Julia process **per space** (defect 4); `--startup-file=no`; wrap each op in `try` and record errors
with `first(sprint(showerror,e),120)` (never byte-slice strings); skip pairs whose diff bits overlap in tangent
spaces unless running them one-per-process (defect 8); remember `TensorAlgebra <: Number` when classifying results.

| suite | spaces | inputs | ops | compare |
|---|---|---|---|---|
| P1 exhaustive basis | E1–E5, M4, S4, `S"--+-+"`, I4, D3, D3deg, D4, dual2/3, mixed2, P4inf/P4orig/P3infneg, C3, C4, C5 | all ordered blade pairs (N≤5 ⇒ ≤1024) | `* ∧ ∨ contraction < << >> ∗ × veedot` | exact ints (terms), strings |
| P2 unary basis | same | every blade, plus `Single` with coef ∈ {2, -3, 1//2, 2.0} | `~ involute clifford conj antireverse ! complementleft ⋆ complementlefthodge metric antimetric x*x` | exact |
| P3 containers | same | `Chain` with one-hot and random dyadic-rational coefficients (k/8, k∈[-16,16]) per grade; Spinor/CoSpinor/Multivector random | the unary ops above; `*`, `∧`, `∨`, `contraction` Chain×Chain, Multivector×Multivector | exact (dyadic rationals are exact in Float64) |
| P4 tangent | tan21, tan22, tanM, `tangent(S"+++",2,3)` | all pairs incl. overlapping ∂ (one process per op when overlapping) | `* ∧ ∨ contraction`; `x*x` | terms + nested-coefficient strings |
| P5 larger N sampling | N = 6, 8, 12, 13, 20, 21, 23, 24 Euclidean & `S"-+…"` | 2 000 random blade pairs per N (fixed seed) | `* ∧ ∨ contraction ⋆ ~` | exercises cache regimes (`cache_limit=12`, `index_limit=20`, `sparse_limit=22`) — values must be regime-independent |
| P6 predicates | E3, M4, C5, D3 | `signbit(V)`, `signbit(V,G)` all G; `even/odd/real/imag/iseven/isodd` on Couple, PseudoCouple, Spinor, CoSpinor, Multivector with random coefficients | exact / Bool |
| P7 ground truth | all non-tangent spaces | same pairs as P1 | `truth.py` Chevalley product | marks divergence classes 1–2 |
| P8 runtime metric | E3, M4, D3 with `g = DiagonalOperator` / `Outermorphism` | all pairs | `wedgedot_metric`, `contraction_metric` | exact |

Record per record: space descriptor (`N, opts, metricbits, diag, diffvars, diffmode, dyadmode, grade, show, basis
bit order, names`) so the Lean loader never needs Julia to interpret it. Known-divergence classes (§8.6) are
tagged, not dropped.
