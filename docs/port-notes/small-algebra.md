# Porting spec: chakravala small algebra packages

Covers **AbstractLattices.jl, PrimitiveBits.jl, DeMorgan.jl, Dendriform.jl, AbstractAnalysis.jl, Wilkinson.jl**, plus the parts of **SyntaxTree.jl** that Wilkinson depends on.

This document is written so the Lean 4 port can be built without re-reading the Julia. Every behavioral claim was either read in the source (a file:line citation is given) or observed by running the registered package under Julia 1.13.0 (marked **[run]**). The probe scripts that produced the **[run]** outputs are in `scratchpad/probes/small/*.jl`.

## 0. Sources, versions, citation keys

| key | path | version / commit | notes |
|---|---|---|---|
| AL | `/Users/alokbeniwal/chakravala/AbstractLattices.jl/src/AbstractLattices.jl` | clone 0.2.2 @5279df6 (2023-11-17) | Registered 0.3.0 and 0.3.1 in the depot (`~/.julia/packages/AbstractLattices/{1rlFH,6cTw5}`) have the same source. 0.2.1 (`J3H2V`, used by juliaenv2) lacks the `Bool` methods (L14-15). |
| PB | `/Users/alokbeniwal/chakravala/PrimitiveBits.jl/src/PrimitiveBits.jl` | 0.1.0 @2947a79 (2018-12-31) | Not registered in any env. Probed via `include`. |
| DM | `/Users/alokbeniwal/chakravala/DeMorgan.jl/src/DeMorgan.jl` | 0.1.0 @4f00ff8 (2023-11-19) | Matches the depot `DeMorgan/upSb9`. |
| DF | `/Users/alokbeniwal/chakravala/Dendriform.jl/src/{Dendriform,morphism,arithmetic,poset}.jl` | 0.2.1 @51a3b52 (2019-10-04) | Byte-identical to the depot `Dendriform/THQ0v`. |
| AA | `/Users/alokbeniwal/chakravala/AbstractAnalysis.jl/src/{AbstractAnalysis,magma,perm,metric}.jl` | 0.2.2 @11d02ed (2026-07-23) | Byte-identical to the depot `AbstractAnalysis/zP6E5`. Extensions are in `ext/{ModsExt,PrimesExt}.jl`. |
| WK | `/Users/alokbeniwal/chakravala/Wilkinson.jl/src/{Wilkinson,polynomial}.jl` | 0.1.1 @2794002 (2024-02-16) | Byte-identical to the depot. **Does not load** in juliaenv because Conda/PyPlot is not built. The numeric kernels were probed by copying them verbatim (see `probes/small/wk3.jl`). |
| ST | `~/.julia/packages/SyntaxTree/Adq4Y/src/{SyntaxTree,exprval}.jl` | 1.0.1 | Dependency of Wilkinson. Loaded via `Base.require(PkgId)`. |

Julia environments:
- `juliaenv`: AbstractAnalysis 0.2.2, AbstractLattices 0.3.1, StaticVectors 1.0.9, Wilkinson 0.1.1 (broken load), Reduce 1.2.17 (works, CSL REDUCE binary built), Combinatorics 1.1.0.
- `juliaenv2`: DeMorgan 0.1.0, Dendriform 0.2.1, AbstractLattices 0.2.1, Combinatorics **0.7.0**, JSON3. PrettyTables is **not** installed.

Line references below have the form `DF/arithmetic.jl:94`, `DM:55`, and so on.

---

## 1. Purpose and scope

| package | purpose | port priority |
|---|---|---|
| **AbstractLattices** | Defines the generic function names `wedge`/`∧` (meet), `vee`/`∨` (join) and `dist`, so that other packages can extend one shared binding. It is the root of `∧`/`∨` for the whole chakravala stack (AbstractTensors → Leibniz → Grassmann). | **P0** (Grassmann depends on it, and it is tiny) |
| **PrimitiveBits** | Fixed-width bit vectors (8/16/32/64/128) stored as Julia `primitive type`s, with 1-based bit indexing and printing. It is not used elsewhere in the ecosystem. | P3 (trivial) |
| **DeMorgan** | Classical propositional logic as a "truth-table magma". `TruthValues{N}` is a 2^N-bit truth column. `TruthTable{N,M}` is an expression that tracks the equivalence classes of every sub-expression it has seen, with their names. There is also a `@truthtable` macro and PrettyTables rendering. | P2 |
| **Dendriform** | Loday's "arithmetree": planar binary trees (`PBTree`), groves (`Grove`, sets/multisets of equal-degree trees), their compressed index (`GroveBin`), dendriform operations `⊣ ⊢ + *`, grafting `∨`, over/under `/ \`, the involution `σ`, the Tamari poset (`⋖ ⋗ < ≤ ⊴`), a canonical total order on trees ("tree integer") and grove compositions/intervals. | P2 |
| **AbstractAnalysis** | Lazy countable sequences (`CountableArray`, `FunctionArray`, memoized `SequenceArray`), standard countable sets (ℕ, ℤ, ℚ via Stern–Brocot/Calkin–Wilf, Cantor/Szudzik pairings, Gaussian integers), `Limit` objects for iterated maps (orbits, series, products), metrics and norms, convergence predicates, finite `Semimagma`/group theory and permutations. **Cartan.jl imports it heavily** (`Limit`, `orbit`, `supnorm`, `SequenceArray`, `extract`, `assign!`, ...). | **P1** (Cartan dependency) |
| **Wilkinson** | Research code on polynomial rounding error. It compares expanded, Horner and factored forms of a polynomial using SyntaxTree's "expression value" `exprval` and a Simpson–Stieltjes log-error-bound integral. It relies on the REDUCE CAS and PyPlot. | P3 (numeric kernels + `exprval`; CAS parts optional) |

---

## 2. Public API inventory

Julia precedence levels quoted below come from `Base.operator_precedence` **[run]**: `⊣ ⊢ ⋖ ⊴` 7 (comparison), `∪ ∨ +` 11, `∧ * / \` 12, `--> <--> →` 4 (arrow, right-assoc). In Julia, `⊣`/`⊢` being comparison-level means `a ⊣ b ⊢ c` is a **chained comparison** (`(a⊣b) && (b⊢c)`), not a composition. `Grove(3,7) ⊣ [1,2]∪[2,1]` parses as `Grove(3,7) ⊣ ([1,2]∪[2,1])`.

### 2.1 AbstractLattices (AL)

| symbol | ASCII alias | signature / semantics | line |
|---|---|---|---|
| `wedge` | – | generic function stub (`function wedge end`) | AL:5 |
| `vee` | – | generic function stub | AL:6 |
| `∧` | `wedge` | `const ∧ = wedge` (the same binding, so extending one extends both) | AL:8 |
| `∨` | `vee` | `const ∨ = vee` | AL:9 |
| `wedge(x)` | | unary identity: `= x` | AL:11 |
| `vee(x)` | | unary identity: `= x` | AL:12 |
| `wedge(p::Bool,q::Bool)` | | `p && q` (only in 0.2.2/0.3.x; missing in 0.2.1) | AL:14 |
| `vee(p::Bool,q::Bool)` | | `p \|\| q` | AL:15 |
| `dist` | – | generic function stub with no methods | AL:17 |

Exports: `∧, ∨, dist, wedge, vee` (AL:3). The test file (`test/runtests.jl:4-15`) defines `∨(a::Number,b::Number)=max`, `∧=min` and checks `5∧10==5`, `5∨10==10`, `wedge(3)==vee(3)`. Downstream, AbstractTensors (`AbstractTensors.jl/src/AbstractTensors.jl:271-274`) imports these and adds nullary `∧()=1`, `∨()=I`.

### 2.2 PrimitiveBits (PB)

`Declare(b)` (PB:6-36) is `eval`ed for `b ∈ [8,16,32,64,128]` (PB:38-40). Each call generates the following, where `W` is `PrimitiveBits$b` and `U` is `UInt$b`:

| API | semantics | line |
|---|---|---|
| `primitive type W b end`, exported | b-bit bitstype | PB:9-10 |
| `W(b::U)` | `reinterpret` (identity on bits) | PB:12 |
| `U(b::W)` | `reinterpret` back | PB:13 |
| `getindex(b::W, i::Integer)` | `d = one(U) << (i-1); (d & U(b)) == d`, i.e. bit i-1, LSB = index 1. **Quirk:** if `i ≤ 0` or `i > b`, Julia's shift gives `d == 0` and the result is `true` **[run]** (`b[0] == b[17] == true` for a 16-bit value). | PB:14-17 |
| `getindex(b, r::UnitRange)` | `[b[j] for j∈r]` → `Vector{Bool}` | PB:18 |
| `getindex(b, :)` | `[b[j] for j∈1:b]` | PB:19 |
| `firstindex`, `lastindex`, `length` | `1`, `b`, `b` | PB:20-22 |
| `iterate(b, i=1)` | **broken**: references an undefined `r` → `UndefVarError` **[run]**. `collect(b)` and `for x in b` therefore fail. | PB:23-27 |
| `W(b::Integer)` | `W(convert(U,b))`. `InexactError` if the value is negative or does not fit. | PB:28 |
| `W(b::Union{BitVector,Vector{Bool}})` | `parse(U, join(reverse(bits) as '0'/'1'), base=2)`: element 1 is the LSB. An empty vector errors (parse of ""). A vector longer than b overflows (parse error). | PB:29-31 |
| `print(io,b)` / `show(io,b)` | `'[' * join(Int(b[i]) for i∈1:b) * ']'`, LSB first, no separators | PB:32-33 |

The generated names are exported: `PrimitiveBits8, PrimitiveBits16, PrimitiveBits32, PrimitiveBits64, PrimitiveBits128`. `==` is bitwise equality (the default for primitive types).

### 2.3 DeMorgan (DM)

Exports: `TruthValues, Tautology, TruthTable, @truthtable` (DM:28) and `⟂, ⊥, ⊤, ¬, ∧, ∨, -->, <--, <-->, →, ←, ↔` (DM:29).

| symbol | alias | signature / semantics | line |
|---|---|---|---|
| `TruthValues{N} <: Integer` | | `struct` with one field `p::UInt` holding a 2^N-row truth column (bit k = row k) | DM:31-33 |
| `TruthValues{0}()` | | `TruthValues{0}(0)` | DM:35 |
| `TruthValues()` | | `TruthValues{0}()` | DM:36 |
| `TruthValues(p::Bool...)` (N args) | | `TruthValues{N}(\|(p .<< (0:N-1))...)`: packs the Bools as bits with arg 1 at bit 0. **N here is the number of args, not log2 of the row count** (odd but literal). `TruthValues(false,true,true,false)` → `TruthValues{4}(6)` **[run]**. | DM:37 |
| `⟂`, `⊥` | | both `TruthValues()`, i.e. `TruthValues{0}(0)` (contradiction) | DM:39 |
| `(::TruthValues{0})(::TruthValues...)` | | returns `⊥` | DM:40 |
| `show(::TruthValues{0})` | | prints `⊥` | DM:41 |
| `Tautology`, `⊤` | | singleton struct and its instance | DM:43-44 |
| `(::Tautology)(::TruthValues...)` | | `⊤` | DM:45 |
| `show(::Tautology)` | | `⊤` | DM:46 |
| `wedge(p::TV{N},q::TV{N})` | `∧` | `TV{N}(p.p & q.p)` | DM:48 |
| `vee(p,q)` | `∨` | `TV{N}(p.p \| q.p)` | DM:49 |
| `&`, `\|` on `TV{N}` | | same as `∧`, `∨` (same-N only; `t2 & ⊥` → error **[run]**) | DM:50-51 |
| `-->(p,q)` | `→` | `¬p ∨ q` | DM:52, 58 |
| `<--(p,q)` | `←` | `p ∨ ¬q` | DM:53, 58 |
| `<-->(p,q)` | `↔` | `(p-->q) ∧ (q-->p)` | DM:54, 58 |
| `!(p::TV{N})` | `¬` | `TV{N}(p.p ⊻ mask(N))`, where `mask(N) = (UInt(1) << (1<<N)) - 1`. Julia's `<<` by ≥64 yields 0, so `mask(6) = 0 - 1 = 0xFFFF_FFFF_FFFF_FFFF` (correct). | DM:55 |
| `!(::TV{0})` | | `⊤` | DM:56 |
| `!(::Tautology)` | | `⊥` | DM:57 |
| mixed `op(TV{0},TV{N})`, `op(TV{N},TV{0})` for op ∈ {∧,∨,-->,<--,<-->} | | lift ⊥: `TV{N}(p.p)` (keeps the raw bits) | DM:148-151 |
| `op(⊤,TV{N})`, `op(TV{N},⊤)` | | lift ⊤ to `TV{N}(tautology(N))` | DM:152-153 |
| `TruthTable{N,M}` | | fields `p::Values{M,UInt}` (distinct class columns), `n::Values{M,Tuple{Vararg{String}}}` (the names/aliases of each class), `i::Int`, `j::Int` (the current expression is alias `j` of class `i`) | DM:60-65 |
| `TruthTable{N}(p::UInt, s::String)` | | the one-class table `(Values(p), Values(((s,),)), 1, 1)` | DM:67 |
| `TruthTable{N,0}()` | | empty table, `i=j=0` | DM:68 |
| `string(t::TruthTable)` | | `t.n[t.i][t.j]` | DM:70 |
| `parstring(p)` (internal) | | parenthesizes when needed (§4.3) | DM:71-78 |
| `select(n,N)`, `select(N)`, `extend(n,N)` (internal) | | projection columns, padding helper (§4.3) | DM:80-85 |
| `@truthtable names...` | | binds each name to a projection `TruthTable{N,1}` and returns `nothing` | DM:87-91 |
| `&`, `\|` on `TruthTable{N}` | | same as `∧`, `∨` | DM:93-94 |
| `!(p::TruthTable{N,M})` | `¬` | `combine(p, !TV{N}(p.p[p.i]), ("¬(" * last alias of class i * ")",))` | DM:95-98 |
| `tautology(n)`, `istautology(n::UInt,N)` (internal) | | `mask(n)`; `n == mask(N)` | DM:100-101 |
| `combine(...)` (internal) | | class-merging algorithm (§4.3) | DM:103-146 |
| `op(p::TruthTable{N,P}, q::TruthTable{N,Q})` for op ∈ {∧ '∧', ∨ '∨', --> '→', <-- '←', <--> '↔'} | | `r = op(TV(p.p[p.i]), TV(q.p[q.i]))`, then `combine(p, q, r, (parstring(p) * sym * parstring(q),))` | DM:148-159 |
| `pretty_table(::TruthTable)` + `show` | | only when PrettyTables is loaded (Requires) (§5.3) | DM:161-172 |

Note: `-->` and `<-->` are parsed as arrow operators (precedence 4, right-assoc): `p-->q<-->r` = `p --> (q <--> r)` **[run]**. `∧` is at 12 and `∨` at 11, so `p ∧ q ∨ r` = `(p∧q)∨r`. `¬` is prefix unary.

### 2.4 Dendriform (DF)

Exports: DF/Dendriform.jl:9 `PBTree, Grove, GroveBin, ==, Cn, grovesort, grovesort!, σ, print, grovecomposition, grovedisplay`; DF/morphism.jl:4 `treecheck, grovecheck, treeindex, treeindexCn, groveindex, grovebit, treeshift`; DF/arithmetic.jl:4 `∪, ∨, graft, left, right, dashv, vdash, ⊣, ⊢, +, *`; DF/poset.jl:4 `⋖, ⋗, posetnext, posetprev, between, ⊴, over, under`. The package also adds methods to `Base.<, >, ≤, ≥, /, \, ==, ∪, +, *`.

Type unions (DF/Dendriform.jl:81-86): `Ar1UI8I = Vector{UInt8}∪Vector{Int}`, `Ar2UI8I = Matrix{UInt8}∪Matrix{Int}`, `AbstractPBTree = PBTree∪Ar1UI8I`, `UI8I = UInt8∪Int`, `NotGrove = GroveBin∪AbstractPBTree∪Ar2UI8I∪UI8I`, `PureGrove = Grove∪GroveBin∪Ar2UI8I`. Plain Julia vectors and matrices are therefore accepted as trees and groves everywhere. That is type piracy on `Base.<` and `Base.∪` for `Vector{Int}`.

**Types**

| type | fields | line |
|---|---|---|
| `abstract type AbstractGrove` | | DF/Dendriform.jl:15 |
| `mutable struct PBTree` | `degr::UInt8` (degree = number of internal vertices = name length), `Y::Vector{UInt8}` (Loday name) | :27-30 |
| `mutable struct Grove` | `degr::UInt8`, `size::Int` (row count), `Y::Matrix{UInt8}` (size × degr, one tree name per row; rows may repeat) | :43-47 |
| `mutable struct GroveBin` | `degr::UInt8`, `size::Int`, `gbin::Integer` (BigInt grove index), `ppos::Float16` (percentage `100*gbin/(2^Cn(d)-1)`) | :61-66 |
| `mutable struct BaseTree` | `μ::Vector{Vector{UInt8}}` (μ[ω] = positions whose label is `d+1-ω`) | :77-79 |
| `Cn = catalannum` | Catalan numbers from Combinatorics. **Returns BigInt** **[run]**. `Cn(0)=1`. | :87 |

**Constructors / conversions**

| call | result | line |
|---|---|---|
| `PBTree(deg, ind::Int)` | row `ind` of the total grove `Υ(deg)` (sorted order). `deg==0` gives the empty tree. `treecheck` is called but **its result is ignored**, so a bad `ind` throws `BoundsError` **[run]**. | :96-100 |
| `PBTree(t::Vector)` | `convert`: `PBTree(isempty ? 0 : length, UInt8.(t))`. No validity check. | :107, 153-155 |
| `Grove(g::Matrix)` | `Grove(GroveDeg(g), GroveSiz(g), UInt8.(g))`: degree = number of columns (0 if empty), size = number of rows | :114, 162-167 |
| `Grove(t::Vector)` | `Grove(PBTree(t))` | :115, 168 |
| `Grove(d, g::Matrix)` | explicit degree | :116 |
| `Grove(t::PBTree)` | 1-row grove. A degree-0 tree gives a **1×0** matrix with size 1. | :123, 157-160 |
| `Grove(d::UI8I)` | total grove `Υ(d)`. **Returns the shared cached object.** | :124, 172 |
| `Grove(d, s::BitVector)` | `TreeLoday(d, s)`: the rows of `Υ(d)` at the set bits, in ascending index order | :125, DF/morphism.jl:150 |
| `Grove(g::GroveBin)` | `Grove(g.degr, g.gbin)` | :126, 171 |
| `Grove(s::BitVector)` | `Grove(CnInv(length(s)), s)`, where the degree is recovered from the Catalan length | :127 |
| `Grove(g::Grove)` | identity (same object) | :128 |
| `Grove(d, s::Integer)` | `Grove(d, grovebit(d,s))`: decodes a grove index | :135 |
| `Grove(g::Vector{PBTree})` | stacks rows (degree from `g[1]`). An empty vector gives `Grove(0)`. | DF/morphism.jl:365-374 |
| `convert(Grove, ::Vector{Any})`, `::Matrix{Any}` | via UInt8 | :169-170 |
| `GroveBin(g::Grove)` | `GroveBin(UInt8(g.degr), g.size, groveindex(g))` → 3-arg ctor | :142 |
| `GroveBin(g::NotGrove)` | `GroveBin(convert(Grove,g))`, so `GroveBin(5)` is the total grove of degree 5 | :143 |
| `GroveBin(d, s::Int, i::Integer)` | `ppos = Float16(100i // (2^Cn(d)-1))` (BigInt arithmetic) | :144 |
| `promote_rule(PBTree, Ar1)`, `promote_rule(Grove, Ar1∪Ar2∪PBTree∪UI8I)` | | :173-174 |

**Equality / order**

| op | semantics | line |
|---|---|---|
| `PBTree == PBTree` | `degr` and `Y` equal | :146 |
| `Grove == Grove` | `degr`, `size` and `grovesort!(a).Y == grovesort!(b).Y` (multiset equality). **Mutates both operands** by sorting their rows in place **[run]**. | :147 |
| `BaseTree ==` | `μ` equal | :148 |
| `GroveBin ==` | `degr`, `size`, `gbin` equal | :149 |
| `<, >, ≤, ≥` on `PureGrove` | compare `groveindex` (integer order) | DF/morphism.jl:346-349 |
| `<(a::PBTree, b::PBTree)` and on vectors | Tamari strict order (§4.4.7) | DF/poset.jl:93-105 |
| `≤` | `a == b \|\| a < b` | :112-113 |
| `>` | Tamari via `posetprev_list` | :120-132 |
| `≥` | `a == b \|\| a > b` | :139-140 |
| `⋖(a,b)` | `b ∈ posetnext_list(a)` (b covers a) | :44-45 |
| `⋗(a,b)` | `b ∈ posetprev_list(a)` (a covers b) | :83-84 |

**Tree operations**

| op | alias | semantics | line |
|---|---|---|---|
| `∨(L,R)` (trees or vectors) | `graft` | graft: `[L.Y; L.degr+R.degr+1; R.Y]` | DF/arithmetic.jl:38-50, 57 |
| `left(t)` | | subtree left of the root label | :66-72 |
| `right(t)` | | subtree right of the root label | :79-85 |
| `σ(x)` | | involution: reverse the name (trees) or reverse the columns (groves, `GroveBin` → `Grove`) | DF/Dendriform.jl:216-219 |
| `over(x,y)` | `/` | `y.degr>0 ? over(x,left(y)) ∨ right(y) : x` (graft x onto y's leftmost leaf) | DF/poset.jl:184-185, 192 |
| `under(x,y)` | `\` | `x.degr>0 ? left(x) ∨ under(right(x),y) : y` (graft y onto x's rightmost leaf) | :199-200, 207 |
| `posetnext(t)` | | `Grove(posetnext_list(t))` (covers above t, unsorted) | :36-37 |
| `posetprev(t)` | | `Grove(posetprev_list(t))` | :75-76 |
| `between(a,b)` | `⊴` | `Grove(between_list(a,b))`: the Tamari interval [a,b] in DFS order; `Grove(0)` if a ≰ b | :165-166, 173 |
| `LeftInherited(t)` (not exported) | | `right(t).degr == 0` | DF/morphism.jl:13-14 |
| `RightInherited(t)` | | `left(t).degr == 0` | :21-22 |
| `PrimitiveTree(t)` | | left- or right-inherited | :29-30 |

**Grove operations**

| op | alias | semantics | line |
|---|---|---|---|
| `∪(x, y...)` | | union: OR of grove bit vectors, then decode. The result is **canonical (sorted, deduplicated)**. `@info "$s duplicate(s) in grove union"` is logged when rows collapse. `∪(x)` returns `Grove(x)` **unchanged** (not canonicalized). | DF/arithmetic.jl:14-29 |
| `⊣(x,y)` | `dashv` | left dendriform "half-sum" (§4.4.4) | :94-151 |
| `⊢(x,y)` | `vdash` | right half-sum | :160-217 |
| `+(x,y)` | | `x ⊣ y ∪ x ⊢ y` per tree pair, as a multiset in a specific order | :226-243 |
| `*(x,y)` | | Loday multiplication (§4.4.5) | :252-274 |

**Index / check / transformation functions**

| function | semantics | line |
|---|---|---|
| `treecheck(d,t)` | `0 < t ≤ Cn(d)` | DF/morphism.jl:39 |
| `treecheck(t::PBTree)` | `treecheck(t.degr, treeindex(t))`. Throws if the tree is not found (`nothing[1]`). | :40-41 |
| `treecheck(g::Grove)` | no row has treeindex 0 (all rows are valid trees) | :42-43 |
| `grovecheck(d,gi)` | `0 ≤ gi < 2^Cn(d)` | :50 |
| `grovecheck(g)` | `grovecheck(g.degr, groveindex(g))` | :51-52 |
| `GroveError(n)`, `GroveError(g)` (not exported) | `treeindex(n) - sortperm(TreeInteger(n))`, or `[1:size] - sortperm(TreeInteger(g))`: zeros iff the rows are sorted | :59-61 |
| `treeindex(g::Grove)` | `Vector{Int}` of 1-based tree indices per row (0 if invalid) | :70-82 |
| `treeindex(t::PBTree)` / `treeindex(d, j::Int)` | index of the tree with tree integer j | :84-85 |
| `treeindex(d)` | `[1:Cn(d)...]` | :86 |
| `treeindexCn(d)` | `treeindex(d) .// Cn(d)` | :87 |
| `grovebit(g)` | `BitVector` of length Cn(d), bit i = tree index i present | :96-108 |
| `grovebit(d, s::Integer)` | binary digits of s, LSB first, padded with `falses` to Cn(d) (errors if `s ≥ 2^Cn(d)`) | :110-113 |
| `groveindex(g)` | `Σ_rows 2^(treeindex-1)` as **BigInt, counting multiplicity** (duplicate rows double-add). On error: `DomainError(g)` if every row is valid, else `-1`. | :122-137 |
| `groveindex(b::BitVector)` | `Σ_{set bits} 2^(i-1)` | :139-146 |
| `TreeLoday(...)` (not exported) | BaseTree→PBTree name; (d, indices)→Grove; `TreeLoday(d)` = `Υ(d)`; `TreeLoday(d, s::Integer)` = `Grove(d,s)` | :150-187 |
| `TreeBase(...)` (not exported) | name→BaseTree (§4.4.2); grove→`Vector{BaseTree}`; `TreeBase(d)` = TreeBase of Υ(d). `TreeBase(d, s::Integer)` is buggy (`grovebit(findall(x->x!=0, s))`). | :196-231 |
| `ΘMax(d)`, `ΘInt(μ)` (not exported) | §4.4.2 | :235-261 |
| `TreeInteger(...)` (not exported) | `ΘMax(d) - ΘInt(μ)`. Also accepts (d, grove index), (d, BitVector), (d, indices) via the cached table, groves, and arrays. `TreeInteger(d)` = the sorted table `ΥI(d)`. | :270-296 |
| `TreeRational(...)` (not exported) | §4.4.2 (depends on `treeshift`) | :305-332 |
| `treeshift(tf=current)` | global toggle, default `true`, returns `Int(state)` | :339-342 |
| `grovesort(tf=current)` | global toggle, default `true`. Changing it **resets the total-grove cache** (`ΥGS()`). Returns the state. | DF/Dendriform.jl:194-197 |
| `grovesort!(g)` | sorts rows by TreeInteger in place, returns the grove | :184-187 |
| `grovedisplay(tf=current)` | global toggle, default `false` | :397-400 |
| `CnInv(n)` (not exported) | smallest d with Cn(d)==n, else `error("$n is not a Catalan number")` | :201-209 |
| `grovecomposition(d, ind)` | prints the grove and all its ordered +‑decompositions, returns the count (§4.4.9) | :366-388 |
| `intervals(d)`, `intcomp`, `intcompt`, `intervals_full`, `print_interval_bin`, `print_intcomp_bin`, `print_intcompt_bin` (not exported) | Tamari-interval research tools (§4.4.10) | DF/poset.jl:211-296 |

### 2.5 AbstractAnalysis (AA)

Exports, gathered from: AA/AbstractAnalysis.jl:36-39, 230, 324-325, 382, 396-398; AA/magma.jl:30, 99-100, 104-108; AA/perm.jl:15, 82, 121; AA/metric.jl:15, 75, 374, 389, 486, 546.

**Countable containers** (AA/AbstractAnalysis.jl)

| symbol | semantics | line |
|---|---|---|
| `AbstractCountable{T,N,F} <: AbstractArray{T,N}` | root type | 41 |
| `CountableFunction{T,N,F} <: AbstractCountable` | | 42 |
| `counter(x)` (not exported) | the generator function `x.f` | 44, 247, metric 87, 383 |
| `broadcast(f, x::CountableFunction)` | `= map(f,x)` (stays lazy) | 45 |
| `x[ϵ::AbstractFloat]` for a 1-D CountableFunction or SequenceArray | `limit(x, ϵ)` | 46, 268 |
| `CountableArray{T,N,F}` | fields `f::F`, `n::Variables{N,Int}` (a **mutable** size). `x[i...] = f(i...)`, **with no bounds check**. | 48-51, 85-89 |
| `CountableVector{T,F}`, `CountableMatrix{T,F}` | N=1/2 aliases | 53-54 |
| `Ones`, `Zeros` | `CountableVector{Int,typeof(one)}` / `{Int,typeof(zero)}`. `Ones(n)` = `CountableVector(one,n)`. | 55-56, 75-76 |
| constructors | `CountableVector(f, n=100)` (T inferred from `f(1)`); `CountableVector(n=100)` = `Naturals(n)`; `CountableMatrix(f, n=100, m=100)`; `CountableArray(f, n...)`; `CountableArray(n...)` = grid of index tuples. `CountableMatrix{T}(f,n,m)` has a **bug**: it builds size `(n,)`. | 58-74 |
| `CountableVector(r::AbstractRange)` | `i ↦ first + step*(i-1)`, length(r) | 78-80 |
| `(x::CountableArray)(n...)` | same f, new size (truncate/extend) | 82-83 |
| `resize!(x::CountableVector, i)` | **mutates** `x.n[1]`, including on global constants like `Naturals` | 86 |
| `x[i,j]` on a CountableVector | `j==1 ? f(i) : f(i,j)` | 88 |
| `Semimagma(v::CountableVector, f=*, g)` | collects | 91 |
| `map(f, x::CountableArray)` | if `F == identity`: `CountableArray(f, size)`, else `f∘counter` | 96-97 |
| `mapmap(f, x)` | **buggy**: `countmapmap` uses an undefined `f` | 93-98 |
| `a ⊙ x`, `x ⊙ b`, `x ⊙ y` for ⊙ ∈ {* + / - ^} | pointwise. Number∘Countable maps. Countable∘Countable gives size `min.(size(a),size(b))`. | 100-109 |
| unary ops `inv - abs ! ~ real imag conj floor ceil round exp exp2 exp10 log log2 log10 sinh cosh sqrt cbrt cos sin tan cot sec csc asec acsc sech csch acsch asech tanh coth asinh acosh atanh acoth asin acos atan acot sinc cosc cis abs2 angle` | `map(op, x)` on any AbstractCountable (and on `Limit`, metric.jl:178-180) | 110-113 |
| `dot(a,b,Σ=sum)` | `Σ(a*b)`: **returns a `Limit`** because `sum` of a CountableVector is a Limit. Ones shortcut. | 115-120 |
| `countabletuple(x,y[,z])`, `countableproduct(x,y[,z],op=*)` | outer products `(i,j)↦op(x(i),y(j))` | 122-131 |
| `FunctionArray{T,N,F}` | `f(x, i...)` families. `x[i]` = `Fix2(f,i)` (a function of x). `(x::FunctionArray)(u)` = `CountableArray(Fix1(f,u), size)`. | 133-167 |
| `FunctionVector`, `FunctionMatrix`, ctors | `FunctionVector(f, n=100)`. `FunctionMatrix(f,n,m)` needs `Fix{3}` (Julia ≥1.12). `FunctionArray(n...)` = `^` family. | 138-155 |
| arithmetic on FunctionArray | as above | 169-175 |
| `dot(c::AbstractArray, f::FunctionArray)` | `Series(c,f)` | 177-178 |
| `functiontuple`, `functionproduct` | **buggy** (undefined `x,y,z`) | 180-189 |
| `Series{N,C,F}` | `v::C` coefficients, `f::F` FunctionArray. `Series(f)` has `Ones` coefficients. `sum(f::FunctionArray)` = `Series(f)`. `(s)(x, Σ=sum)` = `dot(v[1:len], f(x), Σ)`, a Limit. `resize!`. | 191-212 |
| `Product{N,F}` | `prod(f::FunctionArray)`; `(p)(x, Π=prod)` = `Π(f(x))`; `log(p)` = `sum(log(f))` | 214-226 |
| `SequenceArray{T,N,V,F}` | `v::V` storage (Vector/ElasticArray), `f::F` recurrence `f(v,k)` giving element k. **Reading past the end extends and mutates.** | 232-281 |
| `SequenceVector`, `SequenceMatrix` | aliases/ctors | 237-241 |
| `resize!(c::SequenceVector, n)`, `resize_lastdim!` | extend by `assign!(v,k,F(v,k))` for k=m+1..n | 249-266 |
| `extract(x, i)`, `assign!(x, i, s)` | last-dimension slice get/set (views for N ≥ 2, up to 5-D) | 274-281, 300-310 |
| `cumsum`, `cumprod` | `Zeros`→self; `cumsum(Ones)`=`Naturals(len)`; `cumprod(Ones)`=self; CountableVector → SequenceArray of prefix sums/products (eager to `len`, lazy beyond) | 283-298 |
| `map(f, s::SequenceArray)` | lazy `CountableArray(f∘getindex(s))` | 312 |
| arithmetic on SequenceArray | → CountableArray | 314-322 |
| `SequenceArray(n::Int...)` | a `CountableArray` over index tuples whose elements are the CountableVectors `(n..., 1, 1, ...)` (weird but literal) **[run]** | 422-424 |
| `SequenceArray(fun, n...)` | `mapmap(...)` (broken) | 425 |

**Countable sets** (AA/AbstractAnalysis.jl:327-420)

| symbol | definition | line |
|---|---|---|
| `cantorinversion(n)` (internal) | `w=floor((√(8n+1)-1)/2); t=(w^2+2)÷2; (n-t, w-n+t)`. **Bug:** the correct t is `(w^2+w)÷2`, so it yields `(4,-1)` at n=9 **[run]**. | 327-331 |
| `elegantinversion(n)` | Szudzik unpairing from 0: `s=⌊√n⌋; r=n-s²; r<s ? (r,s) : (s, r-s)` | 333-341 |
| `elegantinversion(n,k)`, `elegantinversion1(n)=(n,1)` | offset version: `s=⌊√(n-k)⌋; r=n-s²-k; r<s ? (r+k, s+k) : (s+k, r-s+k)` | 343-352 |
| `elegantpair(a,b)` / `elegantproduct(a,b,op=*)` | `CountableVector(n ↦ op(a(i),b(j)))` with `(i,j)=elegantinversion1(n)`, default length 100 | 354-361 |
| `sternbrocot(n)` | Stern diatomic `fusc`: 1↦1; even `fusc(n/2)`; odd `fusc(k)+fusc(k+1)`, k=(n-1)÷2 | 363-372 |
| `sternbrocot(a, n)` | memo recurrence (reads `a`) | 373-380 |
| `SternBrocot` | `SequenceArray([1], sternbrocot)` | 381 |
| `integer(n)` | `even ? n÷2 : -(n÷2)`: 1→0, 2→1, 3→-1, 4→2, ... | 384 |
| `positiverational(n)` | `fusc(n)//fusc(n+1)` (Calkin–Wilf) | 385 |
| `rational(z)` | `m=integer(z); m==0 ? 0//1 : sign(m)*positiverational(|m|)` | 386-390 |
| `nonzerorational(n)` | `rational(n+1)` | 387 |
| `complextuple(t)` | `Complex(t...)` | 392 |
| `prime(u,i)` | `prime(i)`. `prime(i)` itself comes from **PrimesExt** (`Primes.prime(Int,i)`, ext/PrimesExt.jl:5). | 394 |
| `Naturals` | `CountableVector(identity)` (len 100) | 400 |
| `Integers` | `CountableVector(integer)` | 401 |
| `PrimeIntegers` | `CountableVector{Int}(prime)` (needs Primes) | 402 |
| `PrimeCache` | `SequenceArray([2], prime)` | 403 |
| `CantorPairs` | `CountableVector(cantorinversion)` | 404 |
| `ElegantPairs0`, `ElegantPairs1`, `ElegantPairs` (=1) | | 405-407 |
| `PositiveRationals`, `Rationals`, `NonzeroRationals` | | 408-410 |
| `GaussianNaturals` | `map(complextuple, ElegantPairs1)` | 411 |
| `GaussianIntegers` | `map(complextuple, elegantpair(Integers,Integers))` | 412 |
| `GaussianRationals` | same over Rationals | 413 |
| `prod(x::typeof(Naturals))` | `Limit(1=>fact(1), len=>∏, len, supnorm(val/x[end], val), fact)`, with `fact = factorial∘big` if len>20 | 415-419 |
| `cumprod(x::typeof(Naturals))` | `CountableVector(factorial[∘big], len)` | 420 |

**Magma / groups** (AA/magma.jl, AA/perm.jl)

| symbol | semantics | line |
|---|---|---|
| `Semimagma{T,F,G} <: DenseVector{T}` | `v::Vector{T}`. **F (law) and G (inverse) are type parameters holding function instances.** Ctor `Semimagma(v::Vector, f=*, g=groupinverse(f))` requires a `Vector` (not any AbstractVector). | magma.jl:32-35 |
| `grouplaw(G)`, `groupinverse(G)` | F, G | 37-38 |
| `groupinverse(*)=inv`, `groupinverse(+)=-` | no other defaults (a custom law needs an explicit inverse, else MethodError **[run]**) | 39-40 |
| `(G)(a,b)` | `F(a,b)` | 41 |
| `size`, `getindex`, `length` | vector interface | 43-44, 49 |
| `order(G)` / `abs(G)` | `length(G)` | 46, 50 |
| `order(n, f=*, g)` | `order(group(n,f,g))` = size of the cyclic magma of n | 47 |
| `orders(G)` | `order.(G, F, G)`: per-element cyclic order. `[4,2,4,1]` for ⟨i⟩ **[run]**. | 48 |
| `iseven(G)`, `isodd(G)` | all elements even/odd | 52-53 |
| `G == H` | `G ⊆ H && H ⊆ G` (set equality via `gequal`) | 55 |
| `gexp(a,n,op)` (internal) | right-fold power | 57-63 |
| `gequal(a,b)` (internal) | `a ≈ b` (isapprox). ModsExt makes it `==` for Mods. | 64; ext/ModsExt.jl:5 |
| `g ∈ G` | linear scan with gequal | 65-70 |
| `compose(g,H,F=law)` / `compose(H,g,F)` | translate each element (keeps order and duplicates) | 72-73 |
| `compose(G,H,F)` | all `F(g,h)` for g outer, h inner, deduplicated in first-seen order | 74-83 |
| `∘` | `compose` with the group law | 85-87 |
| `*`, `+` with Number / element / Semimagma | `compose` with op `*` or `+` (not the law). `Int * Semimagma{Complex{Int}}` has **no method** (T must match) **[run]**. | 89-97 |
| `cayley(G)` | matrix `M[i,j] = G(v[i], v[j])` | 102 |
| predicates `iscategory, ismonoid, isgroupoid, issemicategory, issemigroup, ismagma, iscyclic, isabelian, isassociative, isinvertible, isgroup` | default `false` for non-Semimagma | 104-109 |
| `iscategory(G)`=`ismonoid(G)` | `isone(G) ∈ G && issemicategory(G)`: **broken** (`one(::Semimagma)` exists only for permutations, and even then compares wrong types) | 111-112 |
| `isgroupoid`=`isgroup`; `issemicategory`=`issemigroup` | | 113-114 |
| `issemigroup` | `ismagma && isassociative` | 115 |
| `isgroup` | `isinvertible && issemigroup` | 116 |
| `isassociative` | O(n³) check with gequal | 118-127 |
| `ismagma` | closure check | 129-136 |
| `isinvertible` | every `inv(g) ∈ G`; exceptions give false | 138-148 |
| `iscyclic(G)` | `G == group(G[1]) \|\| G == group(G[2])`: checks **only the first two elements** as generators. Broken for permutations. | 150 |
| `magma(p, F=*, Ginv)` | cyclic semigroup `[p, p², p³, ...]` until a repeat | 152-161 |
| `magma(p::AbstractVector, ...)` / `magma(G::Semimagma, out)` | closure (§4.5.6) | 162-178 |
| `group(G::Semimagma, out)` | add inverses of the initial elements, then close | 179-186 |
| `group(p::AbstractVector,...)`, `group(p,...)` | Semimagma / cyclic magma. **`group(::Permutation)` is broken**: Permutation <: AbstractVector, so it dispatches to the vector method, which needs a `Vector` **[run]**. | 187-192 |
| `subsemigroup(G, out)` | default arg uses an undefined `Semigroup` (broken unless `out` is given) | 194-209 |
| `subgroup(G, out)` | keep elements whose inverse is in `out`, then subsemigroup | 211-225 |
| `issubgroup(H,G)`, `issubset(H,G)` | | 227-228 |
| `isabelian(G)` | all pairs commute | 230-237 |
| `center(G)` | **buggy algorithm** (§4.5.6): returns `[id, (1,3,2)]` for S3 **[run]** | 240-258 |
| `centralizer(H, G=defaultgroup(H))` | g ∈ G commuting with all of H | 260-279 |
| `isnormal(H, G)` | `∀g: g∘H == H∘g` (set equality) | 281-286 |
| `normalizer(H, G)` | g with `g∘H == H∘g` | 288-300 |
| `commutator(G, H=G)` | closure of `{g⁻¹h⁻¹gh}` | 302-311 |
| `G / N` | `leftcosets(N, G)` | 313 |
| `leftcosets(H, G)`, `rightcosets(H, G)` | `g∘H` / `H∘g` lists, deduplicated with **ordered** comparison (quirk: S3/⟨(12)⟩ gives 6 "cosets" **[run]**) | 315-330 |
| `AbstractPermutation{N} <: AbstractVector{Int}` | | perm.jl:17 |
| `one(G::Semimagma{<:AbstractPermutation{N}})`, `one(p)` | identity `Permutation{N}(I)` | 19, 48 |
| `isone(a)`, `isodd(a)`, `iseven(a)` | `a==one(a)`; parity of `order(a)` (the transposition count) | 20-22 |
| `a*I`, `I*b` | identity | 23-24 |
| `a∘b`, `a*b` | `a(b)`: **composition, b applied first**: `(a*b)[i] = a[b[i]]`. Only works when a is a `Permutation` (Cycle is not callable). | 25-26, 45 |
| `a/b`, `a\b` | `a(inv b)`, `inv(a)(b)` | 27-28 |
| `a^n` | 1→a; n>0 → `a*a^(n-1)`; n<0 → `inv(a)^-n`; 0 → `one(a)` | 29 |
| `defaultgroup(G)`, `SymmetricGroup(G)` | `SymmetricGroup(N)` for a permutation Semimagma | 31-32 |
| `Permutation{N,T}` | `v::T` (1-based images). `Permutation(v)` sets `N=length(v)`. `Permutation(n::Int...)` uses `Values`. | 34-39 |
| `p[i]`, `p(i)`, `p(q)` | image, image, composition | 43-45 |
| `Permutation{N}(I)` | `Values(1..N)` | 47 |
| `inv(p)` | `sortperm(p.v)` | 49-50 |
| `commutator(g::Permutation,h::Permutation)` | broken (uses `group(::Permutation)`) | 51 |
| `Cycle{N,T}` | `v::T` cycle list; `Cycle{N}(n::Int...)` | 53-60 |
| `Transposition{N}` | `Cycle{N,Values{2,Int}}` | 58 |
| `Permutation(c::Cycle{N})` | `evalperm` over 1..N | 61-66 |
| `CycleProduct{N,T<:Tuple}` | tuple of Cycles | 71-78 |
| `Permutation(c::CycleProduct)` | identity if empty, else `*(Permutation.(cycles)...)` (rightmost cycle applied first) | 80 |
| `CycleProduct(p::Permutation)` | disjoint cycles, each started at its smallest unvisited element, fixed points omitted | 84-93, 98-101 |
| `decompose(p)` | one cycle → `Cycle`, else `CycleProduct` (including empty) | 94-97 |
| `decompose(G::Semimagma)` | elementwise | 103 |
| `order(c::Cycle)` | `length(c.v) - 1`: the **transposition count, not the group order** | 108 |
| `order(c::CycleProduct)` | sum (0 if empty) | 109 |
| `order(p::Permutation)` | via decompose | 110 |
| `levicivita(c)` (`ε`, not exported) | `(-1)^order` (the sign) | 112-115 |
| `isdisjoint(a::Cycle,b::Cycle)` | no shared elements (the name clashes with `Base.isdisjoint`) | 117 |
| `isabelian(a::Cycle,b::Cycle)` | disjoint or equal | 118 |
| `a == b` (Cycles) | same length and same **element set** (orientation ignored, so `(1,2,3)==(1,3,2)` **[run]**) | 119 |
| `unityroots(n)` | `Semimagma(cis.(2π/n .* (0:n-1)))` | 123 |
| `SymmetricGroup(N)` | `Permutation.(Values.(permutations(1:N)))`: Combinatorics **lexicographic** order | 125 |
| `AlternatingGroup(n)`, `AlternatingGroup(Sn)` | even elements of Sn (order preserved) | 127-128 |
| `DihedralGroup(r, s)` | `group(Perm s) * group(Perm r)`: **broken** (`group(::Permutation)`). Intended: products of ⟨s⟩ × ⟨r⟩. | 130-134 |

**Metrics, limits, analysis** (AA/metric.jl)

| symbol | semantics | line |
|---|---|---|
| `@metric f` | defines `f(a::Number,b::Number)=f(a-b)`, `f(a::AbstractArray,b::AbstractArray)=f(a-b)`, `f(a::Pair{Int},b::Pair{Int})=f(last a,last b)`, `f(a::Pair{<:Pair},b::Pair{<:Pair})=f(last a,last b)`, and fallback `f(a,b)=Inf` | 24-34 |
| `@norm f` | `f(x::Pair{Int})=f(last x)`, `f(x::Pair{<:Pair})=f(last x)`, `f(::Fix)=Inf` (Fix1/Fix2 before 1.12), then `@metric f` | 36-57 |
| `supnorm(x)` | `Inf` fallback; arrays/numbers use `LinearAlgebra.norm` (**2-norm for arrays**, abs for numbers) | 59-62 |
| `infnorm(x)` | `0.0` fallback; otherwise `norm` | 64-67 |
| `maxabs(x)` | `maximum(norm, x)` (the true sup-norm) | 69-70 |
| `minabs(x)` | `minimum(norm, x)` | 72-73 |
| `Limit{T,F,D}` | `v0::T`, `v::T`, `n::Int`, `r::Float64` (residual), `f::F` (step), `D` (metric, a type param). Ctors `Limit(v0,v,n,f,D=supnorm)` (r=Inf) and `Limit(v0,v,n,r,f,D)`. | 77-85 |
| `initial/first`, `final/last`, `length`, `lastindex`, `residual` | `first`/`last` return the **value part** for Pair states | 87-96 |
| `(L)(u)` | `Limit(u, length(L)-1, f, D)`: rerun from u. Callable with (x,y) → `D(x,y)`. Special cases for Series/Product/Fix states. | 97-112 |
| `show(L)` | §5.4 | 114-122 |
| `map(f, L)`, unary ops | lazy value map (r=Inf) | 124-137, 178-180 |
| `a ⊙ L`, `L ⊙ b`, `L1 ⊙ L2` for ⊙ ∈ {* + / - ^} | advance one step to compute Δ (§4.5.4) | 139-177 |
| `sum(x::CountableVector)` | `Limit(1=>x[1], len=>Σ, len, x[end], countsum(x))`: **residual = last term** | 204-206 |
| `prod(x::CountableVector)` | `Limit(1=>x[1], len=>Π, len, supnorm(val, val/x[end]), countprod(x))` | 207-210 |
| `sum(L::Limit)`, `prod(L::Limit)` | a series of the sequence of limit values | 211-222 |
| `cumsum(L)`, `cumprod(L)` | **buggy** (the helper uses an undefined `D`) | 224-238 |
| `Limit(v0, n, F, D=supnorm)` | iterate F n times; returns length n+1, `r=D(x_n, x_{n-1})` | 250-258 |
| `L[i::Int]` | re-seek to step i (§4.5.4) | 261-272 |
| `L[ϵ::AbstractFloat]` | `limit(L, ϵ)` | 260 |
| `collect(L)` | a `SequenceArray` of states/values (§4.5.4) | 279-296 |
| `orbit(f, x, ϵ=5eps(), Val(print)=Val(false), d=supnorm)` | iterate until `d(x_{k+1},x_k) ≤ ϵ` | 313-328 |
| `orbit(f, x, n::Int, ...)`, `orbit(f,x,n::AbstractVector,...)`, `orbit(f,x,n,d)` | a fixed n iterations | 299-312 |
| `orbiterror(f, x, ϵ=5eps())` | `(Limit, Vector{Float64} of residuals)` | 298 |
| `orbithold(f, x, n, ...)` | iterate `xn = f(x, xn)` with x held fixed | 330-340 |
| `residuals(x, d=supnorm)` | `[d(x_i, x_{i-1})]` along the last dim (Vector{Float64}). Special cases: Ones→Zeros, Zeros→Zeros, Naturals→Ones, Integers→Naturals (each with length len-1). CountableVector/SequenceArray variants are **buggy** (undefined `d`). | 342-369 |
| `lipschitz(x, d=supnorm, r=/)` | `residuals(residuals(x,d), r)`: ratios of successive residuals | 347 |
| `residualproduct(x, d)` | distance matrix | 371-372 |
| `FixedCycle{F,D}` | `n::Int` (default 100), `f`. `fc[i]` → new n. `(fc)(u, n=len)` = `Limit(u, n, f, D)`. | 374-387 |
| `isbounded(x)` (not exported) | **inverted bug**: true iff all elements are infinite | 391-396 |
| `isconverging(x)` | `!isdiverging(x)` | 398 |
| `isdiverging(x, d)` | true iff the successive residuals never decrease (scanned backwards) | 399-408 |
| `iscauchy(x, d)` | tail diameters are monotone (§4.5.5) | 410-423 |
| `ismonotonic`, `isincreasing`, `isdecreasing` | non-strict | 425-437 |
| `limit(x)` / `limit(x, n)` / `limit(x, ϵ)` | §4.5.4 | 439-484 |
| `supseq(x)`, `infseq(x)` | suffix sup/inf: `out[i] = max(x[i:end])` | 488-510 |
| `supseq(x, m)`, `infseq(x, m)` | windowed: `k ↦ max(x[k..k+m])` (CountableVector, len = length(x), lazy) | 512-535 |
| `limsup(x::AbstractCountable, [m=5], args...)`, `liminf` | `limit(supseq(x,m), args...)` | 537-540 |
| `limsup(x::AbstractVector, m=5)` | `supseq(x,m)[end-m]` = max of the last m+1 elements | 541-544 |
| `derivative(f)` / `derivative(f, x, h=eps()^(1/5))` | 5-point stencil `(-f(x+2h)+8f(x+h)-8f(x-h)+f(x-2h))/(12h)`. `derivative(f)` is curried. | 551-552 |
| `derivative2(f)` / `derivative2(f, x, h=sqrt(sqrt(eps(typeof(x)))))` | `(f(x+h)-2f(x)+f(x-h))/h^2` | 554-555 |

### 2.6 Wilkinson (WK) and the SyntaxTree functions it uses (ST)

Exports (WK/Wilkinson.jl:11): `PolynomialAnalysis, PolynomialComparison, plot, factor, expand, horner, polyfactors, polyexpand, polyhorner`. `factor`, `expand` and `horner` are Reduce's (REDUCE CAS calls); `plot` is a PyPlot method.

| symbol | semantics | line |
|---|---|---|
| `floatset(T, N; scale=identity)` (internal) | `l=scale(eps(T)); u=scale(prevfloat(T(Inf))); l:(u-l)/(N-1):u` (a Julia StepRangeLen) | WK/Wilkinson.jl:17-21 |
| `polyhorner(x, a)` | `a[1] + x*(a[2] + x*(... a[n]))` built with `Reduce.Algebra.+/*`: **REDUCE simplifies each step** (e.g. `[-1,0,2]` → `2 * x ^ 2 - 1`) **[run]** | 23-24 |
| `polyfactors(x, a)` | `(x-a1)*(x-a2)*...*(x-an)`, REDUCE-simplified (`[0.5,2.25]` → `((4x - 9) * (2x - 1)) / 8`) **[run]** | 26-27 |
| `polyexpand(x, a)` | `a_n x^(n-1) + ... + a_1`, REDUCE-simplified | 29-30 |
| `optimal(expr)` (internal) | picks the lowest `exprval` among `horner(expr)`, `factor(horner(expr))` and `expr` (ties favour h over f and h/f over expr) | 32-43 |
| `geonorm(x)` | `1/(1-x)` | 47 |
| `Ω(p)` | `n = length(p)-1` by default (**drops the last point**). If there is an `Inf`, `n = (first Inf index) - 1`. | 49-55 |
| `genabs(expr,T)`, `genalg(expr,T)` | compile `x ↦ |expr|` / `x ↦ expr` with the scalars converted to T | 57-58 |
| `stieltjes(set, expr, T, T2=T; logi=log, expi=exp)` | returns `(Float64.(log.(abs.(p)) .- sc .+ log(callcount(expr)*eps(T2))), bytes_allocated)` where `sc=collect(set)`, `p = |expr|_T.(exp.(sc))` | 60-67 |
| `simpson(set, p, n=Ω(p))` | `(4Σp[1:2:n-1] + 2Σp[2:2:n-1] + p[1] + p[n]) / (3n·(set[n]-set[1]))` | 69-74 |
| `exacterr(set, exprs, T, rx, ex; ...)` | for q ≥ 2, `log|f_big(x) - f_q,T(x)| - log x` | 76-88 |
| `renormalize!(p)` | zero out Infs from the end, return n | 90-96 |
| `errval(expr, T, N=3000)` | `(geonorm(simpson(set, stieltjes(...))), bytes)` | 98-103 |
| `abstract type NumericalData` | | 107 |
| `PolynomialAnalysis <: NumericalData` | fields `expr, set::AbstractRange, val::Tuple (=exprval), stj::Tuple (=stieltjes), smp::Number (=simpson)`. Ctor `(expr, T::Tuple=(Float64,), set=nothing, ω=nothing, stj=nothing; logi, expi)`. | WK/polynomial.jl:4-17 |
| `print(::PolynomialAnalysis)` | §5.6 | 19-28 |
| `PolynomialComparison <: NumericalData` | fields `expr, set, results::Vector{PolynomialAnalysis}, extra::Bool, rxtra::Bool, ω, exact, integral, log, exp, typ`. Ctor `(j, T=Float64, N=3000; logi, expi, round=false)`. | 30-69 |
| `print(::PolynomialComparison)` | §5.6 | 71-94 |
| `plot(::PolynomialComparison)` | PyPlot figure (§5.6) | 96-133 |
| `testpoly(expr, T)`, `tests(d, n, T; apply=polyfactors)` (internal) | random experiments (`rand(d)` roots) | 135-179 |
| `Reduce.stop()` at module load | stops the REDUCE process | WK/Wilkinson.jl:111 |
| ST `callcount(expr)` | number of `:call` nodes | ST/SyntaxTree.jl:199-206 |
| ST `sub(T, expr)` | convert every numeric literal to T (**skips the exponent of `^` when it is a literal**). `@int128_str`/`@big_str` macrocalls are evaluated. | :50-71 |
| ST `abs(expr)` | recursively turn every `-` call head into `+` and abs every literal (the `^` exponent literal is kept) | :78-102 |
| ST `alg(expr, f=:(1+ϵ))` | wrap every call as `f * call(...)` recursively | :109-120 |
| ST `genfun`, `@genfun`, `genlatest`, `@genlatest` | `eval` an anonymous function from an Expr | :131-192 |
| ST `linefilter!` | strip LineNumberNodes | :19-43 |
| ST `expravg(expr)` | `(cs, avgLog, cp, avgExp)` (§4.6.1) | ST/exprval.jl:9-38 |
| ST `exprdev(expr, val, cal)` | Σ (log\|s\|-val)²/(cal-1) over **all** literals | :46-56 |
| ST `exprval(expr)` | `(cal*sqrt(|avg|*sqrt(dev))*avgExp, cal, sqrt(dev), avg, avgExp)` | :66-71 |

---

## 3. Data representations

### 3.1 AbstractLattices
There is no data, only function identities. The important representational fact: **`∧ === wedge` and `∨ === vee` are the same generic functions**, so a method added to either name is visible under both. Arity-polymorphic: unary identity, binary Bool, and (via AbstractTensors) nullary.

### 3.2 PrimitiveBits
- `PrimitiveBits{b}` is a primitive bitstype of exactly b bits (`sizeof = b/8`, `isbitstype`). It is a zero-overhead reinterpretation of `UInt{b}`.
- Index i ∈ 1..b ↔ bit i-1 (LSB = index 1). Printing is LSB-first.
- The width b is compile-time (it is part of the type name).

### 3.3 DeMorgan
- `TruthValues{N}`: N is compile-time (a type param); `p::UInt` (64-bit) is runtime. Row k ∈ [0, 2^N) of the truth table is bit k of p. Bits ≥ 2^N are zero after `!` (masked), but `∧`/`∨` do not mask, so garbage bits from direct construction survive. Practical limit: **N ≤ 6** (64 rows). `⊥` = `TruthValues{0}(0)` is the N-polymorphic contradiction; `⊤` is a separate singleton type.
- Projection columns (§4.3.1): the variable declared at position j (1-based) of N is true on row k iff **bit (N-j) of k is 0**. So row 0 is all-true and row 2^N-1 is all-false; the first-declared variable is the slowest-varying.
- `TruthTable{N,M}`: N compile-time, M = number of distinct classes (a compile-time type param in Julia, **runtime in the port**). `p[c]` is the UInt column of class c and `n[c]` the tuple of alias strings, in insertion order. `(i,j)` points at the class/alias of "this" expression. Invariants: the classes are *meant* to be distinct but are **not always** (quirk §4.3.3). Projection classes are kept in a prefix (inserted before the first non-projection class), while other classes are appended.

### 3.4 Dendriform
- **Loday name** ω(τ) of a planar binary tree with n internal vertices: `ω(τ) = [ω(τ_l); n; ω(τ_r)]`, where each internal vertex is labeled by the degree of the subtree rooted there. The name is a permutation-like word of length n with values in 1..n, and the root label n appears exactly once. The degree-0 tree `|` has the empty name. Stored as `Vector{UInt8}` (labels ≤ 255).
- **Grove**: a `size × degr` UInt8 matrix, one tree per row. **Rows may repeat and order is significant** for everything except `==` (which sorts) and `∪` (which canonicalizes). Degenerate encodings:
  - `Grove(0)` = `Υ(0)`: a 0×1 matrix, `size=0`, `degr=0`. It serves both as the "zero grove" and as the unit in `+`/`⊣`/`⊢` (see §4.4.4). Prints `Y0 #0/1`.
  - `Grove(PBTree([]))`: 1×0 matrix, `size=1`, `degr=0`. Prints `∅Y0 #1/1` **[run]**.
  - `Grove(d, 0)`: 0×d matrix, size 0. Prints `Y3 #0/5`.
- **Total grove** `Υ(d)` (Y_d): all Cn(d) trees of degree d, in **canonical order = ascending TreeInteger** (when `grovesort()` is true, the default). This order defines the **tree index** (1-based rank). Cached globally, extended lazily degree by degree (it prints progress to stdout; §5.1).
- **Grove index** (`groveindex`, `gbin`): a BigInt whose bit (i-1) means "tree index i is present". **It sums with multiplicity**, so duplicates corrupt it. It is the canonical key for groves; grove `<`/`≤` compares these integers.
- `GroveBin`: `(degr, size, gbin, ppos::Float16)`.
- `BaseTree` μ: for a name υ of degree d, `μ[ω] = sorted positions p with υ[p] == d+1-ω`, ω = 1..d (so μ[1] holds the root position).
- Global mutable state (closures): `Υ/ΥI/ΥGS` (total groves + tree-integer tables), `GroveStore/GroveComp/GroveSums` (composition caches), toggles `grovesort` (true), `grovedisplay` (false), `treeshift` (true), and `ΘMax` memo.

### 3.5 AbstractAnalysis
- `CountableArray{T,N,F}`: T element type (inferred by calling f at `(1,...)`), N rank (compile-time), F the generator type (compile-time: Julia specializes on the closure). The size is a mutable `Variables{N,Int}` (runtime and **mutable in place**). The default length is 100. 1-based indices; `getindex` calls f without bounds checks.
- `FunctionArray{T,N,F}`: T is the element *function type* (e.g. `typeof(Fix2(f,1))`). `f(x, i...)`.
- `SequenceArray{T,N,V,F}`: V is the storage type (Vector or ElasticArray, with the last dim growable) and F the recurrence `F(storage, k)`. It is memoized. Out-of-range reads extend the storage (a mutation).
- `Series{N,C,F}`, `Product{N,F}`: coefficient array plus FunctionArray.
- `Limit{T,F,D}`: T is the **state** type, which takes one of three shapes:
  1. a raw value (orbit, `Limit(v0,n,F)`, FixedCycle);
  2. `k => value` (`Pair{Int,V}`: sums, products, `limit(countable)`);
  3. `(k => inner) => value` (`Pair{Pair{Int,S},V}`: arithmetic/map on limits).
  
  F is the step function `state → state`, and D is the metric (a compile-time type param holding the function). `first`/`last` project to the value for the Pair shapes. `n` counts **states** (the initial one counts as 1), so n = iterations + 1 in the plain constructor.
- `Semimagma{T,F,G}`: `v::Vector{T}` in insertion order (significant). F is the law and G the inverse (compile-time function values). Membership uses `≈`.
- Permutations: `Permutation{N,T}` holds **1-based images** `v[i] = σ(i)` (N = length). `Cycle{N,T}` is a cycle list `(a1 a2 ... ak)`, meaning a1→a2→...→ak→a1 (evalperm, perm.jl:63-66). `CycleProduct{N,T<:Tuple}`.

### 3.6 Wilkinson / SyntaxTree
- Expressions are Julia `Expr` ASTs: `:call` nodes whose `args[1]` is the operator symbol (`:+ :- :* :/ :^ ://`), plus Symbol leaves (`:x`) and Number leaves (Int, Float64, Rational literals, BigInt macro literals). Juxtaposition `3x` parses as `Expr(:call, :*, 3, :x)`. n-ary `*`/`+` nodes exist (`(x-1)*(x-2)*(x-3)` is one 3-arg `*`).
- Grids are `StepRangeLen{Float64,TwicePrecision}` (§4.6.3).
- `PolynomialAnalysis.stj = (Vector{Float64} of log-bounds, bytes::Int)`.

---

## 4. Algorithms

### 4.1 AbstractLattices
Trivial. `wedge(x)=x`, `vee(x)=x`, `wedge(p,q)=p&&q`, `vee(p,q)=p||q`.

### 4.2 PrimitiveBits
`get(b,i) = ((1 << (i-1)) & bits) == (1 << (i-1))`, with Julia shift semantics: a shift count ≥ width yields 0, and a negative count shifts the other way. So **any out-of-range i returns true**.
`fromBools(v) = Σ_{k} v[k]·2^(k-1)` via string parse. The string parse errors when `length(v) > b`, when the value overflows, or when `v` is empty.

### 4.3 DeMorgan

#### 4.3.1 Projections
```
select(n, N) = Σ_{i=1}^{2^(N-1)} 1 << ( ((i-1) % j) + 2j*((i-1) ÷ j) ),  j = 2^(n-1)      (DM:80-83)
           = the set of rows k in [0,2^N) with bit (n-1) of k == 0
select(N)  = (select(1,N), ..., select(N,N))                                            (DM:84)
@truthtable x1 ... xN:  x_m = TruthTable{N}(select(N+1-m, N), "x_m")                    (DM:87-91)
```
Examples **[run]**: `select(1,2)=0b0101=5`, `select(2,2)=0b0011=3`, `select(3)=(0x55,0x33,0x0f)`, `select(1,6)=0x5555555555555555`, `select(6,6)=0x00000000FFFFFFFF`. With `@truthtable p q`: p=0b0011, q=0b0101. With `a b c`: a=0x0f, b=0x33, c=0x55.

Mask: `tautology(N) = (1 << 2^N) - 1`, with **Julia semantics: `UInt(1) << 64 == 0`**, so N=6 gives all ones. (Lean's `UInt64 <<<` is taken mod 64, so this must be special-cased.)

#### 4.3.2 Operators on TruthValues
```
¬p   = p ⊻ mask(N)             p∧q = p & q      p∨q = p | q
p→q  = ¬p ∨ q                  p←q = p ∨ ¬q     p↔q = (p→q) ∧ (q→p)
```
With the 0/⊤ lifting (DM:148-153): `TV{0}` is re-tagged as `TV{N}` with the same bits, and `⊤` becomes `mask(N)`.

#### 4.3.3 TruthTable algebra (`combine`, DM:103-146)
Binary op (DM:154-157):
```
op(P::TT{N}, Q::TT{N}):
  r    = op(TV{N}(P.p[P.i]), TV{N}(Q.p[Q.i]))
  name = parstring(string(P)) * sym * parstring(string(Q))     # string(T) = T.n[T.i][T.j]
  return combine(P, Q, r, (name,))
Unary ¬ (DM:95-98):
  np = ¬TV{N}(P.p[P.i]);  name = "¬(" * P.n[P.i][end] * ")"    # LAST alias, never parstring'd
  return combine(P, EMPTY_TT{N}, np, (name,))
```
Merge (a faithful transcription):
```
combine(P, Q, r, n):                      # Q has Qm classes; (r, n) is treated as class Qm+1
  rp ← copy P.p ; rn ← copy P.n ; out ← (0,0) ; sN ← select(N)
  for i in 1..Qm+1:
    (qp, qn) ← i>Qm ? (r.p, n) : (Q.p[i], Q.n[i])
    if qp ∈ P.p:                          # !!! membership in the ORIGINAL P.p, not rp
      k ← first index of qp in P.p
      for each name s in qn (in order):
        if s ∈ P.n[k]:                    # ORIGINAL aliases of P
          if i>Qm: out ← (k, index of s in P.n[k])
        else:
          rn[k] ← rn[k] ++ (s,)
          if i>Qm: out ← (k, length(rn[k]))
    else:
      qnn ← qp==0 ? ("⊥", qn...) : qp==mask(N) ? ("⊤", qn...) : qn
      if qp ∈ sN:                         # it is a projection column
        l ← first index in rp whose column ∉ sN, or length(rp)+1 if none
        insert (qp, qnn) at l ;  if i>Qm: out ← (l, 1)
      else:
        append (qp, qnn) ;       if i>Qm: out ← (length(rp), 1)
  return TT{N, length(rp)}(rp, rn, out...)
```
Consequences **[run]**:
- Both the dedup test and the alias test are against **P's original** classes. If Q contributes a class that P lacks and r equals it, the class is **duplicated**: `p ∧ (p ∧ q)` gives classes `0011 p | 0101 q | 0001 p∧q | 0001 p∧(p∧q)`, with i=4. In contrast `(p∧q)∧p` gives `... | 0001 ("p∧q","(p∧q)∧p")` with i=3, j=2.
- ⊥/⊤ names are prepended as the first alias, so string(result) becomes "⊥" / "⊤" and later parstring leaves it bare.
- Projection columns are inserted before the first non-projection column, but among themselves they keep arrival order (`c ∧ a` has columns `c, a, c∧a`).

#### 4.3.4 parstring (DM:71-78)
Return s unchanged iff `length(s) == 1` (in Unicode chars) **or** s matches `^¬\((?:[^()]+|(?R))*\)$`. Because `(?R)` re-enters the whole anchored pattern, inner recursion can never match. In effect the rule is: **s = "¬(" + a paren-free non-empty string + ")"**. Otherwise return `"(" * s * ")"`. Golden cases **[run]**:
`p→p`, `¬(p)→¬(p)`, `¬(p→q)→¬(p→q)`, `¬(p)∧¬(q)→(¬(p)∧¬(q))`, `¬((p→q)∧r)→(¬((p→q)∧r))`, `¬(¬(p))→(¬(¬(p)))`, `⊤→⊤`, `pq→(pq)`, `¬p→(¬p)`.

Edge case: `"¬()"` has an empty inner part. `[^()]+` needs ≥1 char but `(...)*` allows zero, so `"¬()"` matches (it cannot occur in practice).

### 4.4 Dendriform

#### 4.4.1 Tree primitives
```
graft(L,R) = L ∨ R = [L.Y; L.d+R.d+1; R.Y]                      (arithmetic.jl:38-47)
root position fx = first index with Y[fx] == d  (unique)
left(t)  = fx>1 ? Y[1:fx-1] : |            right(t) = fx<d ? Y[fx+1:end] : |      (:66-85)
σ(t)     = reverse(Y)                       (mirror)
over(x,y)  = y==| ? x : over(x, left y) ∨ right y
under(x,y) = x==| ? y : left x ∨ under(right x, y)
```

#### 4.4.2 Canonical order: ΘInt / ΘMax / TreeInteger / TreeRational
```
μ(υ)[ω] = ascending positions p with υ[p] == d+1-ω,  ω = 1..d        (morphism.jl:209-216)
seq     = concat(μ[1], μ[2], ..., μ[d])            # a permutation of 1..d
ΘInt(υ) = Σ_{t=1}^{d} seq[t] · 10^(d-t)             # "decimal concatenation" of seq (carries if a position ≥ 10)
ΘMax(d) = Σ_{k=1}^{d} k · 10^(k-1)                   # digits d,d-1,...,1: 1, 21, 321, 4321, ...
TreeInteger(υ) = ΘMax(d) - ΘInt(υ)                   # ∈ [0, ΘMax(d)-ΘInt(identity...)]
TreeRational(υ) = treeshift ? TI/ΘMax : 1 - TI/ΘMax  # Rational
TreeRational(d, Θ::Vector) = 1 - s - (-1)^s * Θ/ΘMax(d),  s = Int(treeshift())
```
- **ΘMax memo bug** (morphism.jl:235-250): when extending the memo from length L to d, every new entry uses `δ = d-1` rather than `n-1`. It is correct only when extended one degree at a time, which is the case in practice because GroveExtend! builds degree by degree. **The port must use the closed form.**
- Integer width: Julia uses `Int` (Int64). `ΘMax(18) ≈ 1.975e18` fits; degree ≥ 19 overflows. Irrelevant in practice (Cn(19) ≈ 1.8e9 trees).
- TreeInteger is injective for d ≤ 12 **[run]** (checked exhaustively). Order **[run]**: d=3 gives `[1,2,3]:0, [2,1,3]:9, [1,3,1]:108, [3,1,2]:189, [3,2,1]:198`.
- **Total grove = all trees of degree d sorted by ascending TreeInteger.** An independent generator (all names by recursion) sorted by TI reproduces `ΥI(d)` exactly for d ≤ 10 **[run]**.

#### 4.4.3 Julia's build order (only needed if `grovesort(false)` is to be supported)
`GroveExtend!` (Dendriform.jl:234-288), for new degree n with c=⌈n/2⌉, f=⌊n/2⌋ and `Y_k` = total grove of degree k. The blocks are appended in order:
1. `τ ∨ |` for τ ∈ Y_{n-1} (root last);
2. for left-degree ℓ = n-2 down to c: `λ ∨ Λ` for λ∈Y_ℓ (outer), Λ∈Y_{n-1-ℓ} (inner);
3. if n is odd (ℓ = f = n-1-ℓ): a 7-block interleaving of halves (lines 256-270; `fλ,cλ` = floor/ceil of |Y_f|/2, and the same for Λ): (1..fλ × 1..fΛ), (1..fλ × cΛ if odd), (1..fλ × cΛ+1..end), (cλ if odd × all), (cλ+1..end × 1..fΛ), (cλ+1..end × cΛ if odd), (cλ+1..end × cΛ+1..end);
4. for ℓ = f-1 down to 1: `λ ∨ Λ` with Λ∈Y_{n-1-ℓ} **outer** and λ∈Y_ℓ inner;
5. `| ∨ τ` for τ ∈ Y_{n-1} (root first).

With sorting on (the default), this order is irrelevant. **Recommendation: drop unsorted mode.**

#### 4.4.4 Dendriform half-sums and sum (arithmetic.jl:94-243)
With `|` = degree-0 tree and `0` = `Grove(0)`:
```
PBTree ⊣ PBTree:                                    PBTree ⊢ PBTree:
  x==|  → 0                                           y==|  → 0
  y==|  → Grove(x)                                    x==|  → Grove(y)
  S = right(x) + y       (a Grove)                    S = x + left(y)
  rows = [ left(x) ∨ s  for s in S.rows ]             rows = [ s ∨ right(y) for s in S.rows ]
Grove ⊣ PBTree  = vcat over x-rows i: (x_i ⊣ y)         (x.degr==0 → 0; y.degr==0 → x)
PBTree ⊣ Grove  = vcat over y-rows j: (x ⊣ y_j)
Grove ⊣ Grove   = vcat over x-rows i: (x_i ⊣ y)   [= for i, for j]
(⊢ analogously; the degr==0 checks are ordered y first, then x)
Grove + Grove:
  if x has no entries (isempty(x.Y), i.e. 0 rows OR 0 columns) → return y
  if y empty → return x
  blocks[i,j] = vcat((x_i ⊣ y_j).rows, (x_i ⊢ y_j).rows)
  result = vcat(blocks...) in COLUMN-MAJOR order: for j in y-rows: for i in x-rows: blocks[i,j]
```
- **The +-order is j-major (y outer, x inner)**, while ⊣/⊢ on groves are x-major.
- PBTree + PBTree → `Grove(x) + Grove(y)`, so `| + y = y` and `x + | = x`.
- The zero grove `0` is also treated as the unit by `+` (`isempty`) and by the degr==0 branches of ⊣/⊢. For example `| * y` returns 0, and `0 ⊢ y` returns y. This is exactly what Loday's formula needs, with 0 standing in for `|`.
- Results are **multisets**: no dedup. Degree of the result = sum of degrees.
- Loday identities that hold (as multisets) include `σ(x+y) = σ(y)+σ(x)` and `σ(x*y) = σ(x)*σ(y)` **[run]**, and `Y_p + Y_q = Y_{p+q}`, `Y_p * Y_q = Y_{pq}` (e.g. `GroveBin(3)+GroveBin(2) == GroveBin(5)`, `Grove(2)*Grove(3) == Grove(6)` **[run]**).

#### 4.4.5 Multiplication (arithmetic.jl:252-274)
```
PBTree * Grove:  x==| → 0;  x.degr==1 → y;  else ((left(x) * y) ⊢ y) ⊣ (right(x) * y)
Grove * Grove:   x.degr==0 → 0;  x.degr==1 → y;  else vcat over x-rows j of (x_j * y)
```
Degree(x*y) = deg x · deg y. The tree `[1]` is the multiplicative unit (it returns `y` itself, the same object).

#### 4.4.6 Union ∪ (arithmetic.jl:14-29)
`bits = OR of grovebit(each)` (all must have the same Catalan length, else a broadcasting DimensionMismatch). Then `Grove(bits)` = rows of Υ(d) at the set bits, ascending. `dups = Σ sizes - result.size`; if nonzero, log `@info "$dups duplicate$(dups>1 ? "s" : "") in grove union"` (to stderr: `[ Info: 1 duplicate in grove union`).

#### 4.4.7 Tamari poset (poset.jl)
```
posetnext_list(t):            # upper covers, in this order
  λ=left t, ρ=right t
  x = left(λ) ∨ (right(λ) ∨ ρ)          # right rotation at the root
  if x.degr == t.degr: push x            # i.e. λ ≠ |
  if λ≠|: push [g ∨ ρ for g in posetnext_list(λ)]
  if ρ≠|: push [λ ∨ g for g in posetnext_list(ρ)]
posetprev_list(t): same with x = (λ ∨ left ρ) ∨ right ρ (left rotation)
a < b : h = posetnext_list(a); b ∈ h → true; else any(h[i] < b) scanning in order (DFS, short-circuit)
a > b : the same with posetprev_list
between_list(a,b):
  a==b → [b]
  g=[a]; for h in posetnext_list(a): if h ≤ b: for t in between_list(h,b): if t∉g push t
  return length(g)>1 ? g : []
```
The minimum of Y_n is `[1,2,...,n]` (the left comb) and the maximum is `[n,...,1]`. `between([1,2,3,4],[4,3,2,1]) == Grove(4)`. The complexity is exponential; memoize in the port.

#### 4.4.8 Indices
```
treeindex(tree) = rank of TI(tree) in ΥI(d) (1-based), 0/error if absent
grovebit(g)     = bit i-1 set iff some row has index i
groveindex(g)   = Σ_rows 2^(index-1)     (BigInt, with multiplicity)
Grove(d, s)     = rows of Υ(d) at set bits of s (ascending)
GroveBin.ppos   = Float16( BigFloat(100·gbin) / BigFloat(2^Cn(d) - 1) )   # Julia: Float16(::Rational{BigInt}) divides in BigFloat, then rounds
```

#### 4.4.9 Compositions (Dendriform.jl:322-388)
Intended semantics: `Compose(n)` lists every ordered tuple (γ₁,…,γ_k), k ≥ 2, of non-empty groves with degrees summing to n. Each entry is stored as `[GroveBin(γ₁),…,GroveBin(γ_k), GroveBin(γ₁ + (γ₂ + (… + γ_k)))]` (right-nested sum; each partial sum is round-tripped through GroveBin, which canonicalizes). Recursive calls with η > n also include the singletons k=1. Enumeration order:
```
Compose(n, η=n):
  G = []
  if n < η: G += [[gb(Grove(n,i)), gb(Grove(n,i))] for i in 1..2^Cn(n)-1]
  for s in n-1 down to 1:
    for i in 1..2^Cn(s)-1:                     # all non-empty groves of degree s by index
      for each entry e of Compose(n-s, η):
        push [gb(Grove(s,i)), e[1:end-1]..., gb(Grove(s,i) + Grove(e[end]))]
  dict: sum.gbin → [entry indices...]
```
`grovecomposition(d, ind)` prints `GroveBin(Grove(d,ind))`, then either `" has 1 composition (itself)\n"` (returns 1) or `" has $(k+1) compositions\n"` followed by each composition as `(part1) + (part2) + ...\n`, and returns k+1.

**Cache bug** **[run]**: `GroveStore` caches `Compose(n)` for the first n in increasing order, whether it was called as top level (no singletons) or recursively (with singletons). The top-level `Compose(1)` caches `[]`, and since an empty cache is recomputed, n=1 is harmless. But calling `grovecomposition(2,·)` before `grovecomposition(3,31)` makes the latter return **3** instead of **4**. **The port implements the fresh-process semantics.** The oracle must run each query in a fresh process (or at least with degrees queried in decreasing order).

#### 4.4.10 Interval tools (poset.jl:211-296)
- `intervals(d)`: the sorted BigInt grove indices of all non-empty `PBTree(d,i) ⊴ PBTree(d,j)` over (i,j) ∈ [1,Cn]², **with duplicates kept**.
- `intcomp(d)`: for q=1..d-1 and i ∈ 1..2^Cn(q)-1, j ∈ 1..2^Cn(d-q)-1, compute `gbin(Grove(q,i)+Grove(d-q,j))` and count hits per interval (misses go to `@info "Non-intervals: $cn"`).
- `intcompt`: the same over single trees.
- `intervals_full(d)`: a BitVector that flags whether each interval is "full", sorted by gbin.
- The `print_*_bin` helpers print `lpad(string(i,base=2), Cn(d), "0")` lines.

Goldens are in §6.

### 4.5 AbstractAnalysis

#### 4.5.1 Countable sets
Formulas as in §2.5. Worked values are in §6. `sternbrocot(n)` recursion: the port should use the SequenceArray memo, or a closed-form loop over the binary digits of n (`fusc`).

#### 4.5.2 SequenceArray extension
```
get(c, n): if n > len: for k in len+1..n: v[k] = F(v, k)   (Vector push)
           return v[n]
```
Multi-dim: the storage grows along the last dim (ElasticArray), and `F(v,k)` returns the slice for k.

#### 4.5.3 Metrics
`supnorm(a,b) = supnorm(a-b)` for numbers/arrays. Arrays use the Euclidean `norm`, and **Int inputs return Float64**. Pairs recurse on `last`. Everything else gives `Inf`. `infnorm` is the same except its fallback is `0.0`.

#### 4.5.4 Limit semantics (metric.jl)
```
Limit(v0, n, F, D):  x0=xn=v0; repeat n times {x0=xn; xn=F(xn)}; return Limit(v0, xn, n+1, D(xn,x0), F, D)
L[i]:  i==n → L;  start = i<n ? v0 : v;  steps = i<n ? i-1 : i-n
       iterate; return Limit(v0, xn, i, D(xn, x_prev), F, D)      # D(x,x)=0 if no steps
limit(L, ϵ, Val(p)):  x=final(L); change=5ϵ; n=1
       while change > ϵ: n+=1; x0=xn; xn=F(xn); change = (Pair-state ? D(last xn, last x0) : D(xn, x0))
       return Limit(x, xn, n + length(L), change, F, D)          # NOTE: v0 := old final; length = old + iterations + 1
sum(x::CountableVector)  = Limit(1=>x[1], len=>Σ_{1..len} x, len, x[len], u ↦ (k+1)=>(s + x(k+1)))
prod(x::CountableVector) = Limit(1=>x[1], len=>Π, len, supnorm(Π, Π/x[len]), u ↦ (k+1)=>(p * x(k+1)))
limit(x::CountableFunction, n=len, d) = Limit(1=>x[1], n=>x[n], n, d(x[n],x[n-1]), u ↦ (k+1)=>x(k+1), d)
limit(x::CountableVector, ϵ) = limit(limit(x,2), ϵ)
Arithmetic with a scalar a (op ∈ + - * / ^), e.g. a ⊙ L:
  v0 = (1 => initial L) => a⊙first(L)
  vn = (len => final L) => a⊙last(L)
  vn1 = step(vn): p = F_L(last(first(vn))); ((len+1) => p) => a⊙last(p)
  return Limit(v0, vn1, len+1, D(last vn1, last vn), step, D)    # advanced ONE step
L1 ⊙ L2 (same D):  v0 = (1 => (final a, final b)) => last a ⊙ last b; vn = step both once
                    return Limit(v0, vn, 2, D(last vn, last v0), ...)   # n resets to 2
map(f, L) (Pair state): Limit(initial=>f(first), final=>f(last), len, Inf, u ↦ (F(first u)) => f(last F(first u)), D)
collect(L) (Pair state): values x_1..x_len re-derived by iterating from initial
orbit(f,x,ϵ=5eps()): n=1; change=5ϵ; while change>ϵ {n+=1; x0=xn; xn=f(xn); change=d(xn,x0)}
                     return Limit(x, xn, n, change, f, d)
orbit(f,x,k::Int) = orbit(f,x,1:k): k steps → Limit(x, xn, k+1, d(xn,x0), f, d)
FixedCycle(n,f,d)(u) = Limit(u, n, f, d)
```
Floating-point fidelity: `sum(view(x,:))` uses Julia's `mapreduce` (pairwise with blocks of 1024, and `@simd` inside a block, which **may reassociate**). Compare with rtol ≈ 1e-14 rather than bitwise.

#### 4.5.5 Convergence predicates
```
isdiverging(x,d): r0=ri=d(x[end],x[end-1]); for i=len-1 down to 2: r0=ri; ri=d(x[i],x[i-1]); if r0<ri return false; true
iscauchy(x,d): ϵ0=d(x[end-1],x[end]); for n=N-2 down to 1: ϵmax=max_{i>n} d(x[n],x[i]); if ϵ0>ϵmax return false; ϵ0=ϵmax; true
supseq(x)[i] = max(x[i:end]);  supseq(x,m)[k] = max(x[k:k+m])  (reads past the end for a CountableVector)
```

#### 4.5.6 Magma closure algorithms (ordering matters for goldens)
```
magma(p, F):       out=[p]; q=F(p,p); while q∉out {push q; q=F(q,p)}          # powers p, p², ...
magma(G, out):     i=1; while i≤|out| { j=1; while j≤|out| { h=F(out[i],out[j]); if h∉out push h; j+=1 }; i+=1 }
group(G, out):     for i in 1..|out|₀: if inv(out[i])∉out push   # |out|₀ = the size at loop start
                   then magma(G, out)
compose(G,H,F):    for g in G, h in H: push F(g,h) if new
commutator(G,H):   S=[unique F(F(inv g, inv h), F(g,h)) for g in G, h in H]; return group(G, S)
center (buggy):    out=copy(v); i=1
                   while i≤|out| { g=out[i]; j=1
                     while j≤|out| { h=out[j]; if commute(g,h) j+=1 else { delete out[j]; if j<i: i-=1 } }
                     i+=1 }
                   # deletes the elements that do NOT commute with each surviving g in turn: a greedy commuting subset
subsemigroup(G,out): i=1; while i≤|out| { keep out[i] iff ∃j: F(out[i],out[j]) ∈ out; else delete }
subgroup(G,out):   delete out[i] if inv(out[i])∉out (or it throws); then subsemigroup
left/rightcosets:  for g in G: gH = [F(g,h) for h in H] (ordered); push if no existing coset ≈ gH (ORDERED compare)
```
- `gequal = ≈` (isapprox) with `atol=0`, `rtol = √eps` for float types and 0 for integers/rationals. Complex values use `abs`. Vectors use `norm(x-y) ≤ rtol·max(norm x, norm y)`.
- `isnormal`/`normalizer` use `==` on Semimagmas (mutual ⊆, **unordered**), so they are correct. Cosets use `∈` (**ordered** `≈`), which is the quirk.

#### 4.5.7 Permutations
```
compose: (a*b)[i] = a[b[i]]                           inv = sortperm
evalperm(c, i) = i ∉ c ? i : (i == c[end] ? c[1] : c[next])
CycleProduct(p): for i in 1..N not yet in a cycle: c=[i, p(i), p²(i), … until repeat]; keep if |c|≠1
order(Cycle)=|c|-1;  order(p)=Σ(|c|-1) = N - #cycles(including fixed points);  sign=(-1)^order
SymmetricGroup(N) = lexicographic permutations of 1..N
```

### 4.6 Wilkinson / SyntaxTree

#### 4.6.1 exprval family (ST/exprval.jl)
```
expravg(e) -> (cs, avg, cp, pavg):
  Number literal v:  cs=1, s=log|v|
  call ^ with a Number exponent k:  cp+=1, p+=|k|, then recurse ONLY into the base (k is not counted as a scalar)
  any other Expr: recurse into ALL args (the operator symbol args[1] is a Symbol and contributes nothing)
  combine: cs+=cst; s+=cst*st; cp+=cpt; p+=cpt*pt
  avg  = (s==0 || cs==0) ? 1.0 : s/cs
  pavg = cp==0 ? 1.0 : p/cp
exprdev(e, val, cal) = Σ over ALL numeric literals in e (INCLUDING ^ exponents) of (log|v| - val)^2 / (cal-1)
exprval(e) = (cal * sqrt(|avg| * sqrt(dev)) * pavg,  cal,  sqrt(dev),  avg,  pavg)     with cal = callcount(e)
```
Edge cases: `cal==1` divides by zero, giving Inf or NaN. A literal 0 gives `log 0 = -Inf`. Literal `1` gives `log 1 = 0`, and if every literal is 1 then `s==0`, so avg=1.0.

#### 4.6.2 stieltjes / simpson / Ω (WK/Wilkinson.jl)
```
sc   = collect(floatset(T,3000; scale=log))    # log grid from log(eps T) to log(floatmax T)
xs   = exp.(sc)
p    = |e|_T (xs)                              # abs-transformed expr, literals converted to T, evaluated in T
stj  = log.(abs.(p)) .- sc .+ log(callcount(e) * eps(T2))      # Float64
Ω(p) = (first k with p[k]==Inf) - 1, or length(p)-1 if there is none
simpson(set,p,n) = (4Σ_{i odd, i≤n-1} p[i] + 2Σ_{i even, i≤n-1} p[i] + p[1] + p[n]) / (3n (set[n]-set[1]))
```
(p[1] effectively gets weight 5, because index 1 is odd. This is not textbook Simpson. Port it literally.)

`PolynomialAnalysis(expr, (BigFloat,Float64), set, ω)` evaluates in BigFloat (no overflow, so Ω would be length-1) with eps(Float64). ω is supplied by the Float64 runs.

`PolynomialComparison(j)` builds the forms `[optimal(j), expand(j), horner(j), factor(j), factor(j,rounded)]`. Rounded is dropped if it equals factor; `j` is appended if it differs from all three. Then `ω = min Ω over expand/horner/factor`; `results[1]` is the BigFloat analysis of optimal; `exact = exacterr(...)`; `integral = simpson` of each.

#### 4.6.3 Julia float range semantics for `floatset` (twiceprecision.jl:394-434)
`l:st:u` with `st = (u-l)/(N-1)`. For generic (non-rational) floats Julia falls back to `len = round((u-l)/st)+1`, minus 1 if it overshoots (`l < u < l+(len-1)st`). The elements are `x_i = fl(l + fl((i-1)·st))`: the TwicePrecision lo parts are 0 and add12 is exact. The Float64 values **[run]**: `first = -36.04365338911715`, `last = 709.782712893384`, `step = 0.24869168598949687`, `len = 3000`, `x2 = -35.794961703127655`, `x3 = -35.54627001713816`, `x_end = 709.782712893384`. The port should implement this literally and cross-check the whole vector against a JSON golden (allowing ≤1 ulp).

---

## 5. Display / printing formats

### 5.1 Dendriform
- `print(PBTree)` (Dendriform.jl:404-425):
  - For a **non-empty** tree: `show(Int.(Y))`, i.e. `[1, 2, 3]` (Julia ≥ 0.7 array formatting with `", "`; the README's `[1,2,3]` is Julia 0.6 formatting). With `grovedisplay()` on, it appends `" ↦ "`, then for each ω in 1..d either `∅` (empty μ[ω]) or `show(Int.(μ[ω]))`, all concatenated with no separator, then `" ↦ "`, `"$tin/$(Cn(n)) or $TI"`. It **always ends with `'\n'`**.
  - For the **empty** tree it prints `∅` (plus `" ↦ [∅] ↦ 0/1 or 0"` with display on) and **no newline**.
- `print(Grove)` (:428-437): each row printed as a PBTree (each with its trailing `\n`), then, **without a trailing newline**, either `"Y$(degr) #$(size)/$(Cn(degr))"` or, with display on, `print(GroveBin(g))`.
- `print(GroveBin)` (:451-453): `"$(gbin) Y$(degr) #$(size)/$(Cn(degr)) [$(ppos)%]"`. UInt8 `degr` prints as a decimal (`5`).
- `show(io, MIME"text/plain", x)` = `print` for all three (:178-180). `string(PBTree([1,2])) == "[1, 2]\n"` **[run]**.
- `print(Vector{BaseTree})`, `print(Vector{Grove})`: concatenation with no separators (`print([Grove(1),Grove(2)])` gives `"[1]\nY1 #1/1[1, 2]\n[2, 1]\nY2 #2/2"` **[run]**).
- `ppos` formatting is Julia's `Float16` shortest round-trip (Ryu `writeshortest`, `ryu/shortest.jl:334`). Let pt = decimal-exponent-of-leading-digit + 1. Use **plain** notation if `-4 < pt ≤ 3` and the integer-tail check passes, otherwise `d.ddde±X`. So `22.58`, `100.0`, `0.006092`, `3.227`, `54.75`, `0.0006`, but `6.104e-5`, `1.0e3`, and `0.0` on Float16 underflow (every GroveBin of degree ≥ 6 with a small index shows `[0.0%]`) **[run]**.
- **Side-effect logging to stdout** whenever the total-grove cache grows (Dendriform.jl:236-286): `"Extend Grove Degree Level,\n"`, then `" $n"` per degree plus `"|Θ"` when sorting, then `"\n"`. For example `Extend Grove Degree Level,\n 4|Θ 5|Θ\n`. It is also printed by `GroveInteger!` ("Extend Grove Integer Level,"). **The port omits this** (or prints it behind a debug flag). The oracle should warm the cache (`redirect_stdout(devnull) do Υ(8) end`) before capturing output.
- `@info` messages go to stderr: `[ Info: 1 duplicate in grove union`, `[ Info: Non-intervals: 0`.

### 5.2 PrimitiveBits
`[` + bits LSB→MSB as 0/1 + `]`. Example: `PrimitiveBits16(7)` → `[1110000000000000]`. `show == print`, `repr` is the same.

### 5.3 DeMorgan
- `⊥` prints `⊥` and `⊤` prints `⊤` (DM:41, 46). `TruthValues{N>0}` has no custom show and prints as the default struct: `TruthValues{2}(0x0000000000000003)` **[run]**.
- `TruthTable` without PrettyTables uses the default struct show: `TruthTable{3, 3}(UInt64[0x000000000000000f, 0x0000000000000033, 0x0000000000000003], Tuple{Vararg{String}}[("a",), ("b",), ("a∧b",)], 3, 1)` **[run]**.
- With PrettyTables (v2 API `pretty_table(data; header=...)`; **v3 renamed `header`, so this probably breaks under v3**):
  - data = a `2^N × M` Int matrix, column c = `digits(p[c], base=2, pad=2^N)` (row k = bit k).
  - The header has H rows, H = the maximum alias count. Header row h holds alias h of each class, or `""`.
  - Unicode box format: `┌─┬─┐ │ ├─┼─┤ └─┴─┘`. Each cell is ` content ` with the content **right-aligned** to the column width = max textwidth over the header cells and "0"/"1". There is no separator between header rows. The exact goldens are in §6.3.
- `string(tt)` = the current alias.

### 5.4 AbstractAnalysis
- `show(io, L::Limit)` (metric.jl:114-122): if `last(L)` is a Number, or with `:compact=>true`, it prints `println(io, "$(last(L)) (n → $(length(L)), Δ → $(residual(L)))")` (**with a trailing newline**). Otherwise it prints `println(io, "Limit as n → $(n), Δ → $(r)")` followed by `show(io, last(L))` (no trailing newline). The numbers use Julia's `string(Float64)` shortest repr: `0.01`, `9.999800987259277e-11`, `3.26592e6`, `Inf`.
- Semimagma, CountableArray, Permutation and Cycle use the default AbstractVector display: `"4-element Semimagma{Complex{Int64}, *, inv}:\n  0 + 1im\n -1 + 0im\n  0 - 1im\n  1 + 0im"`. `repr(Permutation(2,3,1)) = "[2, 3, 1]"`. `repr(decompose(Permutation(2,1,4,3))) = "[[1, 2], [3, 4]]"`. The port should provide simple `[a, b, c]` renderings and not try to mimic Julia's type headers.

### 5.5 AbstractLattices
None.

### 5.6 Wilkinson
- `print(::PolynomialAnalysis)` (polynomial.jl:19-26): `display(RExpr(expr))` (REDUCE 2-D pretty print, **port: plain infix**), then
  ```
  characteristic values (c,σ,s,p): (cal, dev, avg, pavg)
  expression value ν: <val[1]>
  predicted error bound ϕ: <smp>
  bytes allocated: <stj[2]/length(set)>
  ```
- `print(::PolynomialComparison)` (:71-92): labels `n = ["e","h","f"]`, plus `"r"` if rxtra and `"o"` if extra. Sections: `characteristic values (c,σ,s,p):` then `"$k = $(val[2:5])"` per form; `expression value ν:` then `"$k = $(val[1])"`; `predicted error bound Φ:` then `"$k = $(smp_k/smp_optimal)"`; `bytes allocated:` then `"$k = $(bytes/N)"`. Bytes are nondeterministic, so the port prints 0 or omits them.
- `plot`: the y series are `results[k].stj[1] - results[1].stj[1]` (the bound) and `exact[k] - results[1].stj[1]` (the actual, dashed, marker "o", ms=1) against sc. Colours: expand r, horner b, factor g, rounded y, original k. The legend order is built in polynomial.jl:106-118. The x label is `$\log|x|,\,\Delta=<step %.2e>$` (LaTeX). This maps to LeanPlot line series.

---

## 6. Golden examples (verbatim)

### 6.1 AbstractLattices
```julia
(∨)(a::Number,b::Number) = max(a,b); (∧)(a::Number,b::Number) = min(a,b)
5 ∧ 10 == 5 ; 5 ∨ 10 == 10 ; wedge(3) == vee(3)          # test/runtests.jl
true ∧ false == false ; true ∨ false == true            # 0.3.x only
```

### 6.2 PrimitiveBits **[run]**
```
PrimitiveBits16(7)                       → [1110000000000000]
PrimitiveBits16(7)[2:4]                  → Bool[1, 1, 0]
PrimitiveBits16(7)[:]                    → Bool[1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0]
UInt16(PrimitiveBits16(7))               → 7
PrimitiveBits8([true,false,true,true])   → [10110000]   (UInt8 13)
PrimitiveBits8(BitVector([1,0,0,0,0,0,0,1])) → [10000001] (UInt8 129)
PrimitiveBits128(UInt128(1)<<127)        → [000…0001]  (127 zeros then 1)
PrimitiveBits64(typemax(UInt64))         → [111…1] (64 ones)
PrimitiveBits8(300), PrimitiveBits8(-1)  → InexactError
b[0], b[17] (b::PrimitiveBits16)         → true, true      (quirk)
iterate / collect                        → UndefVarError (bug)
```

### 6.3 DeMorgan (README.md:9-41, verbatim; PrettyTables v2)
```
julia> @truthtable p q

julia> (p-->q)<-->(¬q-->¬p)
┌───┬───┬───────────┬──────┬──────┬───────────────────┐
│ p │ q │       p→q │ ¬(q) │ ¬(p) │                 ⊤ │
│   │   │ ¬(q)→¬(p) │      │      │ (p→q)↔(¬(q)→¬(p)) │
├───┼───┼───────────┼──────┼──────┼───────────────────┤
│ 1 │ 1 │         1 │    0 │    0 │                 1 │
│ 1 │ 0 │         0 │    1 │    0 │                 1 │
│ 0 │ 1 │         1 │    0 │    1 │                 1 │
│ 0 │ 0 │         1 │    1 │    1 │                 1 │
└───┴───┴───────────┴──────┴──────┴───────────────────┘

julia> @truthtable p q r

julia> ((p-->q)∧(q-->r))-->(p-->r)
┌───┬───┬───┬─────┬─────┬─────────────┬─────┬─────────────────────┐
│ p │ q │ r │ p→q │ q→r │ (p→q)∧(q→r) │ p→r │                   ⊤ │
│   │   │   │     │     │             │     │ ((p→q)∧(q→r))→(p→r) │
├───┼───┼───┼─────┼─────┼─────────────┼─────┼─────────────────────┤
│ 1 │ 1 │ 1 │   1 │   1 │           1 │   1 │                   1 │
│ 1 │ 1 │ 0 │   1 │   0 │           0 │   0 │                   1 │
│ 1 │ 0 │ 1 │   0 │   1 │           0 │   1 │                   1 │
│ 1 │ 0 │ 0 │   0 │   1 │           0 │   0 │                   1 │
│ 0 │ 1 │ 1 │   1 │   1 │           1 │   1 │                   1 │
│ 0 │ 1 │ 0 │   1 │   0 │           0 │   1 │                   1 │
│ 0 │ 0 │ 1 │   1 │   1 │           1 │   1 │                   1 │
│ 0 │ 0 │ 0 │   1 │   1 │           1 │   1 │                   1 │
└───┴───┴───┴─────┴─────┴─────────────┴─────┴─────────────────────┘
```
Class dumps **[run]** (format: column bits shown MSB→LSB, padded to 4 or 8; aliases; then i, j):
```
@truthtable p q
p                       : [0011 ("p",)] i=1 j=1
q                       : [0101 ("q",)]
(p-->q)<-->(¬q-->¬p)    : 0011 p | 0101 q | 1101 ("p→q","¬(q)→¬(p)") | 1010 ¬(q) | 1100 ¬(p) | 1111 ("⊤","(p→q)↔(¬(q)→¬(p))")   i=6 j=1   string="⊤"
p ∧ (p ∧ q)             : 0011 p | 0101 q | 0001 p∧q | 0001 p∧(p∧q)             i=4 j=1   (duplicate class!)
(p ∧ q) ∧ p             : 0011 p | 0101 q | 0001 ("p∧q","(p∧q)∧p")                i=3 j=2
p ∨ ¬p                  : 0011 p | 1100 ¬(p) | 1111 ("⊤","p∨¬(p)")               i=3 j=1
p ∧ ¬p                  : 0011 p | 1100 ¬(p) | 0000 ("⊥","p∧¬(p)")               i=3 j=1
¬(¬p)                   : 0011 ("p","¬(¬(p))") | 1100 ¬(p)                      i=1 j=2
q ∧ p                   : 0101 q | 0011 p | 0001 q∧p                             i=3
p | q                   : ... | 0111 p∨q ;  p & q : ... | 0001 p∧q
p → q : 1101 "p→q" ; p ← q : 1011 "p←q" ; p ↔ q : 1001 "p↔q"
@truthtable a b c:  a=00001111 b=00110011 c=01010101
((a-->b)∧(b-->c))-->(a-->c): a|b|c|11110011 a→b|11011101 b→c|11010001 (a→b)∧(b→c)|11110101 a→c|11111111 ("⊤","((a→b)∧(b→c))→(a→c)")  i=8
c ∧ a                   : 01010101 c | 00001111 a | 00000101 c∧a
(a ∧ b) ∨ c             : a | b | c | 00000011 a∧b | 01010111 (a∧b)∨c          i=5
c ∨ (a ∧ b)             : c | a | b | 00000011 a∧b | 01010111 c∨(a∧b)          i=5
¬(a ∧ b) <--> (¬a ∨ ¬b) : a | b | 00000011 a∧b | 11111100 ("¬(a∧b)","¬(a)∨¬(b)") | 11110000 ¬(a) | 11001100 ¬(b) | 11111111 ("⊤","¬(a∧b)↔(¬(a)∨¬(b))")  i=7
@truthtable x ; ¬x      : 01 x | 10 ¬(x)   (N=1)
TruthValues(true)        → TruthValues{1}(1) ; TruthValues(false,true,true,false) → TruthValues{4}(6) ; ¬ of that → 65529
!⊥ → ⊤ ; !⊤ → ⊥ ; ⊥(t) → ⊥ ; ⊤(t) → ⊤
t2=TV{2}(0b0011): ¬t2 = 12 ; t2∧⊤ = 3 ; ⊥∨t2 = 3 ; t2 → TV{2}(0b0101) = 13
!TV{6}(0) = typemax(UInt64) ; @truthtable x1..x6: ¬x1 = [0x00000000ffffffff, 0xffffffff00000000]
```

### 6.4 Dendriform
README (modern formatting; `README.md:57-76`, `docs/src/index.md:23-42`) **[run]**:
```
julia> Grove(3,7) ⊣ [1,2]∪[2,1]
[1, 2, 5, 1, 2]
[1, 2, 5, 2, 1]
[2, 1, 5, 1, 2]
[2, 1, 5, 2, 1]
[1, 5, 3, 1, 2]
[1, 5, 2, 1, 3]
[1, 5, 1, 2, 3]
[1, 5, 3, 2, 1]
[1, 5, 1, 3, 1]
Y5 #9/42                                   (GroveBin gbin = 267911168)

julia> Grove(2,3) * ([1,2,3]∪[3,2,1]) |> GroveBin
2981131286847743360614880957207748817969 Y6 #30/132 [54.75%]

julia> [2,1,7,4,1,3,1] < [2,1,7,4,3,2,1]
true
```
With `grovedisplay(true)` (docs/src/index.md:26-35, reproduced **[run]**):
```
[1, 2, 5, 1, 2] ↦ [3]∅∅[2, 5][1, 4] ↦ 20/42 or 21807
[1, 2, 5, 2, 1] ↦ [3]∅∅[2, 4][1, 5] ↦ 21/42 or 21906
[2, 1, 5, 1, 2] ↦ [3]∅∅[1, 5][2, 4] ↦ 22/42 or 22797
[2, 1, 5, 2, 1] ↦ [3]∅∅[1, 4][2, 5] ↦ 23/42 or 22896
[1, 5, 3, 1, 2] ↦ [2]∅[3][5][1, 4] ↦ 27/42 or 30807
[1, 5, 2, 1, 3] ↦ [2]∅[5][3][1, 4] ↦ 25/42 or 29007
[1, 5, 1, 2, 3] ↦ [2]∅[5][4][1, 3] ↦ 24/42 or 28908
[1, 5, 3, 2, 1] ↦ [2]∅[3][4][1, 5] ↦ 28/42 or 30906
[1, 5, 1, 3, 1] ↦ [2]∅[4]∅[1, 3, 5] ↦ 26/42 or 30186
267911168 Y5 #9/42 [0.006092%]
PBTree(0,1)  → "∅ ↦ [∅] ↦ 0/1 or 0"
[1,2,3]      → "[1, 2, 3] ↦ [3][2][1] ↦ 1/5 or 0"
```
Total groves and tree integers **[run]**:
```
Y1: [1]:0
Y2: [1,2]:0  [2,1]:9
Y3: [1,2,3]:0 [2,1,3]:9 [1,3,1]:108 [3,1,2]:189 [3,2,1]:198
Y4: [1,2,3,4]:0 [2,1,3,4]:9 [1,3,1,4]:108 [3,1,2,4]:189 [3,2,1,4]:198 [1,2,4,1]:1107 [2,1,4,1]:1197
    [1,4,1,2]:1908 [1,4,2,1]:2007 [4,1,2,3]:2889 [4,2,1,3]:2898 [4,1,3,1]:2997 [4,3,1,2]:3078 [4,3,2,1]:3087
ΥI(5) = [0, 9, 108, 189, 198, 1107, 1197, 1908, 2007, 2889, 2898, 2997, 3078, 3087, 11106, 11196, 12186, 12996,
         13086, 21807, 21906, 22797, 22896, 28908, 29007, 30186, 30807, 30906, 38889, 38898, 38997, 39078, 39087,
         39996, 40086, 40797, 40896, 41778, 41787, 41886, 41967, 41976]
ΘMax(1..6) = [1, 21, 321, 4321, 54321, 654321]
max TI(d) for d=1..10: 0, 9, 198, 3087, 41976, 530865, 6419754, 75308643, 864197532, 9753086421
Cn(0..6) = 1,1,2,5,14,42,132 (BigInt)
```
Printing **[run]**:
```
Grove(3,7)            → "[1, 2, 3]\n[2, 1, 3]\n[1, 3, 1]\nY3 #3/5"
GroveBin(Grove(3,7))  → "7 Y3 #3/5 [22.58%]"
GroveBin(Grove(2))    → "3 Y2 #2/2 [100.0%]"
GroveBin(5)           → "4398046511103 Y5 #42/42 [100.0%]"   (== GroveBin(GroveBin(3)+GroveBin(2)))
GroveBin(Grove(4,1))  → "1 Y4 #1/14 [0.006104%]"
GroveBin(Grove(6,1))  → "1 Y6 #1/132 [0.0%]" ; Grove(8,3) → "3 Y8 #2/1430 [0.0%]" ; Grove(1,1) → "1 Y1 #1/1 [100.0%]"
GroveBin(Grove(3,0))  → "0 Y3 #0/5 [0.0%]"
ppos for d=4 (2^14-1) at i=1,2,3,100,1000,16383: 0.006104, 0.01221, 0.01831, 0.6104, 6.105, 100.0
Grove(PBTree(0,[]))   → "∅Y0 #1/1"   ; Grove(0) → "Y0 #0/1" ; Grove(3,0) → "Y3 #0/5" ; PBTree(0,[]) → "∅"
```
Operations (tree indices within the result's degree, **in row order**) **[run]**:
```
a        b        a+b                      a⊣b          a⊢b         a*b (Grove b)
[1]      [1]      [2,1]                    [2]          [1]         [1]
[1]      [1,2]    [4,2,1]                  [4]          [2,1]       [1]
[1]      [2,1]    [5,3]                    [5]          [3]         [2]
[1,2]    [1]      [3,1]                    [3]          [1]         [1]
[2,1]    [1]      [5,4,2]                  [5,4]        [2]         [2]
[1,2]    [1,2]    [8,3,1]                  [8]          [3,1]       [3,1]
[1,2]    [2,1]    [9,6]                    [9]          [6]         [7]
[2,1]    [1,2]    [13,11,10,5,4,2]         [13,11,10]   [5,4,2]     [8]
[2,1]    [2,1]    [14,12,7]                [14,12]      [7]         [14,12]
[1,3,1]  [1]      [9,8,3]                  [9,8]        [3]         [3]
[1]      [1,3,1]  [12,7,6]                 [12]         [7,6]       [3]
```
Names: `[1]+[1]` → `[2, 1]`, `[1, 2]`; `[1,2]+[1]` → `[1, 3, 1]`, `[1, 2, 3]`; `[1]+[1,2]` → `[3, 1, 2]`, `[2, 1, 3]`, `[1, 2, 3]`; `[2,1]*[1,2]` → `[1, 4, 1, 2]`; `[1,2]*[2,1]` → `[2, 1, 4, 1]`; `Grove([1,2])*Grove([1,2])` → `[1, 3, 1, 4]`, `[1, 2, 3, 4]`.
```
Grove(2)+Grove(1)  rows: [1,3,1],[1,2,3],[3,2,1],[3,1,2],[2,1,3]  (indices [3,1,5,4,2])
Grove(1)+Grove(2)  rows: [3,1,2],[2,1,3],[1,2,3],[3,2,1],[1,3,1]
Grove(2)+Grove(2)  rows: [1,4,1,2],[1,3,1,4],[1,2,3,4],[4,3,1,2],[4,2,1,3],[4,1,2,3],[3,2,1,4],[3,1,2,4],[2,1,3,4],[1,4,2,1],[1,2,4,1],[4,3,2,1],[4,1,3,1],[2,1,4,1]
Grove(2)*Grove(2)  indices: [3,1,6,5,4,2,7,8,9,13,11,10,14,12]
Grove(2,3)*([1,2,3]∪[3,2,1]) indices: [20,6,1,58,41,39,38,33,32,30,14,13,11,5,66,67,74,128,122,120,119,103,101,100,95,94,92,132,127,113]
Grove(3,7) ⊣ [1,2]  indices: [20,22,27,25,24]
∪(Grove([1,2]),Grove([1,2]),Grove([2,1])) → [1, 2] / [2, 1] / Y2 #2/2  + stderr "[ Info: 1 duplicate in grove union"
| ⊣ [1] → Y0 #0/1 ; [1] ⊢ | → Y0 #0/1 ; [1] ⊣ | → [1]/Y1 ; | ⊢ [1] → [1]/Y1 ; | + [1] → [1]/Y1
| * Grove([1,2]) → Y0 #0/1 (0×1) ; [1] * Grove([1,2]) → [1, 2] ; [1,2] * Grove(|) → Y0 #0/1 (0×1)
[1,2] / [2,1] → [1, 2, 4, 1] ; [1,2] \ [2,1] → [1, 4, 2, 1]
σ([1,2,5,1,3]) → [3,1,5,2,1] ; graft([1,2],[1]) → [1,2,4,1] ; left([1,4,2,1]) → [1] ; right → [2,1]
posetnext([1,2,3,4]) rows: [1,2,4,1],[1,3,1,4],[2,1,3,4]  (Y4 #3/14)
posetprev([4,3,2,1]) rows: [1,4,2,1],[4,1,3,1],[4,3,1,2]
posetnext([1,2,3]) == Grove(3,6) ; posetprev([1,2,3]) == Grove(0)
between_list([1,2,3],[3,2,1]) = [[1,2,3],[1,3,1],[3,2,1],[2,1,3],[3,1,2]]
⊴([1,3,1],[3,1,2]) → Y0 #0/1 ; ⊴([1,2,3,4],[4,3,2,1]) == Grove(4)
[1,3,1] ⋖ [3,2,1] ; [3,2,1] ⋗ [1,3,1] ; [1,2] ⋖ [2,1]
[1,2,5,2,1] < [1,5,3,2,1] ; [3,2,1] > [1,3,1] ; [1,2,3,4,5] ≤ [5,4,3,2,1] ; [2,1] < [1,2] is false
Grove(3,1) < Grove(3,2) (index order) ; Grove(5,1) < Grove(5,5)
TreeRational(3) = [0, 3//107, 36//107, 63//107, 66//107] ; TreeRational([1,3,1]) = 36//107
treeindex([2,1,3]) = 2 ; grovebit(Grove(3,5)) = [1,0,1,0,0] ; groveindex([1,2,3]∪[3,2,1]) = 17
TreeBase([1,2,3]).μ = [[3],[2],[1]] ; PBTree(3,2).Y = [2,1,3]
intervals(3) = [1,2,3,4,5,8,10,11,16,20,24,26,31]
intcomp(3)   = [0,0,0,0,1,0,0,1,0,1,0,1,2]         (+ stderr "[ Info: Non-intervals: 0")
intcompt(3)  = [0,0,0,0,1,0,0,1,0,1,0,1,0]
intervals_full(3) = Bool[1,1,0,1,0,1,1,0,1,1,1,1,1]
print_interval_bin(3): 00001 00010 00011 00100 00101 01000 01010 01011 10000 10100 11000 11010 11111 (one per line)
print_intcomp_bin(3):  11111 ; print_intcompt_bin(3): 00101 01011 10100 11010
length(intervals(4)) = 68
```
Compositions **[run]** (each in a fresh process):
```
julia> grovecomposition(3, groveindex(3))       # returns 4
31 Y3 #5/5 [100.0%] has 4 compositions
(3 Y2 #2/2 [100.0%]) + (1 Y1 #1/1 [100.0%])
(1 Y1 #1/1 [100.0%]) + (3 Y2 #2/2 [100.0%])
(1 Y1 #1/1 [100.0%]) + (1 Y1 #1/1 [100.0%]) + (1 Y1 #1/1 [100.0%])
julia> grovecomposition(3, 6)                   # returns 1
6 Y3 #2/5 [19.36%] has 1 composition (itself)
julia> grovecomposition(3, 1)                   # returns 1
1 Y3 #1/5 [3.227%] has 1 composition (itself)
# Cache-pollution quirk, same process: grovecomposition(1,1) → 1 ; (2,3) → 2 ; (3,31) → 3 (!)
```
The test suite (`test/runtests.jl`) contains more equalities. All of them are golden candidates, and the notable ones are listed here:
`Grove(d) == Grove(d, 2^Cn(d)-1)`, `Grove(8,groveindex(Grove(5,1000)+Grove(3,7))) == Grove(5,1000)+Grove(3,7)`, `σ(σ(Grove(3,7))) == Grove(3,7)`, `graft([1,2,3],[2,1]) == σ(graft([1,2],[3,2,1]))`, `under([1,2,3],[3,2,1]) == σ(over([1,2,3],[3,2,1]))`, `left([1,4,2,1]) == right([1,2,4,1])`, `(x=PBTree(3,4),y=PBTree(4,7)): σ(x∨y)==σ(y)∨σ(x), σ(x/y)==σ(y)\σ(x)`, `@test_throws DomainError groveindex(-1,-1,Grove([1,2,3]).Y)`.

### 6.5 AbstractAnalysis **[run]**
```
Naturals[1:10]          [1..10] ; size (100,) ; type CountableVector{Int64, typeof(identity)}
Integers[1:12]          [0, 1, -1, 2, -2, 3, -3, 4, -4, 5, -5, 6]
PositiveRationals[1:12] [1, 1//2, 2, 1//3, 3//2, 2//3, 3, 1//4, 4//3, 3//5, 5//2, 2//5]
Rationals[1:14]         [0, 1, -1, 1//2, -1//2, 2, -2, 1//3, -1//3, 3//2, -3//2, 2//3, -2//3, 3]
NonzeroRationals[1:8]   [1, -1, 1//2, -1//2, 2, -2, 1//3, -1//3]
CantorPairs[1:12]       [(0,1),(1,0),(0,2),(1,1),(2,0),(1,2),(2,1),(3,0),(4,-1),(1,3),(2,2),(3,1)]   (buggy)
ElegantPairs0[1:12]     [(0,1),(1,0),(1,1),(0,2),(1,2),(2,0),(2,1),(2,2),(0,3),(1,3),(2,3),(3,0)]
ElegantPairs1[1:12]     [(1,1),(1,2),(2,1),(2,2),(1,3),(2,3),(3,1),(3,2),(3,3),(1,4),(2,4),(3,4)]
GaussianNaturals[1:6]   [1+1im, 1+2im, 2+1im, 2+2im, 1+3im, 2+3im]
GaussianIntegers[1:10]  [0+0im, 0+1im, 1+0im, 1+1im, 0-1im, 1-1im, -1+0im, -1+1im, -1-1im, 0+2im]
GaussianRationals[1:6]  [0//1+0//1*im, 0//1+1//1*im, 1//1+0//1*im, 1//1+1//1*im, 0//1-1//1*im, 1//1-1//1*im]
sternbrocot(1:20)       [1,1,2,1,3,2,3,1,4,3,5,2,5,3,4,1,5,4,7,3]   (== SternBrocot[1:20])
Ones(5), Zeros(3)       [1,1,1,1,1], [0,0,0]
x = CountableVector(i->1/i^2, 10)
sum(x)                  "1.5497677311665408 (n → 10, Δ → 0.01)\n"  fields v0=1=>1.0, v=10=>1.5497677311665408, n=10, r=0.01
sum(x)[1e-10]           "1.6449240669982403 (n → 100002, Δ → 9.999800987259277e-11)\n"
sum(x)[20]              "1.5961632439130233 (n → 20, Δ → 0.0024999999999999467)\n"
prod(CountableVector(i->1+1/i^2,10))  "3.342847116573682 (n → 10, Δ → 0.03309749620370006)\n"
prod(Naturals(10))      "3628800 (n → 10, Δ → 3.26592e6)\n"
cumsum(x)[1:5]          [1.0, 1.25, 1.3611111111111112, 1.4236111111111112, 1.4636111111111112]
typeof(cumsum(Ones(5))) CountableVector{Int64, typeof(identity)}
residuals([1.0,0.5,0.25,0.125]) = [0.5, 0.25, 0.125] ; lipschitz(same) = [0.5, 0.5]
orbit(cos, 1.0)         "0.7390851332151603 (n → 88, Δ → 7.771561172376096e-16)\n"
orbit(cos, 1.0, 10)     "0.744237354900557 (n → 11, Δ → 0.012833312478047199)\n"  (== FixedCycle(10,cos)(1.0))
orbiterror(x->x/2+1, 0.0) → Limit "1.9999999999999991 (n → 52, Δ → 8.881784197001252e-16)\n", errs[1:5]=[1.0,0.5,0.25,0.125,0.0625], length 51
orbit(x->x/2,[1.0,2.0],3) show → "Limit as n → 4, Δ → 0.2795084971874737\n[0.125, 0.25]" ; compact → "[0.125, 0.25] (n → 4, Δ → 0.2795084971874737)\n"
limit(CountableVector(i->1/i,5)) → "0.2 (n → 5, Δ → 0.04999999999999999)\n"
c=CountableVector(i->1/i,5): c+c=2c=[2.0,1.0,0.6666666666666666,0.5,0.4]; c^2=[1.0,0.25,0.1111111111111111,0.0625,0.04000000000000001]
dot(c,c)                "1.4636111111111112 (n → 5, Δ → 0.04000000000000001)\n"
map(x->2x, sum(c))      "4.566666666666666 (n → 5, Δ → Inf)\n"
sum(c) + 1              "3.4499999999999997 (n → 6, Δ → 0.16666666666666652)\n"   (advanced one step)
collect(orbit(x->x/2+1, 0.0, 5)) = [0.0, 1.0, 1.5, 1.75, 1.875, 1.9375]
collect(sum(c))         = [1.0, 1.5, 1.8333333333333333, 2.083333333333333, 2.283333333333333]
countableproduct(Naturals(3),Naturals(2)) = [1 2; 2 4; 3 6] ; countabletuple(Naturals(2),Naturals(2)) = [(1,1) (1,2); (2,1) (2,2)]
CountableArray(2,3) = [(1,1) (1,2) (1,3); (2,1) (2,2) (2,3)] ; elegantproduct(Naturals,Naturals)[1:6] = [1,2,2,4,3,6]
FunctionVector((x,i)->x^i,5)(2.0) = [2.0,4.0,8.0,16.0,32.0]
sum(FunctionVector((x,i)->x^i,5))(0.5) → "0.96875 (n → 5, Δ → 0.03125)\n"
prod(FunctionVector((x,i)->1+x^i,4))(0.5) → "2.2412109375 (n → 4, Δ → 0.1318359375)\n"
derivative(sin,0.0) = 0.99999999999999 ; derivative2(sin,1.0) = -0.8414709866046906
supnorm([3,4]) = 5.0 ; supnorm(3,5) = 2.0 ; infnorm(:a) = 0.0 ; supnorm(:a,:b) = Inf ; maxabs([1,-5,3]) = 5.0 ; minabs = 1.0
isdecreasing([5,4,3]) = true ; iscauchy([1,.5,.25,.125]) = true ; isdiverging(same) = false ; isconverging(same) = true
supseq([1,3,2,5,4]) = [5,5,5,5,4] ; infseq([5,3,4,1,2]) = [1,1,1,1,2]
supseq([1,3,2,5,4,0,1,2,0,1],2)[1:8] = [3,5,5,5,4,2,2,2] ; limsup(that,2) = 2
-- groups --
magma(Complex(0,1)) = [0+1im, -1+0im, 0-1im, 1+0im]  ("4-element Semimagma{Complex{Int64}, *, inv}")
  order 4, isgroup/isabelian/iscyclic/ismagma/isassociative/issemigroup all true ; ismonoid → MethodError (bug)
  orders = [4,2,4,1] ; cayley rows: [-1 -i 1 i; -i 1 i -1; 1 i -1 -i; i -1 -i 1]
  subgroup = same ; Complex(2,0)*m = [0+2im,-2+0im,0-2im,2+0im] ; m+Complex(1,0) = [1+1im,0+0im,1-1im,2+0im]
  m*m = [-1+0im, 0-1im, 1+0im, 0+1im] ; Complex(0,1)∘m = same ; m == magma(Complex(0,-1)) → true
magma(3, (a,b)->mod(a*b,7), identity) = [3,2,6,4,5,1]
group([1,2], (a,b)->mod(a+b,5), a->mod(-a,5)) = [1,2,4,3,0]
S3 = [[1,2,3],[1,3,2],[2,1,3],[2,3,1],[3,1,2],[3,2,1]] ; order 6, isgroup true, isabelian false
A3 = [[1,2,3],[2,3,1],[3,1,2]]
p=Permutation(2,3,1), q=Permutation(2,1,3): p*q=[3,2,1], q*p=[1,3,2], inv(p)=p^2=p^-1=[3,1,2], p^0=[1,2,3], p/q=[3,2,1], p\q=[1,3,2]
decompose(p) = Cycle{3}[1,2,3] ; decompose(Permutation(2,1,4,3)) = [[1,2],[3,4]] ; decompose(id) = Int64[] (empty CycleProduct)
order(p)=2, order(q)=1, levicivita(p)=1, levicivita(q)=-1, iseven(p)=true
Permutation(Cycle{4}(1,3,4)) = [3,2,4,1] ; Permutation(CycleProduct(Cycle{4}(1,2),Cycle{4}(3,4))) = [2,1,4,3] ; Permutation(CycleProduct{3}()) = [1,2,3]
decompose(S3) = [[],[2,3],[1,2],[1,2,3],[1,3,2],[1,3]] ; levicivita.(S3) = [1,-1,-1,1,1,-1] ; order.(S3) = [0,1,1,2,2,1]
group([p]) = [[2,3,1],[3,1,2],[1,2,3]] ; group([q]) = [[2,1,3],[1,2,3]]
isnormal(⟨p⟩,S3)=true ; isnormal(⟨q⟩,S3)=false ; normalizer(⟨q⟩)=centralizer(⟨q⟩)=[[1,2,3],[2,1,3]]
center(S3) = [[1,2,3],[1,3,2]]  (BUG) ; center(S4) = [[1,2,3,4],[1,2,4,3],[2,1,3,4],[2,1,4,3]] (BUG)
leftcosets(⟨q⟩) = [[[2,1,3],[1,2,3]], [[3,1,2],[1,3,2]], [[1,2,3],[2,1,3]], [[3,2,1],[2,3,1]], [[1,3,2],[3,1,2]], [[2,3,1],[3,2,1]]]  (6, ordered-dedup quirk)
rightcosets(⟨q⟩) = [[[2,1,3],[1,2,3]], [[2,3,1],[1,3,2]], [[1,2,3],[2,1,3]], [[1,3,2],[2,3,1]], [[3,2,1],[3,1,2]], [[3,1,2],[3,2,1]]]
S3/⟨p⟩ has 6 entries (ordered-dedup) ; commutator(S3) = [[1,2,3],[2,3,1],[3,1,2]] ; issubgroup(⟨p⟩,S3) = issubgroup(⟨q⟩,S3) = true
length(subgroup(S3)) = 6 ; magma([p,q]) = [[2,3,1],[2,1,3],[3,1,2],[3,2,1],[1,2,3],[1,3,2]]
unityroots(4) = [1.0+0.0im, 6.123233995736766e-17+1.0im, -1.0+1.2246467991473532e-16im, -1.8369701987210297e-16-1.0im]
group([s]) * group([r]) with s=(1 3), r=(1 2 3 4) = [[2,1,4,3],[4,3,2,1],[1,4,3,2],[3,2,1,4],[2,3,4,1],[4,1,2,3],[3,4,1,2],[1,2,3,4]]  (D4 intent)
Cycle{3}(1,2,3) == Cycle{3}(2,3,1) → true ; == Cycle{3}(1,3,2) → true (quirk)
AbstractAnalysis.isdisjoint(Cycle{4}(1,2),Cycle{4}(3,4)) = true
```

### 6.6 Wilkinson / SyntaxTree **[run]**
```
exprval(:(x^9-2))  = exprval(:((x-2)^9)) = (18.378934415299785, 2, 1.5040773967762742, 0.6931471805599453, 9.0)   # test/runtests.jl:4
exprval(:(2x^2-1//2))        = (4.89405674908118, 4, 0.4704952763295575, 0.7954314537066303, 2.0)
exprval(:(x^2+3x+2))         = (2.829832091381222, 3, 0.2482956558418553, 0.8958797346140275, 2.0)
exprval(:((x+1)*(x+2)))      = (2.1529664988308648, 3, 0.6083693396938659, 0.8465735902799727, 1.0)
exprval(:(2+x*(3+x)))        = (1.278520973825755, 3, 0.20273255405408225, 0.8958797346140275, 1.0)
exprval(:(1.0-3.0x+x^3))     = (9.578148196308588, 4, 0.6071533513798585, 1.049306144334055, 3.0)
exprval(:(((x-1)*x+1)*x+5))  = (5.129220773410258, 5, 0.8746704516540534, 1.2031459708113668, 1.0)
expravg(:(x^9-2)) = (1, 0.6931471805599453, 1, 9.0) ; expravg(:(2x^2-1//2)) = (3, 0.7954314537066303, 1, 2.0)
callcount(:(2x^2-1//2)) = 4
SyntaxTree.sub(Float64, :(2x^2-1//2)) → :(2.0 * x ^ 2 - 1.0 // 2.0)
SyntaxTree.abs(:(2x^2-1//2))          → :(2 * x ^ 2 + 1 // 2)
SyntaxTree.alg(:(2x^2-1//2))          → :((1 + ϵ) * ((1 + ϵ) * (2 * ((1 + ϵ) * x ^ 2)) - (1 + ϵ) * 1 // 2))   (README)
REDUCE forms (Reduce.Rational(false)):
 (x-2)^9  expand: ((((((((x ^ 9 - 18 * x ^ 8) + 144 * x ^ 7) - 672 * x ^ 6) + 2016 * x ^ 5) - 4032 * x ^ 4) + 5376 * x ^ 3) - 4608 * x ^ 2) + 2304x) - 512
          horner: ((((((((x - 18) * x + 144) * x - 672) * x + 2016) * x - 4032) * x + 5376) * x - 4608) * x + 2304) * x - 512
          factor: (x - 2) ^ 9           exprval e/h/f: 643.1128014851948 / 51.3441179785937 / 18.378934415299785
 (x-1)(x-2)(x-3) expand: ((x ^ 3 - 6 * x ^ 2) + 11x) - 6 ; horner: ((x - 6) * x + 11) * x - 6 ; factor: (x - 1) * (x - 2) * (x - 3)
          exprval e/h/f: 20.309556405992176 / 3.5120320655871207 / 2.8950605492432184 ; factor rounded of the expanded form: (x - 1) * (x - 2.0) * (x - 3.0)
 x^9-2: expand = horner = factor = x ^ 9 - 2 ; factor rounded = product of 9 complex linear factors (REDUCE numerics)
polyhorner(:x,[1,2,3]) = (3x + 2) * x + 1 ; polyfactors(:x,[1,2,3]) = (x - 1) * (x - 2) * (x - 3)
polyexpand(:x,[1,2,3]) = 3 * x ^ 2 + 2x + 1 ; polyfactors(:x,[0.5,2.25]) = ((4x - 9) * (2x - 1)) / 8 ; polyhorner(:x,[-1,0,2]) = 2 * x ^ 2 - 1
floatset(Float64,3000;scale=log): first -36.04365338911715, last 709.782712893384, step 0.24869168598949687, len 3000,
          collect[1:3] = [-36.04365338911715, -35.794961703127655, -35.54627001713816]
stieltjes/simpson (Float64 evaluation; BigFloat evaluation with ω from Float64 gives identical smp to all printed digits):
 x^9-2      Ω=463  stj[1:3]=[1.3862943611198872, 1.1376026751303883, 0.8889109891408964] stj[Ω]=595.4647380956859 smp=1.620213711403913  geonorm=-1.6123474563895153
 (x-2)^9    Ω=463  stj[1:3]=[6.93147180559945, 6.682780119609951, 6.43408843362046]      stj[Ω]=595.4647380956859 smp=1.6366920760680022 geonorm=-1.5706179448245474
 horner9    Ω=463  stj[1:3]=[9.071537969095722, 8.822846283106223, 8.574154597116731]    stj[Ω]=597.6048042591822 smp=1.6553048532639636
 (x-1)(x-2)(x-3) Ω=1097 stj[1:3]=[3.1780538303479418, 2.9293621443584428, 2.680670458368951] stj[Ω]=438.38750988274563 smp=0.6344918998259239
 ((x-6)x+11)x-6  Ω=1097 stj[1:3]=[3.4011973816621506, 3.1525056956726516, 2.9038140096831597] stj[Ω]=438.6106534340598 smp=0.6353103279322956
```

---

## 7. Dependencies on other chakravala packages (and externals)

| package | chakravala deps → symbols used | external deps |
|---|---|---|
| AbstractLattices | none | none |
| PrimitiveBits | none | none |
| DeMorgan | **AbstractLattices** (`wedge, vee, ∧, ∨`, extended with methods) · **StaticVectors** (`Values{M,T}` for the TruthTable fields, `Values(...)` ctor, `Vector(::Values)`) | Requires (optional PrettyTables v2), LinearAlgebra (declared, unused) |
| Dendriform | **AbstractLattices** (`∨`, extended with the graft methods; `import AbstractLattices: ∨`, arithmetic.jl:5) | Combinatorics (`catalannum` → BigInt) |
| AbstractAnalysis | **StaticVectors** (`Variables{N,Int}` mutable size in CountableArray/FunctionArray; `Values` for Permutation/Cycle storage; `count(a,b)` = `Values(a:b)`, StaticVectors.jl:72-79) | ElasticArrays (`ElasticArray`, `resize_lastdim!`), Combinatorics (`permutations`), LinearAlgebra (`norm`, `dot`, `I`, `UniformScaling`); weak deps **Primes** (`prime(i)`), **Mods** (`AbstractMod` equality/`is_invertible`) |
| Wilkinson | **SyntaxTree** (`exprval, callcount, sub, abs, genlatest`) · **Reduce** (`rcall`, `horner`, `factor`, `expand`, `Reduce.Rational`, `Algebra.+ - * ^`, `RExpr`) | PyPlot (`figure, plot, legend, xlabel, ylabel, tight_layout`), Printf |

**Reverse dependencies** (why these matter to the port):
- `AbstractTensors.jl/src/AbstractTensors.jl:271-274` imports `∧, ∨, wedge, vee` from AbstractLattices. Leibniz (`src/Leibniz.jl:144`) and Grassmann (`src/algebra.jl:16`) import `∧, ∨` through AbstractTensors. **Every Grassmann wedge/regressive product is a method on the AbstractLattices function.**
- `Cartan.jl/src/Cartan.jl:36-43, 250, 513-560` and `src/grid.jl:1452-1463` import `orbit, orbithold, Limit, orbiterror, derivative, supnorm, infnorm, maxabs, minabs, residual, residuals, lipschitz, CountableVector, CountableArray, SequenceArray, FixedCycle, extract, assign!` and `AbstractAnalysis.counter`. Cartan defines `supnorm(::TensorField) = maximum(norm, fiber)`, a `TensorField` orbit whose storage is `SequenceArray(ElasticArray, (u,k)->f(extract(u,k-1)))`, `Limit{<:TensorField}` collect, and indefinite integrals as `Limit(1=>0, n=>i, n, supnorm(...), G)`. **The Lean Limit/SequenceArray API must be generic enough for Cartan's TensorField states** (arbitrary state type, pluggable metric, memoized growable last-dim storage).
- DeMorgan, Dendriform, PrimitiveBits and Wilkinson have no reverse deps in the ecosystem.

---

## 8. Lean 4 porting notes

### 8.1 Global conventions
- **Notation.** Lean core reserves `∧`/`∨` for `And`/`Or` (`Init/Notation.lean:404-405`, prec 35/30). As in the sibling note `abstracttensors-staticvectors.md:1056`, **use distinct tokens**: `⋏` (wedge, `infixl:70`, like Julia's times-level ∧) and `⋎` (vee, `infixl:65`, like Julia's plus-level ∨), plus named functions `wedge`/`vee`. DeMorgan's `¬`/`→`/`↔` also collide with core; use `!`/`&&&`-style ASCII or scoped notations such as `¬ᵗ`, `⟶`, `⟷`. Dendriform's `⊣`/`⊢`: Lean has `⊢` in tactic syntax (as a token), so use `⊣ᵈ`/`⊢ᵈ` or `dashv`/`vdash` with scoped `infixl:65 " ⊣ "`. Test it in a scratch file first, because `⊢` as an infix term operator is likely to conflict.
- **Unicode ↔ ASCII alias table** (keep the Julia names as `def`s): wedge `⋏`, vee `⋎`, graft `∨`→`⋎`, dashv `⊣`, vdash `⊢`, between `⊴`, over `/`, under `\` (use `HDiv`/`SDiff`? Lean has no `\` infix, so provide `under` plus scoped `⧵`), σ → `involution`/`σ`.
- **Global mutable toggles** (grovesort, grovedisplay, treeshift): replace them with explicit config (`structure DendriformOpts where display := false; treeshift := true`) passed to print/`TreeRational`. Drop `grovesort(false)`.
- **Global caches** (total groves, compositions, SequenceArray memos): pure recomputation plus optional memo. Use `IO.Ref` caches exposed through `@[implemented_by]` pure facades, or an explicit context object. Never reproduce the stateful composition-cache bug.
- **Reproduce the quirks behind a `Julia` namespace, and fix them in the clean API.** Examples: DeMorgan's duplicate classes, `center`, CantorPairs, cosets ordered dedup, `iscyclic` first-two, PrimitiveBits out-of-range → true, Cycle `==`. The oracle compares the `Julia.*` versions. The clean versions get proofs.

### 8.2 AbstractLattices → `Chakravala/AbstractLattices.lean` (~40 LOC)
```lean
class HWedge (α β : Type u) (γ : outParam (Type u)) where wedge : α → β → γ
class HVee   (α β : Type u) (γ : outParam (Type u)) where vee : α → β → γ
class Dist   (α : Type u) (β : outParam (Type v)) where dist : α → α → β
infixl:70 " ⋏ " => HWedge.wedge
infixl:65 " ⋎ " => HVee.vee
instance : HWedge Bool Bool Bool := ⟨(· && ·)⟩
instance : HVee Bool Bool Bool := ⟨(· || ·)⟩
@[inline] def wedge₁ (x : α) := x  -- unary identity
```
Heterogeneous (`H*`) classes are needed because Grassmann's `∧` maps grade r × grade s → grade r+s. Nullary units (`∧()=1`, `∨()=I`) belong in AbstractTensors. Proof tidbits: `Bool` wedge/vee commutativity and associativity `by decide`.

### 8.3 PrimitiveBits → `Chakravala/PrimitiveBits.lean` (~80 LOC)
- `structure PrimitiveBits (w : Nat) where bits : BitVec w`. Since `BitVec w` is Nat-backed (boxed ≥ 63 bits), for performance use a width-indexed family `PrimitiveBits.Repr : Nat → Type` with `8 ↦ UInt8`, …, `64 ↦ UInt64`, `128 ↦ (UInt64 × UInt64)`, or keep `BitVec` (this package is not hot). **w is a type index (zero cost).**
- `getD (b) (i : Nat) : Bool := b.bits.getLsbD (i-1)` for `1 ≤ i ≤ w`. Keep `Julia.getindex (i : Int) : Bool` returning `true` out of range (quirk).
- `ofBools : Array Bool → Except String (PrimitiveBits w)`: error on empty or too long input.
- `toString`: `"[" ++ bits LSB-first ++ "]"`. Implement a working `ForIn`/`toList` (Julia's iterate is broken; the port supplies the intended behavior).
- Proofs: `getD (ofBools v) i = v[i-1]` and round-trips `ofUInt ∘ toUInt = id` by `bv_decide`/`simp`.

### 8.4 DeMorgan → `Chakravala/DeMorgan/{TruthValues,TruthTable,Render,Macro}.lean` (~350 LOC)
- `structure TruthValues (N : Nat) where p : UInt64` (N is a type index, zero cost). Require `N ≤ 6` via a class `[Fact (N ≤ 6)]`-like `NeedsSmall N`, or just document it. `mask N := if N ≥ 6 then 0xFFFF_FFFF_FFFF_FFFF else (1 <<< (1 <<< N)) - 1`. **Lean `UInt64` shifts are mod 64**, so `1 <<< 64 = 1` and the naive formula gives mask 0. Guard it.
- `⊥`/`⊤`: define `TruthValues.bot N := ⟨0⟩`, `top N := ⟨mask N⟩`. Julia's N-polymorphic `⊥ : TruthValues{0}` and `⊤ : Tautology` can be an inductive `Truth N | bot | top | vals p`, or simply `Coe`-free helper functions. Printing `⊥`/`⊤` only matters at the TruthValues level; the TruthTable names already carry "⊥"/"⊤".
- Ops `¬ ∧ ∨ → ← ↔` as bitwise UInt64. Proof standouts: De Morgan laws and involution `∀ p : TruthValues N, ¬(¬p) = p` (given masked p) with **`bv_decide`** after unfolding to UInt64/BitVec. Also `select` correctness: `(select n N >>> k) &&& 1 = if (k >>> (n-1)) % 2 = 0 then 1 else 0`, by `decide` for N ≤ 4.
- `structure TruthTable (N : Nat) where cols : Array UInt64; names : Array (Array String); i j : Nat` (M runtime). An invariant `cols.size = names.size` can be carried as a Prop field (erased). `combine` is transcribed literally (including the original-P membership quirk) as `Julia.combine`. A clean `combine` deduplicates against `rp`. Default ops use Julia semantics so the goldens match.
- `parstring`: codepoint length 1, or `s.startsWith "¬(" && s.endsWith ")" && inner.all (· ∉ ['(', ')']) && inner ≠ ""`. The regex technically allows empty inner; follow the regex (allow empty).
- `@truthtable p q` → a term macro `truthtable! [p, q] => body` expanding to `let p := proj N 1 "p"; let q := ...; body`, or a command `truthtable p q` that declares defs. Projections use `select (N+1-m) N`.
- `Render`: an `Std.Format`/String box-table renderer (right-aligned, width by codepoint count, since all glyphs used are width 1) reproducing PrettyTables v2 output (§6.3).

### 8.5 Dendriform → `Chakravala/Dendriform/{Tree,Order,TotalGrove,Grove,Arith,Poset,Display,Compose}.lean` (~1100 LOC)
**Representation**
- `structure PBTree where name : ByteArray` (or `Array UInt8`), with degree = size. Typed facade: `abbrev PBTreeN (n : Nat) := {t : PBTree // t.name.size = n}` (a subtype Prop, zero cost). Then `graft : PBTreeN a → PBTreeN b → PBTreeN (a+b+1)`, and groves `GroveN n`: `⊣ ⊢ + : GroveN a → GroveN b → GroveN (a+b)`, `* : GroveN a → GroveN b → GroveN (a*b)`. **This statically enforces Loday's degree homomorphism: a genuine standout at zero runtime cost.** `left/right : PBTreeN (n+1) → Σ k, PBTreeN k × PBTreeN (n-k)`.
- `structure Grove where degr : Nat; rows : Array ByteArray` (multiset, ordered), or a flat `ByteArray` with stride `degr` for cache efficiency. Keep the degenerate Julia encodings distinguishable for printing: `zero` (size 0, "Y0 #0/1") vs a `leaf` grove (size 1, degree 0, "∅Y0 #1/1").
- Grove index/bitset: Lean `Nat` (GMP-backed). `∪` = `Nat.lor` on bitsets. `groveindex` = Σ 2^(idx-1) with multiplicity (`Julia` semantics) vs `Nat.lor` (clean).
- TreeInteger: `Nat`, or a `UInt64` fast path for d ≤ 18. `ΘMax d = Σ k·10^(k-1)` closed form (do not replicate the memo bug).

**Total grove / lookup (hot path)**
- `allTrees n`: recursion `[l ++ [n] ++ r | k ∈ 0..n-1, l ∈ all k, r ∈ all (n-1-k)]`, then sort by TreeInteger (`Array.qsort`). Cache per degree (`IO.Ref (Array (Array ByteArray))` behind `implemented_by`). Store the parallel `tiTable : Array UInt64` sorted.
- `treeindex`: **binary search** in `tiTable`, instead of Julia's O(Cn) `findfirst` per lookup. Julia's grove ops are O(size·Cn(d)) because of that scan. This is the main algorithmic speedup.
- Optionally memoize tree-level `+` (`HashMap (idxA, idxB) → Array idx`), since Loday sums recurse heavily. The Julia code has no memo.

**Arithmetic.** Transcribe §4.4.4–4.4.5 exactly, **including the row orders** (x-major for ⊣/⊢/*, y-major for `+`) and the degr-0 shortcuts. Return multisets. Grove `==` is a sorted-multiset comparison (no mutation).

**Poset.** Memoize `posetnext_list` per tree. Implement `<` as a BFS over upper covers with a visited set (same truth value, polynomial rather than exponential). Keep `between_list` in DFS first-seen order for goldens.

**Proofs that aid development.**
- `σ (σ t) = t`; `(graft l r).deg = l.deg + r.deg + 1`; `left (graft l r) = l`, `right (graft l r) = r` (the root label is unique: needs a lemma that valid names contain the max label once, or state it for the constructed trees).
- `(allTrees n).size = catalan n` via `decide` for n ≤ 7, and in general by the Catalan recurrence. TreeInteger injectivity for n ≤ 8 via `decide` (`native_decide` only if policy allows).
- Dendriform axioms on small degrees as `example`s by `decide`: `(x ⊣ y) ⊣ z ≈ x ⊣ (y + z)`, `(x ⊢ y) ⊣ z ≈ x ⊢ (y ⊣ z)`, `(x + y) ⊢ z ≈ x ⊢ (y ⊢ z)` (as sorted multisets); `Y p + Y q ≈ Y (p+q)`, `Y p * Y q ≈ Y (p*q)` for p+q ≤ 5.

**Display.** Per §5.1. The Float16 `ppos` needs a small **Float16 emulation**:
1. Round the exact rational `100·gbin/(2^Cn-1)` to binary16 (11-bit significand, subnormals below 2^-14 with quantum 2^-24, round-half-even).
2. Take the shortest decimal that round-trips. Brute force p = 1..5 significant digits.
3. Apply Julia's plain-vs-sci rule (`-4 < pt ≤ 3`).

This is about 60 LOC and gets its own unit table of goldens.

**Skip or redesign.** Drop the stdout progress logs; `@info` becomes an optional `IO` warning; drop the `grovesort(false)` build order (keep it documented); drop the promote/convert zoo (provide `OfArray`-style coercions); replace the piracy on `Vector` `<`/`∪` with explicit `PBTree.ofList`.

### 8.6 AbstractAnalysis → `Chakravala/AbstractAnalysis/{Countable,Sets,Sequence,Metric,Limit,Magma,Perm}.lean` (~1400 LOC)
- `structure CountableArray (T : Type) (N : Nat) where f : Vector Nat N → T; size : Vector Nat N` (N is a type index). Specialize `CountableVector T := {f : Nat → T, len : Nat}` for speed and ergonomics. Julia's F type param (closure specialization) becomes `@[specialize]` on the consumers (map, sum, limit, orbit), so Lean inlines known lambdas. **Float boxing risk:** a Lean closure `Nat → Float` returns boxed Float. Hot loops (`sum`, `orbit` with `Float → Float`) must be `@[inline]`/`@[specialize]` so the lambda is inlined, or they allocate per step (Julia pays nothing here).
- `resize!` mutation of global constants (`Naturals`) → a pure `withLen`.
- `SequenceArray`: `structure SequenceArray (T) where v : Array T; f : Array T → Nat → T` with `ensure : Nat → SequenceArray T` and `get : SequenceArray T → Nat → T × SequenceArray T` (state-passing), or `IO.Ref` for Cartan-style use. Multi-dim ElasticArray: flat `FloatArray` + shape with last-dim growth.
- `Limit`: `structure Limit (S : Type) where v0 v : S; n : Nat; r : Float; step : S → S; d : S → S → Float; value : S → V` (the projection replaces Julia's `last` on Pair states). Three constructors mirror the state shapes (§3.5). Keep **n-counting and residual conventions exactly** (§4.5.4); they show up in the printed goldens (`n → 100002`).
- `Metric` typeclass `class Metric (α) where dist : α → α → Float` with instances Float (abs diff), Complex, `FloatArray` (2-norm, **not** max), pairs (compare the value), and a default `Inf`. `supnorm`/`infnorm`/`maxabs`/`minabs` as functions.
- `Semimagma`: `structure Semimagma (T) where v : Array T; op : T → T → T; inv : T → T` + `[GEqual T]` (Float: Julia's isapprox `rtol=√eps, atol=0`; Int/Rat/Perm: `==`). Keep insertion order. For exact types, add an `Std.HashSet` alongside the Array to make membership O(1) (a huge win over Julia's O(n) `∈`) without changing the order.
- `Permutation (N : Nat)`: `v : Vector (Fin N) N` stored 0-based, with display adding 1. Optional erased `isPerm` proof field (the standout: `inv`, `mul`, `one` preserve bijectivity, `p * p⁻¹ = 1`, sign multiplicative). `Cycle N`, `CycleProduct N`. Rename `order(::Perm)` to `transpositionCount` (keep an `order` alias for Julia parity) and provide the true `groupOrder` (lcm of cycle lengths) separately.
- Countable sets: pure `Nat → Int`/`Rat` functions. Proof standout: Szudzik `elegantPair`/`elegantinversion` inverse theorems (`Nat.sqrt` lemmas, `omega`), `fusc` recurrence and Calkin–Wilf bijectivity (stretch). Keep `Julia.cantorinversion` (buggy) and add a correct `cantorUnpair` with an inverse proof.
- Primes (weak dep): `nthPrime` via an incremental sieve cache. Mods: skip, or provide `GEqual (Fin n)`.
- Float fidelity: Julia `pow`/`exp`/`log`/`cos` are pure-Julia implementations; Lean's `Float` calls libm. Expect 1-ulp differences, so the oracle uses rtol 1e-13 on Float outputs and exact on counts (n) where the stopping iteration is not borderline.

### 8.7 Wilkinson → `Chakravala/Wilkinson/{Expr,SyntaxTree,FloatRange,Analysis,PolyForms,Plot}.lean` (~600 LOC core + optional CAS ~400)
- `inductive PExpr | var (s : String) | int (z : Int) | float (x : Float) | rat (q : Rat) | call (op : String) (args : Array PExpr)`. `^` stays a call with its exponent as a child (the literal-exponent special cases in `sub`/`abs`/`expravg` need to know it).
- SyntaxTree: `callcount`, `expravg`, `exprdev`, `exprval`, `sub` (→ a `NumKind` switch), `abs`, `alg`. `genfun` becomes an **interpreter** `eval : PExpr → (x : α) → α` over a `[Field-like α]` class (Float, and exact `Rat` in place of BigFloat).
- `floatset`: implement §4.6.3 literally (`len` computation with overshoot fix, `x_i = l + (i-1)*st`).
- `stieltjes`: evaluate `abs(sub(T, e))` at `exp(sc_i)`. For T=BigFloat, use **exact rational evaluation**: x_i is a dyadic Float, so `Rat` evaluation is exact. Then compute `log|q|` via `Nat.log2`-style exponent extraction plus Float log of the normalized mantissa (this avoids overflow at x ≈ 1e308 with degree 9). Timing/bytes → 0.
- `simpson`, `Ω`, `geonorm`, `exacterr`, `renormalize!`: literal.
- Polynomial forms (REDUCE replacement): implement univariate `Poly ℚ` with `expand` and `horner` printers producing **REDUCE's output shapes** (§6.6: descending powers, left-assoc `+`/`-` chain, `c * x ^ k`, `c x` for the linear term, coefficient 1 omitted, and for horner `((x - 18) * x + 144) * x ...`). `factor` over ℚ: rational-root / square-free factoring (covers the product-of-linear-factors test cases). `factor rounded` (numeric complex roots) is **out of scope**. `polyhorner`/`polyfactors`/`polyexpand` produce REDUCE-canonical output in Julia, so the port pipes its raw trees through the same normalizer.
- `plot` → LeanPlot line series (y = bound/actual minus the optimal baseline). Colours and legend order per §5.6.
- Hot path: 3000 points × a handful of forms. Trivial.

### 8.8 Suggested module decomposition and LOC

| module | contents | LOC |
|---|---|---|
| `Chakravala/AbstractLattices.lean` | HWedge/HVee/Dist, notation, Bool | 40 |
| `Chakravala/PrimitiveBits.lean` | width-indexed bits, get/ofBools/toString, lemmas | 90 |
| `Chakravala/DeMorgan/TruthValues.lean` | TV N, mask, ops, ⊥/⊤, bv_decide laws | 110 |
| `Chakravala/DeMorgan/TruthTable.lean` | select, parstring, combine (Julia + clean), ops | 170 |
| `Chakravala/DeMorgan/Render.lean` + `Macro.lean` | box table, `truthtable!` | 110 |
| `Chakravala/Dendriform/Tree.lean` | PBTree, graft/left/right/σ/over/under, typed facade | 150 |
| `Chakravala/Dendriform/Order.lean` | BaseTree μ, ΘInt/ΘMax/TreeInteger/TreeRational | 90 |
| `Chakravala/Dendriform/TotalGrove.lean` | Catalan, allTrees, sorted tables, cache, index/bit/decode | 170 |
| `Chakravala/Dendriform/Grove.lean` | Grove, GroveBin, Float16 ppos, ∪, == | 170 |
| `Chakravala/Dendriform/Arith.lean` | ⊣ ⊢ + * (Julia order), memo | 170 |
| `Chakravala/Dendriform/Poset.lean` | covers, <, ≤, between, intervals tools | 170 |
| `Chakravala/Dendriform/Display.lean` + `Compose.lean` | printing, grovedisplay, compositions | 160 |
| `Chakravala/AbstractAnalysis/Countable.lean` | CountableArray/FunctionArray/Series/Product, arithmetic | 280 |
| `Chakravala/AbstractAnalysis/Sequence.lean` | SequenceArray (1-D + last-dim storage), cumsum/cumprod | 150 |
| `Chakravala/AbstractAnalysis/Sets.lean` | pairings, fusc, rationals, Gaussian, primes; pairing proofs | 180 |
| `Chakravala/AbstractAnalysis/Metric.lean` | Metric class, norms, residuals, lipschitz, predicates, supseq | 170 |
| `Chakravala/AbstractAnalysis/Limit.lean` | Limit, orbit family, sum/prod, arithmetic, limit(ϵ), FixedCycle, derivative | 300 |
| `Chakravala/AbstractAnalysis/Magma.lean` | Semimagma, closure/group/cosets/center(+Julia), predicates | 250 |
| `Chakravala/AbstractAnalysis/Perm.lean` | Permutation/Cycle/CycleProduct, Sn/An/Dn, sign; proofs | 220 |
| `Chakravala/Wilkinson/Expr.lean` + `SyntaxTree.lean` | PExpr, interpreter, exprval family | 200 |
| `Chakravala/Wilkinson/FloatRange.lean` + `Analysis.lean` | floatset, stieltjes/simpson/Ω, Analysis/Comparison + print | 200 |
| `Chakravala/Wilkinson/PolyForms.lean` | ℚ[x] expand/horner printers, rational-root factor | 250 |
| `Tests/Small/*.lean` | golden loaders + property tests | 500 |
| **total** | | **≈ 4,300** |

---

## 9. Oracle test plan

General: generators live in `oracle/small/*.jl` and write `oracle/golden/small/<pkg>_<fn>.json`. Use JSON3 (available in juliaenv2) or JSON (juliaenv). Seed `Random.seed!(0x5EED)`. Always run with `--startup-file=no`. Before capturing Dendriform prints, warm the caches silently: `redirect_stdout(devnull) do; Dendriform.Υ(8); end`. Floats go to JSON as strings from `repr` (bit-exact round-trip) **and** as numbers. BigInts go as decimal strings.

### 9.1 AbstractLattices
None needed. Static `example`s: `wedge true false = false`, and the `max`/`min` instance test.

### 9.2 PrimitiveBits (include-based generator, no env)
For each width w ∈ {8,16,32,64,128}: 200 random `UInt_w` values, recording `string`, `b[i]` for i ∈ {-1,0,1..w,w+1}, and `b[2:5]`. Also 50 random Bool vectors of length 1..w → `UInt(PrimitiveBits(v))`. Error cases: empty vector, length w+1, negative Int, overflow.

### 9.3 DeMorgan (juliaenv2)
- `truthvalues.json`: for N ∈ 1..6, 100 random masked `p,q` → `¬p, p∧q, p∨q, p→q, p←q, p↔q` (UInt as hex strings). `select(n,N)` for all n ≤ N ≤ 6. Lifting with ⊥/⊤.
- `truthtable.json`: a random expression generator over N ∈ {1,2,3,4} variables (the set also covers N=6 once): depth ≤ 4 trees over {¬, ∧, ∨, -->, <--, <-->}, 500 expressions. **Include repeated subterms** (e.g. `p ∧ (p ∧ q)`) to exercise the duplicate-class quirk. Record `cols` (hex), `names`, `i`, `j`, `string(t)`. Also `parstring` on 100 generated names plus the edge set from §4.3.4.
- Rendering: PrettyTables is not installed. Keep the two README tables as hand goldens, and add a Julia-side reimplementation of the v2 unicode renderer (≤ 30 lines in the generator) to render the random tables. That makes the renderer itself part of the spec (it is simple).

### 9.4 Dendriform (juliaenv2)
- `totalgroves.json`: d = 0..8, all names in index order plus TreeIntegers; `TreeRational` (both treeshift settings) for d ≤ 5; `Cn(d)` for d ≤ 20 (strings).
- `tree_ops.json`: **all ordered pairs** of trees with deg a + deg b ≤ 6, recording `+`, `⊣`, `⊢` (row name lists in order), `*` for deg a·deg b ≤ 9, `∨`, `/`, `\`, `σ`, `left`, `right`, `⋖`, `⋗`, `<`, `≤`, `>`, `≥` (Tamari) and `between_list`. Include the degree-0 tree as an operand for every op (edge cases).
- `grove_ops.json`: 300 random groves (degree 1..4, random non-zero gbin, **plus** some groves with duplicated rows built via `+`), recording pairwise `+ ⊣ ⊢ *` (names in row order), `∪` (names + dup count), `groveindex`, `grovebit`, `treeindex`, `==` against the sorted form, and `GroveBin` string.
- `display.json`: `sprint(print, x)` for 100 groves with `grovedisplay(false)` and `grovedisplay(true)`; PBTree prints including the empty tree; `GroveBin` strings for d ∈ 1..8 across gbin ∈ {1, 2, 3, 2^k, 2^Cn-1, random} (this exercises Float16 `ppos` formatting including `e-5` and `0.0`).
- `float16_ppos.json`: 2,000 random rationals `100·i/(2^m-1)` (m ≤ 64) → `string(Float16(...))`.
- `compositions.json`: **one fresh Julia process per d** (d = 1..4), all ind ∈ 1..2^Cn(d)-1 (d=4 → 16,383 inds; subsample 500 if slow), recording the count and the printed text.
- `intervals.json`: `intervals(d)`, `intcomp(d)`, `intcompt(d)`, `intervals_full(d)` for d = 2..4 (d=5 if runtime allows).
- Properties (Lean side, no oracle): dendriform axioms, the σ anti-homomorphism, `Y_p + Y_q = Y_{p+q}`, degree homomorphism.

### 9.5 AbstractAnalysis (juliaenv)
- `sets.json`: the first 1,000 terms of Integers, PositiveRationals, Rationals, NonzeroRationals, CantorPairs (buggy), ElegantPairs0/1, GaussianIntegers/Rationals, SternBrocot. `sternbrocot(n)` for n ≤ 10^4.
- `limits.json`: for a fixed list of maps (cos, x/2+1, x↦(x+2/x)/2, Newton for √3, logistic r=2.5, `[x,y]↦M*[x,y]` for a contraction 2×2 matrix): `orbit(f,x0)` (value, n, r), `orbit(f,x0,k)` for k ∈ {1,5,10}, `orbiterror` residual vectors, `FixedCycle(k,f)(x0)`, `collect(orbit(f,x0,5))`. For CountableVectors (1/i², (-1)^i/i, 1/2^i, 1+1/i²): `sum`, `prod`, `L[k]` for k ∈ {1, n-1, n, n+3}, `L[ϵ]` for ϵ ∈ {1e-4, 1e-8}, `L+1`, `2*L`, `L*L`, `map(sqrt,L)`, `collect(L)`, `dot`, `Series`/`Product` evaluations, and the `show` string of each.
- `metric.json`: `supnorm/infnorm/maxabs/minabs` on numbers, vectors, pairs, symbols; `residuals`, `lipschitz`, `isdiverging`, `iscauchy`, `supseq`, `infseq`, `limsup(x,m)`, `liminf(x,m)` over 200 random Float vectors (length 5..30); `derivative`/`derivative2` of sin/exp/x³ at 10 points (plus the `h` values).
- `groups.json`: for N ∈ 1..4: SymmetricGroup order; for all pairs `(p,q)` in S3∪S4: `p*q`, `p/q`, `p\q`, `inv p`, `p^k` (k ∈ -3..3), `decompose` (cycle lists), `order`, `levicivita`. `group([p])` and `magma([p,q])` element order for every pair in S4. `center`/`centralizer`/`normalizer`/`isnormal`/`commutator`/`leftcosets`/`rightcosets` for every subgroup generated by one or two elements of S4 (ordered outputs). Cyclic/modular magmas `magma(g, (a,b)->mod(a*b,n), identity)` for n ≤ 30, all g; Z_n groups via `group([gens], +mod, -mod)`; `cayley` tables; `unityroots(n)` for n ≤ 12 (compare with tolerance).
- Skipped (broken in Julia): `ismonoid`, `iscategory`, `group(::Permutation)`, `DihedralGroup`, `mapmap`, `functionproduct`, `cumsum(::Limit)`, `residuals(::CountableVector)`, `subsemigroup` default. The Lean clean API gets its own property tests for these.

### 9.6 Wilkinson / SyntaxTree (juliaenv; SyntaxTree and Reduce loaded via `Base.require(PkgId)`)
- `exprval.json`: 500 random polynomial ASTs (degree ≤ 9, random integer/rational/float literals, random mixes of expanded/nested/product shapes, including `cal==1` and all-ones literals) → `callcount`, `expravg`, `exprdev`, `exprval`, `sub(Float64,·)`, `abs(·)`, `alg(·)` as `string(expr)`.
- `reduce_forms.json`: for 200 random polynomials with small integer roots/coefficients: `rcall(e,:expand)`, `:horner`, `:factor` (string and `exprval`). This is the target for the Lean `PolyForms` printers. Also `polyhorner/polyfactors/polyexpand` outputs.
- `floatset.json`: the full `collect(floatset(Float64,3000; scale=log))` (3,000 Float64 reprs) plus N ∈ {10, 100, 2999}.
- `stieltjes.json`: for 30 polynomials: `stj[1]` (full vector), `Ω`, `simpson`, `geonorm`, using the **copied kernels** from `probes/small/wk3.jl` (Wilkinson itself cannot load because of PyPlot/Conda). Also the BigFloat variant with ω from Float64, and `exacterr` vectors for the expand/horner/factor triples.
- Tolerances: stj elements rtol 1e-12 (exp/log libm differences); Ω exact (flag borderline overflow points); smp rtol 1e-12.

### 9.7 Cross-package
The AbstractLattices ↔ Grassmann wedge methods are covered by the Grassmann oracle. Cartan's use of `Limit`/`SequenceArray` with `TensorField` states is covered by the Cartan oracle. Make sure the AbstractAnalysis Lean API accepts the state types Cartan needs before freezing it.

---

## Appendix A: consolidated quirks/bugs (reproduce under `Julia.*`, fix in the clean API)

| # | package | quirk | where |
|---|---|---|---|
| 1 | PrimitiveBits | out-of-range index returns `true` | PB:14-17 |
| 2 | PrimitiveBits | `iterate` references undefined `r` | PB:23-27 |
| 3 | DeMorgan | `combine` dedups against original P only, so duplicate classes appear | DM:112-115 |
| 4 | DeMorgan | `¬` names use the last alias and never go through parstring | DM:97 |
| 5 | DeMorgan | PrettyTables v3 API mismatch (`header=`) | DM:168 |
| 6 | Dendriform | `Grove ==` sorts both operands in place | DF/Dendriform.jl:147 |
| 7 | Dendriform | `groveindex` sums duplicate rows | DF/morphism.jl:127-129 |
| 8 | Dendriform | ΘMax memo is wrong if it is extended by more than one degree at a time | DF/morphism.jl:239-247 |
| 9 | Dendriform | the composition cache depends on call order | DF/Dendriform.jl:322-364 |
| 10 | Dendriform | `PBTree(d,i)` ignores the `treecheck` result | DF/Dendriform.jl:97 |
| 11 | Dendriform | `TreeBase(d, s::Integer)` is malformed | DF/morphism.jl:196 |
| 12 | Dendriform | the zero grove doubles as the unit (`0 ⊢ y = y`, `0 + y = y`) | DF/arithmetic.jl:196-198, 227-228 |
| 13 | AbstractAnalysis | the Cantor unpairing formula is wrong | AA/AbstractAnalysis.jl:329 |
| 14 | AbstractAnalysis | `center` returns a greedy commuting subset | AA/magma.jl:240-258 |
| 15 | AbstractAnalysis | cosets are deduplicated by ordered comparison | AA/magma.jl:315-330 |
| 16 | AbstractAnalysis | `iscyclic` tries only the first two generators | AA/magma.jl:150 |
| 17 | AbstractAnalysis | `ismonoid`/`iscategory` are broken | AA/magma.jl:111 |
| 18 | AbstractAnalysis | `subsemigroup` default arg uses the undefined `Semigroup` | AA/magma.jl:194 |
| 19 | AbstractAnalysis | `group(::Permutation)` / `DihedralGroup` / `commutator(::Perm,::Perm)` are broken | AA/magma.jl:187-189; AA/perm.jl:51, 130-134 |
| 20 | AbstractAnalysis | `order(::Cycle)` is the transposition count | AA/perm.jl:108 |
| 21 | AbstractAnalysis | `Cycle ==` ignores orientation | AA/perm.jl:119 |
| 22 | AbstractAnalysis | `isbounded` is inverted | AA/metric.jl:391-396 |
| 23 | AbstractAnalysis | `mapmap`, `functionproduct`, `cumsum(::Limit)`, `countresiduals` use undefined variables | AA/AbstractAnalysis.jl:94, 184-189; AA/metric.jl:224-225, 343-345 |
| 24 | AbstractAnalysis | `CountableMatrix{T}(f,n,m)` / `FunctionMatrix{T}(f,n,m)` build size `(n,)` | AA/AbstractAnalysis.jl:63, 146 |
| 25 | AbstractAnalysis | `limit(L,ϵ)` resets `v0` to the old final and counts `n = old + iters + 1` | AA/metric.jl:482 |
| 26 | AbstractAnalysis | `supnorm` of an array is the 2-norm | AA/metric.jl:60 |
| 27 | Wilkinson | `simpson` gives p[1] weight 5 and divides by `3n·range` | WK/Wilkinson.jl:69-74 |
| 28 | Wilkinson | `Ω` drops the last point | WK/Wilkinson.jl:50 |
| 29 | Wilkinson | `stieltjes` returns allocation bytes (nondeterministic) | WK/Wilkinson.jl:65 |
| 30 | SyntaxTree | `exprdev` divides by `callcount-1`, not by the scalar count, and includes `^` exponents | ST/exprval.jl:53 |

## Appendix B: probe scripts
`/private/tmp/claude-502/-Users-alokbeniwal-Grassmann/c6cc2308-bfca-4b9a-ad33-d89b110132a8/scratchpad/probes/small/`:
- `dend1-6.jl`, `dm1-2.jl`: juliaenv2
- `aa1-4.jl`, `wk1-4.jl`: juliaenv (SyntaxTree and Reduce via `Base.require(PkgId)`; `wk3.jl` holds verbatim copies of the Wilkinson numeric kernels)
- `pb1.jl`: plain `include`

These are the seeds for the §9 generators.
