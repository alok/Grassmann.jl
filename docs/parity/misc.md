# Parity matrix: misc packages (Fatou, Dendriform, DeMorgan, AbstractLattices, AbstractAnalysis, Wilkinson, PrimitiveBits, Clifford, Heisenberg)

Audited 2026-09-25 against `/Users/alokbeniwal/Grassmann` @ `0ac54fdd` (read-only).
Julia sources `/Users/alokbeniwal/chakravala/<Pkg>.jl`. The export lists were read with `names(Pkg)` in
`scratchpad/juliaenv` (AbstractLattices, AbstractAnalysis, Fatou) and `scratchpad/juliaenv2`
(DeMorgan, Dendriform). PrimitiveBits, Wilkinson (it does not load: PyPlot/Conda), Clifford and
Heisenberg were read from source. The API inventories are §2 of `docs/port-notes/{small-algebra,fatou,applied-misc}.md`.

Status legend:
* **DONE**: implemented and tested against the oracle, or statically (`decide`/`#guard`) where there is nothing to oracle.
* **PARTIAL**: some methods, types or options are missing, or the code is untested.
* **MISSING**: no Lean equivalent.
* **IN_PROGRESS**: covered by in-flight work.
* **SKIP**: Julia-specific, with the justification given in the row.

Effort: S < ½ day, M ≈ 1–2 days, L > 2 days.

Lean paths are relative to the repo root. `Julia.*` means the port reproduces a documented Julia quirk under
a `Julia` namespace and fixes it in the clean API.

Performance references (Julia 1.13, this machine, measured for this audit, best of 5):

| operation | Julia |
|---|---|
| Dendriform `Grove(5)+Grove(4)` (Y9, 4862 rows) | 10.0 ms |
| Dendriform `Grove(3)*Grove(3)` | 9.5 ms |
| Dendriform `GroveBin(Grove(4)+Grove(3))` | 1.0 ms |
| Dendriform `between([1..6],[6..1])` | 31 ms |
| DeMorgan N=6 table expression (11 connectives) | 32 µs |
| AbstractAnalysis `sum(CountableVector(i->1/i^2,10))[1e-10]` (100 002 steps) | 0.13 ms |
| AbstractAnalysis `orbit(cos,1.0)` | 0.75 µs |
| AbstractAnalysis `isgroup(S5)` | 36 ms |
| AbstractAnalysis `magma([2-cycle gens of S6])` | 2.5 s |

The Lean side was **not** measured. The disk had only ~0.9 GiB free (`/System/Volumes/Data` 100% full), so no
scratch build was possible. Fatou is the only package here with measured Lean-vs-Julia numbers (docs/PERF.md
2026-09-24): Lean is at parity with a handwritten Julia kernel and 30–200× faster than Fatou.jl.

---

## 1. AbstractLattices.jl (exports `∧ ∨ dist wedge vee`)

| Julia symbol | Lean name(s) + file | status | gap description | effort |
|---|---|---|---|---|
| `wedge` (generic function) | `AbstractLattices.HWedge.wedge` (`AbstractLattices/Basic.lean`) | DONE | typeclass replaces the generic function; static tests in `Tests/AbstractLattices.lean` | – |
| `vee` (generic function) | `AbstractLattices.HVee.vee` (`AbstractLattices/Basic.lean`) | DONE | as above | – |
| `∧` (`const ∧ = wedge`) | none in AbstractLattices. Grassmann's scoped `∧` (`Grassmann/Notation.lean:65`) maps to **`AbstractTensors.Wedge`** (`AbstractTensors/Ops.lean:110`), a different class | PARTIAL | In Julia there is one function shared by AbstractTensors→Grassmann, DeMorgan and Dendriform. In Lean `AbstractTensors.Wedge`/`Vee` are separate classes that never import AbstractLattices, so `∧`/`∨` cannot reach the Bool/TruthValues/TruthTable/Tree/PBTree instances. The AbstractLattices module doc claims the opposite (doc bug). | M |
| `∨` (`const ∨ = vee`) | same as `∧` (`Grassmann/Notation.lean:67` → `AbstractTensors.Vee`) | PARTIAL | same split: Dendriform graft `HVee Tree` and DeMorgan `HVee` have no infix anywhere | (same fix) |
| `dist` | `AbstractLattices.Dist.dist` | DONE | stub class, as in Julia (no methods) | – |
| `wedge(x)`, `vee(x)` unary identity | `wedge₁`, `vee₁`; folds `wedgeAll`, `veeAll` | DONE | – | – |
| `wedge(::Bool,::Bool)`, `vee(::Bool,::Bool)` | `instance HWedge Bool`, `HVee Bool` + `LawfulDistribLattice Bool` | DONE | static `decide` tests | – |
| test-file `∧=min`, `∨=max` on numbers | `MinMax α` wrapper with lawful instances (Nat, Int) | DONE | – | – |

## 2. PrimitiveBits.jl (exports `PrimitiveBits8/16/32/64/128`)

| Julia symbol | Lean name(s) + file | status | gap description | effort |
|---|---|---|---|---|
| `PrimitiveBits8/16/32/64/128` types | `PrimitiveBits.Bits w` + abbrevs `PrimitiveBits8…128` (`PrimitiveBits/Basic.lean`) | DONE | oracle `oracle/golden/primitivebits/bits.json` (`Tests/PrimitiveBits.lean`) | – |
| `W(b::UIntW)` / `UIntW(b::W)` | `ofUInt8…ofUInt64`, `toUInt8…toUInt64`, `ofBitVec`, `toNat`, `ofNatMod 128` | DONE | Lean has no `UInt128`, so 128-bit goes through `ofNatMod`/`toNat` | – |
| `W(b::Integer)` (InexactError) | `ofInt?`, `ofNat?` (`Except`) | DONE | error cases oracle-checked | – |
| `W(::Vector{Bool}/BitVector)` | `ofBools` (`Except`, Julia's parse errors), total `ofVector` | DONE | – | – |
| `getindex(b,i)` (out of range → `true` quirk) | checked `b[i]` (`GetElem`, static bounds proof), `get?`, `Julia.getindex` | DONE | quirk proven: `julia_getindex_out_of_range` | – |
| `getindex(b, r::UnitRange)`, `b[:]` | `Julia.getRange`, `toList`/`toArray` | DONE | – | – |
| `firstindex`, `lastindex`, `length` | `firstIndex`, `lastIndex`, `length` | DONE | – | – |
| `iterate` (broken in Julia) | `ForIn m (Bits w) Bool` (intended LSB-first) | DONE | intended semantics, property-tested | – |
| `print`/`show` | `ToString`, `Repr` (`Bits.toString`) | DONE | – | – |
| `==` | `DecidableEq` | DONE | – | – |

## 3. DeMorgan.jl (exports `TruthValues Tautology TruthTable @truthtable ⟂ ⊥ ⊤ ¬ ∧ ∨ --> <-- <--> → ← ↔`)

| Julia symbol | Lean name(s) + file | status | gap description | effort |
|---|---|---|---|---|
| `TruthValues{N}` | `DeMorgan.TruthValues N` (`DeMorgan/TruthValues.lean`, `BitVec (2^N)`, any N) | DONE | oracle `truthvalues.json`; laws by `bv_decide`/ext | – |
| `TruthValues()`, `TruthValues(p::Bool...)` | `TruthValues.bot`, `TruthValues.ofBools`, `ofNat`, `toNat` | DONE | – | – |
| `⟂`, `⊥` (N-polymorphic `TruthValues{0}(0)`) | `TruthValues.bot` (implicit N) | PARTIAL | no `⊥`/`⟂` notation; users write `TruthValues.bot` (oracle-checked lifting) | S |
| `Tautology`, `⊤` | `TruthValues.top` | PARTIAL | no `⊤` notation; the singleton `Tautology` type is subsumed by `top` (fine) | S (with ⊥) |
| `(::TruthValues{0})(t...)`, `(::Tautology)(t...)` callables | – | SKIP | constant functions that only exist for Julia dispatch; `bot`/`top` cover them | – |
| `wedge`/`∧`, `vee`/`∨` on TruthValues | `HWedge`/`HVee` instances, `and`/`or`, `&&&`/`\|\|\|` | PARTIAL | methods DONE (oracle). The **infix `∧`/`∨`** is unavailable (see AbstractLattices row). README example 2 `((p-->q)∧(q-->r))-->(p-->r)` has to be written with `&&&` (`Tests/DeMorgan.lean:67`) | (AL fix) |
| `&`, `\|` | `AndOp`/`OrOp` (`&&&`, `\|\|\|`) | DONE | – | – |
| `!`/`¬` | `TruthValues.not`, scoped prefix `¬` (`DeMorgan/TruthTable.lean:41`), `Complement` | DONE | – | – |
| `-->`/`→`, `<--`/`←`, `<-->`/`↔` | `imp`/`rimp`/`iff`, scoped `⇒ ⇐ ⇔` | DONE | tokens renamed: `-->` starts a Lean comment and `→ ← ↔` are core tokens; justified | – |
| lifting `op(TV{0},TV{N})`, `op(⊤,TV{N})` | by elaboration of implicit-N `bot`/`top` | DONE | oracle `bot_or`, `and_top`, … | – |
| `show(::TruthValues)` | `TruthValues.toString` (`⊥`/`⊤`/`TruthValues{N}(0x…)`) | DONE | oracle `show` | – |
| `TruthTable{N,M}` + ctors | `TruthTable N` (runtime M), `TruthTable.Class`, `ofColumn`, `proj`, `vars` | DONE | oracle `truthtable.json` (cols, names, i, j) | – |
| `string(t)` | `TruthTable.toString` | DONE | – | – |
| `combine` (internal, dup-class quirk) | `TruthTable.combine` (Julia-literal), `TruthTable.Clean.*` (fixed) | DONE | quirk reproduced and fixed | – |
| `parstring`, `select`, `tautology`/mask (internal) | `parstring`, `select`, `projections`, `mask` | DONE | oracle `parstring.json` | – |
| binary/unary ops on TruthTable | `and or imp rimp iff not` + instances, `ofFormula`, `ofFormulaClean` | DONE | – | – |
| `pretty_table`/`show(::TruthTable)` | `TruthTable.render`, `Repr` | DONE | both README tables reproduced verbatim (`#guard`) | – |
| `@truthtable p q` (binds REPL globals) | `truthtable p q in e` term macro (`DeMorgan/TruthTable.lean:308`) | PARTIAL | term-scoped only; there is no command form that binds the projections as top-level defs the way the README session does | S |
| (Lean extra) `Formula`, `isTautology_iff` | `DeMorgan/TruthValues.lean` | DONE | soundness/completeness of the bit-parallel checker | – |

## 4. Dendriform.jl

| Julia symbol | Lean name(s) + file | status | gap description | effort |
|---|---|---|---|---|
| `PBTree` | `Dendriform.Tree` (inductive), typed `PBTree n` (`Dendriform/Tree.lean`) | DONE | oracle `tree_ops.json` | – |
| `PBTree(deg, ind)`, `PBTree(::Vector)` | `treeOfIndex?`, `Tree.ofName?`, `Tree.name` | DONE | – | – |
| `Grove` + ctors (`Grove(d)`, `Grove(d,s)`, `Grove(::BitVector)`, `Grove(::Vector{PBTree})`, `Grove(t)`) | `Grove n`, `Grove.total`, `ofIndex`, `SomeGrove.ofBits?`, `ofList?`, `ofNames?`, `ofTree` + `Coe` (`Dendriform/Grove.lean`) | DONE | oracle `grove_ops.json`, `degenerate.json` | – |
| `GroveBin` (+ `ppos` Float16) | `GroveBin`, `ofGrove`, `ppos` (JuliaBase.Float16), `toGrove` (`Dendriform/Display.lean`) | DONE | oracle `display.json`, `float16.json` | – |
| `==` (sorts in place) | `Grove.Equiv` (`≅`, perm), `Julia.eq` | DONE | pure (no mutation) | – |
| `Cn` | `catalan` (`Dendriform/Tree.lean:274`) | DONE | – | – |
| `∨`/`graft` | `Tree.graft`, `PBTree.graft`, `HVee` instances | PARTIAL | functions DONE (oracle); **no infix `∨`** (AbstractLattices split) | (AL fix) |
| `left`, `right` | `Tree.left`, `Tree.right`, `PBTree.split` | DONE | – | – |
| `σ` | `Tree.σ`, `PBTree.σ`, `Grove.σ` | DONE | involution proven | – |
| `over`/`/`, `under`/`\` | `Tree.over` (`Div`), `Tree.under` (`SDiff`), `PBTree.over` (`HDiv`), `PBTree.under` | DONE | `σ_over` proven | – |
| `dashv`/`⊣`, `vdash`/`⊢` | `Tree.dashv/vdash`, `Grove.dashv/vdash` (scoped `⊣ ⊢`), `Julia.dashv/vdash` | DONE | axioms proven for all trees (`Dendriform/Axioms.lean`) | – |
| `+`, `*` | `Tree.sum`, `Tree.mul`, `Grove` `HAdd`/`HMul` (degree-typed), `Julia.add/mul` | DONE | Julia row orders reproduced | – |
| `∪` (+ `@info` dup count) | `Grove.union` (`Union`), `Grove.unionCount` | DONE | – | – |
| `⋖`, `⋗` | `Tree.covers`, `Tree.coveredBy` (`Dendriform/Poset.lean`) | PARTIAL | functions DONE (oracle `poset.json`); no `⋖`/`⋗` notation | S |
| `<`, `>`, `≤`, `≥` on trees (Tamari) | `Tree.tamariLt/Gt/Le/Ge` | PARTIAL | functions DONE (oracle, incl. README `[2,1,7,4,1,3,1] < [2,1,7,4,3,2,1]`); no `LT`/`LE` instances, so `a < b` does not parse on trees | S |
| `<`, `≤` on groves (index order) | `Grove.indexLt`, `indexLe` | DONE | – | – |
| `between`/`⊴` | `Tree.betweenList`, `between` (PBTree→Grove) | PARTIAL | functions DONE; no `⊴` notation | S |
| `posetnext`, `posetprev` | `posetNext`, `posetPrev`, `nextList`, `prevList` | DONE | – | – |
| `treecheck`, `grovecheck` | `treeCheck`, `groveCheck` (Tree validity is by construction) | DONE | – | – |
| `treeindex` (tree/grove/d), `treeindexCn` | `Tree.treeIndex` (binary search), `Grove.treeIndices`, `treeIndexCn`, `treeIndexOfInteger` | DONE | – | – |
| `groveindex`, `grovebit` | `Grove.index` (with multiplicity), `Grove.bits` | DONE | – | – |
| `grovesort!` | `Grove.sort`, `Grove.canonical` | DONE | – | – |
| `grovesort(tf)` toggle | – (always sorted) | SKIP | unsorted build order dropped, as the port notes recommend; ordering is canonical | – |
| `treeshift(tf)`, `grovedisplay(tf)` toggles | explicit `treeshift`/`display` arguments (`Tree.treeRational`, `Tree.print`, `Grove.print`) | DONE | global state replaced by arguments | – |
| `print` (PBTree/Grove/GroveBin, display mode) | `Tree.print`, `Grove.print` (`ToString`, `Repr`), `GroveBin.toString` | DONE | oracle `display.json` | – |
| `grovecomposition` | `groveComposition`, `compositions`, `compose` (`Dendriform/Compose.lean`) | DONE | fresh-process semantics; oracle `compositions_{1..4}.json` | – |
| `BaseTree`/`TreeBase`/`TreeLoday` (documented in library.md) | `Tree.mu`, `Tree.ofMu?`, `muString` (`Dendriform/Order.lean`) | DONE | – | – |
| `TreeInteger`, `TreeRational`, `ΘInt`, `ΘMax` (internal) | `treeInteger`, `treeRational`, `treeRationals`, `thetaInt`, `thetaMax` (closed form) | DONE | – | – |
| `GroveError`, `CnInv`, `LeftInherited`, `RightInherited`, `PrimitiveTree` | `groveError`, `catalanInv?`, `leftInherited`, `rightInherited`, `isPrimitive` | DONE | – | – |
| `intervals`, `intcomp`, `intcompt`, `intervals_full`, `print_*_bin` | `intervals`, `intcomp`, `intcompt`, `intervalsFull`, `printIntervalBin/IntcompBin/IntcomptBin` | DONE | oracle `intervals.json` | – |
| vector-as-tree coercions (`[1,2]∪[2,1]`, promote rules) | `Tree.ofName?`/`Grove.ofNames?` (Option) | PARTIAL | README `Grove(3,7) ⊣ [1,2]∪[2,1]` is expressible and oracle-tested, but verbose (Option plumbing); there is no checked literal syntax | S |
| performance (Julia refs above) | `Tests/Dendriform.lean` (no bench) | IN_PROGRESS | no Lean timing; Bench/Harness in flight | – |

## 5. AbstractAnalysis.jl

| Julia symbol | Lean name(s) + file | status | gap description | effort |
|---|---|---|---|---|
| `AbstractCountable`, `CountableFunction`, `AbstractPermutation` | – | SKIP | abstract dispatch supertypes; Lean uses concrete structures and classes | – |
| `CountableArray`, `CountableVector`, `CountableMatrix` | `CountableArray α N`, `CountableVector α`, rank-2 `CountableArray α 2` (`AbstractAnalysis/Countable.lean`) | DONE | oracle `sets.json`/`limits.json` | – |
| `CountableArray(n...)` index-tuple grid | `CountableArray.grid n m` | PARTIAL | rank 2 only (Julia takes any rank) | S |
| `Ones`, `Zeros`, `Naturals`, `Integers` | `Ones`, `Zeros`, `Naturals`, `Integers` (`Countable.lean`, `Sets.lean`) | DONE | – | – |
| `counter`, `resize!(::CountableVector)`, call `(x)(n)` | `.f`, `withLen` | DONE | pure | – |
| `map`/`broadcast`, unary ops (`inv abs exp log sin …`) on countables | `CountableVector.map`, `CountableArray.map` | DONE | named unary methods become `map f`; oracle | – |
| arithmetic `⊙ ∈ {+ - * / ^}` on countables | `Add/Sub/Mul/Div/Neg`, `HAdd/HSub/HMul/HDiv` with scalars, `HPow (CountableVector) β` | PARTIAL | missing `Number ^ Countable`; `CountableArray` has only `+ - *` | S |
| `dot` | `CountableVector.dot` (a `Limit`) | DONE | oracle | – |
| `countabletuple`, `countableproduct` | `countableTuple`, `countableProduct`, `countableProduct3` | DONE | – | – |
| `FunctionArray`, `FunctionVector`, `FunctionMatrix` | `FunctionVector β α` (`term`, `eval`, `withLen`, `map`, `powers`) | PARTIAL | only rank 1: no `FunctionMatrix`/N-d `FunctionArray` (Julia's needs `Fix{3}`); arithmetic has `+ *` and scalar `*` only (no `- / ^`) | S |
| `functiontuple`, `functionproduct`, `mapmap` | – | SKIP | broken in Julia (undefined variables, quirk #23); no defined semantics to port | – |
| `Series` (+ `dot(c, f)`, call, `resize!`) | `Series`, `Series.eval`, `FunctionVector.series` | DONE | oracle `series_pow_*` | – |
| `Product` (+ call, `log(::Product)`, `resize!`) | `Product`, `Product.eval`, `FunctionVector.product` | PARTIAL | `log(::Product) = sum(log(f))` missing | S |
| `SequenceArray`, `SequenceVector`, `SequenceMatrix` | `SequenceArray σ S` over `LastDimStorage` (`Array`, `FloatArray`, `SlabArray`), `SequenceVector` (`AbstractAnalysis/Sequence.lean`) | PARTIAL | no `SequenceMatrix` alias; `SlabArray` (the multi-dim/ElasticArray storage Cartan needs) is **untested** | S |
| `extract`, `assign!`, `resize_lastdim!` | `LastDimStorage.extract`, `.push`, `SequenceArray.resize/get/take` | DONE | – | – |
| `cumsum`, `cumprod` (countables) | `CountableVector.cumsum/cumprod` (Julia pairwise accumulate) | DONE | oracle | – |
| `cumsum`/`cumprod(::Limit)` | – | SKIP | broken in Julia (undefined `D`) | – |
| `sternbrocot`, `SternBrocot` | `fusc` (+ proofs), `sternBrocotStep`, `SternBrocot` (`Sets.lean`) | DONE | – | – |
| `integer`, `positiverational`, `rational`, `nonzerorational` | same names | DONE | – | – |
| `PositiveRationals`, `Rationals`, `NonzeroRationals` | same | DONE | oracle | – |
| `CantorPairs` (buggy), `cantorinversion` | `CantorPairs` via `Julia.cantorInversion`; correct `cantorPair`/`cantorUnpair` | DONE | quirk reproduced and fixed | – |
| `ElegantPairs0/1`, `ElegantPairs`, `elegantpair`, `elegantproduct`, `elegantinversion` | `ElegantPairs0/1`, `elegantUnpair`, `elegantUnpairFrom`, `elegantPair` (inverse proofs), `elegantProduct` | DONE | – | – |
| `GaussianNaturals/Integers/Rationals` | same | DONE | – | – |
| `PrimeIntegers`, `PrimeCache`, `prime` (PrimesExt) | same (`Sets.lean`) | DONE | – | – |
| ModsExt (`gequal`/`isinvertible` for `AbstractMod`) | – | MISSING | no `ApproxEq (Fin n)` instance or modular `Law` helpers (`+`/`*` mod n with inverse) | S |
| `Semimagma`, `grouplaw`, `groupinverse` | `Semimagma T L`, `Law` (`op`, `inv`), `Law.mul`, `Law.add` (`AbstractAnalysis/Magma.lean`) | DONE | oracle `groups.json` | – |
| `order(G)`, `abs(G)`, `order(n,f,g)` | `Semimagma.order`, `(cyclic p).order` | DONE | – | – |
| `orders(G)` | – | MISSING | per-element cyclic order vector | S |
| `iseven(G)`, `isodd(G)` (Semimagma) | – | MISSING | only `Perm.isEven` exists (no `isOdd`) | S |
| `==`, `∈`, `issubset` | `setEq` (`BEq`), `mem`, `subset` | DONE | – | – |
| `compose`, `∘` | `Semimagma.compose`, `composeLeft`, `composeRight` | DONE | – | – |
| `*`, `+` with Number/element/Semimagma | `composeLeft g H (F := (· * ·))` | PARTIAL | no `HMul`/`HAdd` instances, so `Complex(2,0)*m` must be spelled out | S |
| `cayley` | `Semimagma.cayley` | DONE | – | – |
| `ismagma`, `isassociative`, `isinvertible`, `issemigroup`, `isgroup`, `isabelian` | `isMagma`, `isAssociative`, `isInvertible`, `isSemigroup`, `isGroup`, `isAbelian` | DONE | kernel-checked on S3/S4 | – |
| `ismonoid` (broken in Julia) | `isMonoid G e` (explicit identity) | DONE | intended semantics | – |
| `iscategory`, `issemicategory`, `isgroupoid` | – | MISSING | trivial aliases (`= isMonoid`, `= isSemigroup`, `= isGroup`) | S |
| `iscyclic` | `isCyclic` (correct), `Julia.isCyclic` (first-two quirk) | DONE | – | – |
| `magma` (element / vector / closure) | `cyclic`, `magma`, `closeArray` | DONE | – | – |
| `group` | `group`, `groupOf` | DONE | – | – |
| `subsemigroup`, `subgroup`, `issubgroup` | same (`subsemigroup`, `subgroup`, `isSubgroup`) | DONE | – | – |
| `center` (buggy), `centralizer`, `isnormal`, `normalizer`, `commutator` | `center` (correct) + `Julia.center`, `centralizer`, `isNormal`, `normalizer`, `commutator` | DONE | – | – |
| `leftcosets`, `rightcosets`, `G / N` | clean `leftCosets/rightCosets`, `Julia.leftCosets/rightCosets/quotient` | DONE | – | – |
| `unityroots` | `unityRoots` | DONE | oracle (tolerance) | – |
| `Permutation` (+ `p[i]`, `p(i)`, `p(q)`, `inv`, `^`, `/`, `\`, `one`, `isone`, `iseven`) | `Perm N` (bijectivity carried in the type), `apply`, `mul`, `inv`, `zpow`, `div`, `ldiv`, `one`, `isEven`, group laws proven (`AbstractAnalysis/Perm.lean`) | DONE | `isodd` alias missing (see above) | – |
| `Cycle{N}` | `Cycle N` (`eval`, `toPerm`, `ofList`, `toList`, `transpositionCount`), `Julia.cycleEq` | DONE | – | – |
| `Transposition{N}` | – | MISSING | alias for a 2-cycle | S |
| `CycleProduct`, `decompose`, `order(::CycleProduct)` | `Perm.cycles : List (List (Fin N))`, `cycleProduct : List (Cycle N) → Perm N` | PARTIAL | no `CycleProduct` type and no `decompose : Perm N → Cycle ⊕ CycleProduct` (Julia returns a `Cycle` for one cycle); decomposition is only available as raw lists | S |
| `order(::Perm/::Cycle)`, `levicivita` | `transpositionCount`, `sign` (homomorphism kernel-checked on S3/S4), `groupOrder` | DONE | – | – |
| `isdisjoint(::Cycle,::Cycle)` | `Cycle.isDisjoint` | DONE | – | – |
| `isabelian(::Cycle,::Cycle)` | – | MISSING | "disjoint or equal" predicate | S |
| `commutator(::Perm,::Perm)` (broken in Julia) | – | MISSING | intended element commutator `g⁻¹h⁻¹gh` | S |
| `SymmetricGroup`, `AlternatingGroup`, `DihedralGroup` (broken in Julia) | same names (Dihedral = intended) | DONE | – | – |
| `@metric`, `@norm` | `Metric`, `Normed` classes (instances for Float, Complex, FloatArray, Array) (`AbstractAnalysis/Metric.lean`) | DONE | macro-generated methods become instances | – |
| `supnorm`, `infnorm`, `maxabs`, `minabs` | same | DONE | oracle `metric.json` | – |
| `residual`, `residuals`, `lipschitz`, `residualproduct` | `Limit.residual`, `residuals`, `CountableVector.residuals`, `lipschitz`, `residualProduct` | DONE | – | – |
| `isconverging`, `isdiverging`, `iscauchy`, `ismonotonic`, `isincreasing`, `isdecreasing` | `isConverging`, `isDiverging`, `isCauchy`, `isMonotonic`, `isIncreasing`, `isDecreasing`; `isBounded` + `Julia.isBounded` | DONE | – | – |
| `supseq`, `infseq` (suffix / windowed) | `supseq`, `infseq`, `CountableVector.supseq/infseq` | DONE | – | – |
| `limsup`, `liminf` | `limsup`, `liminf` (Array, `m`) | PARTIAL | missing the `AbstractCountable` methods (`limit(supseq(x,m), args...)`, which return a `Limit`) and the 3-arg `(x,m,n)` form | S |
| `Limit` (+ `first/last/initial/final/length/residual`, call, `show`) | `Limit S V`, `Indexed`, `Derived`, `first`, `last`, `length`, `residual`, `rerun`, `toJulia`/`ToString` (`AbstractAnalysis/Limit.lean`) | DONE | oracle show strings incl. `n → 100002` | – |
| `Limit(v0,n,F,D)`, `L[i]`, `L[ϵ]`, `collect(L)` | `ofIterate`/`iterate`, `seek`, `limitEps`, `collect`, `collectSeq` | DONE | – | – |
| `map(f,L)`, unary ops on Limit | `Limit.map` | DONE | – | – |
| Limit arithmetic `⊙ ∈ {+ - * / ^}` | `HAdd/HSub/HMul/HDiv` scalar⊙L, L⊙scalar; `L+L`, `L*L`, `L-L` | PARTIAL | missing `^` (scalar and Limit) and `L/L` | S |
| `sum`, `prod` (countable and Limit) | `CountableVector.sum/prod`, `Limit.sum/prod`, `prodNaturals` | DONE | oracle | – |
| `limit` (Limit/countable/n/ϵ, SequenceArray) | `CountableVector.limit/limitEps`, `SequenceArray.limit`, `Limit.limitEps` | DONE | – | – |
| `orbit`, `orbiterror`, `orbithold`, `FixedCycle` | `orbit`, `orbitN`, `orbitError`, `orbitNTrace`, `orbitHold`, `FixedCycle.run/withLen` | PARTIAL | functions DONE (oracle). The metric has no default: Julia's `orbit(cos, 1.0)` defaults `d = supnorm`, while Lean requires `(d := …)` on every call (`Tests/AbstractAnalysis/Limits.lean:64`). Cartan-facing | S |
| `derivative`, `derivative2` | same (Float) | DONE | oracle | – |
| performance: `Semimagma` membership | linear `ApproxEq` scan (`Magma.lean:76-83`) | PARTIAL | same O(n) `∈` as Julia (2.5 s for a 720-element closure); the port notes (§8.6) planned a `HashSet` side index for exact types, not done | S |
| performance: `Limit` loops (`sum(x)[1e-10]` 0.13 ms in Julia) | `Limit (Indexed Float) Float` | IN_PROGRESS | unmeasured; risk of a boxed `Indexed` per step; Bench/Harness in flight | – |

## 6. Wilkinson.jl (exports `PolynomialAnalysis PolynomialComparison plot factor expand horner polyfactors polyexpand polyhorner`) + SyntaxTree parts

| Julia symbol | Lean name(s) + file | status | gap description | effort |
|---|---|---|---|---|
| Julia `Expr` (input language) | `JExpr`, `Lit`, `jl⟪…⟫` quotation, `JExpr.parse`, `toJulia` (`Wilkinson/Expr.lean`, `Parse.lean`) | DONE | – | – |
| `PolynomialAnalysis` (+ print) | `PolynomialAnalysis`, `.make`, `.toJulia` (`Wilkinson/Analysis.lean`) | DONE | oracle `comparison.json`; REDUCE 2-D display → infix (justified) | – |
| `PolynomialComparison` (+ print) | `PolynomialComparison.make/ofForms/ofReduce`, `.toJulia`, `labels` | PARTIAL | DONE except the `"r"` (rounded factor) form, which is never produced (`rxtra = false`) | (see `factor`) |
| `plot(::PolynomialComparison)` | `PolynomialComparison.plotData` (root); figure in `gallery/Gallery/Wilkinson.lean` | DONE | rendering lives in the gallery package (LeanPlot) | – |
| `expand` (REDUCE) | `Wilkinson/Reduce.lean` `expand` (ℚ[x], REDUCE shapes) | DONE | oracle `reduce.json` | – |
| `horner` (REDUCE) | `horner` | DONE | oracle | – |
| `factor` (REDUCE) | `factor` (`Wilkinson/Poly.lean`: rational roots + bounded Kronecker) | PARTIAL | no full Zassenhaus (factors found only by a full search are missed); `factor` under `on rounded` (numeric complex roots) is **missing** | M |
| `polyfactors`, `polyexpand`, `polyhorner` | same names (`Wilkinson/Reduce.lean`) | PARTIAL | output goes through the canonical expand/horner shapes; the `Reduce.Algebra` intermediate shapes are not reproduced (documented) | S |
| `floatset`, `geonorm`, `Ω`, `stieltjes`, `simpson`, `exacterr`, `renormalize!`, `errval`, `optimal` | `floatset`/`floatset32`/`logset`, `geonorm`, `Ω`, `stieltjes`, `simpson`, `exacterr`, `renormalize`, `errval`, `optimal` | DONE | bit-exact (Julia exp/log kernels, 256-bit BigFloat); oracle `ranges/kernels/stieltjes.json` | – |
| `NumericalData` (abstract) | – | SKIP | abstract supertype only | – |
| `testpoly`, `tests` | `testpoly`, `Reduce.tests` | DONE | allocation tie-break dropped (nondeterministic in Julia) | – |
| bytes allocated | `0` | SKIP | nondeterministic in Julia | – |
| ST `callcount`, `sub`, `abs`, `alg`, `expravg`, `exprdev`, `exprval` | same (`Wilkinson/SyntaxTree.lean`) | DONE | oracle `exprval.json` | – |
| ST `genfun`/`genlatest`/`@genfun` | `SyntaxTree.eval` (interpreter over `JNum`) | DONE | eval-and-invokelatest becomes an interpreter | – |
| ST `linefilter!` | – | SKIP | strips `LineNumberNode`s, which `JExpr` does not have | – |
| performance (3000-point Stieltjes × forms, 256-bit BigFloat) | – | IN_PROGRESS | Julia cannot load Wilkinson here (PyPlot); unmeasured on both sides; Bench/Harness in flight | – |

## 7. Fatou.jl (exports `fatou juliafill mandelbrot newton basin orbit plot`)

| Julia symbol | Lean name(s) + file | status | gap description | effort |
|---|---|---|---|---|
| `ComplexBundle` | – | SKIP | abstract dispatch type | – |
| `Rectangle` (∂ scalar/2-vec/4-vec, UInt16 n) | `Bounds` (`square`, `interval`, explicit), `Rectangle` (`rows` ties-to-even, `cols`, `check`) (`Fatou/Grid.lean`) | DONE | oracle `grids.json` (bit-exact axes) | – |
| `ComplexRectangle`, `ComplexRectangle(Ω::Matrix)` | `Plane rows cols`, `Plane.ofFn`, `Rectangle.grid`, `Plane.pixelBounds` | DONE | – | – |
| `Define` (fields/kw) | `Spec`, `Define`, `Options`, `Number` (`Fatou/Define.lean`) | PARTIAL | the map is a Lean closure and the title text is a hand-written `label`; Julia takes one `Expr` and derives F, Q, the title and (Newton) the derivative from it (see the Newton/basin rows) | M |
| `juliafill` | `juliafill` | DONE | oracle catalog (`Tests/Fatou/Catalog.lean`, README R2 at full resolution) | – |
| `juliafill(E; newt=true, m)` (undocumented kw) | – (use `newton`) | PARTIAL | the mode is not exposed from `juliafill`; `newton` has different defaults (ϵ=0.01, m=1) | S |
| `mandelbrot` | `mandelbrot` (optional `df` for the `m ≠ 0` Newton switch) | PARTIAL | Julia switches to Newton when `m ≠ 0` using REDUCE's derivative; Lean needs a hand-supplied `df` | (Newton fix) |
| `newton` | `newton f df (map := …)` | PARTIAL | Julia derives `df` **and REDUCE's factored Newton map** symbolically. Lean needs `df` by hand, and bit-exact Julia rasters additionally need REDUCE's factored map passed as `map` (the unfactored `newtonMap` rounds differently). README R4/R5 are reproduced only because the tests hard-code REDUCE's maps | L |
| `fatou` (Define/ComplexRectangle/Rectangle/FilledSet/Define chaining) | `fatou`, `Define.onPlane`, `FilledSet.chain`, `refatou`, `computeWith` (`Fatou/Kernel.lean`) | DONE | oracle `chain.*` | – |
| `(K::Define)(Z)`, `(K::FilledSet)(Z)` call syntax | `chain`/`onPlane` | DONE | no `CoeFun` sugar (cosmetic) | – |
| `FilledSet` | `FilledSet rows cols` (sizes proven), `iterAt`, `mixAt`, `zAt`, `set`, `iterHistogram` | DONE | – | – |
| `bounds`, `size`, `ranges`, `Rectangle(K)` | `FilledSet.bounds`, `Rectangle.rows/cols`, `xRange/yRange`, `xs/ys` | DONE | – | – |
| `plane`, `disk` | `C64.plane`, `C64.disk` | DONE | oracle `complex.json` | – |
| `orbit(K, z0)` kernel | `Define.orbit` (`iter ≤ N` proven), `orbitLoop`, `sweep` | DONE | – | – |
| `Compute` (`@time @threads`) | `computeRaster`, parallel `spawnChunks` | DONE | `@time` printing dropped; perf parity measured (docs/PERF.md) | – |
| `typeplot`, `String(K)` | `Define.typeplot`, `Define.title`, `latexTitle`, `yLabel`, `latexYLabel` | DONE | – | – |
| `nonan`, `(C::ColorScheme)(K)` | `nonan`, `FilledSet.colorScheme` (`Fatou/Raster.lean`) | DONE | oracle `mpl.json`/colour tests | – |
| `plot`, `imshow`, `title` (PyPlotExt) | `Raster`, `toRGBA8`, gallery `rasterFigure` (`gallery/Gallery/Fatou.lean`) | DONE | rendering and named colormaps live in the gallery package (LeanPlot) | – |
| `orbit(K::Define)` cobweb plot, `real_orb` | `Define.realOrbit`, `realOrb` (sizes proven), titles/legends (`Fatou/Orbit.lean`); gallery `orbitFigure` | DONE | README R1 reproduced in the gallery | – |
| UnicodePlotsExt `orbit` (text backend) | – | MISSING | braille cobweb text plot (the port notes list the text goldens under oracle/applied-misc for FlowGeometry only) | M |
| ImageInTerminalExt `show(io, K; c, bare)` | – | MISSING | terminal image display (ANSI half-blocks/sixel from `colorScheme`) | S |
| MakieExt (dead code) | – | SKIP | not a module; commented out in Project.toml | – |
| GrassmannExt `orbit` over `Couple{V,B}` (broken in Julia) | `Fatou.Couple.mul/sq/abs2` (B² = ±1, 0) (`Fatou/Couple.lean`) | PARTIAL | intended semantics only, with no oracle (Julia is broken); there is no `B` option and no bridge to the Lean `Grassmann` Couple type | S |
| `basin(K, j)` | `basin newt j body` (templates `basinSet0/J`, suffixes) | PARTIAL | Julia computes `body` (the LaTeX of the j-fold composition with c=0, `recomp` + REDUCE `latex`); Lean needs it by hand. README `basin(nf,3)` cannot be reproduced automatically | M |
| internals `newton_raphson`, `recomp`, `nL`, `jL`, `rdpm`, `nrset`, `jset` | – | MISSING | symbolic layer: derivative, substitution, factoring, LaTeX printer (see the Newton/basin rows) | (Newton/basin fix) |
| `z^p` for complex/real non-integer `p` in maps (wiki nf16 `z^(4.0+3.0im)`) | `JuliaBase.ComplexF64.pow` exists; `Fatou.C64` has only `NatPow` and `HPow C64 Int` | PARTIAL | no `HPow C64 C64`/`HPow C64 Float` instance, so wiki maps must call `ComplexF64.pow` explicitly | S |
| String input (`juliafill("z^2")`) | – | SKIP | broken in Julia 1.x | – |
| `__init__` thread banner, `Reduce.stop()` | – | SKIP | load-time side effects | – |
| performance | `Tests/Fatou/Bench.lean`, docs/PERF.md | DONE | at parity with a handwritten Julia kernel; 30–200× faster than Fatou.jl | – |

## 8. Clifford.jl (dead code upstream; sparse graded storage per applied-misc.md §2.3/§4.3)

Clifford.jl's module defines only the unexported `greet()`. `algebra.jl`, `multivectors.jl` and `products.jl` are never
`include`d. Current Grassmann.jl *exports* `SparseChain`/`MultiGrade` but defines neither. There is no Lean
counterpart (`rg SparseChain|MultiGrade` finds nothing; `Grassmann.TA` in `Grassmann/Dynamic/Basic.lean` has
no sparse kinds). There is no oracle, since the Julia code cannot run.

| Julia symbol | Lean name(s) + file | status | gap description | effort |
|---|---|---|---|---|
| `greet()` | – | SKIP | hello-world stub, not exported | – |
| `SparseChain{V,G,T}` (+ ctors from `Chain`, `Vector{TensorTerm}`) | – | MISSING | sparse k-vector (sorted `(bladeIndex, value)` pairs, length `binomial(N,G)`) | M |
| `chainvalues` densify rule (`fill_limit = 0.5`) | – | MISSING | dense `Chain` if under 50% zeros, else sparse; `G ∈ {0,N}` always dense | (with SparseChain) |
| `MultiGrade{V,G}` (+ ctors from `Vector{TensorGraded}`, `MultiVector`) | – | MISSING | grade-mask `G` + ascending-grade terms; `MultiGrade(::MultiVector)` sparsifies per grade | (with SparseChain) |
| `+`/`-` (SparseChain±SparseChain/TensorTerm, MultiGrade±MultiGrade/graded, mixed grades → MultiGrade) | – | MISSING | two-pointer merges; implement the **intended** signs (Julia loses the sign of `b` in `Term − SparseChain` and in mixed-grade `-`) | (with SparseChain) |
| scalar `*`, mixing with dense `MultiVector`/`Chain` (`generate_sums`) | – | MISSING | termwise scale; scatter into dense at `binomsum(N,G)+index` | (with SparseChain) |
| `reverse`, `involute`, `conj`, unary `±` | – | MISSING | termwise, keeping the MultiGrade structure (Julia wrongly returns a SparseChain) | (with SparseChain) |
| `complementleft`, `complementright` | – | MISSING | termwise; grade g ↦ N−g with the mask bit-reversed over N+1 bits (Julia XORs the mask, which is a bug) | (with SparseChain) |
| `scalar`, `vector`, `volume`, `isscalar`, `isvector`, `terms`, `value`, `valuetype`, `adjoint` | – | MISSING | accessors on MultiGrade/SparseChain | (with SparseChain) |
| `show` (SparseChain, MultiGrade), `==` | – | MISSING | `" + "`/`" - "abs` joined terms with blade indices; termwise equality, and both zero across grades | (with SparseChain) |

## 9. Heisenberg.jl

| Julia symbol | Lean name(s) + file | status | gap description | effort |
|---|---|---|---|---|
| `greet()` (not exported; the whole package is a 2019 stub) | – | SKIP | nothing to port | – |

---

## Documented-behaviour coverage (README/docs examples)

| example | expressible in Lean today? | notes |
|---|---|---|
| AbstractLattices README (shared `∨` across modules) | **no** (for Grassmann + Dendriform/DeMorgan together) | This is the point of the package. The Lean split between `AbstractLattices.HVee` and `AbstractTensors.Vee` breaks it |
| PrimitiveBits README `PrimitiveBits16(7)`, `b[2:4]` | yes | `#guard` + oracle |
| DeMorgan README tables 1 and 2 | yes (verbatim render) | table 2 uses `&&&` for `∧` |
| Dendriform README `Grove(3,7) ⊣ [1,2]∪[2,1]`, `Grove(2,3)*(…)\|>GroveBin`, `[2,1,7,4,1,3,1] < […]`, `grovedisplay(true)` | yes | the Tamari example is `Tree.tamariLt …` (no `<`); tree literals go through `Tree.ofName?` |
| AbstractAnalysis README | – | prose only; the port-notes §6.5 goldens are all covered |
| Wilkinson README (exprval optimal form selection) | yes | – |
| Fatou README R1–R5 | yes, **only with hand-derived inputs** | R4/R5 need `df`, REDUCE's factored Newton map and `label` typed in. `basin(nf,3)` is not reproducible (needs the LaTeX body) |
| Fatou wiki (34 examples) | yes, with the same caveat | nf16 needs `ComplexF64.pow` spelled out; o11 `2z%1` needs the `real` override |

---

## Counts

Computed from the status column of the tables above (one row per symbol or symbol group).

| status | rows |
|---|---|
| DONE | 125 |
| PARTIAL | 32 |
| MISSING | 19 |
| IN_PROGRESS | 3 |
| SKIP | 14 |
