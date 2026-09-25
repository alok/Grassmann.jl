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

Updated 2026-09-25 by the misc parity work (branch `worktree-wf_4ea667ef-018-7`): statuses below reflect it.

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

The Lean side is measured by the benchmark harness (`lake exe bench dendriform demorgan wilkinson fatou`,
docs/perf/latest.md) and, for AbstractAnalysis, by the temporary cases recorded in docs/PERF.md (2026-09-25).

---

## 1. AbstractLattices.jl (exports `∧ ∨ dist wedge vee`)

| Julia symbol | Lean name(s) + file | status | gap description | effort |
|---|---|---|---|---|
| `wedge` (generic function) | `AbstractLattices.HWedge.wedge` (`AbstractLattices/Basic.lean`) | DONE | typeclass replaces the generic function; static tests in `Tests/AbstractLattices.lean` | – |
| `vee` (generic function) | `AbstractLattices.HVee.vee` (`AbstractLattices/Basic.lean`) | DONE | as above | – |
| `∧` (`const ∧ = wedge`) | scoped `∧` in `DeMorgan` (`Connectives.and`) and `Dendriform` (`Graft`); Grassmann's scoped `∧` (`Grassmann/Notation.lean:65`) maps to **`AbstractTensors.Wedge`** (`AbstractTensors/Ops.lean:110`) | PARTIAL | each package now has the Julia infix under `open scoped`, but there is still no single `∧` shared with AbstractTensors (unifying `AbstractTensors.Wedge`/`Vee` with `AbstractLattices.HWedge`/`HVee` is outside the misc ownership: integrator request). The AbstractLattices module doc still claims the opposite (doc bug) | M |
| `∨` (`const ∨ = vee`) | scoped `∨` in `DeMorgan` and `Dendriform` (graft), Grassmann's → `AbstractTensors.Vee` | PARTIAL | as `∧` | (same fix) |
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
| `TruthValues{N}` | `DeMorgan.TruthValues N` (`DeMorgan/TruthValues.lean`): one `UInt64` word (unboxed) and a masking invariant, `rows N = 2^min(N,6)` as Julia's `UInt64` storage | DONE | oracle `truthvalues.json`; laws per row; `Formula.isTautology_iff` for `N ≤ 6`; `select` by word literals (`@[csimp]`) | – |
| `TruthValues()`, `TruthValues(p::Bool...)` | `TruthValues.bot`, `TruthValues.ofBools`, `ofNat`, `toNat` | DONE | – | – |
| `⟂`, `⊥` (N-polymorphic `TruthValues{0}(0)`) | `TruthValues.bot`, scoped `⊥`/`⟂` (`DeMorgan/TruthTable.lean`) | DONE | `#guard`s in `Tests/DeMorgan.lean` | – |
| `Tautology`, `⊤` | `TruthValues.top`, scoped `⊤` | DONE | the singleton `Tautology` type is subsumed by `top` | – |
| `(::TruthValues{0})(t...)`, `(::Tautology)(t...)` callables | – | SKIP | constant functions that only exist for Julia dispatch; `bot`/`top` cover them | – |
| `wedge`/`∧`, `vee`/`∨` on TruthValues | `HWedge`/`HVee` instances, `Connectives.and`/`or`, scoped `∧`/`∨`, `&&&`/`\|\|\|` | DONE | oracle; README table 2 `((p-->q)∧(q-->r))-->(p-->r)` is written with `∧` (`Tests/DeMorgan.lean`) | – |
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
| `@truthtable p q` (binds REPL globals) | command `truthtable p q` (top-level defs), term form `truthtable p q in e` (`DeMorgan/TruthTable.lean`) | DONE | README session reproduced (`Tests/DeMorgan.lean`, namespace `Readme`) | – |
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
| `∨`/`graft` | `Tree.graft`, `PBTree.graft`, `HVee` instances, scoped `∨` (`Graft` class) | DONE | oracle; `#guard`s | – |
| `left`, `right` | `Tree.left`, `Tree.right`, `PBTree.split` | DONE | – | – |
| `σ` | `Tree.σ`, `PBTree.σ`, `Grove.σ` | DONE | involution proven | – |
| `over`/`/`, `under`/`\` | `Tree.over` (`Div`), `Tree.under` (`SDiff`), `PBTree.over` (`HDiv`), `PBTree.under` | DONE | `σ_over` proven | – |
| `dashv`/`⊣`, `vdash`/`⊢` | `Tree.dashv/vdash`, `Grove.dashv/vdash` (scoped `⊣ ⊢`), `Julia.dashv/vdash` | DONE | axioms proven for all trees (`Dendriform/Axioms.lean`) | – |
| `+`, `*` | `Tree.sum`, `Tree.mul`, `Grove` `HAdd`/`HMul` (degree-typed), `Julia.add/mul` | DONE | Julia row orders reproduced | – |
| `∪` (+ `@info` dup count) | `Grove.union` (`Union`), `Grove.unionCount` | DONE | – | – |
| `⋖`, `⋗` | `Tree.covers`, `Tree.coveredBy`, scoped `⋖`/`⋗` (`Dendriform/Poset.lean`) | DONE | oracle `poset.json` | – |
| `<`, `>`, `≤`, `≥` on trees (Tamari) | `LT`/`LE` instances (decidable) on `Tree`, `PBTree n`, `Grove n`; `Tree.tamariLt/Gt/Le/Ge` | DONE | README `[2,1,7,4,1,3,1] < [2,1,7,4,3,2,1]` as `tree![…] < tree![…]` | – |
| `<`, `≤` on groves (index order) | `Grove.indexLt`, `indexLe` | DONE | – | – |
| `between`/`⊴` | `Tree.betweenList`, `between`, scoped `⊴` | DONE | – | – |
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
| vector-as-tree coercions (`[1,2]∪[2,1]`, promote rules) | `tree![…]`, `grove![[…],…]` literals checked at elaboration (`by decide`), `PBTree.ofName`, `Grove.ofNames`; `ToString Tree` | DONE | README `Grove(3,7) ⊣ [1,2]∪[2,1]` written with literals | – |
| performance (Julia refs above) | `Bench/Dendriform.lean` (`dendriform`, `demorgan` suites), Julia twins `oracle/bench/dendriform.jl`, `demorgan.jl` | DONE | DeMorgan `tv_formula_N6` went from 1556× to 1.7× Julia with the `UInt64` storage (docs/PERF.md) | – |

## 5. AbstractAnalysis.jl

| Julia symbol | Lean name(s) + file | status | gap description | effort |
|---|---|---|---|---|
| `AbstractCountable`, `CountableFunction`, `AbstractPermutation` | – | SKIP | abstract dispatch supertypes; Lean uses concrete structures and classes | – |
| `CountableArray`, `CountableVector`, `CountableMatrix` | `CountableArray α N`, `CountableVector α`, rank-2 `CountableArray α 2` (`AbstractAnalysis/Countable.lean`) | DONE | oracle `sets.json`/`limits.json` | – |
| `CountableArray(n...)` index-tuple grid | `CountableArray.grid n m`, any rank `CountableArray.gridN` | DONE | – | – |
| `Ones`, `Zeros`, `Naturals`, `Integers` | `Ones`, `Zeros`, `Naturals`, `Integers` (`Countable.lean`, `Sets.lean`) | DONE | – | – |
| `counter`, `resize!(::CountableVector)`, call `(x)(n)` | `.f`, `withLen` | DONE | pure | – |
| `map`/`broadcast`, unary ops (`inv abs exp log sin …`) on countables | `CountableVector.map`, `CountableArray.map` | DONE | named unary methods become `map f`; oracle | – |
| arithmetic `⊙ ∈ {+ - * / ^}` on countables | `CountableVector`/`CountableArray`: all five pointwise, with a number on either side, array⊙array on the pointwise minimum size | DONE | oracle `2^x`, `x/(x+1)`, `abs(x)^x` (`limits.json`) | – |
| `dot` | `CountableVector.dot` (a `Limit`) | DONE | oracle | – |
| `countabletuple`, `countableproduct` | `countableTuple`, `countableProduct`, `countableProduct3` | DONE | – | – |
| `FunctionArray`, `FunctionVector`, `FunctionMatrix` | `FunctionVector β α`; rank-N `FunctionArray β α N`, `FunctionMatrix` (`eval`, `term`, `map`, `zipWith`); `+ - * / ^` and number⊙family | DONE | Julia's `FunctionMatrix(f, n, m)` size quirk (#24) not reproduced | – |
| `functiontuple`, `functionproduct`, `mapmap` | – | SKIP | broken in Julia (undefined variables, quirk #23); no defined semantics to port | – |
| `Series` (+ `dot(c, f)`, call, `resize!`) | `Series`, `Series.eval`, `FunctionVector.series` | DONE | oracle `series_pow_*` | – |
| `Product` (+ call, `log(::Product)`, `resize!`) | `Product`, `Product.eval`, `Product.log` (Julia's `log`), `FunctionVector.product` | DONE | oracle `product_log_*` | – |
| `SequenceArray`, `SequenceVector`, `SequenceMatrix` | `SequenceArray σ S` over `LastDimStorage` (`Array`, `FloatArray`, `SlabArray`), `SequenceVector`, `SequenceMatrix` (`AbstractAnalysis/Sequence.lean`) | DONE | `SlabArray` property-tested (`Tests/AbstractAnalysis/Props.lean`) | – |
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
| ModsExt (`gequal`/`isinvertible` for `AbstractMod`) | `ApproxEq (Fin n)` (exact), `Law.addMod`, `Law.mulMod`, `invMod` | DONE | `U(7)`, `ℤ₁₂` checks; Mods.jl is not in the oracle env | – |
| `Semimagma`, `grouplaw`, `groupinverse` | `Semimagma T L`, `Law` (`op`, `inv`), `Law.mul`, `Law.add` (`AbstractAnalysis/Magma.lean`) | DONE | oracle `groups.json` | – |
| `order(G)`, `abs(G)`, `order(n,f,g)` | `Semimagma.order`, `(cyclic p).order` | DONE | – | – |
| `orders(G)` | `Semimagma.orders` | DONE | oracle (Gaussian units, `ℤ_n`); for permutations Julia throws (`group(p.v)`), the port gives the intended orders | – |
| `iseven(G)`, `isodd(G)` (Semimagma) | `Semimagma.isEven/isOdd` over `HasParity` (Int, Nat, Perm) | DONE | oracle `parity` | – |
| `==`, `∈`, `issubset` | `setEq` (`BEq`), `mem`, `subset` | DONE | – | – |
| `compose`, `∘` | `Semimagma.compose`, `composeLeft`, `composeRight` | DONE | – | – |
| `*`, `+` with Number/element/Semimagma | `HMul`/`HAdd` instances (element on either side, plain operation) | DONE | oracle `times2`/`plus1` | – |
| `cayley` | `Semimagma.cayley` | DONE | – | – |
| `ismagma`, `isassociative`, `isinvertible`, `issemigroup`, `isgroup`, `isabelian` | `isMagma`, `isAssociative`, `isInvertible`, `isSemigroup`, `isGroup`, `isAbelian` | DONE | kernel-checked on S3/S4 | – |
| `ismonoid` (broken in Julia) | `isMonoid G e` (explicit identity) | DONE | intended semantics | – |
| `iscategory`, `issemicategory`, `isgroupoid` | `isCategory G e`, `isSemicategory`, `isGroupoid` | DONE | `iscategory` takes the identity (Julia's is broken, quirk #17) | – |
| `iscyclic` | `isCyclic` (correct), `Julia.isCyclic` (first-two quirk) | DONE | – | – |
| `magma` (element / vector / closure) | `cyclic`, `magma`, `closeArray` | DONE | – | – |
| `group` | `group`, `groupOf` | DONE | – | – |
| `subsemigroup`, `subgroup`, `issubgroup` | same (`subsemigroup`, `subgroup`, `isSubgroup`) | DONE | – | – |
| `center` (buggy), `centralizer`, `isnormal`, `normalizer`, `commutator` | `center` (correct) + `Julia.center`, `centralizer`, `isNormal`, `normalizer`, `commutator` | DONE | – | – |
| `leftcosets`, `rightcosets`, `G / N` | clean `leftCosets/rightCosets`, `Julia.leftCosets/rightCosets/quotient` | DONE | – | – |
| `unityroots` | `unityRoots` | DONE | oracle (tolerance) | – |
| `Permutation` (+ `p[i]`, `p(i)`, `p(q)`, `inv`, `^`, `/`, `\`, `one`, `isone`, `iseven`) | `Perm N` (bijectivity carried in the type), `apply`, `mul`, `inv`, `zpow`, `div`, `ldiv`, `one`, `isEven`, `isOdd`, `Hashable`, group laws proven (`AbstractAnalysis/Perm.lean`) | DONE | – | – |
| `Cycle{N}` | `Cycle N` (`eval`, `toPerm`, `ofList`, `toList`, `transpositionCount`), `Julia.cycleEq` | DONE | – | – |
| `Transposition{N}` | `Transposition N` (2-cycle subtype), `Transposition.mk?` | DONE | – | – |
| `CycleProduct`, `decompose`, `order(::CycleProduct)` | `CycleProduct N` (`toPerm`, `transpositionCount`, `sign`, Julia show incl. `Int64[]`), `Perm.decompose : Cycle N ⊕ CycleProduct N`, `Semimagma.decompose` | DONE | oracle `decompose` show strings for all of S₄ | – |
| `order(::Perm/::Cycle)`, `levicivita` | `transpositionCount`, `sign` (homomorphism kernel-checked on S3/S4), `groupOrder` | DONE | – | – |
| `isdisjoint(::Cycle,::Cycle)` | `Cycle.isDisjoint` | DONE | – | – |
| `isabelian(::Cycle,::Cycle)` | `Cycle.isAbelian` (decides commutation), `Julia.cycleIsAbelian` (disjoint-or-quirk-#21-equal) | DONE | Julia's accepts `(1,2,3,4)`/`(1,2,4,3)` | – |
| `commutator(::Perm,::Perm)` (broken in Julia) | `Perm.commutator g h = g⁻¹h⁻¹gh` | DONE | intended semantics | – |
| `SymmetricGroup`, `AlternatingGroup`, `DihedralGroup` (broken in Julia) | same names (Dihedral = intended) | DONE | – | – |
| `@metric`, `@norm` | `Metric`, `Normed` classes (instances for Float, Complex, FloatArray, Array) (`AbstractAnalysis/Metric.lean`) | DONE | macro-generated methods become instances | – |
| `supnorm`, `infnorm`, `maxabs`, `minabs` | same | DONE | oracle `metric.json` | – |
| `residual`, `residuals`, `lipschitz`, `residualproduct` | `Limit.residual`, `residuals`, `CountableVector.residuals`, `lipschitz`, `residualProduct` | DONE | – | – |
| `isconverging`, `isdiverging`, `iscauchy`, `ismonotonic`, `isincreasing`, `isdecreasing` | `isConverging`, `isDiverging`, `isCauchy`, `isMonotonic`, `isIncreasing`, `isDecreasing`; `isBounded` + `Julia.isBounded` | DONE | – | – |
| `supseq`, `infseq` (suffix / windowed) | `supseq`, `infseq`, `CountableVector.supseq/infseq` | DONE | – | – |
| `limsup`, `liminf` | Array `(x, m)`, `limsupAt/liminfAt (x, m, n)`, `CountableVector.limsup/liminf` (a `Limit`) | DONE | oracle | – |
| `Limit` (+ `first/last/initial/final/length/residual`, call, `show`) | `Limit S V`, `Indexed`, `Derived`, `first`, `last`, `length`, `residual`, `rerun`, `toJulia`/`ToString` (`AbstractAnalysis/Limit.lean`) | DONE | oracle show strings incl. `n → 100002` | – |
| `Limit(v0,n,F,D)`, `L[i]`, `L[ϵ]`, `collect(L)` | `ofIterate`/`iterate`, `seek`, `limitEps`, `collect`, `collectSeq` | DONE | – | – |
| `map(f,L)`, unary ops on Limit | `Limit.map` | DONE | – | – |
| Limit arithmetic `⊙ ∈ {+ - * / ^}` | all five with a number on either side and `L⊙L` (`opLeft`/`opRight`/`op₂`) | DONE | oracle `sum^2`, `2^sum`, `sum/prod`, `abs(sum)^prod` (bit-exact with Julia's `pow`) | – |
| `sum`, `prod` (countable and Limit) | `CountableVector.sum/prod`, `Limit.sum/prod`, `prodNaturals` | DONE | oracle | – |
| `limit` (Limit/countable/n/ϵ, SequenceArray) | `CountableVector.limit/limitEps`, `SequenceArray.limit`, `Limit.limitEps` | DONE | – | – |
| `orbit`, `orbiterror`, `orbithold`, `FixedCycle` | `orbit`, `orbitN`, `orbitError`, `orbitNTrace`, `orbitHold`, `FixedCycle.run/withLen` | DONE | the metric defaults to the state's `Metric.dist` (Julia's `supnorm`) | – |
| `derivative`, `derivative2` | same (Float) | DONE | oracle | – |
| performance: `Semimagma` membership | `magmaHashed`/`groupHashed` (hash side index), `isGroupHashed` (index Cayley table), `@[csimp]` allocation-free scans | DONE | S₆ closure 64 ms (Julia 2.59 s, linear port 3.17 s); `isgroup(S₅)` 4.4 ms (Julia 78 ms; generic 336 ms) | – |
| performance: `Limit` loops (`sum(x)[1e-10]` 0.13 ms in Julia) | `Limit (Indexed Float) Float`, `@[inline]` `orbit`/`sum`/`limitEps` | PARTIAL | measured (docs/PERF.md 2026-09-25): `orbit(cos, 1.0)` 0.96 µs (Julia 0.75 µs); `sum(x)[1e-10]` 4.8 ms, 37× Julia: the `Indexed Float` state is a heap object with a boxed `Float` per step. Needs a scalar fast path for sums | S |

## 6. Wilkinson.jl (exports `PolynomialAnalysis PolynomialComparison plot factor expand horner polyfactors polyexpand polyhorner`) + SyntaxTree parts

| Julia symbol | Lean name(s) + file | status | gap description | effort |
|---|---|---|---|---|
| Julia `Expr` (input language) | `JExpr`, `Lit`, `jl⟪…⟫` quotation, `JExpr.parse`, `toJulia` (`Wilkinson/Expr.lean`, `Parse.lean`) | DONE | – | – |
| `PolynomialAnalysis` (+ print) | `PolynomialAnalysis`, `.make`, `.toJulia` (`Wilkinson/Analysis.lean`) | DONE | oracle `comparison.json`; REDUCE 2-D display → infix (justified) | – |
| `PolynomialComparison` (+ print) | `PolynomialComparison.make/ofForms/ofReduce`, `.toJulia`, `labels` | PARTIAL | the `"r"` form is analysed bit-exactly from REDUCE's forms (`ofForms`, 3 golden cases with `rxtra`), but the REDUCE emulation cannot produce REDUCE's rounded factorization (next row), so `ofReduce` never has `rxtra` | (rounded) |
| `plot(::PolynomialComparison)` | `PolynomialComparison.plotData` (root); figure in `gallery/Gallery/Wilkinson.lean` | DONE | rendering lives in the gallery package (LeanPlot) | – |
| `expand` (REDUCE) | `Wilkinson/Reduce.lean` `expand` (ℚ[x], REDUCE shapes) | DONE | oracle `reduce.json` | – |
| `horner` (REDUCE) | `horner` | DONE | oracle | – |
| `factor` (REDUCE) | `factor` (`Wilkinson/Poly.lean`: rational roots, then Berlekamp–Zassenhaus in `Wilkinson/Zassenhaus.lean`), REDUCE's factor order (`ZPoly.reduceBefore`, its `ordp`) | DONE | oracle `factor.json` (85 REDUCE factorizations: Swinnerton-Dyer, cyclotomic, random products to degree 16) | – |
| `factor` under `on rounded` | – | MISSING | not reproducible from the polynomial: REDUCE splits over `ℂ` with 12-digit roots, keeps trial roots as integers, and orders the factors by its internal bigfloat representation (probed: neither by value nor by exact factor) | L |
| `polyfactors`, `polyexpand`, `polyhorner` | same names; `Reduce.Alg` replays each `Reduce.Algebra` step (`off exp`, `mkprod` with REDUCE's `tmsf`) | DONE | oracle `reduce.json` + `algebra.json` (603 shapes, identical trees) | – |
| `floatset`, `geonorm`, `Ω`, `stieltjes`, `simpson`, `exacterr`, `renormalize!`, `errval`, `optimal` | `floatset`/`floatset32`/`logset`, `geonorm`, `Ω`, `stieltjes`, `simpson`, `exacterr`, `renormalize`, `errval`, `optimal` | DONE | bit-exact (Julia exp/log kernels, 256-bit BigFloat); oracle `ranges/kernels/stieltjes.json` | – |
| `NumericalData` (abstract) | – | SKIP | abstract supertype only | – |
| `testpoly`, `tests` | `testpoly`, `Reduce.tests` | DONE | allocation tie-break dropped (nondeterministic in Julia) | – |
| bytes allocated | `0` | SKIP | nondeterministic in Julia | – |
| ST `callcount`, `sub`, `abs`, `alg`, `expravg`, `exprdev`, `exprval` | same (`Wilkinson/SyntaxTree.lean`) | DONE | oracle `exprval.json` | – |
| ST `genfun`/`genlatest`/`@genfun` | `SyntaxTree.eval` (interpreter over `JNum`) | DONE | eval-and-invokelatest becomes an interpreter | – |
| ST `linefilter!` | – | SKIP | strips `LineNumberNode`s, which `JExpr` does not have | – |
| performance (3000-point Stieltjes × forms, 256-bit BigFloat) | `Bench/Wilkinson.lean` (`wilkinson` suite), twin `oracle/bench/wilkinson.jl` | DONE | 0.36–0.88× Julia against Wilkinson's per-call code generation; Julia with the function precompiled (`*_nocodegen`) is 3–17× faster than Lean's AST interpreter (follow-up: compile the AST) | – |

## 7. Fatou.jl (exports `fatou juliafill mandelbrot newton basin orbit plot`)

| Julia symbol | Lean name(s) + file | status | gap description | effort |
|---|---|---|---|---|
| `ComplexBundle` | – | SKIP | abstract dispatch type | – |
| `Rectangle` (∂ scalar/2-vec/4-vec, UInt16 n) | `Bounds` (`square`, `interval`, explicit), `Rectangle` (`rows` ties-to-even, `cols`, `check`) (`Fatou/Grid.lean`) | DONE | oracle `grids.json` (bit-exact axes) | – |
| `ComplexRectangle`, `ComplexRectangle(Ω::Matrix)` | `Plane rows cols`, `Plane.ofFn`, `Rectangle.grid`, `Plane.pixelBounds` | DONE | – | – |
| `Define` (fields/kw) | `Spec`, `Define`, `Options`, `Number` (`Fatou/Define.lean`); `Symbolic`, `juliafill!`/`mandelbrot!`/`newton!` (`Fatou/Symbolic.lean`) | DONE | one Julia expression string gives F, Q, the Julia-typed map (compiled at elaboration), the title and the LaTeX; oracle `symbolic.json` (43 README/wiki expressions) | – |
| `juliafill` | `juliafill` | DONE | oracle catalog (`Tests/Fatou/Catalog.lean`, README R2 at full resolution) | – |
| `juliafill(E; newt=true, m)` (undocumented kw) | `juliafill! "E" (m := "…")` (Newton mode, `ϵ = 4`) | DONE | – | – |
| `mandelbrot` | `mandelbrot`, `mandelbrot! "E" (m := "…")` (Newton switch with the CAS derivative) | DONE | – | – |
| `newton` | `newton!` (CAS derivative and Newton map), `newton f df (map := …)` | PARTIAL | the map is always REDUCE's rational function; its **text** is REDUCE's for 11 of 21 golden maps. The other 10 are REDUCE `off exp` arrangements (`((2i - 5)((z⁶ + z³) - 1) + …)`) of the same function, which round differently in the last bits; `(map := …)` takes REDUCE's text when bit-exact rasters are needed | M |
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
| UnicodePlotsExt `orbit` (text backend) | – | MISSING | braille cobweb text plot; UnicodePlots is not in the oracle environment (and cannot be added), so there is nothing to test a port against; `Define.realOrbit` gives the data | M |
| ImageInTerminalExt `show(io, K; c, bare)` | – | MISSING | output depends on the terminal (sixel vs 24-bit half blocks, resized to the window); `FilledSet.colorScheme`/`Raster` give the image | S |
| MakieExt (dead code) | – | SKIP | not a module; commented out in Project.toml | – |
| GrassmannExt `orbit` over `Couple{V,B}` (broken in Julia) | `(B := "1" / "0" / "im")` on `juliafill!`/`mandelbrot!` (the map compiled over `Couple` numbers, `Q` = Grassmann's `abs2`), `Fatou.Couple.mul/div/rdiv/pow/inv/abs2` (`B² = ±1, 0`) (`Fatou/Couple.lean`) | DONE | intended semantics (Julia's extension is broken, so no oracle): the hyperbolic set's histogram (Julia `t8.jl` with the intended return), `B² = -1` equal to the complex set, quotient/power laws | – |
| `basin(K, j)` | `Define.basinOf j` (CAS `recomp` + rlfi LaTeX), `basin newt j body` | PARTIAL | `basin(K, 1)` equals Julia's for the 31 expressions whose body REDUCE leaves expanded; the others differ in the same `off exp` arrangement as `newton` | M |
| internals `newton_raphson`, `recomp`, `nL`, `jL`, `rdpm`, `nrset`, `jset` | `CAS.newtonRaphson`, `recomp`, `latexOf`, `latexFactor`, `latexAllfac` (`Fatou/CAS.lean`), `Define.basinOf` | DONE | titles: 42 of 43 `latex(E)` exact (the other is a Reduce.jl complex-constant conversion defect) | – |
| `z^p` for complex/real non-integer `p` in maps (wiki nf16 `z^(4.0+3.0im)`) | `HPow C64 C64`, `HPow C64 Float` (Julia's `_cpow`), literal integer powers kept | DONE | – | – |
| String input (`juliafill("z^2")`) | – | SKIP | broken in Julia 1.x | – |
| `__init__` thread banner, `Reduce.stop()` | – | SKIP | load-time side effects | – |
| performance | `Tests/Fatou/Bench.lean`, docs/PERF.md | DONE | at parity with a handwritten Julia kernel; 30–200× faster than Fatou.jl | – |

## 8. Clifford.jl (dead code upstream; sparse graded storage per applied-misc.md §2.3/§4.3)

Clifford.jl's module defines only the unexported `greet()`. `algebra.jl`, `multivectors.jl` and `products.jl` are never
`include`d. Current Grassmann.jl *exports* `SparseChain`/`MultiGrade` but defines neither. The port implements the
intended semantics over the Grassmann static layer (`Clifford/Sparse.lean`, `Clifford/MultiGrade.lean`), property-tested
against the dense `Chain`/`Multivector` (`Tests/Clifford.lean`, 36 properties; registration in `Tests.lean` requested). There is no oracle, since the Julia code cannot run.

| Julia symbol | Lean name(s) + file | status | gap description | effort |
|---|---|---|---|---|
| `greet()` | – | SKIP | hello-world stub, not exported | – |
| `SparseChain{V,G,T}` (+ ctors from `Chain`, `Vector{TensorTerm}`) | `Clifford.SparseChain V G α` (`ofChain`, `ofTerms`, `toChain`, `get`, `bladeTerms`) | DONE | property tests vs dense | – |
| `chainvalues` densify rule (`fill_limit = 0.5`) | `chainValues`, `Graded` (dense/sparse), `fillLimit` | DONE | `G ∈ {0,N}` always dense | – |
| `MultiGrade{V,G}` (+ ctors from `Vector{TensorGraded}`, `MultiVector`) | `Clifford.MultiGrade V α` (`ofGraded`, `ofMultivector`, `ofChain`, `mask`, `grades`) | DONE | – | – |
| `+`/`-` (SparseChain±SparseChain/TensorTerm, MultiGrade±MultiGrade/graded, mixed grades → MultiGrade) | `SparseChain.add/sub/addSingle/singleSub`, `MultiGrade.add/sub/addChain/subChain` | DONE | intended signs (Julia loses the sign of `b`) | – |
| scalar `*`, mixing with dense `MultiVector`/`Chain` (`generate_sums`) | `smul`, `toMultivector`, `ofMultivector` | DONE | – | – |
| `reverse`, `involute`, `conj`, unary `±` | `reverse`, `involute`, `clifford`, `neg` on both, keeping the MultiGrade structure | DONE | – | – |
| `complementleft`, `complementright` | same names; `complementMask` bit-reverses the mask over `N+1` bits | DONE | Julia's XOR mask bug fixed | – |
| `scalar`, `vector`, `volume`, `isscalar`, `isvector`, `terms`, `value`, `valuetype`, `adjoint` | same names on `MultiGrade` (`valuetype` is the type parameter) | DONE | – | – |
| `show` (SparseChain, MultiGrade), `==` | `ToString` (Julia's joined terms, `0` when empty), `BEq` (termwise, zero across grades) | DONE | – | – |

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
| DeMorgan README tables 1 and 2 | yes (verbatim render) | table 2 written with `∧`; the `@truthtable p q` session with the `truthtable p q` command |
| Dendriform README `Grove(3,7) ⊣ [1,2]∪[2,1]`, `Grove(2,3)*(…)\|>GroveBin`, `[2,1,7,4,1,3,1] < […]`, `grovedisplay(true)` | yes | literals `tree![…]`/`grove![…]`, Tamari `<` |
| AbstractAnalysis README | – | prose only; the port-notes §6.5 goldens are all covered |
| Wilkinson README (exprval optimal form selection) | yes | – |
| Fatou README R1–R5 | yes | from the Julia expressions (`juliafill!`, `mandelbrot!`, `newton!`); R4/R5 rasters bit-exact because their Newton maps are among REDUCE's exact texts |
| Fatou wiki (34 examples) | yes | from the expressions; 10 Newton maps differ from REDUCE's text in the `off exp` arrangement (same function) |

---

## Counts

Computed from the status column of the tables above (one row per symbol or symbol group).

| status | rows |
|---|---|
| DONE | 171 |
| PARTIAL | 6 |
| MISSING | 3 |
| IN_PROGRESS | 0 |
| SKIP | 14 |
