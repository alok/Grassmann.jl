# Parity matrix: foundations (DirectSum.jl, Leibniz.jl, AbstractTensors.jl, StaticVectors.jl)

Audit of `/Users/alokbeniwal/Grassmann` at `0ac54fdd` (master, read-only) against the Julia sources in
`/Users/alokbeniwal/chakravala/{DirectSum,Leibniz,AbstractTensors,StaticVectors}.jl` and the oracle env
(`scratchpad/juliaenv`, Julia 1.13; `names(Pkg)` dump in `parity/names.txt`: DirectSum 77, Leibniz 65,
AbstractTensors 108, StaticVectors 5 exports). Port specs: `docs/port-notes/{directsum,leibniz,abstracttensors-staticvectors}.md` §2.

Totals (rows): DONE 208, PARTIAL 27, MISSING 50, SKIP 40, IN_PROGRESS 2.

Status legend: **DONE** implemented + oracle-tested (goldens or kernel `decide` against oracle values);
**PARTIAL** implemented but missing methods/types/options/notation, or untested; **MISSING**;
**IN_PROGRESS** covered by in-flight work; **SKIP** Julia-specific, justified.
Effort: S (< half day), M (1-2 days), L (> 2 days). `-` for DONE/SKIP.

Test evidence used: `Tests/DirectSum/{Spaces,Blades,Derived,Index,Literals,Props,Plans}.lean`
(goldens `Tests/DirectSum/golden/spaces.json`, `derived.jsonl`, `oracle/golden/blades/*`),
`Tests/AbstractTensors/{GenericTests,StaticVectorsTests,ComplexTests,Notation}.lean`,
`Tests/Golden/*` (dynamic element layer), kernel `decide` examples in `Leibniz/*.lean`, `DirectSum/Bits.lean`.

Probes run for this audit (`parity/probe/P1-P3.lean` against master oleans, `parity/eq.jl` against Julia):
`basis! (ℝ^3)′` works (declares `«w¹²»`/`w12`); `ℝ` is an unknown identifier; `(ℝ^3) + (ℝ^3)′` and `(ℝ^1)^3`
have no `HAdd`/`HPow` instance; `ℝ3 == ℝ^3` is `false` in Lean but `true` in Julia; `toString` of a
`Values Float` prints `[0.500000, …]` (Julia `[0.5, …]`). Julia: `(ℝ^3)(1,2) ∪ (ℝ^3)(2,3) = ⟨+++⟩`,
`∩ = ⟨_+_⟩`, `(ℝ^2)' ∪ ℝ^2 = ⟨++--⟩*`, `(ℝ^3)(2,3) ⊕ (ℝ^3)(1) = ⟨_+++__⟩`, `χ(Λ(3).v12) = -1`,
`count_gdims(Λ(3).v12) = [0,0,1,0]`, `∇^2 == Δ`, `(∇,Δ) = (∂ₖvₖ, ∂ₖ²v)`, `subtangent(tangent(ℝ^3)) = T¹⟨___₁⟩`,
`Λ(3)[5] = v₁₂`, `Λ"+++"` shows the `Basis` container.

---

## 1. DirectSum.jl (77 exports + public Base-method behaviour)

### 1.1 Exports

| Julia symbol | Lean name(s) + file | status | gap description | effort |
|---|---|---|---|---|
| `@S_str` | `S!"…"` `DirectSum/Parse.lean:137` (`parseSignature`) | DONE | oracle `spaces.json:signature_parse`; Julia quirks Q1–Q3 fixed on purpose | - |
| `@D_str` | `D!"…"` `DirectSum/Parse.lean:140` (`parseDiagonal`) | DONE | oracle `diagonal_parse` | - |
| `@V_str` | `V!"…"` `DirectSum/Parse.lean:143` (`parseBundle`) | DONE | oracle `bundle_parse` (corrected grammar Q1) | - |
| `@basis` | `basis!` `Grassmann/Basis.lean:48` | PARTIAL | declares `V`, `v`, every blade + ASCII aliases and kernels; no custom arguments (`@basis q sig vec cov duo dif`, README: "assign the vector space name to `S` … basis elements to `b`"), no tuple result, space name fixed to `V` | S |
| `@basis_str` | `basis! S!"…"` | DONE | same command with a literal space (`basis"+++"` ≡ `basis! S!"+++"`) | - |
| `@dualbasis` | `basis! (V)′` (probe P1) | PARTIAL | works but binds the space as `V` (Julia `VV`) and has no dedicated command / custom `cov`/`dif` names | S |
| `@dualbasis_str` | `basis! (S!"…")′` | PARTIAL | as `@dualbasis` | S |
| `@mixedbasis` | `basis! (V ⊕ V′)` | PARTIAL | only the mixed algebra is declared; Julia also binds `V'` (`VV`) and `V` bases and names the space `W`; used by Grassmann docs `algebra.md:1397` | S |
| `@mixedbasis_str` | `basis! (S!"…" ⊕ (S!"…")′)` | PARTIAL | as `@mixedbasis` | S |
| `@Λ_str` | — | MISSING | `Λ"+++"` (= `Basis(str)`) not available; depends on the `Λ` container gap | S |
| `DiagonalForm` | `Metric.diagonal`, `TensorBundle.diag`, `D!` `DirectSum/Space.lean:35,88` | DONE | oracle spaces | - |
| `Signature` | `Metric.signature`, `TensorBundle.sig`, `ofCode` `DirectSum/Space.lean:79,84` | DONE | ctor `Signature(n,d,o,s)` = `ofCode`; conversions tracked below | - |
| `TensorBundle` | `DirectSum.TensorBundle` `DirectSum/Space.lean:48` | DONE | one value type for all space kinds (+ `MetricTensor`, `Int` spaces) | - |
| `Manifold` | `AbstractTensors.Manifold` `AbstractTensors/Ops.lean:69`; `parseBundle` for `Manifold(str)` | DONE | | - |
| `Submanifold` | `DirectSum.Submanifold V G` (blade) `DirectSum/Blade.lean:18`; `SubSpace V` + `TensorBundle.sub`/`handle` (subspace) `DirectSum/Show.lean:184-208` | PARTIAL | blade role DONE (oracle); subspace role has only `rank`, `toString`, `sub`: missing `⊆ ∪ ∩ ⊕`, `V[i]`, `mdims`/`diffvars` of a subspace, calling a subspace `(M::Submanifold)(i…)`, `collect(V(1,4))` basis display | S |
| `Single` | `Grassmann.Single V G α` `Grassmann/Types/Single.lean:22`; `BladeResult.single`; `TA.single` | DONE | oracle via blades + dynamic goldens | - |
| `Zero` | `BladeResult.zero` `DirectSum/BladeAlgebra.lean`; `TA.zero` `Grassmann/Dynamic/Basic.lean:42` | DONE | | - |
| `One` | `Submanifold.one` `DirectSum/Blade.lean:51`; `TA.one` | DONE | | - |
| `Infinity` | `TA.infinity` `Grassmann/Dynamic/Basic.lean:46` (show `∞`, absorbing arithmetic `Dynamic/Arith.lean:216`) | DONE | dynamic kind only (no static `Infinity V` type; not needed) | - |
| `Grade` | — | SKIP | `Grade{N,G} <: Integer` is a type-level grade marker for dispatch; Lean grades are the `Nat` index of `Chain V G` | - |
| `SubAlgebra` | — | SKIP | abstract supertype of the cached basis containers; the user-facing part is the `Λ` row | - |
| `Λ` (`Basis`, `SparseBasis`, `ExtendedBasis`) | functions only: `TensorBundle.lookup` `DirectSum/Names.lean:95` (`Λ(V).name`, oracle 373 lookups), `showBasis` `DirectSum/Show.lean:155`, `labels` `Space.lean:257`, `Leibniz.basisAt` | PARTIAL | no `Λ V` value or syntax: `Λ(V).v12` / `Λ(3).v12` / `Λ(62).v32a87Ng`, `Λ(V)[i]`, `Λ(n)`, `Λ(n,d,o,s)`, `Λ(V)'`, `Λ(V) ⊕ Λ(W)` (DirectSum README + tests, Grassmann docs use `Λ(ℝ5).v12` throughout) | M |
| `TensorAlgebra` | `AbstractTensors.TensorAlgebra` class `AbstractTensors/Ops.lean:40` | DONE | | - |
| `basis` | `Single.basis` `Grassmann/Types/Single.lean:44`; blades are their own basis | DONE | | - |
| `clifford` | `TensorBundle.clifford` `BladeAlgebra.lean`; class `Clifford`; Grassmann instances `Algebra/Unary.lean:231` | DONE | oracle blades | - |
| `complementleft` | `TensorBundle.complementleft` `BladeAlgebra.lean` | DONE | oracle blades | - |
| `complementleftanti` | `TensorBundle.complementleftanti` | DONE | | - |
| `complementlefthodge` | `TensorBundle.complementlefthodge` | DONE | | - |
| `complementright` | `TensorBundle.complementright`, `!` notation | DONE | | - |
| `complementrightanti` | `TensorBundle.complementrightanti` | DONE | | - |
| `complementrighthodge` | `TensorBundle.complementrighthodge`, `⋆` | DONE | | - |
| `diffmode` | field `TensorBundle.diffmode` | DONE | oracle spaces | - |
| `diffvars` | field `TensorBundle.diffvars` | DONE | (subspace variant only inside `showSub`) | - |
| `dyadmode` | field `TensorBundle.dyadmode` | DONE | | - |
| `gdims` | `Leibniz.gdims`, `AbstractTensors.gdims`, `gdimsOf` | DONE | | - |
| `getalgebra` | — | SKIP | global cache of `Basis`/`SparseBasis`/`ExtendedBasis`; Lean memoizes index tables with `Thunk` (`Leibniz/Combinatorics.lean:193`) | - |
| `getbasis` | `Submanifold.ofBits?`, `TensorBundle.labelBlade?`, `TA.blade` | DONE | | - |
| `grade` | `TensorBundle.grade` `Space.lean:143`, `gradeOf` `Parity.lean`, `AbstractTensors.rank`; `grade(t,G)` = `GradeProj` | DONE | | - |
| `hasinf` | field `hasinf`; `bladeHasInf` `Parity.lean` | DONE | | - |
| `hasorigin` | field `hasorigin`; `bladeHasOrigin`, `originBit` | DONE | | - |
| `indices` | `Bits.indices`, `indicesList` `DirectSum/Bits.lean`, `Submanifold.indices` | DONE | | - |
| `involute` | `TensorBundle.involute`, class `Involute`, postfix `ˣ` | DONE | | - |
| `isbasis` | — | SKIP | decided by type (`Submanifold V G` is always a basis blade, `SubSpace V` never) | - |
| `isdual` | `TensorBundle.isdual` | DONE | | - |
| `isdyadic` | `TensorBundle.isdyadic` | DONE | | - |
| `isorigin` | — | MISSING | `isorigin(e)` (and `Base.isinf(e::Submanifold)`): single null generator tests on a blade | S |
| `istangent` | `TensorBundle.istangent` | DONE | | - |
| `mdims` | `TensorBundle.mdims`, `AbstractTensors.mdims` | DONE | | - |
| `metric` | field `metric`, `metricAt`, `bladeMetric`, `metricProduct`, `sigBits`, `gram` | DONE | oracle blades | - |
| `metrichash` | — | SKIP | legacy alias of `metric` (Julia marks the family `# deprecate`) | - |
| `norm` | `Values.norm`, Grassmann `norm` | DONE | | - |
| `order` | — | MISSING | `order(b) = popcount(b & diffmask)`, `order(::Single)`, `order(V) = diffvars`; logic exists inline in `nestTangent` | S |
| `options` | `TensorBundle.options`/`withOptions` `Space.lean:120-127` (Julia `tensorhash`) | DONE | | - |
| `polymode` | field `polymode` | DONE | | - |
| `pseudoclifford` | `TensorBundle.anticlifford` | DONE | name differs (Julia alias `anticlifford`) | - |
| `pseudograde` | `TensorBundle.pseudograde`, `pseudogradeOf` | PARTIAL | no element projection `pseudograde(t,G) = grade(t, grade(V)-G)` | S |
| `pseudoinvolute` | `TensorBundle.antiinvolute` | DONE | | - |
| `pseudoreverse` | `TensorBundle.antireverse` | DONE | | - |
| `tangent` | `TensorBundle.tangent` `SpaceOps.lean:133` | DONE | oracle (quirk Q10 replicated) | - |
| `value` | `AbstractTensors.Value` | DONE | | - |
| `valuetype` | `AbstractTensors.valuetype` | DONE | | - |
| `χ` | — | MISSING | Euler characteristic (Leibniz generic, DirectSum re-export); Grassmann docs `algebra.md:1342` | S |
| `ℝ` | — (only `ℝ^n` syntax) | MISSING | `ℝ = Signature(1)` constant; README `ℝ'⊕ℝ^3`, `ℝ⊕ℝ' ⊇ …`, `ℝ ∩ ℝ'` all use it | S |
| `ℝ0`…`ℝ9` | `DirectSum/Common.lean` | DONE | | - |
| `≅` | — | MISSING | same `grade`, `order`, `diffmode` | S |
| `⊕` | `TensorBundle.oplus`/`oplus!`, `infixr ⊕` `SpaceOps.lean:76-118` | PARTIAL | spaces DONE (oracle); missing `SubSpace ⊕ SubSpace` (`(ℝ^3)(2,3) ⊕ (ℝ^3)(1) = ⟨_+++__⟩`), `Λ(V) ⊕ Λ(W)` (README test), and the `+` alias | S |
| `⋆` | `Hodge.hodge`, scoped prefix `⋆` | DONE | | - |

### 1.2 Public Base-method behaviour on DirectSum types (not in `names`, but README/test-visible)

| Julia symbol | Lean name(s) + file | status | gap description | effort |
|---|---|---|---|---|
| `'`/`adjoint`, `dual` | `adjoint`, `dual`, postfix `′` `SpaceOps.lean:26-44` | DONE | oracle | - |
| `+` (space direct sum alias) | — | MISSING | README `V+V'` → `T¹⟨+++---₁¹⟩*`; no `HAdd TensorBundle` | S |
| `^` (`V^i`) | `TensorBundle.pow` `SpaceOps.lean:122`; `ℝ^n` syntax | PARTIAL | function returns `Except`; no `HPow TensorBundle Nat` so `(ℝ^2)^2` fails | S |
| `∪` | — | MISSING | union of spaces / subspaces / blades, n-ary fold (`DS/operations.jl:91-116`); README `ℝ ∪ ℝ' == ℝ⊕ℝ'` | M |
| `∩` | — | MISSING | README `ℝ ∩ ℝ' == TensorBundle(0)` | M |
| `⊆` | — | MISSING | README `v1 ⊆ v12`, `v12 ⊆ V`, `(ℝ^3)(1,2) ⊆ ℝ^3` | M |
| `⊇` | — | MISSING | README `ℝ⊕ℝ' ⊇ TensorBundle(1)` | S |
| `==`/`equal` (spaces) | derived `DecidableEq TensorBundle` | PARTIAL | structural, not Julia's `a⊆b && a⊇b`: `ℝ3 == ℝ^3` is `false` (Julia `true`) | S |
| `V(i…)`, `V(range)`, `V(vector)` | `TensorBundle.sub` `Show.lean:204` | DONE | README `(ℝ^5)(3,5)` golden | - |
| `(M::Submanifold)(G)`, `(M::Single)(G)` grade projection | `GradeProj` instances `Grassmann/Algebra/Unary.lean:286` | DONE | | - |
| `(W::Submanifold)(b)` restriction/embedding, `(W::Signature)(b)` | `Forms.restrict`, `Chain.project/embed`, `Multivector.project/embed` `Grassmann/Forms/Eval.lean:33-97` | PARTIAL | element-level projection/embedding exists (correct `pext`); blade-level `W(b)` for `Submanifold`/`Single`/`Zero`, embedding into `V⊕V'` (needs `mixed`) and covector evaluation `w¹(v₁)` (`evaluate1/2`, `eval_shift`) missing | M |
| `(V)(λI)` UniformScaling → pseudoscalar | `Submanifold.pseudoscalar`, `TensorBundle.pseudoscalar` | PARTIAL | no application of `UniformScaling` to a space | S |
| `Signature(::DiagonalForm)`, `DiagonalForm(::Signature)`, `Signature(::Submanifold)` | `Forms.restrict` (subspace → bundle) | PARTIAL | kind conversions between signature/diagonal metrics missing | S |
| `V[i]`, `V[:]` | `metricAt`, `diagValues` `Space.lean:183-199` | DONE | | - |
| `det(V)`, `isdiag(V)` | `TensorBundle.det`, `isdiag` | DONE | | - |
| `abs(V)` | — | SKIP | StackOverflow in the Julia oracle (broken) | - |
| `loworder` | `TensorBundle.loworder` `Space.lean:177` | DONE | | - |
| `subtangent` | — | MISSING | `V(grade(V)+1:mdims(V)…)` | S |
| `supermanifold`, `submanifold`, `Manifold(::Submanifold)` | — | SKIP | parent space is the type index of `Submanifold V G`/`SubSpace V` | - |
| `reverse`/`~`/`conj`, `even`, `odd`, `real`, `imag` on blades | `TensorBundle.reverse/conj`, `evenPart/oddPart/realPart/imagPart` `BladeAlgebra.lean` | DONE | oracle | - |
| `paritymetric`, `parityanti`, `parity*` complements | `DirectSum/Parity.lean` | DONE | oracle | - |
| `signbool` | — | SKIP | Bool/Int sign coercion helper | - |
| `labels`, `generate` | `TensorBundle.labels` `Space.lean:257`; `Submanifold.all`, `indexBasisAll` | DONE | oracle | - |
| `lookup_basis`, `indexparity(V,::Symbol)` | `TensorBundle.lookup`/`generatorsOf`/`labelBlade?` `Names.lean` | DONE | Julia defect Q16 fixed (correct signs), oracle-checked | - |
| `alloc` | — | SKIP | `@basis` macro body builder (the Lean command elaborator replaces it) | - |
| `show` (spaces, subspaces, `Basis`, `collect`) | `toString`, `showSub`, `showHandle`, `showBasis`, `showCollect` `Show.lean` | DONE | oracle byte-identical, incl. README 256-element `collect(Submanifold(W))` | - |
| `nameindex`/`namelist`/`namecache` | `Leibniz.nameScheme` (2 fixed schemes) `Leibniz/Indices.lean:67` | PARTIAL | Julia registers new naming schemes from `@basis` custom prefixes; Lean has `pre`/`PRE` only | S |
| `diagonalform`, `diagsig`, `diagonalform_cache` | `diagValues`; metric stored inline | DONE | cache is Julia-only | - |
| `tensorhash` | `options`/`withOptions` | DONE | round-trip theorem `options_withOptions` | - |
| `one`/`zero` on spaces/blades | `Submanifold.one`, `TA.one/zero` | DONE | | - |
| `V0` | `TensorBundle.V0` `Space.lean:94` | DONE | | - |
| `div rem mod mod1 fld cld ldexp round rationalize …` on `Single` | `Single.map` | PARTIAL | no named coefficient-wise methods | S |
| `Real/Float64/Int/Complex(::Single/Zero/Infinity)` conversions | — | PARTIAL | value extraction exists (`Single.val`); Julia conversion rules (e.g. `Complex(Single grade>0)` into imaginary part) not mirrored | S |
| `==`/`isapprox` Single vs Number, `*` Number×Submanifold | `Grassmann/Dynamic/Equal.lean`; `HMul β (Submanifold V G)` `Grassmann/Algebra/Arith.lean:138` | DONE | | - |
| `rand(::SamplerType{Submanifold/Single/Manifold})`, `orand` | — | SKIP | Julia RNG streams are not reproducible; tests use `Tests/Util/Random` | - |
| `evaluate2` | — | SKIP | broken in Julia (undefined `N`); covered by the `(W)(b)` row | - |

---

## 2. Leibniz.jl (65 exports + downstream-public helpers)

### 2.1 Exports

| Julia symbol | Lean name(s) + file | status | gap description | effort |
|---|---|---|---|---|
| `Derivation` | — | MISSING | `Derivation{T,O}` coefficient × `∂ₖ^O vₖ`: `^`, `+ - *` (same order), scalar `* / \`, `-`, show (`∂ₖvₖ`, `∂ₖ²v`), op-lifts onto `TensorAlgebra` through `V(∇)` | M |
| `Nabla` | — | MISSING | `Derivation{Bool,1}` alias | S |
| `Laplacian` | — | MISSING | `Derivation{Bool,2}` alias | S |
| `nabla` / `∇` | — | MISSING | constant; Leibniz README/test `∇^2 == Δ`; Grassmann docs `V(∇)`, `tangent(ℝ^3)(∇)` | S |
| `laplacian` / `Δ` | — | MISSING | `Δ = ∇^2` | S |
| `differential` / `d` | — | MISSING | generic `d(ω) = Manifold(ω)(∇) ∧ ω` (Grassmann method) | M |
| `codifferential` / `δ` | — | MISSING | `δ(ω) = -∂(ω)` | S |
| `boundary` / `∂` | — | MISSING | `∂(ω) = ω ⋅ Manifold(ω)(∇)`; Grassmann docs `∂(Λ(tangent(ℝ^4,2,4)).v1234)`, `boundary_rank`, betti | M |
| `Differential` | — | SKIP | exported but undefined in Julia (`UndefVarError`) | - |
| `⊕`, `tangent`, `isorigin` | — | SKIP | exported but undefined in Leibniz (DirectSum defines them; see §1) | - |
| `Leibniz` | — | SKIP | module | - |
| `Manifold`, `basis`, `value`, `valuetype`, `norm`, `⋆`, `complementleft`, `complementlefthodge`, `complementright`, `complementrighthodge` | re-exports, see §1/§3 | DONE | | - |
| `anticumsum` | `Leibniz.anticumsum` `Leibniz/Combinatorics.lean:110` | DONE | oracle `index_tables`; quirk Q2 (n<2) fixed | - |
| `antiindex` | `Leibniz.antiIndex` (1-based), `antiRank` | DONE | | - |
| `antisum` | `Leibniz.antisum` | DONE | | - |
| `basisindex` | `Leibniz.basisIndex`, `basisRank` | DONE | oracle + exhaustive n ≤ 16 | - |
| `binomcumsum` | `Leibniz.binomcumsum` | DONE | | - |
| `binomsum` | `Leibniz.binomsum` | DONE | | - |
| `bladeindex` | `Leibniz.bladeIndex`, `bladeRank` (+ closed form to n = 62) | DONE | | - |
| `count_gdims` | — | MISSING | per-grade nonzero component counts (Grassmann: betti numbers, `χ`) | S |
| `diffmode`, `diffvars`, `dyadmode`, `options`, `polymode` | `TensorBundle` fields | DONE | | - |
| `expandbits` | `Bits.pdep` `DirectSum/Bits.lean` | DONE | oracle `expandbits` | - |
| `gdimsall` | `Leibniz.gdimsall` | DONE | | - |
| `gdimseven` | — | MISSING | `[C(n,0), C(n,2), …]` | S |
| `gdimsodd` | — | MISSING | `[C(n,1), C(n,3), …]` (total for n = 0, Julia errors) | S |
| `grade`, `pseudograde` | see §1 | DONE | | - |
| `hasinf`, `hasorigin`, `isdual`, `isdyadic`, `istangent` | see §1 | DONE | | - |
| `indexbasis` | `Leibniz.indexBasis`, `indexBasisAll` | DONE | oracle; Q4 (n ∈ {0,1}) fixed | - |
| `indexeven` | `Leibniz.indexEven` | DONE | quirk Q3 fixed (true even list) | - |
| `indexodd` | `Leibniz.indexOdd` | DONE | quirk Q3 fixed | - |
| `indices` | `Bits.indices` | DONE | | - |
| `isbasis` | — | SKIP | type-level (see §1) | - |
| `lowerbits` | `Bits.pext` | DONE | quirk Q1 (history-dependent cache) fixed; kernel `decide` examples + Forms projection goldens | - |
| `metric` | see §1 | DONE | | - |
| `order` | — | MISSING | see §1 | S |
| `spincumsum` | `Leibniz.spincumsum` | DONE | | - |
| `spinindex` | `Leibniz.spinIndex`, `spinRank` | DONE | | - |
| `spinsum` | `Leibniz.spinsum` | DONE | | - |
| `χ` | — | MISSING | `χ(t) = Σ (-1)^p B[p]` with Julia's (anti-docstring) sign, `χ(V,b,t)` for terms | S |
| `≅` | — | MISSING | see §1 | S |

### 2.2 Downstream-public helpers (imported by DirectSum/Grassmann/Cartan)

| Julia symbol | Lean name(s) + file | status | gap description | effort |
|---|---|---|---|---|
| `printindex` | `Leibniz.printIndex` `Leibniz/Indices.lean:75` | DONE | oracle `printindex` grid | - |
| `printindices` (1-list, 4-list, `(io,V,e)`) | `printIndices`, `printIndices4`, `bladeLabel` | DONE | README 62-index goldens | - |
| `printlabel` | `Leibniz.printLabel` `Indices.lean:163` | DONE | via oracle labels of 29 spaces | - |
| `indexstring` | `Leibniz.indexString` | DONE | | - |
| `indexsymbol` | — | SKIP | returns a Julia `Symbol` | - |
| `subs`, `sups`, `alphanumv`, `alphanumw`, `vio`, `pre`, `PRE` | `Leibniz/Indices.lean:22-64` | DONE | | - |
| `vsn`, `VSN`, `digs`, `low_greek`, `upp_greek` | — | SKIP | macro variable-name defaults / unused | - |
| `showvalue`, `showstar`, `showparens` | `JuliaShow.showValue/showStar/needsParens` `JuliaBase/Show.lean:27` | DONE | | - |
| `parval`, `parnot`, `check_parval`, `check_parnot`, `check_field`, `extend_field`, `extend_parnot`, `Fields`, `Field`, `ExprField` | `JuliaShow` / `Coeff` classes | SKIP | mutable global type registries → typeclass instances (port-notes §8.4) | - |
| `shift_indices`, `shift_indices!` | `LabelCtx.shiftIndices`/`shiftList` | DONE | | - |
| `indexbits`, `bit2int`, `index2int` | `Bits.ofIndices` (mask instead of `BitVector`) | DONE | | - |
| `indexsplit` | — | MISSING | `[1<<(k-1) for k ∈ indices(B)]` | S |
| `digitsfast`, `intlog` | `Bits` ops (`ctz`, popcount) | SKIP | cache/float-log helpers superseded by bit intrinsics | - |
| `combo`, `combinations` | `Leibniz.combo`; `MeshTopology.combinations` | DONE | | - |
| `binomial` | `Leibniz.binomial`/`choose` | DONE | | - |
| `indexbasis_set`, `indexeven_set`, `indexodd_set`, `*_set` cumsums | per-grade `indexBasis n g` | SKIP | Julia cache shapes (inconsistent across n = 22) | - |
| `algebra_limit`, `sparse_limit`, `cache_limit`, `fill_limit` | `tableLimit`; thresholds in `showBasis` | DONE | `fill_limit` is Grassmann sparse→dense (Grassmann scope) | - |
| `mvec`, `svec`, `mvecs`, `svecs`, `insert_expr`, `assign_expr!`, `parity*nullpre`, `promote_type`, `VTI`, `SVTI` | `Values α (choose n g)`, `Grassmann.Kernel.Codegen` | SKIP | `@generated` code-generation helpers | - |
| `diffmask` | `TensorBundle.diffmask`/`diffmaskPair` | DONE | | - |
| `symmetricmask` | `TensorBundle.symmetricmask` `Parity.lean` | DONE | via blades/derived goldens | - |
| `symmetricsplit` | — | MISSING | dyadic split of tangent bits | S |
| `diffcheck` | `TensorBundle.diffcheck`, `diffcheck2` | DONE | | - |
| `mixed` | — | MISSING | embed a `V`/`V'` mask into `V⊕V'` (needed by blade `W(b)` embedding) | S |
| `combine` | — (only Compat `combinebasis`) | MISSING | direct-sum embedding of two masks | S |
| `hasconformal` | `TensorBundle.hasconformal` | DONE | | - |
| `hasinf(V,A,B)`, `hasorigin(V,A,B)`, `hasinf2`, `hasorigin2` | — | SKIP | conformal special cases of Julia's `mul`; Lean uses the exact Chevalley product over the Gram matrix | - |
| `loworder(::Int)`, `supermanifold(::Int)` | `TensorBundle.loworder` (see §1) | DONE | `supermanifold` is the type index (SKIP rationale in §1.2) | - |
| `parityreverse`, `parityinvolute`, `parityclifford`, `parityconj` | `Leibniz/Generic.lean:15-26` | DONE | oracle `grade_parities` | - |
| `parityright`, `parityleft`, `parityrighthodge`, `paritylefthodge` | `*Raw` `Leibniz/Generic.lean`, space forms `DirectSum/Parity.lean` | DONE | proved `parityrightRaw_eq_sigma` | - |
| `parityrightnull`, `parityleftnull` | `TensorBundle.nullFactor` | DONE | | - |
| `complement(N,B,D,P)` | `Leibniz.complement` | DONE | oracle `complement`; proof `complement_eq` | - |
| `grade_basis`, `grade(V,B)`, `pseudograde(V,B)` | `gradeOf`, `pseudogradeOf` | DONE | | - |
| `indexparity!(::Values)` | `MeshTopology.indexParity` `MeshTopology/Basic.lean:125` | DONE | lives in MeshTopology (only consumer) | - |
| `indexparity!(::Vector, s)` | `TensorBundle.lookup` (geometric-product signs) | DONE | quirk Q6 fixed | - |
| `∪(x)`, `∪(a,b,c…)`, `∩` variadic | — | MISSING | folds of the binary DirectSum ops (§1.2) | S |
| `isless`, `<=` on grade-0 `TensorTerm` | — | MISSING | compare `value`s of scalar terms | S |
| `==(::Real, ::TensorTerm)`, `equal(::TensorTerm, ::TensorTerm)` | `Grassmann/Dynamic/Equal.lean` | DONE | | - |
| `getbasis(V,::Integer)`, `UInt(::TensorTerm)`, `value_diff`, `unitype` | `.bits`, coercions | SKIP | dispatch shims | - |
| `LinearAlgebra.reflectorApply!(x, τ::TensorAlgebra, A)` | — | SKIP | Householder QR over multivectors not ported (port-notes §8.4) | - |

---

## 3. AbstractTensors.jl (108 exports + public generic methods)

### 3.1 Exports

| Julia symbol | Lean name(s) + file | status | gap description | effort |
|---|---|---|---|---|
| `@co` | `AbstractTensors.co`, `co₂` `AbstractTensors/Ops.lean:275-282`; `Generic.coOf` | DONE | combinator instead of a named-function macro (port-notes §8.5) | - |
| `@pseudo` | `AbstractTensors.pseudo` `Ops.lean:285` | DONE | | - |
| `TensorAlgebra` | class `TensorAlgebra X M V T` `Ops.lean:40` | DONE | | - |
| `Manifold` | `AbstractTensors.Manifold` `Ops.lean:69` | DONE | | - |
| `TensorGraded` | class `TensorGraded` `Ops.lean:44` | DONE | (+ `TensorTerm`, `TensorMixed`) | - |
| `Scalar` | — | MISSING | `TensorGraded{V,0}` alias | S |
| `GradedVector` | — | MISSING | `TensorGraded{V,1}` alias | S |
| `Bivector` | — | MISSING | `TensorGraded{V,2}` alias | S |
| `Trivector` | — | MISSING | `TensorGraded{V,3}` alias | S |
| `Values` | `StaticVectors.Values` | DONE | see §4 | - |
| `Variables`, `FixedVector`, `TupleVector` | `Values` | SKIP | merged into one packed type updated in place when unshared (DESIGN, port-notes §8.5); `FixedVector` aliasing has no pure analog | - |
| `FloatVector`, `FloatMatrix`, `FloatArray`, `RealVector`, `RealMatrix`, `RealArray` | — | SKIP | aliases of Base `AbstractArray` unions; `FloatArray` clashes with Lean core | - |
| `antiabs` | — | MISSING | alias of `coabs` (docstring in `Generic.lean` mentions it, no def) | S |
| `antiabs2` | — | MISSING | alias of `coabs2` | S |
| `antimetric` | unary blade `TensorBundle.antimetric` `BladeAlgebra.lean` | PARTIAL | AT binary `antimetric(a,b) = cometric(a,b)` alias missing | S |
| `antisandwich` | — | MISSING | `complementleft(!R >>> !x)` (+ `g` variant) | S |
| `bivector` | `AbstractTensors.bivector` (GradeProj 2) | DONE | | - |
| `coabs` | `Generic.coabs` `AbstractTensors/Generic.lean` | DONE | oracle GenericTests | - |
| `coabs2` | `Generic.coabs2` | DONE | | - |
| `cocbrt` | `Generic.cocbrt` | DONE | | - |
| `cocos` | `Generic.cocos` | DONE | | - |
| `cocosh` | `Generic.cocosh` | DONE | | - |
| `coexp` | `Generic.coexp` | DONE | | - |
| `coinv` | `Generic.coinv` | DONE | | - |
| `colog` | `Generic.colog` | DONE | | - |
| `cometric` | `Generic.cometric` | DONE | | - |
| `contraction` | class `Contraction`, `⋅`/`⨽` | DONE | | - |
| `cosandwich` | `AbstractTensors.cosandwich` `Ops.lean:290` | DONE | | - |
| `cosin` | `Generic.cosin` | DONE | | - |
| `cosinh` | `Generic.cosinh` | DONE | | - |
| `cosqrt` | `Generic.cosqrt` | DONE | | - |
| `cotan` | `Generic.cotan` | DONE | | - |
| `cotanh` | `Generic.cotanh` | DONE | | - |
| `even` | class `Even`, postfix `₊` | DONE | | - |
| `expansion` | class `Expansion`; Grassmann instance `Algebra/Products.lean:170` (`antidot`) | DONE | | - |
| `gdims` | `AbstractTensors.gdims`, `gdimsOf` `Dims.lean` | DONE | | - |
| `geomabs` | `Generic.geomabs` | DONE | | - |
| `hodge` | class `Hodge`, `⋆` | DONE | | - |
| `interform` | — | MISSING | cross-manifold evaluation `M(a)(M(b))`, `M = V ∪ W` (AT README + test suite) | M |
| `interop` | — | MISSING | cross-manifold operator fallback `op(M(a), M(b))`, `M = V ∪ W` (AT README + test suite) | M |
| `involute` | class `Involute`, postfix `ˣ` | DONE | | - |
| `isbivector` | — | MISSING | `rank(t)==2 || iszero(t)` | S |
| `isgraded`, `ismanifold`, `ismixed`, `istensor`, `isterm` | instance existence | SKIP | type-membership predicates decided at compile time by the class hierarchy | - |
| `isscalar` | `Grassmann/Dynamic/Norms.lean:46` (dynamic), `TensorRing.isScalar`, `isScalarGrade` | PARTIAL | no uniform AT-level `isscalar` on typed elements | S |
| `isvector` | — | MISSING | `rank(t)==1 || iszero(t)` | S |
| `isvolume` | — | MISSING | `rank(t)==mdims(t) || iszero(t)` | S |
| `mdims` | `AbstractTensors.mdims` | DONE | | - |
| `metric` | `Generic.metric` (binary `abs(a-b)`); DirectSum unary | DONE | | - |
| `odd` | class `Odd`, postfix `₋` | DONE | bug B3 fixed (`0 : α`) | - |
| `pseudoabs` … `pseudotanh` (13: `pseudoabs pseudoabs2 pseudocbrt pseudocos pseudocosh pseudoexp pseudoinv pseudolog pseudosin pseudosinh pseudosqrt pseudotan pseudotanh`) | `Generic.pseudo*` abbrevs | DONE | one row for the 13 aliases (same functions as `co*`) | - |
| `pseudometric` | — | MISSING | alias of `cometric` | S |
| `pseudosandwich` | — | MISSING | alias of `cosandwich` (docstring only) | S |
| `rank` | `AbstractTensors.rank` | DONE | | - |
| `sandwich` | class `Sandwich`, `⊘`; Grassmann instances | DONE | | - |
| `scalar` | `AbstractTensors.scalar` | DONE | | - |
| `tdims` | `AbstractTensors.tdims`, `tdimsOf` | DONE | | - |
| `unit` | `Generic.unit` | DONE | | - |
| `unitize` | `Grassmann/Composite/Ring.lean` (`counit`/`unitize`) | DONE | | - |
| `unitnorm` | `Generic.unitnorm` | DONE | | - |
| `valtype` | — | SKIP | alias of `valuetype` that clashes with `Base.valtype` (unusable unqualified in Julia) | - |
| `value` | `AbstractTensors.Value` | DONE | | - |
| `valuetype` | `AbstractTensors.valuetype` | DONE | | - |
| `vector` | `AbstractTensors.vector` | DONE | | - |
| `veedot` | class `VeeDot`, `⟇`; Grassmann `Products.lean:164` | DONE | | - |
| `volume` | class `Volume`; Grassmann `Unary.lean:289` | DONE | | - |
| `wedgedot` | class `WedgeDot`, `⟑` | DONE | | - |
| `×` | class `Cross`, `instCrossOfWedgeHodge` `Ops.lean:270` | DONE | (Julia: undefined in AT, `LinearAlgebra.cross`) | - |
| `ǂ` | scoped postfix `ǂ` → `Conj.conj` | DONE | | - |
| `ˣ` | scoped postfix `ˣ` | DONE | | - |
| `⁻¹` | core `Inv` postfix; Grassmann `Inv` instances | DONE | | - |
| `₊` | scoped postfix `₊` | DONE | | - |
| `₋` | scoped postfix `₋` | DONE | | - |
| `∗` | scoped `∗` → `reverseProduct` | DONE | | - |
| `⊖` | scoped `⊖` (geometric product at `+` level) | DONE | | - |
| `⊗` | class `TensorProd`, `⊗` | PARTIAL | AT's scalar lift `a ⊗ λ = a*λ`, `λ ⊗ a` missing (tensor product itself is Grassmann scope) | S |
| `⊘` | `⊘` | DONE | | - |
| `⊙` | class `SymProd`, `⊙` | DONE | declared only, as in AT | - |
| `⊛` | `⊛` → `scalarProduct` | DONE | | - |
| `⊠` | class `AntiSymProd`, `⊠` | DONE | declared only, as in AT | - |
| `⋆` | `⋆` | DONE | | - |
| `⟇` | `⟇` | DONE | | - |
| `⟑` | `⟑` | DONE | | - |
| `⨼` | `⨼` → `leftContraction` | DONE | | - |
| `⨽` | `⨽` | DONE | | - |

### 3.2 Public generic methods and non-exported API

| Julia symbol | Lean name(s) + file | status | gap description | effort |
|---|---|---|---|---|
| `TensorTerm`, `TensorMixed` | classes `Ops.lean:48-53` | DONE | | - |
| `trivector`, `istrivector` | `AbstractTensors.trivector`; — | PARTIAL | `istrivector` missing (see `isvector`) | S |
| `pseudoscalar` (= `volume`) | `Volume`, `Submanifold.pseudoscalar` | DONE | | - |
| `complement`, `complementright` (`!`) | `ComplementRight`, `!` | DONE | | - |
| `UniformScaling` / `I` | `AbstractTensors.UniformScaling` + complement instances `Ops.lean:301-317` | PARTIAL | AT's lifts `op(a, λI) = op(a, V(λI))` / `op(λI, a)` for `+ - * ⊘ ⊛ ∗ ⨼ ⨽ ⋅ ⟇ ⟑ ∧ ∨ …` (AT test `Manifold(a+I) == ℝ`) missing for tensor types; only `TensorOperator ± I` in Forms | M |
| `interop`/`interform` contract | — | MISSING | see §3.1 | M |
| `/`, `\`, `^`, `exp`, `log(b,t)`, `log2`, `log10`, `exp2`, `exp10` | `Generic.div/ldiv/rpow/logBase/log2/log10/exp2/exp10`, `TensorRing.exp` | DONE | oracle; B1 fixed | - |
| `cos sin tan cot sec csc asec acsc sech csch asech acsch tanh coth asinh acosh atanh acoth asin acos atan acot sinc cosc` | `Generic.*` `AbstractTensors/Generic.lean` | DONE | oracle on scalar carriers (B2 replicated) | - |
| `abs`, `abs2`, `norm`, `iszero`, `isapprox` | `Generic.abs/abs2/isZero/isapprox`; Grassmann norms | DONE | | - |
| `isone` | — | MISSING | `norm(t) ≈ value(scalar(t)) ≈ 1` | S |
| `norm(a,b)` | — | MISSING | `norm(a-b)` | S |
| `isfinite(::TensorTerm)`, `isnull` | — | MISSING | trivial predicates | S |
| metric family (`wedgedot_metric`, `contraction_metric`, `log_metric`, `f(t,g)` for every transcendental, `abs(t,g)`, `unit(t,g)`, `/(a,b,g)`, `^(a,b,g)`) | skeletons `TensorBundle.mulSkeleton`/`contractionSkeleton` `BladeAlgebra.lean:180-192`; doc mentions `metricRing` | PARTIAL | no runtime-metric `TensorRing` instance / products; `metricRing` referenced in `Generic.lean:23` but undefined (Cartan Riemannian fields need it) | M |
| `<<`, `>>` | `shiftLeftContraction`, `shiftRightContraction` `Ops.lean:261-266` | PARTIAL | functions only, no notation | S |
| `<`, `>`, `\|` (contraction aliases), unary `\|` | `⨼`, `⨽`, `⋅` | SKIP | Lean `<`/`>` are Prop-valued relations; `\|` is reserved syntax | - |
| `>>>` | `HShiftRight` instances `Grassmann/Algebra/Products.lean:219` | DONE | | - |
| `cross(a,b) = hodge(a∧b)` | `instCrossOfWedgeHodge` | DONE | | - |
| `!(t::Real)`, `!(λI)`, `hodge(scalar)` | `ComplementRight`/`Hodge` scalar instances | DONE | AT test `!I == 1` covered | - |
| `rtoldefault(::Type{TA})`, `parent(x)` | `JApprox.rtolDefault`, `Manifold` | DONE | | - |
| symbolic hooks (`∏ ∑ PROD SUM SUB √`, `norm/signbit/≈` on `Expr`/`Symbol`) | `Values.prod/sum` | SKIP | symbolic coefficients need Reduce/SymPy; deferred by port-notes §8.5 | - |
| `Postfix{Op}`, `TAG`, `plus/minus/times/equal` internals | notation / classes | SKIP | Julia dispatch plumbing | - |

---

## 4. StaticVectors.jl (4 exported types + the public `AbstractVector` API)

| Julia symbol | Lean name(s) + file | status | gap description | effort |
|---|---|---|---|---|
| `Values` | `StaticVectors.Values α n` `StaticVectors/Values.lean:24` (`Packed`: `FloatArray` for `Float`) | DONE | oracle StaticVectorsTests | - |
| `Variables` | `Values.set`/`modify` (in place when unshared) | SKIP | merged into `Values` | - |
| `FixedVector` | — | SKIP | wraps and aliases a mutable `Vector`; no pure analog | - |
| `TupleVector` | — | SKIP | abstract supertype | - |
| `SVector`, `MVector`, `SizedVector`, `SOneTo`, `TupleMatrixLike` | `Fin n` | SKIP | aliases / static axes | - |
| `TV[…]`, `Values(x…)`, `Values{N,T}(x…)` literals | `Values.ofFn`, `ofList?`, `ofArray?` | PARTIAL | no length-inferring literal (README quick start `Values(1, 2, 3)`); construction from lists returns `Option` | S |
| `Values{N}(::AbstractVector)`, generators | `ofList?`/`ofArray?` | DONE | `DimensionMismatch` → `none` | - |
| `zeros`, `ones`, `fill` | `Zero` instance, `replicate` | DONE | `ones` = `replicate 1` | - |
| `rand`, `randn`, `randexp` | — | SKIP | Julia RNG streams not reproducible (port-notes §8.5) | - |
| `similar`, `similar_type`, `copy`, `convert`, `promote` | — | SKIP | static result types / immutability | - |
| `Tuple(v)`, `Vector(v)` | `toArray`, `toList` | DONE | | - |
| `length`, `size`, `axes`, `IndexStyle`, `strides`, `view` | length is the type index | SKIP | | - |
| `getindex` (`v[i]`, `v[idx::TupleVector]`, `v[:]`) | `GetElem`, `get`, `gather` | DONE | | - |
| `setindex!` (scalar, scatter) | `set`, `modify`, `scatter` | DONE | B16 fixed | - |
| `+`, `-`, unary `-`, `s*a`, `a*s`, `a/s`, `s\a`, `muladd` | `Values` instances `Values.lean:279-305`, `leftDiv`, `muladd` | DONE | oracle | - |
| `map`, `map!` | `map`, `mapIdx`, `zipWith`, `zipWith3` | DONE | B10 fixed; arity > 3 via `ofFn` | - |
| `mapreduce`, `reduce`, `foldl`, `mapfoldl` | `mapReduce`, `reduce`, `foldl`, `mapFoldl` `StaticVectors/Reduce.lean` | DONE | Julia `reduce_first` rule kept | - |
| `sum`, `prod`, `count`, `all`, `any`, `in`, `iszero` | `Reduce.lean` | DONE | | - |
| `minimum`, `maximum` (+ `f` forms) | `minimum/maximum/minimumMap/maximumMap` | DONE | Julia NaN/`-0.0` semantics; B8 fixed | - |
| `accumulate`, `cumsum`, `cumprod` | `accumulate`, `accumulateInit`, `cumsum`, `cumprod` | DONE | | - |
| `diff` / `_diff` | `Values.diff` | DONE | | - |
| `dot`, `bilinear_vecdot` | `Values.dot`, `bilinearDot` `StaticVectors/LinAlg.lean` | DONE | left-conjugating, Julia order | - |
| `norm`, `norm(a,p)`, `norm_sqr` | `norm`, `normP`, `normSqr` | DONE | B9 fixed | - |
| `normalize`, `normalize!` | `normalize`, `normalizeP` | DONE | reciprocal multiply replicated | - |
| `isapprox` | `JApprox` instance, `Values.isapprox` | DONE | | - |
| `cross` (3-vectors), `a*b'` | `Values.cross`, `outer` | DONE | B19 fixed | - |
| `reverse`, `vcat` | `reverse`, `append`/`vcat`/`++` | DONE | | - |
| `reduce(vcat, A)`, `reduce(hcat, A)` | — | SKIP | heterogeneous-length results; use `append` folds | - |
| broadcasting (`sin.(v)`, `.+`) | `map`/`zipWith` | SKIP | redesigned as explicit maps (port-notes §8.5) | - |
| `countvalues`, `evenvalues`, `evens` | `StaticVectors/Ranges.lean` | DONE | B17 fixed | - |
| `==`, `isless`, `hash` | `BEq`, `DecidableEq`, `Ord`, `Hashable` | DONE | | - |
| `show`/`print`/`repr` (`[1.0, 2.0]`, eltype prefix, text/plain display) | `ToString`/`Repr` `Values.lean:330-342` | PARTIAL | element `toString` is Lean's (`0.500000`), not Julia's shortest repr; no eltype prefix (`Float32[…]`), no `N-element Values{N, T} with indices SOneTo(N):` display; no `JuliaShow (Values α n)` instance | S |
| `Base.rest` destructuring | — | SKIP | broken in Julia (B13) | - |

---

## 5. Performance parity (foundation data structures)

| Item | Lean | status | gap description | effort |
|---|---|---|---|---|
| Small `Values Float n` results (allocation floor) | `FloatArray` per result | IN_PROGRESS | PERF.md: 9–13 ns floor vs Julia 0.7–3 ns (isbits tuples); in-place reuse exists; expression fusion + SoA batch arrays (`Grassmann/Fuse`, `Grassmann/Batch`) in flight | - |
| `Values` reductions (`foldl`, `mapReduce`, `sum`, `dot`, `norm`) | structural `Nat`-indexed loops `Values.lean:151-190`, `Reduce.lean:26-40`, `LinAlg.lean:36` | PARTIAL | PERF.md: ≈ 2 ns per coefficient (Julia unrolls/SIMD); `norm` sits inside every series stopping rule (`expm1Series`, `qlog`, …) | M |
| Index tables (`bladeindex`, `basisindex`, `indexbasis`) vs Julia caches | `Thunk` tables n ≤ 12, closed forms to n = 62 | IN_PROGRESS | no Lean-vs-Julia timing yet; Lean-vs-Julia benchmark harness (`Bench/Harness`) in flight. Lean closed forms avoid Julia's O(C(n,k)) search for n > 20 | - |

---

## 6. JuliaBase (Lean-side support for Julia `Base` semantics the foundations print/compare with)

Not a Julia package; listed for completeness. All oracle-tested in `Tests/JuliaBase/*`.

| Base behaviour | Lean | status |
|---|---|---|
| `show(::Float64/Float32)` (Ryu shortest, compact 6 digits) | `JuliaBase/Ryu.lean`, `Float.lean` (`F64.showString`) | DONE |
| `isapprox`, `max`/`min` (NaN, `-0.0`), `rtoldefault`, `rem/mod/div/fld/cld`, `round` | `JuliaBase/Num.lean`, `Round.lean` | DONE |
| `exp log expm1 log1p ^ sin cos tan asin … sinh cosh tanh …` bit-exact | `JuliaBase/Math.lean`, `Trig.lean`, `Hyperbolic.lean` | DONE |
| `Complex{T}` / `ComplexF64` algorithms | `JuliaBase/Complex.lean` | DONE |
| `parse(Float64, s)`, `sum(::Vector{Float64})`, `Float16`, ranges | `Parse.lean`, `Sum.lean`, `Float16.lean`, `Range.lean` | DONE |
| `show` of `Values` elements | — | see §4 `show` row (PARTIAL) |

---

## 7. Documented behaviour not yet expressible in Lean

| Source | Example | Blocking gap |
|---|---|---|
| DirectSum README:69-76, test lines 6, 9, 10 | `ℝ⊕ℝ' ⊇ TensorBundle(1)`, `ℝ ∩ ℝ' == TensorBundle(0)`, `ℝ ∪ ℝ' == ℝ⊕ℝ'` | `ℝ` constant; `∪ ∩ ⊆ ⊇` |
| DirectSum README:43, test line 5 | `ℝ'⊕ℝ^3` | `ℝ` constant (works as `(ℝ^1)′ ⊕ ℝ^3`) |
| DirectSum README:124 | `V+V'` | `+` alias |
| DirectSum README:167-171, test line 12 | `v1 ⊆ v12`, `v12 ⊆ V` | blade/subspace `⊆` |
| DirectSum README:179-183, test line 11 | `indices(Λ(3).v12)` | `Λ` container syntax (works as `(V!"3").lookup "v12"`) |
| DirectSum test line 13 | `Λ(62).v32a87Ng == -1Λ(62).v2378agN` | `Λ` syntax (lookup itself DONE) |
| DirectSum test line 15; Grassmann `design.md:115` | `Λ(ℝ^14) ⊕ Λ(ℝ^14)'`, `Λ(7) ⊕ Λ(7)'` | `Λ` container `⊕`/`'` (display exists as `showBasis`) |
| DirectSum README:143-150 | `@basis` with custom space/prefix names | `basis!` arguments |
| Grassmann `algebra.md:1397` | `@mixedbasis tangent(ℝ^1)` | `@mixedbasis` binding `V`, `V'`, `V⊕V'` |
| Grassmann `algebra.md:309` | `collect(V(1,4))` | subspace basis display |
| Leibniz README:30-53, test | `∇^2 == Δ`, `(∇, Δ)` display | `Derivation`, `∇`, `Δ` |
| Grassmann `algebra.md:1104-1120, 1342, 1414` | `tangent(ℝ^3)(∇)`, `∂(Λ(tangent(ℝ^4,2,4)).v1234)`, `χ(Δ(ω))`, `V(∇) ⋅ V(∇)` | `Derivation`, `V(∇)` functor, `d/δ/∂`, `χ` |
| AbstractTensors README + `test/runtests.jl:1-40` | `interop(op,a,b)`, `interform`, `op(a,I)`, `a+I` | `∪`, `interop`/`interform`, `UniformScaling` lifts |
| StaticVectors/AbstractTensors README quick start | `Values(1, 2, 3)`, printed `[1.0, 2.0, 3.0]` | `Values` literal; Julia `show` for `Values` |
