# Parity matrix: grassmann-core (Grassmann.jl 0.8.46 vs Lean port @ master 0ac54fdd)

Scope: every name in `names(Grassmann)` (316 rows incl. re-exports from DirectSum / Leibniz /
AbstractTensors / LinearAlgebra, enumerated live with the oracle env: `scratchpad/parity/names.tsv`,
method counts in `meth.tsv`), the Base/LinearAlgebra methods Grassmann adds (`basemeth.tsv`, 99
functions), Julia-visible behaviour of `ext/`, documented behaviour (README + docs goldens), display
and performance. Lean side searched: `Grassmann/**`, `AbstractTensors/`, `StaticVectors/`,
`JuliaBase/`, plus `DirectSum/`, `Leibniz/`, `Cartan/`, `gallery/` where a name lives there.

Evidence runs (read-only, prebuilt `.lake/build/bin/tests` of HEAD):
`tests Golden` → construct 1219/1222 (3 unimplemented), arith 20427 pass, products 74488 pass,
unary 10220 pass, composite 1039 pass, floats 20394 pass, **docs 51 pass / 416 unimplemented / 29
defect-skipped of 501**. `tests Grassmann Dynamic Composite Forms Codegen AbstractTensors` → all pass
(Forms: exact 2511, float 1821, spectral 775, diag 359, geometry 998).

Legend: status DONE (implemented + oracle-tested) · PARTIAL (missing methods/kinds/options, or untested)
· MISSING · IN_PROGRESS (in-flight workstream) · SKIP (Julia-specific; justified). Effort S/M/L.
"typed" = static layer (`Chain/Half/Multivector/Single/Couple/...`), "TA" = dynamic Julia-exact layer
(`Grassmann/Dynamic/*`).

## A. Spaces, basis generation (DirectSum/Leibniz re-exports)

| Julia symbol | Lean name(s) + file | status | gap description | effort |
|---|---|---|---|---|
| `⊕` | `TensorBundle.oplus`, `V ⊕ W` (DirectSum/SpaceOps.lean:76) | DONE | — | — |
| `ℝ` | `ℝ^1` / `V!"+"` (DirectSum/Parse.lean:147) | PARTIAL | no bare `ℝ` constant (Mathlib `ℝ` token clash); `ℝ'⊕ℝ^3` (docs 03) must be spelled `(ℝ^1).dual ⊕ ℝ^3` | S |
| `ℝ0`…`ℝ9` | DirectSum/Common.lean:14-32 | DONE | — | — |
| `@V_str` `@S_str` `@D_str` | `V!"…"` `S!"…"` `D!"…"` (DirectSum/Parse.lean:137-143) | DONE | — | — |
| `@basis`, `@basis_str` | `basis! V` (Grassmann/Basis.lean:48) | PARTIAL | no custom names (`@basis ℝ^3 E e`, docs 31), no `sig vec cov duo dif` args; `𝟎`,`∞`,`v⃖` not bound; blades are `Submanifold` only (no `Coe` into `TA`, so the Julia-exact layer is not reachable from basis names) | S |
| `@dualbasis`, `@dualbasis_str` | `basis! V.dual` / `basis! V′` (labels `w¹…`) | PARTIAL | works via `basis!` on the dual bundle but untested (Tests only cover `S!"+++"`, `S!"∞∅+++"`); no alias command | S |
| `@mixedbasis`, `@mixedbasis_str` | `basis! (V ⊕ V′)` | PARTIAL | untested; mixed/dyadic *products* have no product goldens (no DUAL/DYAD/TAN product shards) | S |
| `Λ` | `TensorBundle.lookup` (DirectSum/Names.lean:93), `show(Λ(V))` (DirectSum/Show.lean:151) | PARTIAL | `Λ(V).v21` returns a DirectSum `BladeResult`, no conversion helper to `TA`/`Single`; `Λ(V).b`, `Λ(V)[i]` not provided at Grassmann level | S |
| `Signature`, `DiagonalForm`, `Submanifold`, `Manifold` | `TensorBundle` + `Metric.signature/diagonal/tensor` (DirectSum/Space.lean), `DirectSum.Submanifold V G`, `AbstractTensors.Manifold` (Ops.lean:69) | DONE | — | — |
| `mdims` | `TensorBundle.mdims` (Space.lean:101), `AbstractTensors.mdims` (Ops.lean:78) | DONE | — | — |
| `tangent`, `istangent` | `TensorBundle.tangent` (SpaceOps.lean:133), `istangent` (Space.lean:110) | DONE | space level only; tangent-space element calculus see §H | — |
| `hasinf`, `hasorigin` | `TensorBundle.hasinf/hasorigin` fields | DONE | — | — |
| `metric` (Leibniz) | element map: typed `.metric` (Algebra/Unary.lean:57), `TA.metric` (Dynamic/Unary.lean:248) | DONE | unary goldens | — |
| `indices` | `Submanifold.indices` (DirectSum/Blade.lean:48), `Bits.indices` | PARTIAL | no `indices` of `Single`/`TA` term (`indices(basis(t))`) | S |
| `One`, `Zero` | `TA.one`, `TA.zero` (Dynamic/Basic.lean:40), `One`/`Zero` instances (Algebra/Arith.lean:41-54) | DONE | — | — |
| `Single` | `Grassmann.Single` (Types/Single.lean:22), `TA.single` | DONE | — | — |
| `Values` | `StaticVectors.Values` | DONE | — | — |

## B. Element types and type aliases

| Julia symbol | Lean name(s) + file | status | gap description | effort |
|---|---|---|---|---|
| `Chain` | `Chain V G α` (Types/Chain.lean:20), `TA.chain` | DONE | literal ctor gap see §M | — |
| `Multivector` | `Multivector V α` (Types/Multivector.lean:18), `TA.multi` | DONE | — | — |
| `Spinor` | `Spinor V α := Half V false α` (Types/Half.lean:26), `TA.spinor` | DONE | — | — |
| `CoSpinor`, `AntiSpinor` | `CoSpinor`/`AntiSpinor` abbrevs (Types/Half.lean:29-32), `TA.cospinor` | DONE | — | — |
| `AbstractSpinor` | — | SKIP | abstract Julia supertype; `Half V p α` covers both parities | — |
| `Couple` | `Couple V α` (Types/Couple.lean:24), `TA.couple` | DONE | typed `1 + v12` yields `Multivector` (kind loss by design); Julia kind via TA only | — |
| `PseudoCouple` | `PseudoCouple V α` (Types/Couple.lean:34), `TA.pseudo` | DONE | — | — |
| `Phasor`, `∠` | `Phasor V α` (Types/Couple.lean:46), `Phasor.mk'`, `Phasor.angleOn` (Composite/Couple.lean:552), `TA.phasor` | PARTIAL | no `∠` notation; Phasor ops Float-only; TA phasor has no arithmetic/composite (`==` against Couple unsupported); `(z::Phasor)(t,θ)` 2-arg call missing | S |
| `Quaternion` | `Spinor V α` on n=3; `Spinor.quaternion` (Types/Half.lean:118) | PARTIAL | no `Quaternion`/`LipschitzInteger`/`AntiQuaternion` aliases; typeof display not reproduced | S |
| `GaussianInteger` | `Couple V Int` | SKIP | Julia type alias only visible through `typeof` printing | — |
| `Simplex` | `Simplex V W α := TensorOperator V (.chain 1) W (.chain 1) α` (Forms/Operator.lean:86) | DONE | simplex.json goldens | — |
| `Multiplex` | — | MISSING | `Multivector{V,<:Multivector}` nested coefficients; no nested-coefficient containers (Forms uses `Mat` instead) | M |
| `ChainBundle` | — | SKIP | legacy mesh bundle type superseded by Cartan `TensorField`/bundles (Cartan in its own key) | — |
| `TensorNested` | — (per-type structures + `InLayout`/`OfLayout` classes, Forms/Operator.lean:42-49) | SKIP | Julia abstract supertype; Lean has no subtyping | — |
| `TensorAlgebra`, `TensorGraded`, `TensorTerm`, `TensorMixed` | classes (AbstractTensors/Ops.lean:40-52) | DONE | — | — |
| `Scalar`, `GradedVector`, `Bivector`, `Trivector` | `Chain V 0/1/2/3 α` | PARTIAL | no alias abbrevs | S |
| `AbstractReal` `AbstractComplex` `AbstractRational` `AbstractInteger` `AbstractBool` `AbstractSigned` `AbstractUnsigned` `ScalarFloat` `ScalarIrrational` | — | SKIP | Julia `Union` aliases for dispatch; no Lean analog needed | — |
| `UniformScaling` | `AbstractTensors.UniformScaling` (Ops.lean:301), `T + λI` (Forms/Operator.lean:289-295) | DONE | — | — |
| `I` | — | PARTIAL | no `I : UniformScaling` constant; README "universal pseudoscalar `I`" not expressible as `I` | S |
| `MultiGrade`, `SparseChain` | — | SKIP | stale exports (undefined in 0.8.46) | — |
| coefficient types (Julia any `Number`) | `Coeff` instances Float, Float32, Int, Rat, Complex α (AbstractTensors/Coeff.lean:101-132) | PARTIAL | no automatic promotion (Int·v1 + 2.5·v2 is a type error; harness promotes outside the library); no BigFloat/Float16/Irrational coefficients; no nested (element-valued) coefficients | M |

## C. Arithmetic, equality, inversion, powers

| Julia symbol | Lean name(s) + file | status | gap description | effort |
|---|---|---|---|---|
| `+`, `-` (incl. Julia promotion lattice) | typed `Add/Sub/HAdd` (Algebra/Arith.lean:38-101), `TA.add/sub` (Dynamic/Arith.lean:212-320) | DONE | arith goldens 20427 | — |
| `*` scalar, `/` scalar, `//` | typed `HMul/HDiv/SMul` (Arith.lean:106-140), `TA.smul/divScalar` | DONE | — | — |
| `/` element÷element | typed `HDiv X Y Z` (Algebra/Norms.lean:177-185) | PARTIAL | TA has no `/` between elements (docs 30/31/45: `-n*a/n`, `a/a`) | S |
| `\` | `Simplex.ldiv`/`solve` (Forms/Compound.lean:548-554) | PARTIAL | element `n\a` (docs 31) missing on typed and TA (Lean `\` via `SDiff`/custom notation) | S |
| `^` | `Single/Chain/Half/Multivector/Couple/Phasor.pow` (Float only; Composite/*.lean), `powJulia` (Composite/Series.lean:184) | PARTIAL | no `HPow` instance; no exact Int/Rat powers (`(v1+v2)^3`, `v12^2`, `i^2`); no negative powers via `inv`; no TA powers; `2^v12` = `rpow` Float only | M |
| `inv` | typed `Inv` (Norms.lean:64-154), `Half/Multivector.inv?` | PARTIAL | TA has no `inv` (Julia result kinds: `inv(3v1)` Single, `inv(1+v12)` Couple) | S |
| `==` | typed `BEq`, `TA.equal` (Dynamic/Equal.lean:64) | DONE | — | — |
| `≈`, `isapprox` | typed `isapprox` (Norms.lean:45), `Chain.isapprox` | PARTIAL | no `TA.isapprox` | S |
| `iszero`, `isone`, `isfinite` | `isZero` (typed) | PARTIAL | `isone`/`isfinite` missing | S |
| `zero`, `one` | `Zero/One` instances, `TA.zero/one` | DONE | — | — |

## D. Products and binary operators

| Julia symbol | Lean name(s) + file | status | gap description | effort |
|---|---|---|---|---|
| `∧`, `wedge` | `Wedge` instances (Algebra/Products.lean:94-109), `TA.wedge` (Dynamic/Products.lean:552) | DONE | products goldens; TA lacks the infix instance (§M) | — |
| `∨`, `vee`, `&` | `Vee` (Products.lean:115-133), `TA.vee` | DONE | ASCII `&` SKIP (Lean `&&&` is bitwise) | — |
| `*`, `⟑`, `⊖`, `wedgedot` | `HMul`/`WedgeDot` (Products.lean:58-90), `TA.mul` | DONE | — | — |
| `⋅`, `dot`, `contraction`, `⨽`, `\|`, `>` | `Contraction` (Products.lean:139-154), `TA.contraction` | DONE | ASCII `\|`/`>` SKIP (Lean `>` is Prop-valued) | — |
| `⨼`, `<` | `leftContraction` (AbstractTensors/Ops.lean:249), `TA.lcontraction` | DONE | ASCII `<` SKIP | — |
| `<<`, `>>` | `shiftLeftContraction`/`shiftRightContraction` (Ops.lean:261-265), `TA.lshift/rshift` | PARTIAL | functions only, no infix notation | S |
| `∗` | `reverseProduct` (Ops.lean:253), `TA.revmul` | DONE | — | — |
| `⊛` | `scalarProduct` (Ops.lean:257), `TA.scalarprod` | DONE | — | — |
| `×`, `cross` | `Cross` (Ops.lean:270), `TA.cross` | DONE | — | — |
| `⊘`, `sandwich` | `Sandwich` (Products.lean:197-332), fused `SandwichKernels`, `TA.sandwich` | DONE | — | — |
| `>>>` | `HShiftRight` (Products.lean:219-341), `TA.tsandwich` | DONE | — | — |
| `⟇`, `veedot` | `VeeDot` (Products.lean:163), `TA.veedot` | DONE | — | — |
| `antidot`, `codot` (`expansion`) | `antidot`/`Expansion` (Products.lean:169-174), `TA.antidot` | PARTIAL | `codot` alias missing | S |
| `cosandwich`, `pseudosandwich` | `cosandwich` (Ops.lean:290) | PARTIAL | `pseudosandwich` alias missing (named only in docstring); untested | S |
| `antisandwich` | — | MISSING | `complementleft(complementright(R) >>> complementright(x))` | S |
| `⊗` | `TensorProd (Chain) (Chain) (Dyadic)` (Forms/Dyadic.lean:95) | PARTIAL | only Chain⊗Chain; scalar⊗graded (= `*`), Single/Submanifold/TA operands missing | S |
| `⊙`, `⊠` | notation only (Notation.lean:91-93), no instances | MISSING | Julia broken (defect `symmetrize-permutations`); implement intended symmetrization `Σσ∏ω/K!` | S |
| `∥` | — | MISSING | `iszero(a∧b)` parallel test | S |
| `⟂` | — | SKIP | stale export | — |

## E. Unary maps, parts, predicates, accessors

| Julia symbol | Lean name(s) + file | status | gap description | effort |
|---|---|---|---|---|
| `~`, `reverse` | `Reverse` instances (Algebra/Unary.lean:217-222), `TA.reverse` | DONE | — | — |
| `involute`, `ˣ` | `Involute` (Unary.lean:224-229), `TA.involute` | DONE | — | — |
| `clifford` | `Clifford` (Unary.lean:231-236), `TA.clifford` | DONE | — | — |
| `conj`, `ǂ` | `Conj` (Unary.lean:239-244) | DONE | — | — |
| `'`, `adjoint` | `TensorBundle.adjoint` + `TA.retarget` (Dynamic/Unary.lean:388) | PARTIAL | composed only in the test harness (`AnyTA.adjoint`); no library `adjoint` on TA/typed | S |
| `antireverse`, `pseudoreverse` | `.antireverse` (Unary.lean:51), `TA.antireverse` | PARTIAL | `pseudoreverse` alias missing | S |
| `even`/`₊`, `odd`/`₋` | `Even/Odd` (Unary.lean:274-282), `TA.even/odd` | DONE | — | — |
| `real`, `imag` (Base) | `.realPart/.imagPart`, `TA.realPart/imagPart` | DONE | — | — |
| `!`, `complement`, `complementright` | `ComplementRight` (Unary.lean:255-258), `TA.complementright` | DONE | — | — |
| `complementleft` | `ComplementLeft`, `TA.complementleft` | DONE | — | — |
| `⋆`, `hodge`, `complementrighthodge` | `Hodge`, `TA.hodge` | DONE | — | — |
| `complementlefthodge` | `.complementlefthodge`, `TA.complementlefthodge` | DONE | — | — |
| `complementrightanti`, `complementleftanti` | typed `.complementrightanti/leftanti` (Unary.lean:78-80) | PARTIAL | not in TA; untested vs oracle | S |
| `antimetric`, `cometric`, `pseudometric` | `.antimetric`, `TA.antimetric`, `Multivector.cometric a b` (Composite/Ring.lean:201) | PARTIAL | `cometric`/`pseudometric` aliases of the unary map missing | S |
| `scalar`, `vector`, `bivector`, `trivector` | `GradeProj` abbrevs (Ops.lean:238-244), `TA.scalar/vector/bivector/trivector` | DONE | — | — |
| `pseudoscalar`, `volume` | `Volume` (Unary.lean:289), `TA.volume`, `Submanifold.pseudoscalar` | DONE | — | — |
| `grade` | static `G`, `rank` (Ops.lean:75), `TA.grade?`; `gradePart x g`, `TA.gradeProj` | DONE | call syntax `A(g)` see §M | — |
| `pseudograde`, `antigrade` | `TensorBundle.pseudogradeOf` (bits, DirectSum/Parity.lean:124) | PARTIAL | no element-level `pseudograde`/`antigrade` | S |
| `abs2` | typed `.abs2` (Norms.lean:58-171), `TA.abs2` (Dynamic/Norms.lean:58) | DONE | — | — |
| `norm` | `Grassmann.norm` (Norms.lean:31), `TA.norm` | DONE | — | — |
| `abs` | `Chain.abs` (Float, Composite/Ring.lean:357), `Multivector.abs` (Ring.lean:182) | PARTIAL | Julia returns an element (`abs(a)=3.74v`, `abs(1+v12)` Single); Lean returns `Float` for chains; missing for Single/Couple/Spinor/TA | S |
| `unit` | `Multivector.unit` (Ring.lean:184) | PARTIAL | missing for Chain/Single/Couple/Spinor/TA (`unit(a)` docs 45) | S |
| `unitize`, `unitnorm`, `geomabs` | `Multivector.unitize/unitnorm/geomabs` (Ring.lean:190-195) | PARTIAL | Multivector-only | S |
| `antiabs`, `antiabs2` (`coabs`, `pseudoabs`) | `Multivector.coabs/coabs2`, `Chain.coabs/coabs2` (Ring.lean:389-392), `Generic.pseudoabs` | PARTIAL | `antiabs*` aliases missing; Single/Couple/TA missing | S |
| `value` | `AbstractTensors.Value` instances (Types/*.lean) | DONE | — | — |
| `valuetype` | `AbstractTensors.valuetype` (Ops.lean:72) | DONE | — | — |
| `basis` | `Single.basis` (Types/Single.lean:44) | PARTIAL | `basis(V)`/basis list per space missing at Grassmann level | S |
| `gdims`, `tdims` | `gdims n g`, `tdims n` (AbstractTensors/Dims.lean), `gdimsOf/tdimsOf` (Ops.lean:81-84) | DONE | — | — |
| `isscalar` | `TA.isscalar` (Dynamic/Norms.lean:46), `Multivector/Half.isScalar` (Float) | DONE | — | — |
| `isvector`, `isbivector`, `istrivector`, `isvolume` | — | MISSING | `rank(t) == k \|\| iszero(t)` | S |
| `isgraded`, `isterm`, `istensor` | `TA.isGraded`, `TA.isTerm` (Dynamic/Products.lean:590-595, internal) | PARTIAL | not public API; `istensor` missing; README-listed | S |
| `imaginary` | `Couple.imaginary` (Types/Couple.lean:75) | PARTIAL | Spinor/PseudoCouple variants missing | S |
| `realvalue`, `imagvalue` | fields `.re/.im` | PARTIAL | no named accessors (Couple/PseudoCouple/Phasor/Complex) | S |
| `radius` | `Couple/Half/Phasor.radius` (Composite/Couple.lean:138, Spinor.lean:46, Couple.lean:545) | PARTIAL | missing for Chain/Multivector/Single (`Real(abs z)`) and `radius(z,g)` | S |
| `angle` (Base) | `Couple.angle` (Couple.lean:151), `Half.angle` (Spinor.lean:66) | PARTIAL | Phasor/TA `angle` missing | S |
| `amplitude`, `phase`, `unitangle` | `Phasor.amp` field | PARTIAL | `phase`, `unitangle`, `amplitude(z)=radius(z)` for non-phasors missing | S |
| `complexify` | `Chain.complexify` (Spinor.lean:229), `Couple.complexify`, `PseudoCouple.complexify` (Spinor.lean:220), `Phasor.complexify` (Couple.lean:496), `Single.toCouple` | PARTIAL | non-simple phasor case (`amplitude ⊘ exp(angle/2)`) and `g` variant missing; docs 09 tested | S |
| `vectorize` | `Couple.vectorize → Values α 2` (Couple.lean:162) | PARTIAL | Julia returns `Chain` over `_subspace(V,B)`; PseudoCouple/Phasor/Single/Complex variants missing | S |
| `polarize` | `Couple.polarize`, `Chain.polarize` (Spinor.lean:234) | PARTIAL | Spinor/Single/One/Complex variants missing | S |
| `quaternion` | `Spinor.quaternion` (Types/Half.lean:118) | DONE | — | — |
| `quatvalue`, `quatvalues` | `Spinor.quatvalue`, `CoSpinor.quatvalue`, `Spinor.quatvalueOf` (Composite/Spinor.lean:139-153) | PARTIAL | `quatvalues` alias missing; untested | S |
| `betti`, `χ` | — | MISSING | combinatorial Betti numbers / Euler characteristic of simplicial elements (`count_gdims`, `boundary_rank`); docs 39 | M |
| `angular`, `radial`, `coscalar` | — | SKIP | stale exports | — |

## F. Composite functions (composite.jl + AbstractTensors generics)

| Julia symbol | Lean name(s) + file | status | gap description | effort |
|---|---|---|---|---|
| `exp`, `expm1` | `Single/Chain/Half/CoSpinor/Multivector/Couple/PseudoCouple/Phasor.exp/expm1` (Composite/*.lean) | PARTIAL | Float coefficients only; typed results lose Julia kinds (`Chain.exp` → `Multivector` where Julia returns `Couple`/`Spinor`; `expEven` exists); no TA `exp`; composite suite compares values only | M |
| `log`, `log1p` | `*.log/log?/log1p` (all kinds) | PARTIAL | same kind/TA/coefficient gaps | M |
| `sqrt`/`√`, `cbrt`/`∛` | `*.sqrt/cbrt` (not PseudoCouple) | PARTIAL | PseudoCouple missing; same kind/TA gaps | S |
| `sin`, `cos`, `tan` | Single/Chain/Half/CoSpinor/Multivector/Couple/PseudoCouple (Ring.lean) | PARTIAL | Phasor missing; kinds/TA | S |
| `sinh`, `cosh`, `tanh` | all but Phasor (tanh missing CoSpinor/PseudoCouple) | PARTIAL | as above | S |
| `cot`, `sec`, `csc`, `coth`, `sech`, `csch` | `Multivector.*` (Ring.lean:126-138), `Couple.coth` | PARTIAL | Multivector-only | S |
| `asin` `acos` `atan` `acot` `asec` `acsc` `asinh` `acosh` `atanh` `acoth` `asech` `acsch` | `Multivector.*` (Ring.lean:140-162); `Single.asin/atan/asinh/…`, `Couple.asinh/…`, `Half.asinh/…` | PARTIAL | per-kind coverage incomplete (Chain, CoSpinor, PseudoCouple none) | S |
| `sinc`, `cosc`, `exp2`, `exp10`, `log2`, `log10` | `Multivector.*`, `Couple.exp2/exp10/log2/log10` | PARTIAL | Multivector/Couple only | S |
| `exph` | `Multivector/Half/Couple.exph` (Ring.lean:180,281,439) | PARTIAL | untested vs oracle | S |
| `log_fast`, `logh_fast` | `logFast/loghFast` (Ring.lean:495-535) | DONE | Unit tests vs Julia | — |
| `pseudoexp` `pseudolog` `pseudosqrt` `pseudocbrt` `pseudoinv` `pseudocos` `pseudosin` `pseudotan` `pseudocosh` `pseudosinh` `pseudotanh` `pseudoabs` `pseudoabs2` | `Generic.pseudo*` abbrevs (AbstractTensors/Generic.lean:427-451) for `TensorRing` (Multivector; Spinor in even dim) | PARTIAL | no Chain/Single/Couple/TA instances (Chain has only `co*`); names not exported under `Grassmann` | S |
| `coexp` `colog` `cosqrt` `cocbrt` `coinv` `cocos` `cosin` `cotan` `cocosh` `cosinh` `cotanh` `coabs` `coabs2` | `Multivector.co*` (Ring.lean:203-223), `Chain.co*` (Ring.lean:366-392) | DONE | Unit tests vs Julia | — |
| `@pseudo`, `@co` | combinators `co`, `co₂`, `pseudo` (AbstractTensors/Ops.lean:275-287) | DONE | Lean combinator instead of name-generating macro | — |
| `pseudodot` | `antidot` | SKIP | stale in Grassmann (AT defines it = codot) | — |
| `vandermonde` | `Forms.vandermonde` (Forms/Spectral.lean:66) | PARTIAL | least-squares fit `vandermonde(x,y,V)`, `vandermondeinterp`, `approx` missing; untested | S |
| `pfaffian` | `Chain.pfaffian`, `Endomorphism.pfaffian` (Forms/Compound.lean:598-609) | DONE | exact.json | — |
| `invdet`, `adjugate`, `cofactor` | `Simplex.invdet/adjugate/cofactor` (Compound.lean:406-543), Diagonal/Outermorphism variants | DONE | exact/float/simplex goldens | — |
| `compound` | `Simplex.compound` (Compound.lean:305), `DiagonalMorphism.compound` | DONE | — | — |
| `companion` | `Endomorphism.companion` (Forms/Operator.lean:357) | DONE | — | — |
| `volumes` | `Forms.volumes` (Forms/Simplex.lean:184), `Simplex.volume/edgelength/area` | PARTIAL | untested vs oracle | S |
| `affineframe` | `Simplex.affineframe` (Simplex.lean:49) | DONE | simplex.json | — |
| `mean`, `centroid`, `barycenter` | `Simplex.mean/centroid/barycenter` (Simplex.lean:63-71) | DONE | simplex.json | — |
| `means`, `centroids`, `barycenters`, `curls` | — (Cartan has bundle `centroids`) | MISSING | index-mapped mesh variants `op.(getindex.(Ref(p), m))` | S |
| `curl` | — | MISSING | `curl(m) = V(∇) × m` (and `Values{N,Chain}` form) | S |
| `grad` (`gradient`) | `Simplex.gradient`, `gradienthat` (Simplex.lean:126-153) | PARTIAL | simplex form tested; `gradient(m::TensorAlgebra) = d(m)` missing | S |
| `divergence` | — | MISSING | `divergence(m) = ∂(m)`; `Values{N,Chain}` form | S |
| `roots`, `rootsreal`, `rootscomplex` | — | MISSING | non-monic wrappers `monicroots*(a[1:N-1]./a[N])`; README-listed | S |
| `monicroots`, `monicrootsreal`, `monicrootscomplex` | `Roots.monicroots?/monicrootsreal?/monicrootscomplex?` (Forms/Roots.lean:210-256) | PARTIAL | n ≤ 4 only (returns `none` for n ≥ 5 instead of `eigvals(companion)`); Complex coefficients unsupported; roots.json tested | S |
| element utilities `div rem mod mod1 fld fld1 cld ldexp ÷ % mod2pi rem2pi rad2deg deg2rad round rationalize isfinite signbit iseven isodd rand` | `map` on every container (Types/*.lean) | PARTIAL | only `map`; named elementwise ops, `rand` samplers (only in Tests), `iseven/isodd` (grade parity) missing | S |

## G. Forms / operators (forms.jl)

| Julia symbol | Lean name(s) + file | status | gap description | effort |
|---|---|---|---|---|
| `Projector`, `Proj` | `Projector V G α` (Forms/Dyadic.lean:101), `ofVector` | PARTIAL | `Proj` alias missing; `exp/log(::Proj)` heuristic missing | S |
| `Dyadic` | `Dyadic` (Dyadic.lean:48) | PARTIAL | `exp/expm1/log(::Dyadic)` (via Endomorphism) not wired | S |
| `SpectralOperator` | `SpectralOperator` (Dyadic.lean:169), `exp/log/inv/invdet` | DONE | dyadic/eigen goldens | — |
| `outer` | `Forms.outer` (Dyadic.lean:38) | DONE | — | — |
| `operator` | `operator`, `operatorDiag`, `gradedoperator`, `TensorOperator.ofLinear` (Forms/Cayley.lean:32-53) | DONE | spaces.json `operators` | — |
| `gerschgorin` | `TensorOperator.gerschgorin` (Operator.lean:261), Diagonal | DONE | — | — |
| `diag` | `Endomorphism.diag` (Operator.lean:340), `DiagonalOperator.ofEndomorphism` | DONE | — | — |
| `DiagonalOperator`, `DiagonalMorphism`, `DiagonalOutermorphism` | Forms/Diagonal.lean:23-31 | DONE | diag.json | — |
| `TensorOperator`, `Endomorphism` | Forms/Operator.lean:75-81 | DONE | exact/float/rect goldens | — |
| `Outermorphism`, `outermorphism` | Forms/Outermorphism.lean:88, :262 | PARTIAL | `exp/expm1/log(::Outermorphism)` missing | S |
| `sylvester` | `TensorOperator.sylvester` (Spectral.lean:230), Diagonal | DONE | — | — |
| `characteristic` | `characteristic`, `characteristicExact` (Spectral.lean:92-124) | DONE | — | — |
| `eigen`, `eigvals`, `eigvecs` | `eigen/eigvals` (Spectral.lean:153-219), `DiagonalMorphism.eigvecs` (:324), `Chain/Half/Couple.eigvals` (Cayley.lean:135-150) | PARTIAL | `eigvecs(::Endomorphism)` only complex-typed (`eigvecscomplex`), Julia real-typed when real; Float-only matrices | S |
| `eigvalsreal`, `eigvalscomplex`, `eigvecscomplex`, `eigenreal`, `eigencomplex` | Spectral.lean:166-226 | DONE | float/eigen goldens | — |
| `eigvecsreal` | — | MISSING | README-listed | S |
| `eigpolys`, `eigmults` | Spectral.lean:141, :236 | DONE | — | — |
| `eigprods` | — | SKIP | stale export | — |
| `discriminant`, `discriminantcomplex` | Spectral.lean:253-263 | DONE | float.json | — |
| `discriminantreal`, `disc`, `discreal`, `disccomplex` | — | MISSING | aliases | S |
| `vandermondereal`, `vandermondecomplex` | Spectral.lean:242-247 | PARTIAL | untested vs oracle | S |
| `MetricTensor` | `Metric.tensor` (DirectSum/Space.lean:91) | DONE | — | — |
| `metrictensor`, `metricextensor` | Forms/Cayley.lean:68-81 | DONE | spaces.json | — |
| `InducedMetric` | Cartan `Induced` (Cartan/Bundle.lean:80) | DONE | lives in Cartan | — |
| `@TensorOperator`, `@Endomorphism`, `@Outermorphism`, `@SpectralOperator` | `TensorOperator.ofRows?` (Operator.lean:119), `Outermorphism.ofSimplex`, `SpectralOperator.ofVectors`/`eigen` | PARTIAL | no matrix-literal syntax; `ofRows?` returns `Option` (docs 18 `@TensorOperator([1 2; 3 4])\Chain(5,6)`) | S |
| `𝓛`, `Lie`, `LieBracket`, `bracket`, `LieDerivative` | `bracket`, `lieBracket`, `LieDerivative` (Forms/Lie.lean:20-55) | PARTIAL | no `𝓛[X,Y]` notation; `LieDerivative` untested | S |
| `det`, `tr` | operators/simplex/diagonal/projector/spectral `det`/`tr` | DONE | — | — |
| `isdiag` | `TensorBundle.isdiag` (DirectSum/Space.lean:167) | PARTIAL | operator `isdiag` missing | S |
| `cayley` | `cayley V op l` → `CayleyTable` (Cayley.lean:97), `printtex`/`alltex` (Forms/Show.lean:272-283) | DONE | spaces.json; docs 14 display not wired | — |
| `transpose`, `Matrix(t)` | `TensorOperator.transpose` (Operator.lean:230), `toRows` | DONE | — | — |
| form evaluation `t(y...)`, subspace maps `W(x)` | `Chain/Multivector.eval`, `vecdot`, `Chain.project/embed` (Forms/Eval.lean:61-140) | PARTIAL | eval.json tested; no call syntax (CoeFun) on elements | S |
| `(T)(x)` operator application | `CoeFun` on `TensorOperator` (Operator.lean:328); `⋅` for others | DONE | — | — |

## H. Top-level Grassmann.jl functions (calculus, projective, simplicial, fields)

| Julia symbol | Lean name(s) + file | status | gap description | effort |
|---|---|---|---|---|
| `hyperplanes` | — | MISSING | `[I ⟑ v_k]` for k < rank−diffvars (docs 16, 38) | S |
| `𝕚`, `𝕛`, `𝕜` | — | MISSING | `hyperplanes(ℝ3)` = `(v₂₃, −v₁₃, v₁₂)` | S |
| `points` | `Gallery.Versor.points3` (gallery/Gallery/Versor.lean) | PARTIAL | gallery-only helper; library `points(f, r)` missing (README plots); legacy mesh `points(t)` SKIP | S |
| `↑`, `project` | `Gallery.Versor.upRiemann/upConformal` (gallery only, `Chain V 1 Float`) | PARTIAL | not in the library; no generic element version, no `project(ω,b)`/`project(ω,p,m)`, no `Submanifold` form (README `↑(v1+v2+v3)`, docs 41) | M |
| `↓`, `reject` | `Gallery.Versor.downRiemann/downConformal` (gallery only) | PARTIAL | as above (`reject(ω,b)`, `reject(ω,∞,∅)`) | M |
| `∇`, `nabla`, `Nabla` | — | MISSING | Leibniz `Derivation`; `V(∇)` (all-ones vector in plain spaces, `Σ ∂ₖvₖ` in tangent spaces) (docs 20, 27) | M |
| `Δ`, `Laplacian` | — | MISSING | `V(Δ) = (∇⋅∇)`; Julia's simplicial `Δ(t)` is broken (defect `laplacian-not-callable`) | M |
| `∂`, `boundary` | — (Cartan/MeshTopology boundaries are mesh-level) | MISSING | element `∂(ω) = ω⋅V(∇)` (docs 22, 39) and `∂(ω::Chain{V,1,<:Chain})` | S (plain) / M (tangent) |
| `d`, `differential` | — | MISSING | `d(ω) = V(∇)∧ω` (docs 21) | S/M |
| `δ`, `codifferential` | — | MISSING | `δ = -∂` | S |
| `skeleton` | — (MeshTopology `skeleton` is mesh-level) | MISSING | recursive `absym(x)+skeleton(absym(∂x))` (docs 39) | S |
| `𝒫`, `subcomplex` | — | MISSING | Julia broken (Δ not callable); implement intended `skeleton(·, Val(false))` / `Δ(absym(∂x))` | S |
| `collapse` | — | MISSING | `a⋅absym(∂(b))` | S |
| `chain`, `path` | — | MISSING | 2-chain of a simplex boundary cycle / path (docs 39) | S |
| `column`, `columns` | `TensorOperator.column/columns` (Operator.lean:145-168) | PARTIAL | Julia `column(t,i)` = i-th coordinate across a point list (an operator *row*); semantics differ | S |
| `vectorfield`, `pointfield` | `Gallery.Grassmann.Fields.planeField/sphereField` (gallery only) | PARTIAL | 0 core methods in Julia (ext GeometryBasics); library closure `p ↦ V(vector(↓(↑p ⊘ t)))` missing (README streamplots) | S |
| `chainfield` | gallery-only (as above) | PARTIAL | `chainfield(t,V,W)` and mesh interpolation `chainfield(t,ϕ)` (barycentric `Pi\P`) missing (docs 42, 43) | M |
| `scalarfield`, `rectanglefield` | — | MISSING | mesh barycentric interpolation samplers | M |
| `TensorAlgebra` | class (AbstractTensors/Ops.lean:40) | DONE | — | — |
| AbstractFFTs methods (`fft`, `ifft`, … on arrays of elements) | — | MISSING | via `complexify`/Couple; needs an FFT (Cartan Spectral work in flight) | M |

## I. Display / printing

| Julia behaviour | Lean name(s) + file | status | gap description | effort |
|---|---|---|---|---|
| `show` of every element kind (Zero/One/∞/Submanifold/Single/Chain/Spinor/CoSpinor/Multivector/Couple/PseudoCouple/Phasor) | `TA.showIO` (Dynamic/Show.lean:48), typed `ToString` (Types/Show.lean) | DONE | str compared in construct/arith/products/unary goldens | — |
| compact IO (6 significant digits) | `TA.showCompact`, `F64.showIO true` | DONE | — | — |
| Julia float printing (Ryu, `exp_form`) | JuliaBase/Ryu.lean, Show.lean | DONE | floats suite 20394 | — |
| operator 2/3-arg `show`, `summary`, `display_matrix` | Forms/Show.lean:182-368 | DONE | forms goldens `show/display/summary` | — |
| `printtex`, `alltex` | Forms/Show.lean:223-283 | DONE | exact/spaces goldens | — |
| typed-layer display of Julia-kind-changing results (`v1*v2` → typed `Couple` prints `0 + 1v₁₂`, Julia `v₁₂`) | — | PARTIAL | only TA reproduces Julia kinds; typed results print their static container (by design) — acceptable once TA is ergonomic (§M) | — |
| Irrational coefficients (`π*v₁`), `typeof` alias names | — | SKIP | no Irrational type in Lean; Julia type printing | — |

## J. `ext/` Julia-visible behaviour

| Julia ext | Lean | status | gap description | effort |
|---|---|---|---|---|
| ReduceExt, SymPyExt, SymEngineExt, SymbolicsExt, AbstractAlgebraExt | — | SKIP | DESIGN.md non-goal (symbolic backends); any Lean `Coeff` instance works | — |
| GaloisFieldsExt | — | SKIP | finite-field coefficients possible via a `Coeff` instance; no demand | — |
| SpecialFunctionsExt, EllipticFunctionsExt, FewSpecialFunctionsExt | — | MISSING | lift complex special functions (gamma, erf, bessel, elliptic) to `Couple`/`Chain` via `complexify`; needs JuliaBase complex special functions | L |
| MakieExt, GeometryBasicsExt, MeshesExt, UnicodePlotsExt | gallery/ (LeanPlot) | SKIP | plotting interop (DESIGN non-goal: Makie reactivity); README figures reproduced in gallery | — |
| StaticArraysExt | `Mat`, `Values` | SKIP | SMatrix conversions are Julia container interop | — |
| LightGraphsExt | gallery/Gallery/Grassmann/Graphs.lean (local) | SKIP | digraph of a simplicial element is plotting glue | — |

## K. Base / LinearAlgebra method extensions (not exported, user-visible)

| Julia behaviour | Lean name(s) + file | status | gap description | effort |
|---|---|---|---|---|
| `getindex` (`c[i]`, `c[b::Submanifold]`, `m[G]`, `(c)(i)`, `m.v12`) | `GetElem Nat`, `coeff`, `gradeValues`, `Chain.term` (Types/*.lean) | PARTIAL | `getproperty` `m.v12` missing | S |
| call syntax `A(g)` (grade), `t(y…)` (form), `W(x)` (subspace), `z(t)` (phasor) | functions `gradePart`, `eval`, `project/embed`, `Phasor.eval` | PARTIAL | no `CoeFun` instances (docs 31/37/56 `A(0)`, docs 33 `ℒ(v1+v2)`) | S |
| `∈`/`in` (point in simplex), `findfirst/findlast/findall` | `Simplex.contains`, `findfirstSimplex/…` (Forms/Simplex.lean:103-213) | PARTIAL | no `Membership` instance (docs 32 `barycenter(T) ∈ T`) | S |
| `:` (double contraction `T:T`) | `TensorOperator.frobenius` (Operator.lean:257) | PARTIAL | no notation | S |
| `Complex(m::Imaginary)`, `Couple(m::Imaginary)`, `reim` | `Couple.toComplex` (Composite/Couple.lean:128) | PARTIAL | `Spinor{V,T,2}` ↔ Complex/Couple conversions missing | S |
| `length`, `firstindex`, `lastindex`, `ones`, `widen`, `parent`, `promote_rule` | `size` | SKIP | Julia container/type machinery | — |

## L. Metric-argument (`g`) method family

| Julia behaviour | Lean | status | gap description | effort |
|---|---|---|---|---|
| `wedgedot_metric`, `contraction_metric`, `log_metric`, `abs(t,g)`, `abs2(t,g)`, `exp(t,g)`, `inv(t,g)`, `hodge(t,g)`, `sandwich(x,R,g)`, `>>>(R,x,g)`, `radius(z,g)`, `complexify(z,g)`, `unit(t,g)`, `cosandwich(x,R,g)` … (≈120 methods across products.jl/algebra.jl/forms.jl/multivectors.jl) | — (only a docstring mention, AbstractTensors/Generic.lean:23) | MISSING | runtime (point-dependent) metric passed as a Gram operator; needed by Cartan diffgeo with non-induced metrics | L |

## M. Cross-cutting ergonomics that block documented usage

| Julia behaviour | Lean | status | gap description | effort |
|---|---|---|---|---|
| operators on the Julia-exact layer (`v1∧v2`, `a⋅b`, `x⊘R`, `R>>>x`, `⋆a`, `!a`, `~a`, `a×b`, `a₊`) | only `+ - *` and scalar actions on `TA` (Dynamic/Arith.lean:322-328, Products.lean:576) | PARTIAL | no `Wedge/Vee/Contraction/Sandwich/HShiftRight/Hodge/ComplementRight/Reverse/Even/Odd/Cross/…` instances for `TA`; no `Coe (Submanifold V G) (TA V α)` / `OfNat`; users must call `TA.wedge` etc. | M |
| literal constructors `Chain{V,1}(4,5,6)`, `Multivector{V}(1,…,8)`, `Spinor{V}(…)`, `Chain(1,2,3)` | `ofList?` (Option), `ofFn` | PARTIAL | no length-checked literal syntax (README Lean example needs `(Chain.ofList? […]).get!`) | S |
| interop across spaces (`Λ(ℝ^2).v1 ∧ Λ(ℝ^3).v3`, docs 36) | `Chain.embed x W` (Forms/Eval.lean:79) | PARTIAL | no automatic promotion to the union space | M |
| tangent (Leibniz) products with tensor-valued coefficients (`∂1*∂1v1 = ∂₁⊗∂₁v₁`, docs 27) | DirectSum BladeAlgebra blade results; TA scalar coefficients only | PARTIAL | `TA` cannot hold derivation-valued coefficients; tangent products untested beyond arith/unary shards | L |

## N. Documented behaviour coverage (README + docs goldens)

| source | status | gap description | effort |
|---|---|---|---|
| `oracle/golden/docs/*.json` (58 shards, 501 statements) | PARTIAL | only `grassmann/composite-docs` evaluates (51 pass); **416 statements unimplemented** in the harness, although many are expressible (products/complements/grades/norms/forms/cayley/display). Not expressible today: `hyperplanes`/`𝕚𝕛𝕜` and `^` (16, 17, 54), `↑`/`↓`/`points` (41), `chainfield` (42, 43), `∇`/`d`/`∂`/`skeleton`/`χ`/`betti`/`chain`/`path` (20-22, 27, 39), `@TensorOperator` literal (18), `A(g)` call syntax (31, 37, 56), `ℒ(v)` form call on mixed spaces (33), `n\a` (31), `∥` (55), `@basis V E e` names (31), cross-space interop (36) | L |
| README `vectorfield`/`↑`/`↓`/`points` plots | PARTIAL | reproduced in `gallery/` with local helpers (Versor.lean, Fields.lean), not via library API | M |
| README "API design overview" list | PARTIAL | missing `roots/rootsreal/rootscomplex`, `eigvecsreal`, `istensor/isgraded/isterm`, element `abs`/`unit`, `I` | S |

## O. Performance parity

| area | status | gap description | effort |
|---|---|---|---|
| typed products, large algebras (STA/PGA3/CGA3 multivector, CGA3 sandwiches) | DONE | 0.7–1.4× Julia (docs/PERF.md) | — |
| typed small ops (ℝ3 `∧`, `~`, `⋆`, spinor products: 10–15 ns vs 0.7–3 ns) | IN_PROGRESS | per-result `FloatArray` allocation floor; expression fusion + SoA batches (Grassmann/Fuse, Grassmann/Batch) in flight | L |
| dynamic `TA` layer products | PARTIAL | run through interpreted cached plans (Dynamic/Loops.lean), not the generated kernels; never benchmarked vs Julia | M |
| spaces without `basis!`/`grassmann_kernels` (runtime-built `V`) | PARTIAL | fall back to reference plans (≈10× slower than generated, PERF.md "ref" rows); Julia generates on first use | M |
| composite (exp/log/…) and forms perf | IN_PROGRESS | composite/forms perf workstream in flight; no Julia-vs-Lean table in PERF.md yet | M |
| Lean-vs-Julia benchmark harness | IN_PROGRESS | Bench/Harness in flight (today only Bench/Grassmann/Products.lean) | M |

## Summary counts (rows above)

223 rows (several rows group aliases of one Julia function): DONE 90 · PARTIAL 86 · MISSING 27 ·
IN_PROGRESS 3 · SKIP 17.

Biggest levers, in order: (1) make `TA` the ergonomic Julia-exact surface (operator instances, `Coe`
from basis blades, literal constructors) and give it `inv`/`/`/`\`/`^`/composite functions with Julia
result kinds; (2) wire the 416 unimplemented docs statements into the harness (most are already
expressible); (3) upstream `↑`/`↓`/`points`/`vectorfield`/`chainfield` from `gallery/`; (4) plain-space
calculus `∇ ∂ d δ grad divergence curl` + simplicial `skeleton χ betti chain path`; (5) README-listed
one-liners (`roots*`, `eigvecsreal`, `istensor/isgraded/isterm`, `hyperplanes`, `𝕚𝕛𝕜`, aliases).
