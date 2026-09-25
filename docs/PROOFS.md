# Proofs

What is proved about the geometric algebra, at what strength, and how it
connects to the code that runs. This covers DESIGN.md §8 targets 3 and 4 (the
reordering-sign cocycle and associativity for diagonal metrics over any
`Lean.Grind.CommRing`; graded commutativity of `∧`, `~(ab) = ~b ~a`, and the
Hodge double complement), plus a link from those theorems to the
implementation.

All of it is core Lean only: no mathlib, no `sorry`, no custom `axiom`, no
`native_decide`, no `bv_decide` (it relies on `Lean.ofReduceBool`, the same
trust as `native_decide`). Every theorem depends only on `propext`,
`Classical.choice` and `Quot.sound`; `Tests/Proofs/Axioms.lean` pins this with
`#guard_msgs` on the flagship theorems, so a regression fails the build.

## The three layers

| layer | module | what it is about |
|---|---|---|
| bit level | `DirectSum.Proofs` | the sign rules on bitmask blades, for every width, and the `UInt64` kernels |
| specification | `Grassmann.Spec` | a small model of the Clifford algebra `Cl(g)` of a diagonal metric, with its laws |
| link | `Grassmann.Proofs` | the implementation's blade rules and plans against the model |

Tests: `Tests.Proofs` (`Tests/Proofs.lean`, run with `Tests.Proofs.runAll`)
compares the compiled implementation with the model at run time.

## Status legend

* **Proved**: a theorem for all inputs (all widths, all metrics, all
  commutative rings, all `UInt64`s, as stated).
* **Checked**: a theorem whose proof is a finite computation evaluated by the
  Lean kernel (`decide +kernel`), for the named spaces only.
* **Tested**: checked by compiled code on the stated inputs (exhaustive where
  noted, random otherwise). Not a proof.

## 1. Bit level: `DirectSum.Proofs`

Blades are masks, bit `i` for generator `i+1`. `bitCount n a` is the grade,
`bitParity n a` its parity, `inversions n a b` counts the pairs
`j < i < n` with `i ∈ a`, `j ∈ b`, and the reordering sign is
`sigma n a b = inversions n a b % 2 == 1`.

| theorem | statement | status |
|---|---|---|
| `sigma_xor_left`, `sigma_xor_right` | `σ` is xor-linear in each argument (bilinear over 𝔽₂) | proved |
| `sigma_cocycle` | `σ(a,b) + σ(a⊕b,c) = σ(b,c) + σ(a,b⊕c)` | proved |
| `sigma_swap` | `σ(a,b) + σ(b,a) = (\|a\| \|b\| + \|a∧b\|) mod 2` | proved |
| `sigma_add_sigma_swap` | `σ(a,b) + σ(b,a) = (\|a\|\|b\| - \|a∧b\|) mod 2` (Nat subtraction, exact) | proved |
| `sigma_self` | `σ(a,a) = parityreverse \|a\|` (the reversion sign, Julia's formula) | proved |
| `sigma_of_lt`, `bitCount_of_lt`, `metricFactor_of_lt` | widening the space changes nothing for blades that fit | proved |
| `reorderParitySpec_eq_sigma` | the repository's naive `Bits.reorderParitySpec` (two nested folds) is `σ` | proved |
| `bitCount_xor_add` | `\|a⊕b\| + 2\|a∧b\| = \|a\| + \|b\|` | proved |
| `metricFactor_cocycle` | `g(a∧b)·g((a⊕b)∧c) = g(b∧c)·g(a∧(b⊕c))` for every diagonal metric `g` over every commutative ring | proved |
| `bladeCoef_cocycle` | the blade coefficient `(-1)^σ(a,b) · Π_{a∧b} gᵢ` is a 2-cocycle | proved |
| `metricFactor_sigMetric`, `bladeCoef_sigMetric` | signature metrics: the factor is `(-1)^{#negative shared generators}` | proved |
| `bladeCoef_zero_metric` | zero metric: the reordering sign on disjoint blades, `0` otherwise | proved |
| `metricFactor_mul_compl` | `g(a)·g(ā) = det g` | proved |

The `UInt64` kernels of `DirectSum.Bits`, for **all** 64-bit masks:

| theorem | statement | status |
|---|---|---|
| `parity_eq_bitParity` | `Bits.parity x` (six folding xors) is the popcount parity | proved |
| `prefixParity_testBit` | bit `i` of `Bits.prefixParity b` (a Hillis-Steele prefix-xor scan) is the parity of the bits of `b` below `i` | proved |
| `reorderParity_eq_sigma`, `reorderParity_eq_spec` | `Bits.reorderParity a b = reorderParitySpec 64 a b`; this replaces the 4-bit `decide` check `reorderParity_eq_spec_4` | proved |
| `reorderParity_cocycle`, `reorderParity_swap` | the implementation itself satisfies the cocycle and swap identities | proved |
| `parityjoin_eq`, `signOf_parityjoin` | Julia's `parityjoin` (the signature-space product sign) is the spec blade coefficient | proved |

Method: every function involved is 𝔽₂-linear, and a linear functional on 𝔽₂⁶⁴
is determined by its values on the 64 unit vectors (`linear_eq_xorSum`, proved
once by induction on the number of low bits). The 64 values (64 × 64 for the
prefix scan) are closed terms that the kernel evaluates in well under a second.
This avoids SAT (`bv_decide`), which would add `Lean.ofReduceBool` to the trust
base and struggles with xor-heavy circuits.

## 2. Specification: `Grassmann.Spec`

`Cl g` for `g : Fin n → R`, `R` a `Lean.Grind.CommRing`, is a coefficient
function on `BitVec n` blades. The geometric product is the explicit finite
sum

```
(x y)(c) = Σ_a x(a) · y(a ⊕ c) · (-1)^σ(a, a⊕c) · Π_{i ∈ a ∧ (a⊕c)} gᵢ
```

(`Cl.coeff_mul`), with `bsum` the sum over the `2ⁿ` blades. The exterior
product uses `(-1)^σ(a,b)` on disjoint blades and `0` otherwise; reversion
negates grades `≡ 2, 3 (mod 4)`; the right complement is
`!e_a = (-1)^σ(a,ā) e_ā`; the Hodge star is `⋆e_a = (-1)^σ(a,ā) Π_{i∈a} gᵢ e_ā`.
Nothing in the definitions mentions the laws below: they are theorems.

The key structural fact is `twist_assoc`: the twisted convolution
`(x ⋆ y)(c) = Σ_a x(a) y(a⊕c) k(a, a⊕c)` over `(ℤ/2)ⁿ` is associative for
every 2-cocycle `k`. The Clifford algebra of `g` is the case
`k = bladeCoef g`, and the exterior algebra is the case of the zero metric
(`wcoef_eq_coef_zero`).

All of the following are **proved** for every `n`, every diagonal `g` (positive,
negative or zero entries) and every commutative ring `R`:

| theorem | statement |
|---|---|
| `Cl.mul_assoc` | `(x y) z = x (y z)` |
| `Cl.one_mul`, `Cl.mul_one` | `1` is a two-sided unit |
| `Cl.mul_add`, `Cl.add_mul`, `Cl.smul_mul`, `Cl.mul_smul`, `Cl.neg_mul`, `Cl.mul_neg`, `Cl.zero_mul`, `Cl.mul_zero`, `Cl.scalar_mul`, `Cl.mul_scalar` | bilinearity, and scalars are central |
| `Cl.blade_mul_blade` | `e_a e_b = (-1)^σ(a,b) Π_{a∧b} gᵢ · e_{a⊕b}` |
| `Cl.gen_mul_self` | `eᵢ² = gᵢ` |
| `Cl.gen_mul_gen_comm` | `eᵢ eⱼ = -eⱼ eᵢ` for `i ≠ j` |
| `Cl.mul_self_of_vector` | `v² = B(v,v) = Σ gᵢ vᵢ²` for every vector (the Clifford relation), including characteristic 2 |
| `Cl.mul_eq_dot_add_wedge`, `Cl.mul_add_mul_swap` | `u v = B(u,v) + u ∧ v`, `u v + v u = 2B(u,v)` for vectors |
| `Cl.wedge_assoc`, `Cl.one_wedge`, `Cl.wedge_one`, `Cl.wedge_add`, … | the exterior product is an associative unital bilinear product |
| `Cl.wedge_eq_mul_zero` | the exterior product is the geometric product of the zero metric |
| `Cl.isGrade_wedge` | a `p`-vector wedged with a `q`-vector is a `(p+q)`-vector |
| `Cl.wedge_comm` | `x ∧ y = (-1)^{pq} y ∧ x` for a `p`-vector `x` and a `q`-vector `y` |
| `Cl.wedge_comm_vec`, `Cl.wedge_self_of_vector` | `u ∧ v = -(v ∧ u)` and `v ∧ v = 0` for vectors |
| `Cl.proj_*`, `Cl.isGrade_*` | grade projections: idempotent, additive, orthogonal |
| `Cl.reverse_mul`, `Cl.reverse_wedge` | `~(x y) = ~y ~x`, `~(x ∧ y) = ~y ∧ ~x` |
| `Cl.involute_mul`, `Cl.involute_wedge` | the grade involution is an automorphism of both products |
| `Cl.clifford_mul` | Clifford conjugation is an anti-automorphism |
| `Cl.reverse_reverse`, `Cl.involute_involute`, `Cl.clifford_clifford` | all three are involutions |
| `Cl.reverse_blade`, `Cl.involute_blade` | on blades they are Julia's `parityreverse`/`parityinvolute` signs |
| `Cl.blade_mul_reverse` | `e_a ~e_a = Π_{i∈a} gᵢ` |
| `Cl.blade_wedge_compl` | `e_a ∧ !e_a = I` (the defining property of the right complement) |
| `Cl.compl_compl` | `!!x = (-1)^{k(n-k)} x` for a `k`-vector |
| `Cl.hodge_eq_reverse_mul` | `⋆x = ~x · I` (Julia's definition for general metrics agrees with the diagonal formula) |
| `Cl.hodge_hodge` | `⋆⋆x = (-1)^{k(n-k)} det(g) x` for a `k`-vector |
| `Cl.contract_eq_proj` | Julia's contraction is `x ⋅ y = ⟨~y x⟩_{p-q}` for a `p`-vector `x` and a `q`-vector `y`, `q ≤ p` |
| `Cl.contract_of_vector` | on vectors, `u ⋅ v = B(u, v)` |
| `Cl.compl_vee`, `Cl.vee_assoc` | the regressive product is the De Morgan dual `!(x ∨ y) = !x ∧ !y`, and it is associative |

## 3. Link: `Grassmann.Proofs`

The implementation describes every operation by its action on basis blades
(`TensorBundle.terms₂`/`terms₁`, exact `Rat` term lists), and the reference
kernels are the bilinear (linear) extensions of those rules, compiled into
multiply-accumulate plans (`Grassmann.Kernel.build`, DESIGN.md §5.1).

**Proved in general:**

| theorem | statement |
|---|---|
| `bilin_eq_twist` | the bilinear extension of any blade rule `e_a ⋆ e_b = k(a,b) e_{a⊕b}` is the twisted convolution with `k` |
| `implMul_eq_mul`, `implWedge_eq_wedge`, `implContract_eq_contract` | so a geometric (exterior, contraction) table that agrees with the spec on basis blades gives the spec product on **all** multivectors |
| `mulSign_eq_coef` | for every space and every `n ≤ 64`, `(-1)^{TensorBundle.mulSign a b}` is the spec coefficient of the signature metric `V.sigBits`, on every pair of blades |
| `IsSignatureSpace.terms_mul` | in every plain signature space (`Signature` or `Int` metric, no conformal pair, no tangent variables), `terms₂ .mul a b` is the single term `(-1)^{parityjoin} e_{a⊕b}` for all 64-bit masks; `metricProduct` is a product of `±1`s, so its absolute value is `1` whatever its loop visits |
| `implMul_eq_mul_of_signature` | hence **the implementation's geometric product is the spec product on all multivectors of every plain signature space of dimension `≤ 64`** (`R7_mul`, `S33_mul` instantiate it) |
| `IsFlatSpace.terms_wedge`, `implWedge_eq_wedge_of_flat` | in every space without a conformal pair or tangent variables (any metric: signatures, `DiagonalForm`s including degenerate ones, `MetricTensor`s) and every width `≤ 64`, the implementation's exterior product is the spec exterior product on all multivectors (`PGA4_wedge` instantiates it) |

**Checked** by the kernel (`Grassmann.Proofs.Tables`), on every basis blade
(pair), in `ℝ2`, `ℝ3`, `STA = S!"-+++"`, `PGA2 = D!"0,1,1"`,
`PGA3 = D!"0,1,1,1"` and `D!"1,2,-3"`:

| check | spaces |
|---|---|
| `terms₂ .mul` is the spec blade product (`*_mul_table`) | all six |
| hence `implMul V x y = x * y` for all multivectors (`R2_mul`, `R3_mul`, `STA_mul`, `PGA3_mul`, `D123_mul`) | all six (theorems stated for five) |
| `terms₂ .wedge` is the spec exterior product (`*_wedge_table`), hence `implWedge V x y = x ∧ y` | `ℝ2`, `ℝ3`, `STA`, `PGA3` |
| reversion, grade involution, right complement and Hodge star, at blade level (`terms₁`) and at the container level the reference kernels use (`Grassmann.Kernel.unTermsC`) (`*_unary`) | all six |
| the reference kernel's `Multivector × Multivector` plan (`Grassmann.Kernel.build`) is exactly the spec table in Julia's storage order (`*_mul_plan`, `R3_wedge_plan`) | `ℝ2`, `ℝ3`, `STA`, `PGA3`, `D!"1,2,-3"` |
| `terms₂ .contraction` is the spec contraction (`*_contraction_table`), hence `implContract V x y = x ⋅ y` (`R3_contract`, `STA_contract`, `PGA3_contract`) | all six |
| `terms₂ .vee` is the spec regressive product on every pair of blades (`*_vee_table`, `Grassmann.Proofs.Regressive`) | `ℝ2`, `ℝ3`, `STA`, `PGA3`, `D!"1,2,-3"` |

Negative controls (a wrong metric, a flipped complement sign, a wrong plan)
make these checks fail, so they are not vacuous.

### Conformal spaces (`Grassmann.Proofs.Conformal`)

Conformal spaces use the Gram (Chevalley) product in the null outer-product
basis, not a sign table. The specification is transport of structure: the
outermorphism `T` of `n∞ = e₊ + e₋`, `n∅ = (e₋ - e₊)/2` maps the null basis
isometrically to the diagonal algebra `Cl(1, -1, 1, …)`.

| item | status |
|---|---|
| `toDiag_implMul`: if the blade table transports (`ConfTable`), then `T(x y) = T(x) T(y)` for all multivectors | proved |
| `implMul_assoc_of_conf`, `CGA2_mul_assoc`, `CGA3_mul_assoc`: the conformal product is then associative | proved (conditional on `ConfTable`) |
| `conf_inverse_3/4/5`: `T⁻¹ ∘ T = id` | checked |
| `ConfTable` for `S!"∞∅+"`, `CGA2`, `CGA3` (every pair of blades) | tested, exhaustively |
| random `CGA3` multivector products through `T` | tested |

Why not checked: the conformal branch of `TensorBundle.mul` sorts its terms with
`Terms.sortBasis`, which uses `Array.qsort`. The kernel cannot reduce
`Array.qsort` (not even `#[3,1,2].qsort`), and its auxiliary definitions are
private to core, so no permutation lemma can be proved here. The Chevalley
recursion itself is kernel-friendly: a copy of it without the sort decides the
`CGA2` table in about 25 s. With a structural sort in `Terms.sortBasis`, the
`ConfTable` hypotheses become `decide +kernel` proofs.

## 4. Tests: `Tests/Proofs`

`Tests.Proofs.Model` runs the compiled implementation against the spec model
evaluated at run time, in spaces beyond the `decide` range:

| test | inputs |
|---|---|
| full `Multivector` products `*`, `∧`, `∨`, `⋅`, and `~`, `involute`, `!`, `⋆` | random integer multivectors in `E5`, `M5 = S!"-++++"`, `S33 = S!"++-+--"`, `PGA4 = D!"0,1,1,1,1"`, `D5 = D!"1,2,-3,5,-1"`, `E6`, `E7` |
| every typed `Chain G × Chain H` product (the typed kernels and their even/odd result plans) | the same spaces, every grade pair |
| `Bits.reorderParity` against `reorderParitySpec 64` | 2000 random mask pairs (the equality is proved; this checks the compiled code) |
| `ConfTable` | exhaustive, `S!"∞∅+"`, `CGA2`, `CGA3` |
| `T(x y) = T(x) T(y)` for the compiled `CGA3` product | random rational multivectors |

This is where the plan interpreter (`Grassmann.Kernel.Plan.eval₂`) and
whatever kernel the `Kernels` instance dispatches to (including future
generated kernels) are exercised; they are not proved.

`Tests.Proofs.Axioms` is the compile-time axiom audit.

## Not covered (yet)

* `Bits.popcount` (SWAR), `Bits.ctz`, `Bits.sumIndices` and the
  `metricProduct` loop are not proved for all masks. They are exercised by every
  check and test above, and the general statements for `parityjoin`/`mulSign` do
  not depend on them. `popcount` is not 𝔽₂-linear, so the linearity method of
  §1 does not apply.
* `DiagonalForm` products in general dimension go through `metricProduct`, whose
  loop visits the set bits with `ctz`, so they are checked (`PGA*`,
  `D!"1,2,-3"`) and tested (`PGA4`, `D5`), not proved; plain signature spaces
  are proved in every dimension (`implMul_eq_mul_of_signature`).
* The involutions and complements are linked per space (checked, `n ≤ 4`) and
  tested (`n ≤ 7`), not in general: their blade rules read the grade through
  `Bits.popcount` (or `Bits.sumIndices`).
* The other contractions (`⨼`, `<<`, `>>`), `cross`, `veedot`, `antidot` and the
  sandwiches have no spec yet; `Tests/Grassmann/Props.lean` tests their
  algebraic laws. The regressive product is linked blade by blade, not yet
  lifted to all multivectors (the spec side is not a plain twisted product).
* Tangent (`∂`), dyadic and `MetricTensor` spaces are outside the diagonal
  model.
* Mathlib's `CliffordAlgebra` bridge (DESIGN.md §8.5) belongs in `bridge/`.

## Building and running

```
lake build DirectSum.Proofs Grassmann.Spec Grassmann.Proofs Tests.Proofs
```

About 25 s for the kernel checks in `Grassmann.Proofs.Tables` and 6 s for
`Grassmann.Proofs.Regressive` (they build in parallel); everything else builds
in seconds. The run-time suite is `Tests.Proofs.runAll : IO (Nat × Nat)`,
about 2600 checks, 5 s compiled.
