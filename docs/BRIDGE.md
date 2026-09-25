# Bridge: the spec algebra is mathlib's Clifford algebra

`bridge/` is a separate Lake package (`GrassmannBridge`) that depends on the root
package and on mathlib. It proves that the specification model
`Grassmann.Spec.Cl g` (docs/PROOFS.md §2) is **isomorphic as an `R`-algebra to
mathlib's `CliffordAlgebra`** of the diagonal quadratic form `Σ gᵢ vᵢ²`, for
every commutative ring `R`, every dimension `n` and every diagonal metric `g`.
It then transports facts in both directions.

The root package keeps its zero-dependency rule (DESIGN.md §1): nothing outside
`bridge/` imports mathlib, and the root `lake build` does not build the bridge.

## 1. What is proved

All statements hold for every commutative ring `R` (mathlib `CommRing`), every
`n`, every `g : Fin n → R` (positive, negative, zero or non-unit entries), and
every quadratic form `Q` on `Rⁿ = Fin n → R` with `hQ : ∀ v, Q v = Σᵢ gᵢ vᵢ²`.
**There is no `Invertible 2`, no field and no characteristic assumption**;
characteristic 2 is included. The only extra hypothesis anywhere is
`Nontrivial R` for the rank statement `finrank_eq`.

Every theorem depends only on `propext`, `Classical.choice` and `Quot.sound`;
`bridge/BridgeTests/Axioms.lean` pins this with `#guard_msgs` (it is a default
target, so a regression fails `lake build` in `bridge/`).

### The isomorphism (`GrassmannBridge.Clifford`, namespace `Grassmann.Bridge`)

| declaration | statement |
|---|---|
| `Cl.instRing`, `Cl.instAlgebra` | `Cl g` is a mathlib `Ring` and `Algebra R`; every field is a spec theorem (`Cl.mul_assoc`, `Cl.one_mul`, `Cl.mul_add`, `Cl.smul_mul`, …), nothing is reproved (`GrassmannBridge.Algebra`) |
| `Cl.equivFun`, `Cl.basis` | `Cl g ≃ₗ[R] (BitVec n → R)`; the blades `e_a` are a basis |
| `toVec_mul_self` | `(Σ vᵢ eᵢ)² = Q v` in `Cl g` (the cross terms cancel in pairs; no division by 2) |
| `toCl hQ` | the algebra map `CliffordAlgebra Q →ₐ[R] Cl g` given by `CliffordAlgebra.lift` with `ι(v) ↦ Σ vᵢ eᵢ` |
| `genAt_mul_monomial` | in mathlib's algebra, `ι(eᵢ) · monomial a = coef g eᵢ a • monomial (eᵢ ⊕ a)`, where `monomial a = ι(e_{i₁}) ⋯ ι(e_{iₖ})` (`i₁ < ⋯ < iₖ` the bits of `a`) and `coef` is the spec blade coefficient `(-1)^{σ} Π gᵢ` (`GrassmannBridge.Monomial`) |
| `fromCl_toCl`, `toCl_fromCl` | `fromCl : e_a ↦ monomial a` is a two-sided inverse of `toCl` |
| `toCl_injective`, `toCl_surjective` | hence `toCl` is bijective |
| **`cliffordEquiv hQ`** | **`CliffordAlgebra Q ≃ₐ[R] Cl g`** |
| `cliffordEquiv_ι`, `cliffordEquiv_symm_gen`, `cliffordEquiv_symm_blade`, `cliffordEquiv_monomial` | `ι(v) ↦ Σ vᵢ eᵢ`, `eᵢ ↦ ι(eᵢ)`, `e_a ↦ monomial a` |

### Consequences for mathlib (`GrassmannBridge.Transport`)

| declaration | statement |
|---|---|
| `weightedSumSquaresEquiv g` | `CliffordAlgebra (QuadraticMap.weightedSumSquares R g) ≃ₐ[R] Cl g` (mathlib's own diagonal form) |
| `monomialBasis hQ` | the `2ⁿ` ordered monomials are a basis of `CliffordAlgebra Q` |
| `free`, `finite`, `finrank_eq` | `CliffordAlgebra Q` is free and finite, of rank `2ⁿ` (the last for nontrivial `R`) |
| `ι_injective` | `ι : Rⁿ → CliffordAlgebra Q` is injective |
| `monomial_mul_monomial` | the multiplication table of the monomial basis: `monomial a * monomial b = coef g a b • monomial (a ⊕ b)` |
| `repr_mul` | products in monomial coordinates are the twisted convolution `Σ_a xₐ y_{a⊕c} coef g a (a⊕c)` (`Cl.coeff_mul`) |

What mathlib has without the bridge (rev `5e0c4e52`): a basis of the exterior
algebra of a free module (`Module.Basis.ExteriorAlgebra`) and, when `2` is
invertible, the linear equivalence `CliffordAlgebra.equivExterior`. So over
`ℚ` or `ℝ` the rank `2ⁿ` was reachable in mathlib already; over rings where `2`
is not a unit (`ℤ`, `ZMod 2`, …) the basis, the rank and the injectivity of `ι`
for diagonal forms are new. `bridge/BridgeTests/Examples.lean` instantiates them
for Euclidean `ℚ³` (rank 8), `Cl(1,3)` over `ℤ` (rank 16), `ZMod 2` (rank 4,
`ι` injective), a degenerate metric over `ℤ` and `ExteriorAlgebra ℤ ℤ⁴`
(rank 16).

### The spec's operations are mathlib's

| declaration | statement |
|---|---|
| `cliffordEquiv_reverse` | mathlib's `CliffordAlgebra.reverse` is the spec's `Cl.reverse` (Julia `reverse`, sign `parityreverse`) |
| `cliffordEquiv_involute` | mathlib's `CliffordAlgebra.involute` is the spec's `Cl.involute` (Julia `involute`) |
| multiplicativity of `cliffordEquiv` | the spec geometric product is mathlib's product; so `Cl.mul_assoc` and mathlib's associativity are the same fact, and every spec law (`Cl.reverse_mul`, `Cl.mul_self_of_vector`, …) holds in `CliffordAlgebra Q` and conversely |

### The exterior algebra (`GrassmannBridge.Exterior`)

| declaration | statement |
|---|---|
| `exteriorEquiv` | `ExteriorAlgebra R (Fin n → R) ≃ₐ[R] Cl 0` (the zero form is diagonal with zero weights) |
| `exteriorLinearEquiv g` | `ExteriorAlgebra R Rⁿ ≃ₗ[R] Cl g`, for **every** metric `g` |
| `exteriorLinearEquiv_mul` | `x * y ↦ Cl.wedge x' y'`: mathlib's exterior product is the spec `∧` in every diagonal algebra |
| `exteriorLinearEquiv_ι`, `exteriorLinearEquiv_one` | `ι(v) ↦ Σ vᵢ eᵢ`, `1 ↦ 1` |

## 2. How the proof goes

DESIGN.md §8.5 planned "universal property + dimension count" over `ℚ`/`ℝ`.
The bridge replaces the dimension count by an explicit inverse, which works
over every commutative ring:

1. **Lift.** `v ↦ Σ vᵢ eᵢ` squares to `Q v` in `Cl g` (`toVec_mul_self`, from
   `eᵢ² = gᵢ` and `eᵢeⱼ = -eⱼeᵢ` by induction on the support; the cross terms
   `vᵢvⱼ(eᵢeⱼ + eⱼeᵢ)` vanish without dividing by 2). `CliffordAlgebra.lift` gives
   `toCl`.
2. **Generator table in mathlib.** The ordered monomial `monoBelow Q k m` is built
   one position at a time on the right, the same recursion on the top generator
   as `DirectSum.Proofs.inversions` and `metricFactor`. Induction on `k` with
   `sigma_succ`/`bitParity_succ` proves (a) a generator above position `k`
   commutes past the monomial up to `(-1)^{|m below k|}` and (b) a generator
   below `k` multiplies into it with coefficient `(-1)^{σₖ(eᵢ, m)} (gᵢ if i ∈ m)`.
   At `k = n` this is exactly the spec blade coefficient (`genAt_mul_monomial`).
   Only `ι_sq_scalar` and `ι_mul_ι_comm_of_isOrtho` are used.
3. **Left inverse.** `fromCl` (blade `e_a` ↦ monomial `a`, defined on the blade
   basis) therefore satisfies `fromCl (eᵢ x) = ι(eᵢ) fromCl x`. By
   `CliffordAlgebra.induction` on `y`, `fromCl (toCl y · x) = y · fromCl x`; at
   `x = 1` this is `fromCl ∘ toCl = id`.
4. **Right inverse.** `toCl (monoBelow Q k m)` is the blade of the bits of `m`
   below `k` (`toCl_monoBelow`): each new generator is above the previous ones,
   so the spec coefficient is `1` (`sigma_of_lt`, `sigma_congr`).

## 3. Building

```
cd bridge
./fetch-mathlib.sh   # first run: clones mathlib + deps, builds mathlib's cache tool, downloads oleans
lake build           # the bridge, the spec modules it needs from the root package, and BridgeTests
```

* **Toolchain**: `bridge/lean-toolchain` is the root's
  (`leanprover/lean4:v4.35.0-rc3`), which is also mathlib master's at the pinned
  revision.
* **Pinned mathlib**: `lakefile.toml` requires `mathlib` at `rev = "master"`;
  `lake-manifest.json` pins it to `5e0c4e5239cb0a2d86d68a884bf52cfd963fce22`
  (master on 2026-09-25) and pins its dependencies (batteries, aesop, Qq,
  plausible, ProofWidgets4, import-graph, LeanSearchClient, lean4-cli) to the
  revisions of mathlib's own manifest. Do **not** run `lake update` casually:
  it moves mathlib to the new master and, unless
  `MATHLIB_NO_CACHE_ON_UPDATE=1` is set, mathlib's post-update hook downloads
  the cache for all of mathlib.
* **Only the needed oleans**: `fetch-mathlib.sh` runs
  `lake exe cache get <the Mathlib modules the bridge imports>`, which fetches
  those modules and their imports: about 1,850 files, ~120 MB compressed
  (stored in `~/.cache/mathlib`), ~1.8 GB unpacked under
  `bridge/.lake/packages/*/.lake` (1.5 GB of it mathlib). A bare
  `lake exe cache get` would fetch all of mathlib (~8,600 modules, several GB).
  Nothing from mathlib is compiled locally except the small `cache` executable.
* **Clones**: Lake clones mathlib with full history (~480 MB of git objects
  plus ~120 MB of sources) and its dependencies (~20 MB). On a disk-constrained
  machine, pre-create shallow clones at the manifest revisions before the first
  `lake` command, e.g.
  `git init .lake/packages/mathlib && git -C .lake/packages/mathlib remote add origin https://github.com/leanprover-community/mathlib4 && git -C .lake/packages/mathlib fetch --depth 1 origin <rev> && git -C .lake/packages/mathlib checkout --detach FETCH_HEAD`
  (the same for each dependency, with the directory names of the manifest).
  Lake accepts an existing checkout that is at the pinned revision (~150 MB for
  mathlib).
* **Time** (measured on the development machine): cache tool build plus
  download about 40 s on the first run; `lake build` from a clean `bridge/`
  and root build directory about 17 s (the 27 root modules `Grassmann.Spec`
  needs, then the bridge and its tests, 1-2 s per module).
* **Library imports**: `import GrassmannBridge` (or one of
  `GrassmannBridge.{Algebra, Monomial, Clifford, Transport, Exterior}`).
  Declarations live in `Grassmann.Bridge`; the `Ring`/`Algebra` instances and
  small `Cl` lemmas (`Cl.basis`, `Cl.reverse_smul`, …) in `Grassmann.Spec.Cl`.

### Instance note

`Grassmann.Spec` is written against `Lean.Grind.CommRing`. The bridge is
stated for a mathlib `CommRing R`, and inside it the spec operations use
mathlib's `CommRing.toGrindCommRing R`, so for a generic `R` the spec structure
and mathlib's agree definitionally and no conversion lemmas are needed. For the
concrete rings `ℚ` and `ℤ`, core also provides `Lean.Grind.CommRing` instances
(`Lean.Grind.instFieldRat`, `Lean.Grind.instCommRingInt`) that instance search
prefers to mathlib's (priority 100). The bridge theorems instantiated at `ℚ`
are still correct and usable (`BridgeTests/Examples.lean`), but spec terms
elaborated in the root package over core `Rat` (for instance in
`Grassmann.Proofs`) use core's instance, and for `Rat` it is not definitionally
equal to mathlib's by `rfl`. Linking those theorems to the bridge needs a
`Cl`-level lemma that the two instances give the same product (§4).

## 4. Not covered (yet)

* **The implementation, end to end.** `Grassmann.Proofs.implMul_eq_mul_of_diag`
  says the implementation's geometric product is the spec product in every
  `DiagonalForm` space over core `Rat`; composing it with
  `weightedSumSquaresEquiv (R := ℚ)` would state that the compiled kernels
  compute mathlib's Clifford product. This needs the instance cast above and
  builds `Grassmann.Proofs` (the implementation, ~200 MB of oleans) from the
  bridge, so it is left for a follow-up.
* **Non-diagonal forms.** `Cl g` models diagonal metrics only; mathlib's
  `CliffordAlgebra Q` for a general symmetric bilinear form (Julia
  `MetricTensor` spaces) is not bridged. Over rings where every form is
  diagonalizable one could compose with an isometry
  (`QuadraticForm.equivalent_weightedSumSquares`, over fields with `Invertible 2`).
* **Conformal spaces** (`∞`, `∅` null basis): the spec side is transport of
  structure through the diagonal algebra (docs/PROOFS.md, conformal section);
  not bridged.
* **The other spec operations**: the Hodge star, complements, contraction and
  regressive product have no counterpart in mathlib's `CliffordAlgebra`; they
  are transported only as far as `cliffordEquiv` is multiplicative and linear.
  Clifford conjugation (`Cl.clifford`) vs mathlib's `star` follows from the two
  involution theorems but is not stated.
* **Grading**: mathlib's `CliffordAlgebra.evenOdd` `ZMod 2`-grading and the
  spec's `Cl.proj`/`IsGrade` are not linked; neither is the exterior basis
  `Module.Basis.ExteriorAlgebra (Pi.basisFun R (Fin n))` with the blade basis
  through `exteriorEquiv`.
