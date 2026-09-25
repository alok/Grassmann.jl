# Tactics for the specification algebra

Two kinds of automation for the proved model `Grassmann.Spec` (`Cl g`, the
Clifford algebra of a diagonal metric `g : Fin n → R` over a commutative ring
`R`; docs/PROOFS.md §2):

| tool | decides | where it works |
|---|---|---|
| `clifford` | identities between multivector expressions, by computing coordinates | a concrete space: `n` a numeral (≤ 6), any metric, any `R`, symbolic scalars and multivectors |
| `grind`, `grind [grassmann]` | abstract identities from the algebra laws | any dimension, any metric, any `R` |

Both are imported by `import Grassmann.Tactic`. Examples that are compiled on
every build: `Tests/Proofs/TacticExamples.lean` and
`Tests/Proofs/GrindExamples.lean`.

## 1. `clifford`

```lean
import Grassmann.Tactic
open Grassmann.Spec

variable {R : Type} [Lean.Grind.CommRing R]

abbrev E3 (R : Type) [Lean.Grind.CommRing R] : Fin 3 → R := fun _ => 1
abbrev v₁ : Cl (E3 R) := Cl.gen 0
abbrev v₂ : Cl (E3 R) := Cl.gen 1

example (a b : R) : (a • v₁ + b • v₂) * (a • v₁ + b • v₂) = Cl.scalar (a ^ 2 + b ^ 2) := by
  clifford

example (c s : R) (h : c ^ 2 + s ^ 2 = 1) :
    (Cl.scalar c + s • (v₁ * v₂)) * Cl.reverse (Cl.scalar c + s • (v₁ * v₂)) = 1 := by
  clifford
```

### What it accepts

* **The goal** is `x = y` with `x y : Cl g`, `g : Fin n → R`, `n` a numeral
  (up to 6: coordinates are dense), `R` any `Lean.Grind.CommRing`.
* **Operations**: `+ - * •`, numerals, `^` with a literal exponent,
  `Cl.scalar`, `Cl.blade`, `Cl.gen`, `Cl.pseudoscalar`, `Cl.wedge`,
  `Cl.contract`, `Cl.vee`, `Cl.reverse`, `Cl.involute`, `Cl.clifford`,
  `Cl.proj`, `Cl.compl`, `Cl.complInv`, `Cl.hodge`. Definitions (`def` and
  `abbrev`) are unfolded, so named elements (`v₁`, `rotor c s`) work.
* **Atoms**: any other scalar term (a variable `a : R`, `f x`, `Int.cast k`)
  is a symbolic scalar; any other multivector (a variable `x : Cl g`) is
  opaque, and its `2ⁿ` coordinates `x.coeff k#n` become symbolic scalars.
* **The metric**: an entry `g i` that is (definitionally) an integer numeral,
  after unfolding `g` and deciding `if`s on closed conditions, is folded into
  the blade table as a constant (`E3`, the STA metric
  `fun i => if i.1 = 0 then 1 else -1`, PGA's `0`); anything else stays
  symbolic as `g i` (so `Cl g` for a variable `g : Fin 3 → R` works too).
* **Hypotheses**: every hypothesis `h : a = b` between multivectors of the
  same space is converted to its coordinate equations; scalar hypotheses
  (`c ^ 2 + s ^ 2 = 1`) are used by `grind` directly.

### How it works

1. **Reify** both sides (and the multivector hypotheses) into
   `Grassmann.Tactic.MExpr`, a syntax tree of multivector operations whose
   leaves are blades, scalars (`Poly`) and opaque multivectors. `MExpr.denote`
   maps it back to `Cl g`, and the reified tree denotes the goal's own terms
   up to definitional unfolding (so `a - b` is `Poly.sub`, not `a + -b`, and
   `x ^ 2` is `pow`, not `x * x`: in an abstract ring those are not
   definitionally equal).
2. **Evaluate** `MExpr.eval n ms : MExpr → List Poly`, the `2ⁿ` coordinates
   of the expression as coefficient polynomials. The product of two dense
   vectors is `Z[c] = Σ_a X[a] Y[a ⊕ c] k(a, a ⊕ c)`, with `k` the spec's own
   blade coefficient (`sigma` and the metric factor of `DirectSum.Proofs`, the
   same functions `Grassmann.Spec.coef` is built from); zero terms are pruned
   as they arise (`addS`, `mulS`), so products of explicit blades fold to
   constants. The tactic runs `MExpr.eval` natively.
3. **State** the coordinate equations `rx_c = ry_c` (`c < 2ⁿ`) as ring
   expressions over the atoms. The proof term is
   `eq_of_coords hms x y ⟨p₀, ⟨p₁, …⟩⟩`, whose last argument must have type
   `AllEq … (x.eval n ms) (y.eval n ms)`; the kernel checks that this is
   definitionally the conjunction of the stated equations by evaluating
   `MExpr.eval` itself. The metric entries that were folded to constants are
   justified the same way (`metricOK_of_allBelow`, one `rfl` per entry).
4. **Close** every coordinate equation that is not syntactically trivial
   with `grind` (its commutative ring solver, with Gröbner bases for the
   hypotheses). A coordinate whose two sides are different integers fails
   immediately with a message naming the blade.

The soundness theorems `Grassmann.Tactic.eq_of_coords` (equal coordinates ⇒
equal multivectors) and `coords_of_eq` (the converse, for hypotheses) are
proved once for every dimension, metric and commutative ring, from the spec
model's `bsum`/`twist` definitions; they use only the standard axioms
(`Tests/Proofs/Axioms.lean`).

### Variants

* `clifford [p₁, …, pₖ]` passes extra parameters to `grind` (lemmas,
  definitions to unfold, `grind` modifiers).
* `clifford_nf` stops after step 3 and leaves one goal per non-trivial
  coordinate, tagged with its blade (`scalar`, `e₁`, `e₁₂`, …). Use it to see
  what the identity amounts to, or to close the coordinates another way.

```lean
example (u₁ u₂ u₃ w₁ w₂ w₃ : R) :
    Cl.hodge (Cl.wedge (vec u₁ u₂ u₃) (vec w₁ w₂ w₃))
      = vec (u₂ * w₃ - u₃ * w₂) (u₃ * w₁ - u₁ * w₃) (u₁ * w₂ - u₂ * w₁) := by
  clifford_nf
  -- case e₁ ⊢ u₂ * w₃ + -(u₃ * w₂) = u₂ * w₃ - u₃ * w₂
  -- case e₂ ⊢ -(u₁ * w₃ + -(u₃ * w₁)) = u₃ * w₁ - u₁ * w₃
  -- case e₃ ⊢ u₁ * w₂ + -(u₂ * w₁) = u₁ * w₂ - u₂ * w₁
  all_goals grind
```

### Examples (`Tests/Proofs/TacticExamples.lean`)

| identity | space |
|---|---|
| `(a v₁ + b v₂)² = a² + b²`, `(a v₁ + b v₂ + c v₃)² = a² + b² + c²` | ℝ³ |
| `v₁ v₂ = -v₂ v₁`, `(v₁ v₂)² = -1`, `(v₁ v₂)⁴ = 1`, `I² = -1` | ℝ³ |
| triple product `u ∧ v ∧ w = det(u, v, w) I` | ℝ³ |
| Lagrange `(u ∧ v)(u ∧ v)~ = |u|²|v|² - (u·v)²` | ℝ³ |
| `⋆(u ∧ v) = u × v`, `u v = u·v + u ∧ v` | ℝ³ |
| Jacobi for the commutator product of bivectors; bivectors closed under it | ℝ³ |
| Jacobi for opaque multivectors `x y z` (24 coordinate atoms) | ℝ³ |
| quaternions `i² = j² = k² = ijk = -1`, `ij = k` (`i = v₃v₂`, …) | ℝ³ |
| rotor normalization `R R̃ = 1` from `c² + s² = 1` | ℝ³ |
| `R v R̃` has no trivector part (even `R`, symbolic) | ℝ³ |
| isometry `(R v R̃)² = v²` from `a² + b² + c² + d² = 1`, or from the multivector hypothesis `R R̃ = 1` | ℝ³ |
| `γ₀² = 1`, `γ₁² = -1`, `γ₀ γ₁ γ₀ = -γ₁`, `γ₀γ₁γ₂γ₃ = I`, `I² = -1`, Minkowski norm, `(γ₁γ₀)² = 1` | STA `(+,-,-,-)` |
| Clifford relation for a symbolic metric `g` | `Cl g`, `g : Fin 3 → R` |
| `e₀² = 0` | PGA₃ |
| `~(x y) = ỹ x̃` for opaque `x y` | ℝ⁵ |
| `1 + e₁₂₃₄` sandwiches `e₅` to `2 e₅ + 2 I` (grade preservation stops at `n = 4`) | ℝ⁵ |

**Timing** (`trace.profiler`): every example elaborates in under 0.8 s (most
under 0.15 s: explicit elements fold to a handful of terms per coordinate), and
the kernel re-checks each in under 1.3 s; the whole file takes about 10 s.
Costs grow with the number of symbolic coordinates: associativity of three
opaque multivectors takes 0.2 s in ℝ³ but about 2 s of elaboration and 25 s of
kernel checking in STA (16 coordinates, each a 256-term polynomial identity
for `grind`'s certificate).

### Limits

* Concrete spaces only: the dimension must be a numeral, and coordinates are
  dense (`n ≤ 6`). For identities in every dimension, use the laws
  (`Grassmann.Spec`) or `grind [grassmann]`.
* Operations outside the list above are opaque: their coordinates are atoms,
  so identities that depend on what they compute will not close.
* Goals must be multivector equations (not `≠`, not coefficient equations).

## 2. `grind` on the specification algebra

### Extension points used

`grind` (v4.35) offers these extension points, all used here:

| mechanism | used for |
|---|---|
| `Lean.Grind.Ring` instance | `Cl.instRing` (`Grassmann.Spec.Ring`): `grind`'s non-commutative ring normalizer handles multivector expressions |
| `register_grind_attr` | the `grassmann` lemma set (`Grassmann.Spec.GrindAttr`): opt-in with `grind [grassmann]` |
| `@[attr =]`, `@[attr ←]` | equational lemmas by their left side; grade-closure lemmas backward (they fire when a `IsGrade k t` term appears) |
| `grind_pattern [attr] thm => p₁, p₂, …` | multi-patterns for graded commutativity: fire on an existing `x ∧ y` whose factors are known to be homogeneous, instead of creating new wedge terms |
| `[grind norm]` | pushing the involutions inward, in `grind`'s preprocessor (only the default `grind` attribute can carry normalization rules) |

Not used: `[grind ext]`/`funext`-style extensionality (coordinates are the
`clifford` tactic's business), `hom` rules (they are for embedding into a
solver's domain, and there is no module solver for `R`-scalars).

### The ring instance

`Cl g` is a `Lean.Grind.Ring`: numerals `0`, `1`, `k` (`k ≥ 2` is the scalar
`k`), integer casts, powers. All numerals of `Cl g` come from one `OfNat`
family (`Cl.instOfNat`), which is also the ring's `ofNat`, so the goal's `0`
and `1` are `grind`'s. With it, plain `grind` proves

```lean
example (x y z w : Cl g) : x * (y * z) * w = x * y * (z * w) := by grind
example (x y : Cl g) : (x + y) * (x - y) = x * x - y * y - x * y + y * x := by grind
example (x : Cl g) : (2 : Cl g) * x - x = x := by grind
```

`grind`'s non-commutative normalizer decides equalities that follow from the
ring axioms, comparing the two sides of the goal as non-commutative
polynomials. It does not rewrite with equations between products (there is
no non-commutative Gröbner basis), so a hypothesis `y * z = 0` is only used
where `y * z` literally occurs: `x * y * z = 0` needs the product
re-bracketed, `grind [Cl.mul_assoc]`.

### Involutions: normalization rules

Reversion, grade involution and Clifford conjugation are pushed through
`+ - * • ∧` and evaluated on `0`, `1`, scalars and generators, by `[grind
norm]` rules (`Grassmann.Spec.Grind`). This is a terminating, confluent
rewrite system and it only touches terms built from `Cl.reverse`,
`Cl.involute`, `Cl.clifford`; it is active in modules that import
`Grassmann.Spec.Grind` (or `Grassmann.Tactic`). Products then reach the ring
normalizer with the involutions on their atoms:

```lean
example (x y z : Cl g) : reverse (x * y * z) = reverse z * reverse y * reverse x := by grind
example (r x : Cl g) : reverse (r * x * reverse r) = r * reverse x * reverse r := by grind
example (x y : Cl g) : clifford (x * y) = clifford y * clifford x := by grind
```

### The `grassmann` lemma set

| group | lemmas | how they fire |
|---|---|---|
| generators | `eᵢ² = gᵢ`; `eᵢeⱼ = -eⱼeᵢ` (`i ≠ j`, decided by `grind`) | `=` |
| vectors | `v² = B(v,v)`, `u v + v u = 2B(u,v)`, `u ⋅ v = B(u,v)`, `u ∧ v = -(v ∧ u)`, `v ∧ v = 0`, `ṽ = v`, `v̂ = -v` (all conditional on `IsGrade 1`) | `=` |
| grades | `IsGrade k` of `0`, `x + y`, `-x`, `x - y`, `r • x`, `⟨x⟩ₖ`; scalars have grade 0, generators grade 1 | `←` (backward) |
| graded commutativity | `x ∧ y` is homogeneous of grade `p + q`; `x ∧ y = y ∧ x` for `pq` even, `= -(y ∧ x)` for `pq` odd | multi-pattern on `x ∧ y` with `IsGrade p x`, `IsGrade q y` |
| sandwiches | `R̃R = 1 ⇒ (R x R̃)(R y R̃) = R (x y) R̃`; `R R̃ = 1 ⇒ R c R̃ = c`; isometry `(R v R̃)² = B(v,v)`; grade preservation (below) | `=`, `←` |

```lean
-- the vector hypothesis is derived from the shape of the element
example (a b : R) : (a • gen 0 + b • gen 1 : Cl g₃) * (a • gen 0 + b • gen 1)
    = scalar (dot (a • gen 0 + b • gen 1 : Cl g₃) (a • gen 0 + b • gen 1)) := by grind [grassmann]
-- graded commutativity: a vector and a bivector commute under ∧
example (u B : Cl g) (hu : IsGrade 1 u) (hB : IsGrade 2 B) : wedge u B = wedge B u := by
  grind [grassmann]
-- grade preservation (NoNatZeroDivisors: no 2-torsion)
example [NoNatZeroDivisors R] (r v : Cl g₃) (hr : involute r = r) (hv : IsGrade 1 v) :
    IsGrade 1 (r * v * reverse r) := by grind [grassmann]
```

`Tests/Proofs/GrindExamples.lean` has 29 such identities; the file checks in
about half a second.

### Sandwiches and grade preservation (`Grassmann.Spec.Sandwich`)

For an even `R` (`R̂ = R`) and a vector `v`, `R v R̃` is self-reverse (so its
parts of grade `≡ 2, 3 (mod 4)` vanish) and odd (so its even parts vanish),
over any commutative ring without 2-torsion. Hence its only parts have grade
`≡ 1 (mod 4)` (`proj_sandwich_of_even`), and in dimension `≤ 4` it is a vector
(`isGrade_sandwich_of_even`). No normalization `R R̃ = 1` is needed; with it,
the sandwich is an isometry (`sandwich_sq_of_vector`). In dimension 5 and up
the grade-5 part can survive for a general even `R` (`clifford` checks that
`1 + e₁₂₃₄` sandwiches `e₅` to `2 e₅ + 2 I`); for versors it does not, but
that needs the versor structure, which the model does not have yet.

### Where `grind` stops

The non-commutative normalizer compares the goal's two sides as they stand;
equalities that `grind` learns about sub-products (from E-matching) are used
by congruence closure only where those sub-products literally occur. So:

* `ṽ v = v²` for a vector works (`ṽ` and `v` are atoms, merged), but
  `r (ṽ r̃) = r v r̃` does not (the atom `ṽ` inside a product);
* products of generators that need several anticommutations and
  re-bracketings (`e₀ e₁ e₀ = -g₀ e₁`) are out of reach.

These are coordinate computations in a concrete space: use `clifford`
(with a symbolic metric if needed). For statements in every dimension, prove
the law once in `Grassmann.Spec` and add it to the set.

## 3. Choosing

* A concrete space and explicit (or partly symbolic) elements: `clifford`.
  Without hypotheses it is a decision procedure (each coordinate is a
  polynomial identity, which `grind`'s ring normalizer decides); with
  polynomial hypotheses `grind` searches for an ideal-membership certificate
  (Gröbner basis).
* Abstract elements in any dimension, identities that follow from the ring
  structure, the involution laws and the lemma set: `grind [grassmann]`.
* Anything else: a lemma in `Grassmann.Spec`, then tag it.
