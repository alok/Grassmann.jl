# Design: the chakravala ecosystem in Lean 4

This is the contract for the port. Per-package porting specs, with exact
semantics, file:line citations into the Julia sources and golden candidates,
live in [`docs/port-notes/`](port-notes/). Read the relevant one before you
touch a module.

## 0. Goals and non-goals

* **Goal:** a faithful, fast Lean 4 port of Michael Reed's Julia ecosystem.
  The core is AbstractTensors, StaticVectors, Leibniz, DirectSum and Grassmann.
  Downstream come Cartan, MeshTopology, Adapode, Fatou, the UnitSystems family
  and the small algebra packages.
* **Faithful** means it agrees with the Julia oracle on values, result kinds
  and printed strings. The exceptions are the documented Julia defects listed
  in the port notes (§8.6 of each), which we *fix*, not replicate.
* **Fast** means within about 1.5× of Julia on the hot paths (products,
  sandwiches, exp/log, field sampling) for the common algebras.
  Measured, not guessed: see [`docs/PERF.md`](PERF.md).
* **Dependent types where they are free.** Grades, dimensions, lengths and
  parities live in types; proofs are erased. Never pay runtime for a
  type-level nicety.
* **Proofs where they buy velocity or trust:** kernel-checked tables (`decide`),
  homomorphism theorems that make whole case tables correct at once, and a
  few flagship algebraic theorems.
* **Non-goals (v1):**
  * Julia's symbolic backends (Reduce/SymPy/Symbolics). Any Lean coefficient
    type that satisfies the classes works instead.
  * `@generated` caching quirks.
  * Makie reactivity.
  * Pixel-exact Makie reproduction. Plot *data* is compared numerically;
    images are compared visually.

## 1. Repository layout

```
lakefile.toml / lean-toolchain (leanprover/lean4:v4.35.0-rc3)   # zero [[require]]
JuliaBase/      # Julia Base semantics: F64/F32/JInt numerics, exact IEEE, Julia's own exp/log/pow,
                #   parse/round, sum, Complex, show, ranges, Float16
StaticVectors/  AbstractTensors/  Leibniz/  DirectSum/  Grassmann/     # core
Cartan/  MeshTopology/  Adapode/  Fatou/                                 # geometry & numerics
FieldAlgebra/  FieldConstants/  UnitSystems/  Similitude/  MeasureSystems/
Dendriform/  DeMorgan/  AbstractLattices/  AbstractAnalysis/  Wilkinson/  PrimitiveBits/
Geophysics/  FlowGeometry/
Tests/          # `lake test` driver: unit, golden (oracle), property tests
Bench/          # `lake exe bench`: benchmarks; `--smoke` for CI
oracle/         # Julia Project.toml/Manifest.toml + generators → oracle/golden/*.json (committed)
gallery/        # sub-package: requires root + LeanPlot; renders the plot gallery
bridge/         # sub-package: requires root + mathlib; CliffordAlgebra bridge theorems
docs/           # DESIGN.md (this), PERF.md, port-notes/, guides/
```

Each Julia package becomes one `lean_lib` with a root file `Pkg.lean`
re-exporting `Pkg/*.lean`. Namespaces match the package names. `Grassmann`
re-exports the user-facing API of its dependencies, as Julia's `Grassmann`
does.

## 2. Coding rules (enforced in review)

1. **Floats in bulk:**
   * Never store them in `Array Float` or `Array (Float × Float)`: every
     element is boxed.
   * Use `StaticVectors.Values α n` (a packed `FloatArray` at `α = Float`),
     or raw `FloatArray`/`ByteArray` in structure-of-arrays form.
2. **Hot loops over Floats** must be tail-recursive functions with explicit
   Float accumulators and a `Nat` fuel/index. Do not use `for … do … break`
   with `let mut` Floats: the `ForInStep` closure boxes every Float (measured
   8× slower).
3. **Generics** over a coefficient type use one bundled class argument
   (`[Coeff α]`, §4.1) and are marked `@[specialize]`. Specialization at
   `Float` must produce unboxed code; check hot kernels with
   `set_option trace.compiler.ir.result true` when in doubt.
4. **Kernel-reducible definitions:** anything used in types or checked by
   `decide` uses structural recursion only. No `termination_by` or `for`
   loops. Examples: `binomial`, `ofFn`, table builders used at small sizes.
5. **Exactness first in tests.** Prefer `Int`/`Rat` coefficients for goldens
   where Julia is exact. Float comparisons use explicit tolerances
   (`rtol = 1e-12` for kernels, looser for iterative numerics).
6. **Every public declaration gets a docstring.** Cite the Julia source
   (`Grassmann.jl src/products.jl:123`) when porting a specific function.
7. **No `sorry`, no custom `axiom`, no `native_decide`** in library code.
   Tests may use `#guard`/`decide`.
8. **Atomic commits:** one logical change each, building green. Message
   format `area: imperative summary`.
9. **One home for Julia `Base`.** Scalar Julia semantics (`F64.max`/`min`,
   `isapprox`, `hypot`, `cbrt`, `Float64(::Rational)`, the exact IEEE toolkit
   `IEEEFloat`, Julia's own `exp`/`log`/`expm1`/`log1p`/`^` kernels and its
   trigonometric and hyperbolic functions (`JuliaBase.Trig`, `JuliaBase.Hyperbolic`;
   no library calls the platform `libm` where Julia has its own kernel), the one
   literal macro `f64!`/`f32!`, `parse`,
   `round(digits/sigdigits)`, `sum(::Vector{Float64})`, `Float16`, the
   `Complex` type and its `ComplexF64` algorithms, `show`, ranges) live in
   `JuliaBase` and nowhere else. Other libraries import it; they add only their
   own class instances (`Coeff`, `Analytic`, `JNorm`, …) on top. A package that
   needs more of Julia `Base` adds it to `JuliaBase` (with oracle goldens in
   `Tests/JuliaBase/`), not locally.

## 3. The space layer (DirectSum)

```lean
namespace DirectSum

/-- Metric of a tensor bundle (Julia `Signature` / `DiagonalForm` / `MetricTensor`). -/
inductive Metric where
  /-- bit k set ⇔ e_{k+1}² = -1 (Julia `Signature` bits `S`) -/
  | signature (neg : UInt64)
  /-- diagonal values (Julia `DiagonalForm`); 0 allowed (degenerate) -/
  | diagonal (d : Array Rat)
  /-- general symmetric Gram matrix (Julia `MetricTensor`), row-major -/
  | tensor (g : Array (Array Rat))
  deriving DecidableEq, Repr, Hashable

/-- A tensor bundle / vector space: Julia `TensorBundle{n,Options,Metrics,Vars,Diff,Name}`. -/
structure TensorBundle where
  n        : Nat               -- mdims: total generators incl. tangent vars
  metric   : Metric
  hasinf   : Bool := false     -- ∞ null generator present (index 1)
  hasorigin: Bool := false     -- ∅ null generator present
  dyadmode : Int  := 0         -- -1 dyadic V⊕V', +1 dual V', 0 plain
  polymode : Bool := true
  diffvars : Nat  := 0         -- ν tangent variables (Julia `Vars`)
  diffmode : Nat  := 0         -- μ Leibniz-Taylor order (Julia `Diff`)
  name     : Nat  := 1         -- prefix set index (v/w/∂/ϵ)
  deriving DecidableEq, Repr, Hashable
```

* Element types are indexed by a value `V : TensorBundle`. Common spaces are
  `abbrev`s (`ℝ2`, `ℝ3`, `ℝ4`, `STA := S!"-+++"`, `PGA3 := D!"0,1,1,1"`,
  `CGA3 := S!"∞∅+++"`, …). Typeclass instances keyed on them are found by
  discrimination-tree matching after reducible unfolding.
* **Syntax:**
  * Julia string macros become the tokens `S!"+++"`, `D!"1,1,0"`, `V!"∞∅+++"`
    (the `s!`/`m!` convention: `!` after a one-letter prefix is a token, so
    the identifiers `S`/`D`/`V` stay free).
  * `ℝ^n` is the token `ℝ^` followed by a term. Mathlib's `ℝ` notation is a
    different, shorter token, so the two coexist.
  * Dual: `V.dual` or postfix `V′`. Direct sum: `V ⊕ W`, overloaded with `Sum`
    at `Sum`'s precedence.
* **Submanifolds and basis blades.** A blade is a `UInt64` bitmask (bit k ⇔
  generator k+1) *at runtime*. `Submanifold V G` carries static grade `G`
  and runtime `bits`, with the invariant `popcount bits = G` maintained by
  smart constructors. The space-as-submanifold view (`V(1,2)`, masks) is
  `SubSpace V` with a runtime mask.
* **Index tables** (Leibniz `indexbasis`/`bladeindex`/`basisindex`/
  `spinindex`/`antiindex`) are lex order within a grade and grade-major
  across grades, exactly as in port-notes/directsum.md §3 and
  grassmann-parity.md §3.4. Build them per `n` as closed terms memoized with
  `Thunk` for n ≤ 12, and compute them by closed-form lex rank beyond that.
  Prove the bijections by `decide` for small n.
* **Parity/sign functions** (DirectSum `operations.jl`, Grassmann
  `parity.jl`) are pure functions on `(V, a, b : UInt64)`. Port them
  bit-for-bit from port-notes/grassmann-parity.md §4. The conformal space
  uses the *Gram* (Chevalley) product, not a sign table, and must reproduce
  the verified behavior (C3/C5 match the true Clifford product). Fix the
  documented defects (C4neg, MetricTensor).

## 4. Element types (Grassmann)

### 4.1 Coefficients

```lean
/-- Everything a kernel needs from a coefficient type. Bundled so generic
kernels take one instance argument and specialize cleanly. -/
class Coeff (α : Type) extends Add α, Sub α, Mul α, Neg α, Inhabited α where
  zero : α
  one  : α
  ofInt : Int → α
  ofRat : Rat → α          -- metric factors of DiagonalForm / conformal ½
  isZero : α → Bool        -- exact zero test (Julia `iszero`)
  [packed : StaticVectors.Packed α]
```

Instances: `Float`, `Float32`, `Int`, `Rat`, and `Complex α` (our own
computable `JuliaBase.Complex`, Julia's `Complex{T}`; the `Float64` algorithms live in
the `JuliaBase.ComplexF64` namespace). Recursive instances (`Chain V G α` as a coefficient)
come later. Transcendentals use a separate class `Analytic α` (sqrt, exp,
log, sin, cos, sinh, cosh, atan2, …), with instances for `Float` and
`Complex Float`.

### 4.2 Static layer: typed containers, zero-cost indices

```lean
structure Chain        (V : TensorBundle) (G : Nat) (α) [Coeff α] where v : Values α (binomial V.n G)
structure Multivector  (V : TensorBundle) (α) [Coeff α]           where v : Values α (2 ^ V.n)
structure Half         (V : TensorBundle) (odd : Bool) (α) [Coeff α] where v : Values α (halfDim V.n odd)
abbrev Spinor V α   := Half V false α     -- even grades (Julia `Spinor`; "Quaternion" when n = 3)
abbrev CoSpinor V α := Half V true  α     -- odd grades  (Julia `CoSpinor`/`AntiSpinor`)
structure Single       (V) (G : Nat) (α) where bits : UInt64; val : α     -- scaled blade, static grade
structure Submanifold  (V) (G : Nat)     where bits : UInt64              -- unit blade, static grade
structure Couple       (V) (α) where bits : UInt64; re : α; im : α      -- scalar + blade B (runtime)
structure PseudoCouple (V) (α) where bits : UInt64; re : α; im : α      -- blade B + pseudoscalar
structure Phasor       (V) (α) where amp : α; angle : Couple V α        -- per Julia MV:852+
```

`binomial` is our own structural, kernel-reducible, multiplicative
definition: `binomial n k = 0` for `k > n`. `halfDim n odd` is `2^(n-1)` for
`n ≥ 1`, and `(1, 0)` for `n = 0`.

**Result-type rules.** A result type is static whenever the output
grade/parity is a function of the input grades/parities. Otherwise the
output is the smallest static container that is always correct.

| op | signature |
|---|---|
| `+ -` | `Chain V G + Chain V G → Chain V G`; `Single V G + Single V G → Chain V G`; `Half V p + Half V p → Half V p`; anything else → `Multivector V` |
| `*` (geometric, `⟑`) | `Chain V G * Chain V H → Half V ((G+H)%2==1)`; `Half p * Half q → Half (p ^^ q)`; `Chain G * Half p → Half (p ^^ (G%2==1))`; with `Multivector` → `Multivector`; `Submanifold V 1 * Submanifold V 1 → Couple V` (eᵢeⱼ = g(eᵢ,eⱼ) + eᵢ∧eⱼ holds for any symmetric metric) |
| `∧` | `Chain V G ∧ Chain V H → Chain V (G+H)` (empty, hence zero, when `G+H > n`) |
| `∨` | `Chain V G ∨ Chain V H → Chain V (G+H-n)` (truncated subtraction yields a zero scalar when `G+H < n`) |
| `⋅` (Julia `contraction`, right contraction `a ∨ ⋆b`) | `Chain V G ⋅ Chain V H → Chain V (G-H)` |
| `⋆`, `!` (complements) | `Chain V G → Chain V (n-G)`; `Half V p → Half V (p ^^ (n%2==1))` |
| `~`, `involute`, `clifford` | preserve the type |
| `×` (cross) | `Chain V 1 × Chain V 1 → Chain V (n-2)` = `⋆(a∧b)` |
| `⊘` (sandwich), `>>>` | per port-notes/grassmann-products.md §4.6 |

Generic instances match `Chain V G`, `Half V p` and so on with the indices as
variables, so typeclass resolution never has to reduce a computed index.
Kernels dispatch on the runtime values of `G`, `H`, `p`, `q`. `@[inline]`
dispatchers let concrete call sites constant-fold the branch.

### 4.3 Dynamic layer: Julia-exact semantics

```lean
inductive TA (V : TensorBundle) (α) [Coeff α] where
  | zero | one | infinity
  | blade  (b : UInt64)                 -- Submanifold (unit)
  | single (b : UInt64) (x : α)
  | chain  (g : Nat) (c : Chain V g α)
  | couple (b : UInt64) (re im : α) | pseudo (b : UInt64) (re im : α)
  | spinor (s : Spinor V α) | cospinor (s : CoSpinor V α) | multi (m : Multivector V α)
  | phasor …
```

* `+`/`-` implement Julia's promotion lattice (grassmann-types.md §4.5,
  including the space-option guards that disable Couple in conformal and
  tangent spaces).
* Products dispatch to the static kernels, then re-wrap into Julia's result
  kind (grassmann-products.md §4.5).
* `toString` reproduces Julia's `show` exactly (§6).
* **Correctness theorem (one proof covers the whole lattice):**
  `toDense (a + b) = toDense a + toDense b`, together with `toDense_neg` and
  `toDense_smul`, where `toDense : TA V α → Multivector V α`.
* The oracle compares `TA` results: kind tag, dense values and printed string.

### 4.4 Notation (scoped in `Grassmann`; `open Grassmann` to use)

| op | token | precedence | notes |
|---|---|---|---|
| geometric product | `*`, `⟑` | 70 | |
| exterior | `∧` | 35, right-assoc (Lean's `And` level) | overloaded with `And` via choice nodes. **Differs from Julia (12):** write `(a ∧ b) + c` |
| regressive | `∨` | 30, right-assoc (Lean's `Or` level) | overloaded with `Or`. Same caveat |
| contraction | `⋅`, `⨽`, `⨼` | 70 | |
| cross | `×` | 35 (Lean's `Prod` level) | overloaded with `Prod` |
| sandwich | `⊘` | 70 | |
| tensor | `⊗` | 70 | |
| Hodge / complement | prefix `⋆`, `!` | max | `!` overloads `Bool.not` by type |
| reverse | prefix `~` | max | |
| postfix `₊ ₋ ǂ ⁻¹` | postfix | max | `⁻¹` via `Inv` |

**Porting rule:** when translating Julia expressions that mix `∧`/`∨` with
`+`/`-`/`*`, parenthesize every wedge/vee operand. The oracle tests catch
misparses.

### 4.5 Basis generation

`basis! S!"∞∅+++"` (Julia `@basis`) declares in the current namespace:
* `V`;
* the unit `v`;
* every blade `v₁`, `v₁₂`, …, with conformal names `v∞`, `v∅`, `v∞∅₁` as
  `«v∞»` plus ASCII aliases `vinf`/`vo`;
* dual names `w¹…`.

Each blade is a `Submanifold V G`. A `Coe` to `Single V G Int` and `TA V α`
makes `2 • v₁ + 3 • v₂ : Chain V 1 Int` work. `basis!` also emits the
unrolled kernels for `V` (§5.2) when `n ≤ 6`.

## 5. Kernels

### 5.1 Reference semantics

The blade-level source of truth is `DirectSum.Ops`: `BinOp`/`UnOp`, `terms₂`/`terms₁` (exact `Rat` term lists)
and `plan₂`/`plan₁` (multiply-accumulate plans in Julia storage order for any `Layout`), all oracle-verified.

`Grassmann/Kernel/Reference.lean` defines every product, blade by blade:
geometric, wedge, regressive, contraction, and the complements, from the
parity functions. It uses plain loops and is correct for every space. It is
the specification that all fast paths are tested against, and the object of
the flagship theorems.

### 5.2 Generated kernels (Julia `@generated` ≅ Lean elaboration-time codegen)

A command elaborator (`Grassmann/Kernel/Codegen.lean`) takes `V` and a shape
pair. It enumerates the nonzero blade-pair contributions using the reference
sign and metric functions, *evaluated at elaboration time*. It then emits a
`@[specialize] def` with straight-line code generic over `[Coeff α]`, reading
inputs with `Values.get!` at literal indices and building the output with a
push chain.

The spike (docs/PERF.md) measured these kernels. Specialized at `Float`,
they match hand-written `FloatArray` code:

| full product | Julia | Lean |
|---|---|---|
| n=3 | 19.8 ns | 23 ns |
| n=5 | 152 ns | 250 ns |
| n=6 | 8.2 µs | 1.2 µs |

Emission policy mirrors Julia's thresholds:
* all Chain×Chain pairs with `binomial(n,G)·binomial(n,H) < 4096`;
* Half×Half and Half×Chain for `n < 12`;
* Multivector×Multivector for `n ≤ 6`.

Every generated kernel is registered as an instance of a per-space kernel
class. The instance is generic over `α`, so the compiler inlines the
projection and specializes it.

### 5.3 Fallback kernels

For spaces without generated kernels (large or runtime-constructed `V`):
1. A plan is built from the reference functions: arrays of
   `(ia, ib, ic, coeff)`.
2. It is memoized per `(V, op, shapes)` in a global `IO.Ref (Std.HashMap …)`
   cache read through `unsafeBaseIO`. This is referentially transparent,
   exactly like Julia's parity caches.
3. It is interpreted by a tight `USize` loop.

### 5.4 Dispatch

`class Kernels (V : TensorBundle)` bundles per-shape product functions,
polymorphic in `α`. A low-priority instance for every `V` uses the fallback.
`basis!`/`grassmann_kernels` add high-priority generated instances.

## 6. Display

Julia's printing is part of the oracle contract (grassmann-types.md §5,
leibniz.md §5):
* index glyphs;
* `showvalue`/`showterm`;
* per-type rules (zeros printed in Chain/Spinor, suppressed in Multivector,
  the `v⃖` suffix);
* the compact-IO context (6 significant digits);
* Julia's shortest-round-trip float printing (Ryu), with its exact
  `exp_form` rule.

`Grassmann/Show/JuliaFloat.lean` implements Ryu shortest and is fuzz-tested
against 10⁵ oracle doubles. `ToString`/`Repr` instances on both layers use it.

## 7. Oracle and tests

> Normative schema: [`docs/port-notes/oracle-schema.md`](port-notes/oracle-schema.md). Element-level goldens are
> sharded (`oracle/golden/<suite>/manifest.json` + shards + an inputs pool) with machine-readable defects in
> `oracle/golden/defects.json`; the summary below is the original plan.

* `oracle/Project.toml` pins the registered Julia packages
  (Grassmann 0.8.46, Cartan 0.4.16, …).
* `oracle/generate_all.jl` runs one generator per suite and writes
  `oracle/golden/<suite>.json`:
  `{"meta":{julia,pkgs,seed}, "cases":[{"space":…, "op":…, "args":[…], "out":{kind, dense, str}}]}`.
* Encoding:
  * spaces as their Julia string plus decoded fields;
  * elements as `{kind, grade?, bits?, dense:[…], str}`, where `dense` is
    the full `2^n` coefficient vector in Julia's `Multivector` order;
  * numbers as exact strings when Rational/Int and as `repr(Float64)` for
    floats, so they round-trip bit-exactly.
* `Tests/Golden/*.lean` load the JSON with `Lean.Json`, run the Lean
  operation on the `TA` layer, and compare kind, dense values (exact or
  rtol) and string.
* Documented Julia defects are listed in `oracle/defects.toml` and skipped
  with a reason.
* Property tests (SplitMix64 from `Tests/Util/Random.lean`): associativity,
  graded commutativity of `∧`, `a·b = a⌋b + a∧b` for vectors, involution
  laws, `⋆⋆` signs, and fast-kernel ≡ reference kernel on random inputs for
  every generated space.
* Compile-time tests: `example : … := by decide` over `Int` coefficients in
  small spaces.

## 8. Proof targets (in priority order)

1. Index-table bijections and sizes (`decide` for n ≤ 6; structural in
   general).
2. `toDense` homomorphism theorems for the dynamic layer (§4.3).
3. Reordering-sign cocycle, hence associativity of the reference geometric
   product for diagonal metrics, over any `Lean.Grind.CommRing α`.
4. Graded commutativity of `∧`; `~(ab) = ~b ~a`; the Hodge double-complement
   sign.
5. `bridge/`: our algebra over `ℚ`/`ℝ` is isomorphic to Mathlib's
   `CliffordAlgebra Q` for diagonal `Q` (universal property + dimension
   count).

## 9. Visualization (LeanPlot co-development)

LeanPlot is restructured (port-notes/leanplot-audit.md §8):
* a **zero-dependency core**:
  `Figure → layout → DrawOp` IR, with SVG and anti-aliased raster/PNG (real
  DEFLATE) backends;
* Makie-faithful recipes: lines, scatter, arrows, streamplot, heatmap,
  contour(f), mesh, surface, wireframe;
* colormaps, ticks and an Axis3 camera;
* widgets and docs as optional sub-packages.

The `gallery/` sub-package reproduces the Julia README/docs plots. The Julia
side dumps the plot *data* (JSON) and a CairoMakie PNG, and the gallery
compares the data numerically and shows both images side by side.
