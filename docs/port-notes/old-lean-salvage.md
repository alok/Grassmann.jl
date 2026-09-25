# Salvage audit of the old Lean port (`Grassmann4/`, branch `archive/lean-port-v1-wip`)

Scope: this is a read-only audit of the first Lean 4 port of Grassmann.jl, at
`/Users/alokbeniwal/Grassmann/Grassmann4` (outer repo HEAD `7c29d7d`, 692
commits). Weaker models wrote it over Dec 2025 – Jul 2026, and the hard-cutover
rewrite will replace it. This document is meant to save the new implementer from
re-reading that code. It records:

* (a) which ideas and code are worth salvaging, with paths and reasons;
* (b) the performance findings the old port measured, including which
  compiled-Lean patterns were fast or slow;
* (c) the pitfalls and mistakes to avoid;
* (d) the places where the old port disagrees with Grassmann.jl. I re-checked
  those points against the live Julia oracle in
  `scratchpad/juliaenv` (Grassmann.jl master, Julia 1.13).

All paths below are relative to `/Users/alokbeniwal/Grassmann/`. `G4/` means
`Grassmann4/`. Line numbers refer to the working tree at `7c29d7d`.

The Julia probe scripts I used are in `scratchpad/notes/probe{1..7}.jl`. Their
outputs are quoted verbatim in §6.2 and Appendix A.

---

## 0. Executive verdict

**The hard cutover is correct.** The old port's architecture has several
problems. Mask-order storage differs from Grassmann.jl's order. The dense
`Multivector` is built from closures. There are six representations with
disjoint notations. Signatures are values that Lean never monomorphizes.
Several products and operators disagree semantically with Grassmann.jl.
Theorems about Float are false and still carry `sorry`. None of this is worth
carrying forward as code.

A small number of **algorithms, techniques, harness ideas, and measured
lessons** are worth keeping. The top items to salvage are:

| # | What | Where | Why |
|---|------|-------|-----|
| S1 | Straight-line fixed-algebra kernels: quaternion, dual quaternion, even×odd, odd×even, and a **fused motor sandwich** that makes one allocation | `G4/Grassmann/PGA3Kernel.lean:104-141, 254-345, 346-404`; `G4/Grassmann/MV.lean:700-718` | This is the performance shape the new port should *generate*: a few ns of arithmetic and exactly one `FloatArray` allocation. The measured PGA3 point transform went from 4326.7 → 542.3 ns/point after fusion (`ralph/progress.txt:137`). |
| S2 | Motor → 3×4 affine extraction, applied to flat XYZ batches | `G4/Grassmann/PGA3Kernel.lean:437-476` | 10.53 ns/point for the Lean batch vs 660.7 ns/point per scalar call (62.75x) (`ralph/progress.txt:139`). Batch APIs are mandatory. |
| S3 | Rigid-motor validity via the Study condition, plus checked normalize/inverse | `G4/Grassmann/PGA3Kernel.lean:156-244`; `G4/c/grassmann_cabi.c:~80-110` | These are correct and oracle-checked formulas. The new port should re-derive them in Grassmann.jl's basis order. |
| S4 | Output-stationary exterior product that enumerates submasks (O(3ⁿ), not O(4ⁿ)) | `G4/Grassmann/MV.lean:477-560` | Each output coefficient is accumulated in one unboxed Float and written with one push. It has no scatter writes and needs no sign table. |
| S5 | Metric-free complement signs packed in a `UInt64` bit stream for n ≤ 6 | `G4/Grassmann/MV.lean:859-902` | This is the cheapest complement kernel (79 ns vs 27 µs for the boxed version, `G4/docs/PackedMVPerformance.md:226`). For Grassmann.jl `⋆` it needs a metric correction (§4.4). |
| S6 | Parity-packed rank/unrank arithmetic (`mask>>>1`, with the low bit rebuilt from popcount parity) | `G4/Grassmann/MV.lean:145-248` | This is a clean trick, but it only fits **mask order**. Use it only for an internal mask-order layout. Grassmann.jl's `Spinor`/`AntiSpinor` order differs for n ≥ 4 (§3.3). |
| S7 | Contraction sign conventions that match Grassmann.jl | `G4/Grassmann/Products.lean:95-107`, commits `79902b3` and `3d8fd9a` | These were found empirically against Julia, and my probes confirm them (§A). |
| S8 | The versioned, caller-owned C ABI pattern: init sequence, per-thread attach, copy-in/copy-out `FloatArray`, Init-only kernel module, symbol audit, ownership stress | `G4/include/grassmann/cabi.h`, `G4/c/grassmann_cabi.c`, `G4/Grassmann/CABI.lean`, `G4/scripts/cabi_smoke.sh`, `G4/c/cabi_smoke.c` | This pattern works (13–19 ns per boundary crossing). The main lesson is that the exported module must import only `Init`, as explained in §8.7. |
| S9 | Julia-oracle harness ideas: spawn Julia with `env -i`, retry once on the precompile race, use JSON on stdout, and keep exact example evaluators for `S"∞+++"` and `S"∞∅+++"` | `G4/Grassmann/JuliaOracle.lean:81-129`; `G4/oracle/grassmann_oracle.jl` | Keep these ideas, but redesign the harness as batch golden generation (§9). |
| S10 | Visual-comparison pipeline: Lean SVG → PNG via `rsvg-convert` → ImageMagick RMSE against `paper/img/*.png`, gated on stddev and RMSE, plus numeric "witness" samples | `G4/scripts/compare_julia_examples.sh`; `G4/docs/JuliaExamplesVisualComparison.md` | Directly reusable for LeanPlot co-development. The reference PNGs already exist locally in `paper/img/` and `~/chakravala/Grassmann.jl/paper/img/`, so the curl download is unnecessary. |
| S11 | A generated-C structural guard: build the `+Mod:c` facet with the Lake cache disabled, then assert on the function bodies (one `lean_mk_empty_float_array`, direct `lean_float_array_get/push`, a tail `goto`, and no closures or boxing) | `G4/scripts/packed_linear_codegen_guard.sh` (677 lines of awk) | Keep the idea, but rewrite it as a small Lean or Python checker. Allocation-freedom is invisible to timing, and the guard catches regressions that benchmarks miss. |
| S12 | The exclusivity debug helpers | `G4/Grassmann/Linearity.lean` | These are useful while tuning in-place `FloatArray` code. |

**Discard everything else** as code. That includes the dense `Multivector`
(closure storage), `MultivectorS`/`TruncatedMV`/`NativeMV`/`EvenMV`/`Spinor`
(redundant representations), `GAlgebra` (a monolithic typeclass), the DSL
(keyword-token pitfalls), `SignatureGen`, the SciLean/LeviCivita/Unreal/Metal
physics experiments, the theorem files (false Float statements with `sorry`),
and `Proof.lean` (data axioms).

---

## 1. Purpose and scope of the old port

`G4/CLAUDE.md:1-12` and the root `README.md:1-20` describe the old port as "a
Lean 4 implementation of Clifford/Grassmann algebras". It had these parts:

* A proof-oriented dense `Multivector sig F`.
* A Float hot-path `MV sig p` with parity-packed `FloatArray` storage.
* Sparse, truncated, native-vector, and "even" alternatives.
* PGA3/CGA3 helpers.
* A versioned C ABI for PGA3.
* A Julia oracle.
* Extensive benchmark and codegen guards.
* Application experiments: curve shortening, physics, Metal, Unreal,
  SciLean AD, LeviCivita, and optimizers.

Toolchain: Lean `v4.27.0-rc1`, with mathlib pinned at `32d24245…`
(`lakefile.toml:13-16`, `lean-toolchain`).

The *Linear* issue trail is ALOK-749 and ALOK-762…770 (`ralph/PRD.md`,
`ralph/progress.txt`). Late work (Jun–Jul 2026) was spent almost entirely on
micro-optimizing packed `MV` unary and linear kernels and the PGA3 ABI.

It **never ported** the following:

* DirectSum/Leibniz/AbstractTensors as packages.
* Grassmann.jl's `Chain{V,G}`, `Single`, `Submanifold`, `Spinor`, `AntiSpinor`,
  or `Couple` type algebra with its dispatch.
* The conformal `∞`/`∅` basis semantics.
* Diagonal-form metrics in products.
* Grassmann.jl display.
* Grassmann.jl's `exp`/`log` algorithms.
* Anything else from Reed's ecosystem, such as Cartan, Adapode, or
  MeshTopology.

---

## 2. Inventory with verdicts

Legend:

* **S**: salvage the algorithm or code as a reference to re-derive (never copy
  verbatim, because conventions differ).
* **I**: salvage the idea only.
* **D**: discard.

LOC figures come from `wc -l`.

### 2.1 "Supported runtime" (`import Grassmann`, `G4/Grassmann.lean:12-28`, about 5.9k LOC and 627 declarations)

| File | LOC | Content | Verdict |
|---|---|---|---|
| `G4/Grassmann/BitMask.lean` | 219 | Recursive `popcount` on `Nat` (:32-34), `binomsum`, a **colex** `combinations` (:121-129; see pitfall P7), `lowerbits`/`expandbits` (:177-207) | **I** (use `lowerbits`/`expandbits` as a Leibniz reference). **D** for code: the popcount is slow and the ordering is wrong. |
| `G4/Grassmann/Manifold.lean` | 541 | `Signature n := {metric degenerate : BitVec n}` (:39-44); `cl`, `clr` (:63-75); `R1..R4`, `STA=cl 1 3`, `CGA3=cl 4 1`, `PGA3=clr 3 0 1` (:118-137); a bogus `Manifold` instance that always reports Euclidean (:152-154); `DiagonalForm` holding `Fin n → Float` (:179-181); direct sum, dual, set ops; `SubManifold` | **D**. The new DirectSum port supersedes it. Keep one lesson: store bitmasks, not `Fin n → R` functions. |
| `G4/Grassmann/Blade.lean` | 184 | `Blade sig := {bits : BitVec n}`, `Single sig F := {coeff, blade}` | **D** |
| `G4/Grassmann/Parity.lean` | 255 | `countTranspositions` (O(n) loop on `Nat`, :80-92), `parityJoin`, `geometricSign` (:132-135), `SignTable` as `Array Int8` of size 4ⁿ (:149-174), involution signs, complement signs (:219-226) | **S** for the algorithms (§4.2); the implementation is slow. |
| `G4/Grassmann/Products.lean` | 441 | Blade products; **contraction signs matching Julia** (:95-107); regressive blade sign fix (:167-185); a bug where `geometricProductSingles` returns a nonzero value for degenerate products (:191-197) | **S** for the contraction signs; **D** for the rest. |
| `G4/Grassmann/SimplexChain.lean` | ~200 | Documentation of Julia types (outdated names such as `Simplex`) | **D** |
| `G4/Grassmann/GATypeclass.lean` | 185 | Monolithic `GAlgebra sig M F` class with 17 fields | **D**. Use per-operator heterogeneous classes instead (§8.6). |
| `G4/Grassmann/Notation.lean` | 111 | Per-representation suffixed operators `⋀ᵇ ⊛ᵇ ⌋ᵇ ⌊ᵇ ⋁ᵇ` | **D** (pitfall P14) |
| `G4/Grassmann/DataArray.lean` | 137 | `abbrev DataArray := FloatArray` plus helpers; replaced an earlier SciLean `DataArray` (`ralph/progress.txt:31-33`) | **I**: use `FloatArray` directly. |
| `G4/Grassmann/NativeVector.lean` | 958 | `NativeMV sig := {coeffs : Vector Float (2^n)}` with mask order and many simple `coeff_*` lemmas (:325-660) | **I**. It shows that `Vector Float (2^n)` is both provable and computable, but boxed Floats make it slow. |
| `G4/Grassmann/MV.lean` | 1410 | The packed runtime (details in §3.3 and §4) | **S** for the algorithms listed; **D** for the type design. |
| `G4/Grassmann/SignTablesCore.lean` | 48 | Cached tables for R2/R3/R4/STA/PGA3/CGA3. `cachedSignTable` compares `sig == R3` **at runtime on every product** (:36-46). | **D** |
| `G4/Grassmann/EvenKernelTables.lean` | 374 | Even×even sign and index tables (`Array Int8`, `Array Nat`) | **D**. Codegen replaces them. |
| `G4/Grassmann/PGA3Kernel.lean` | 477 | Init-only straight-line PGA3 kernels shared with the C ABI | **S** (S1, S2, S3) |
| `G4/Grassmann/PGA3Packed.lean` | 124 | Typed wrappers over PGA3Kernel | **D** |

### 2.2 Reference and extended layer (`import Grassmann.Reference`, `G4/Grassmann/Reference.lean`)

| File | LOC | Verdict and reason |
|---|---|---|
| `Multivector.lean` | 1118 | **D**. Coefficients are stored as `Fin (2^n) → F` (:36-38), so each op wraps a precomputed `Array` in a closure (:252-272). It measured 400 µs per PGA3 point transform (`G4/docs/PackedMVPerformance.md:163-165`, `ralph/progress.txt:137`). |
| `SparseMultivector.lean` | 428 | **D**. It stores `Std.TreeMap Nat F`, and the claim that "Grassmann.jl tiers N≤8 dense / N>8 sparse" is folklore. Take the real limits from DirectSum instead. |
| `TruncatedMV.lean` | 427 | **D**. It is not a Grassmann.jl concept. |
| `MultivectorArray.lean`, `Storage.lean`, `StorageCompare.lean`, `Repr.lean`, `ReprTheorems.lean` | ~900 | **D** |
| `PrettyPrint.lean` | 202 | **D**. It uses the `e₁₂` style, which differs from Julia (§5). |
| `Versor.lean`, `Spinor.lean` | 678 | **I**. Keep only the `versorInv?` precondition idea: the reverse-based inverse is valid only if `m·m†` is exactly scalar (`VersorInverseTests.lean`). |
| `RotorExp.lean` | 358 | **D**. It hand-rolls scalar Taylor series for sin/cos/exp and had indexing bugs (commit `14770a0`). Port Grassmann.jl's `exp` instead. |
| `PGA.lean`, `PGATransforms.lean` | 153 | **D** |
| `CGA.lean`, `CGAGen.lean` | 931 | **I**. Keep the `e∞ = e₊+e₋`, `e₀ = (e₋−e₊)/2` identities and the origin-weight normalization fix (`776d584`). |
| `LinearAlgebra.lean`, `Calculus.lean`, `SpecialFunctions.lean` | ~1050 | **D**. These are finite-difference "calculus" and are unrelated to Grassmann.jl's `∇`/`∂`/`d`/`δ`. |
| `VectorUtils.lean`, `R3Utils.lean` | 500 | **D** |
| `Visualization.lean`, `GenVectorField.lean` | 377 | **I**. It shows SVG emission for the plane-* stream fields, but the fields were hand-written (§6.3). |
| `SignTables.lean`, `GradeSet.lean`, `BladeIndex.lean`, `StaticOpt.lean` | ~1640 | **I** for `GradeSet` as a type-level grade-set bitmask with product grade-set rules (`GradeSet.lean:81-120`), which maps onto Julia's `Chain{G}`/`Spinor`/`AntiSpinor`/`Multivector` kinds. **D** for the rest. |
| `GANotation.lean`, `DSL.lean`, `DSL/Context.lean`, `DSL/Subscript.lean`, `DSLDemo.lean`, `DSLTests.lean` | ~1330 | **I** for "`Cl(p,q,r) { … }` binds `e₁…e₁₂₃` via `let`" (`DSL/Context.lean:54-80`), as the analogue of `@basis`. **D** for the syntax (pitfalls P12 and P13). |
| `CoeffOps.lean` | 26 | **I**. Keep the lawless ops bundle (`Zero One OfNat 2 Add Sub Neg Mul`, :17-25). Float must never get `Ring` laws. |
| `SignatureGen.lean` | 195 | **D** |

### 2.3 Tests, oracle, benchmarks

| File | LOC | Verdict |
|---|---|---|
| `G4/oracle/grassmann_oracle.jl` | 920 | **S** for the Julia-side constructions in §9. Redesign the protocol. |
| `G4/Grassmann/JuliaOracle.lean` | 1207 | **I**. Keep the process-spawn recipe (:81-129). The protocol (one process per check) is too slow. |
| `G4/Grassmann/OracleTests.lean`, `Tests.lean`, `StressTests.lean` | ~1340 | **I** for the anchor values. |
| `G4/Grassmann/PropertyTests.lean` + `RunPropertyTests.lean` | 4760 + 89 | **I**. Keep differential testing across representations and focused CLI modes. The generators are weak: `genFloat` maps a Nat to Float in [-scale, scale] with low entropy (:36-44). |
| `G4/Grassmann/AnchorTheorems.lean` | 1170 | **I**. Exact-`Rat` anchor theorems proved by `native_decide` (:255-310) are a good pattern. Discard the Float statements marked `sorry` (:22-40). |
| `G4/Grassmann/Theorems.lean` | 720 | **D**. It states ring laws over `[Ring F]` with `sorry` (:194-259) and imports `Proof`. |
| `G4/Grassmann/MV*Tests.lean`, `G4/*Tests.lean` | ~1600 | **I** for `#guard`-based compile-time regression checks (for example `MVHodgeTests.lean:38-63`). |
| `G4/RunPackedMVBench.lean`, `G4/Grassmann/Bench.lean` | 1373 + 481 | **I** for the salt-to-timestamp trick (`RunPackedMVBench.lean:210-220`). **D** for the harness, which has flaws (§8.3). |
| `G4/scripts/*.sh` | ~2400 | **I** (S10, S11, cabi_smoke) |

### 2.4 C ABI, GPU, and applications

| File | Verdict |
|---|---|
| `G4/include/grassmann/cabi.h`, `G4/c/grassmann_cabi.c`, `G4/c/cabi_smoke.c`, `G4/c/cabi_header_probe.cpp`, `G4/Grassmann/CABI.lean`, `G4/scripts/cabi_smoke.sh` | **S** (S8) |
| `G4/Grassmann/MetalCodegen.lean` (840) + `G4/*.metal`, `*.air`, `*.metallib`, `*.swift`, `run_physics.sh` | **I** for "emit backend source from Lean-computed tables". **D** for the code: it emits *table-driven* loops over `signs[i][j]` (:82-114), not straight-line code, and binary build outputs are committed. |
| `G4/Grassmann/UnrealFFI.lean`, `UnrealAssets.lean`, `GrassmannPGA*.h` | **D**. Per `ralph/progress.txt:14-17`, the FFI used simplified formulas and the header declared unimplemented functions. |
| `G4/Grassmann/Physics.lean`, `GPUPhysicsPipeline.lean`, `MultivectorGPU.lean`, `Constraints.lean`, `CollisionLC.lean`, `LCBridge.lean`, `SciLeanAD*.lean`, `CowboyHatOpt.lean`, `HatOptimizer.lean`, `CurveShortening*.lean`, `Demo10D.lean`, `Test11D*.lean`, `CoffeeshopExamples.lean`, `LeanPlotDemo.lean`, `Couple.lean`, `ChainBundle.lean` | **D**. These are experiments and depend on path deps (SciLean, LeviCivita, LeanPlot) that are not part of the canonical build. |
| `G4/Manual/*`, `G4/verso-docs/` | **D**. They were never wired up. |

### 2.5 Repository-level state that matters for the cutover

* **Nested stale git repo.** `G4/.git` still exists and is stale. `ralph/PRD.md:9-11` says: "the nested `Grassmann4/.git` metadata is stale and must not be used for commits". Delete it.
* **Broken submodules.** `deps/AbstractTensors.jl`, `deps/DirectSum.jl`, and `deps/Leibniz.jl` are gitlinks (mode `160000`) with **no `.gitmodules`**. Remove them. The sources live under `~/chakravala/*.jl`.
* **Upstream Julia fork contents.** The root still holds the upstream Grassmann.jl package: `src/*.jl`, `test/`, `docs/`, `ext/`, `paper/`, and `Project.toml`/`Manifest.toml`. That `Project.toml` pulls dev deps (Cthulhu, JET, Revise, Pluto, IJulia, PackageCompiler, …). Those dev deps caused the "first-run precompile" failures in the old oracle (`JuliaOracle.lean:119-129`). Never point the oracle at the repo root project. Use the dedicated `scratchpad/juliaenv` or a new `oracle/Project.toml`.
* **Two lakefiles.** `lakefile.toml` (canonical, mathlib) and `G4/lakefile.toml` (SciLean/LeviCivita path deps, `release = true`) contradicted each other for months. Keep one.
* **Committed build outputs.** `mandelbrot_ga.png` (1.4 MB, twice), `*.metallib`, `*.air`, SVGs, and HTML dashboards are committed. Keep generated artifacts out of git.

---

## 3. Data representations used by the old port

### 3.1 `Signature n` (`G4/Grassmann/Manifold.lean:39-44`)

```lean
structure Signature (n : ℕ) where
  metric : BitVec n          -- bit i ⇒ e_i² = −1
  degenerate : BitVec n := 0 -- bit i ⇒ e_i² = 0 (overrides metric)
```

`Signature n` is used as a *value index* in `MV (sig : Signature n) (p : Parity)`.
Because it is data and not a type, **every kernel receives `sig` at runtime**,
and Lean never monomorphizes on it (§8.4).

Mistakes and divergences:

* **Null and infinity placement.** Julia puts `∞`/`∅` **first**, while the old
  port put `e₊`/`e₋` last. Old `CGA3 = cl 4 1` has e₄ = e₊ and e₅ = e₋
  (`Manifold.lean:133`, `:257-261`), and old `PGA3 = clr 3 0 1` has the null
  vector **last** (`:137`). The old oracle matched this with `S"++++-"` and
  `D"1,1,1,0"` (`oracle/grassmann_oracle.jl:19-28`). Grassmann.jl's native
  conformal model is `S"∞∅+++"`, with v∞ and v∅ as the **first two** basis
  vectors and special product rules (v∞² = v∅² = 0, v∞·v∅ = −1; see §A.6). The
  projective examples use `S"∞+++"`, with v∞ first and v∞² = +1. The old port
  never modeled the `∞`/`∅` flags and instead hand-translated every example
  (`JuliaExamples.lean:52-58`, `:120-130`).
* **STA ordering.** `STA = cl 1 3` means (+,−,−,−), which matches Julia
  `S"+---"`.
* **`numPositive`** (`:78-79`) computes `n − grade metric − grade degenerate`.
  That is wrong when a bit is set in both masks.
* **The `Manifold` instance** (`:152-154`) always reports a Euclidean
  `basisSign`. That is a latent bug.
* **`DiagonalForm n`** stores `Fin n → Float` (a closure) and was never used in
  products.
* **Julia pitfall, verified.** `S"0+++"` and `S"+++0"` do **not** create a
  degenerate basis. Both parse as `⟨++++⟩` (probe3). A degenerate metric needs
  `D"1,1,1,0"`. Also, `S"∅+++"` alone makes v∅² = **−1** (probe4).

### 3.2 `Blade sig` and `Single sig F` (`G4/Grassmann/Blade.lean:31-99`)

`Blade` is `{bits : BitVec n}` and `Single` is `{coeff : F, blade : Blade sig}`.
Neither encodes the grade in the type. That differs from Julia's
`Submanifold{V,G,B}` and `Single{V,G,B,T}`, where the grade and the blade bits
are type parameters.

### 3.3 `MV sig p`, the packed runtime (`G4/Grassmann/MV.lean:27-93`)

```lean
inductive Parity | even | odd | full          -- MV.lean:27-31
def Parity.mul : even*even=even, odd*odd=even, even*odd=odd, odd*even=odd, _=full   -- :37-42
def storageSize n p := match p with | .even|.odd => 2^(n-1) | .full => 2^n            -- :74-77
structure MV {n} (sig : Signature n) (p : Parity) where private mk :: coeffs : FloatArray  -- :90-92
```

Invariant: `coeffs.size = storageSize n p`. The raw constructor is private. The
checked importer is `ofDataArray?` (:264-268), and the proof-carrying one is
`ofDataArray` (:277-279).

**Index ordering.** Storage is **binary mask order**:

* Full storage has index = mask.
* Even and odd storage have packed rank = `mask >>> 1`, with the discarded low
  bit rebuilt from popcount parity (§4.1).

Packed order is therefore "ascending masks of the right parity". That order is
**not** Grassmann.jl's order. Julia uses grade-major, lexicographic-within-grade
ordering (`indexbasis`), and so do `Multivector`, `Spinor`, and `AntiSpinor`
values. The table below was generated by probe7 from `Grassmann.indexbasis`:

| n | layout | Grassmann.jl order (masks) | old MV order (masks) |
|---|---|---|---|
| 3 | full | `[0,1,2,4,3,5,6,7]` | `[0,1,2,3,4,5,6,7]` (**differs**) |
| 3 | even | `[0,3,5,6]` | `[0,3,5,6]` (same) |
| 3 | odd | `[1,2,4,7]` | `[1,2,4,7]` (same) |
| 4 | full | `[0,1,2,4,8,3,5,9,6,10,12,7,11,13,14,15]` | `0..15` |
| 4 | even | `[0,3,5,9,6,10,12,15]` | `[0,3,5,6,9,10,12,15]` (**differs**) |
| 4 | odd | `[1,2,4,8,7,11,13,14]` | `[1,2,4,7,8,11,13,14]` (**differs**) |
| 5 | even | `[0,3,5,9,17,6,10,18,12,20,24,15,23,27,29,30]` | `[0,3,5,6,9,10,12,15,17,18,20,23,24,27,29,30]` |
| 5 | odd | `[1,2,4,8,16,7,11,19,13,21,25,14,22,26,28,31]` | `[1,2,4,7,8,11,13,14,16,19,21,22,25,26,28,31]` |

Consequences:

* **The oracle needed hand-written permutations.** For example, it swaps the two
  middle PGA3 motor channels with `vals[[1,2,3,5,4,6,7,8]]`
  (`oracle/grassmann_oracle.jl:530-545`).
* **Two point conventions coexisted in one oracle file.** The "semantic" point
  is `e123 + x e423 + y e431 + z e412` → `[w, z, −y, x]` (:460-477). The "raw
  packed" point is `(w, z, y, x)` (:547-568).
* **The C ABI froze mask order as public API**
  (`G4/include/grassmann/cabi.h:42-98`).

> Recommendation: the new port's *storage order* should be Grassmann.jl's
> `indexbasis` order. Then `value(x)` round-trips 1:1 with the oracle and with
> display. For generic runtime kernels, precompute per-`n` tables
> `bladeAt : Array UInt64` and `indexOf` (Leibniz's `indexbasis` and
> `bladeindex` caches). Code-generated fixed-algebra kernels make the order free.

**The dimension-0 quirk.** Because Nat subtraction truncates,
`storageSize 0 .odd = 2^(0-1) = 2^0 = 1`. So a `.odd` MV in dimension 0 has a
"hidden compatibility slot" that needs special cases throughout (:147-160,
:309-313, :348-349, :396-398). Define the sizes explicitly instead: even `1`,
odd `0` at n=0.

**Where `p` lives.** `p : Parity` is a runtime value (a small enum, unboxed as
`uint8`), so `match p` inside kernels costs a byte compare unless the kernel is
inlined at a literal. The result type `MV sig (p1 * p2)` is computed by `rfl`
reduction. This part of the design **worked well**: it was type-safe and cost
almost nothing at runtime.

### 3.4 Dense `Multivector sig F` (`G4/Grassmann/Multivector.lean:36-38`)

`coeffs : Fin (2^n) → F`. Each product computes an `Array` eagerly and then
wraps it as `⟨fun k => resultArray.getD k.val 0⟩` (:252-272), so every
coefficient read is an indirect closure call with a boxed `F`. It is correct but
slow: 38 µs for an R3 rotor composition and 412 µs for a PGA3 point transform
(`README.md:213-219`). Its `hodgeDual` (:408-419) is signature-independent (§A.3).

### 3.5 Other stores

* `SparseMultivector.lean`: `Std.TreeMap Nat F`.
* `TruncatedMV.lean`: a TreeMap per grade.
* `NativeVector.lean`: `Vector Float (2^n)`.
* `EvenMV.lean`: deprecated.
* `SignatureGen.lean`: `Std.TreeMap Nat F` over `SignatureG`.

Maintaining six representations with pairwise conversions and suffixed
notations consumed a large share of the effort (`PropertyTests.lean` is 4760
lines) for little value.

### 3.6 Sign tables (`G4/Grassmann/Parity.lean:149-174`)

The sign table is an `Array Int8` of size `4^n` (boxed scalars, no heap
allocation), indexed as `signs[i*2^n + j]` with mask indices. It is built once
per standard signature (`SignTablesCore.lean:15-30`). The even×even variant
adds an `Array Nat` of output indices (`EvenKernelTables.lean`).

---

## 4. Algorithms worth salvaging, in exact form

### 4.1 Parity-packed rank and unrank (mask order only; `MV.lean:145-248`)

This holds for n ≥ 1. Each adjacent mask pair `(2r, 2r+1)` contains exactly one
even-popcount mask and one odd-popcount mask. Therefore:

```
packIdx(p ∈ {even,odd}, mask) = mask >>> 1
unpackIdx(p, r) = 2r + lowbit,   lowbit = popcount(r) mod 2        (p = even)
                                 lowbit = 1 − (popcount(r) mod 2)  (p = odd)
parity widening: packed r ↦ writes (value,0) or (0,value) at full slots 2r, 2r+1 depending on lowbit
grade of packed slot r = popcount(r) + lowbit
```

A perf lesson came from this code. Writing `(r <<< 1) ||| low` on `Nat` was a
**boxed-Nat shift/OR hotspot** (1.27 µs). Rewriting it as `r + r + low` brought
it to 164 ns (`G4/docs/PackedMVPerformance.md:249-254`). The deeper fix is to
use `UInt64`/`USize` for masks.

### 4.2 Blade product signs (`Parity.lean:80-135`)

```
geometricSign(a, b):                       -- a, b blade masks
  if (a & b & degenerateMask) ≠ 0: return 0
  swaps = #{(i ∈ a, j ∈ b) : j < i}          -- Koszul reordering count
  neg   = popcount(a & b & negMetricMask)     -- shared basis vectors squaring to −1
  return (−1)^(swaps + neg)
result blade = a XOR b
wedgeSign(a,b) = 0 if a&b ≠ 0 else (−1)^swaps ; result a|b
```

The old code computes `swaps` in an O(n) Nat loop (:80-92). Use the O(1)-ish
form with hardware or SWAR popcount on `UInt64` instead:

```
swaps(a,b) = Σ_{j ∈ b} popcount(a >> (j+1))
  -- equivalently: t = a >> 1; s = 0; while t ≠ 0: s += popcount(t & b); t >>= 1
```

This sign rule is correct only for **diagonal ±1/0 metrics**. Grassmann.jl
additionally supports `DiagonalForm` (arbitrary diagonal values, which multiply
the coefficient) and the conformal `∞`/`∅` null basis. Neither is handled here.

### 4.3 Contraction signs that match Grassmann.jl (`Products.lean:95-107`; verified in §A.1)

In Grassmann.jl (AbstractTensors `src/AbstractTensors.jl:259-265`):

* `a < b` is `a ⨼ b`, which is `contraction(b, a)`.
* `a > b` is `a ⨽ b`, which is `a ⋅ b`, which is `a | b`, which is
  `contraction(a, b)`.

The old port matched Julia on basis blades with these rules:

```
left  a⌋b  (Julia a < b):   requires a ⊆ b and |a| ≤ |b|;  sign = rev(|a|) · geomSign(a, b);  blade = a XOR b
right a⌊b  (Julia a > b, a ⋅ b): requires b ⊆ a and |b| ≤ |a|; sign = rev(|b|) · geomSign(b, a); blade = a XOR b
rev(k) = (−1)^(k(k−1)/2)
```

These are the *reversed-left* conventions, not Dorst's. In R3 Julia gives
`v12 > v1 = +v₂`, while Dorst's right contraction gives e12⌊e1 = −e2.
Degenerate shared vectors give 0 through `geomSign`.

### 4.4 Complements and Hodge

The old kernel computes a **metric-free right complement**: for input blade `c`,
the result is `s(c)·blade(~c)`, where `c ∧ ~c = s(c)·I`, so
`s(c) = (−1)^{swaps(c, ~c)}`. For n ≤ 6 it packs the sign of output slot `o`
(which reads input `~o`) as bit `o` of a `UInt64` (`MV.lean:859-867`):

```
n: 0 → 0x0, 1 → 0x0, 2 → 0x2, 3 → 0x24, 4 → 0x24b2, 5 → 0x24b24d24, 6 → 0x24b24d24b2db24b2
```

Julia's formula (Leibniz `src/generic.jl:202-205`) is:

```
parityright(V,B,G,N) = isodd(B + (G+1)G/2)   -- B = Σ of 1-based indices of the blade, G = grade
parityrighthodge(V,B,G,N) = isodd(V) ⊻ parityright(...)  -- V = # negative-metric vectors in blade
parityleft = (isodd(G) && iseven(N)) ⊻ parityright
```

* Grassmann.jl `!x` (`complementright`) is metric-free, so it equals the old
  kernel.
* Grassmann.jl `⋆x` (`complementrighthodge`) additionally flips the sign when
  the blade contains an odd number of negative-metric vectors. For a
  **degenerate** basis vector in the blade it gives **coefficient 0**, not a
  sign. For example, `⋆e4 = 0v₁₂₃` in `D"1,1,1,0"`, while `!e4 = −v₁₂₃`
  (probe3).
* The old docs call the kernel a "left complement" (`README.md:64-69`,
  `PackedMVPerformance.md:70-76`). That name is **wrong**. The kernel is the
  right complement: in R4 it maps `e4 → −e123`, as `!`/`⋆` do, whereas
  Grassmann.jl `complementleft(v4) = +v₁₂₃`.

### 4.5 Output-stationary exterior product (`MV.lean:477-560`)

```
for each output mask o (ascending in the output layout):
  acc = 0
  l = o
  loop:                       -- visits every submask l of o exactly once, descending
    r = o XOR l
    if l in layout(a) and r in layout(b): acc += (−1)^swaps(l,r) · a[l] · b[r]
    if l == 0: break
    l = (l − 1) & o
  out.push(acc)
```

The cost is Σ_o 2^{|o|} = 3ⁿ products instead of 4ⁿ. It is metric-independent,
so it needs no sign table, and it produces the output in one pass with pushes
only.

### 4.6 Straight-line kernels (salvage the *shape*, generate the code)

* **R3 even×even** (the quaternion product) in mask order `[1, e12, e13, e23]`,
  from `MV.lean:700-718`. For n=3 the even mask order equals Julia's
  `Spinor{ℝ3}` order:

  ```
  c0 = a0b0 − a1b1 − a2b2 − a3b3
  c1 = a0b1 + a1b0 − a2b3 + a3b2
  c2 = a0b2 + a1b3 + a2b0 − a3b1
  c3 = a0b3 − a1b2 + a2b1 + a3b0
  ```

* **PGA3 motor×motor** (a dual quaternion) `motorMul` (`PGA3Kernel.lean:104-141`).
* **PGA3 even×odd** `evenOddMul` (:254-290) and **odd×even** `oddEvenMul`
  (:300-336).
* **The fused sandwich** `motorSandwichOdd` (:346-404). It computes
  `t = M·x` in 8 locals, sets `r = rev(M)` inline (signs `+,−,−,−,−,−,−,+`),
  computes `c = t·r`, and makes **one** allocation. It is exhaustively checked
  against the composed kernels over every basis pair
  (`ralph/progress.txt:109-112`).

These were **hand-written**, and the old codegen only emitted table loops. The
new port should write a metaprogram that expands a product into straight-line
`let`s, dropping terms that are zero at compile time from the sign table and
from grade or parity sparsity. Run it for each registered algebra and
input-kind pair, and emit Lean `def`s. The same metaprogram can emit C (for the
ABI or `@[extern]`) and Metal.

### 4.7 PGA3 motor → affine 3×4 (the batch transform, `PGA3Kernel.lean:437-476`)

In old mask order, with null vector e4 last and the old point convention:

```
q = m0²+m1²+m2²+m3²; invQ = 1/q
xx=(m0²−m1²−m2²+m3²)/q  xy=−2(m0m1−m2m3)/q  xz= 2(m0m2+m1m3)/q  xt=−2(m0m4+m1m5+m2m6+m3m7)/q
yx= 2(m0m1+m2m3)/q      yy=(m0²−m1²+m2²−m3²)/q  yz=−2(m0m3−m1m2)/q  yt= 2(m0m5−m1m4−m2m7+m3m6)/q
zx=−2(m0m2−m1m3)/q      zy= 2(m0m3+m1m2)/q      zz=(m0²+m1²−m2²−m3²)/q  zt=−2(m0m6+m1m7−m2m4−m3m5)/q
(x',y',z') = rows · (x,y,z,1);   q == 0 ⇒ all outputs 0
```

Re-derive these in the new basis. Do not copy them: the channel signs depend on
the old `(w, z, y, x)` point convention.

### 4.8 Rigid-motor checks (`PGA3Kernel.lean:156-244`, `c/grassmann_cabi.c`)

```
normSq(M) = a0²+a1²+a2²+a3²                     (quaternion part)
study(M)  = a0a7 − a1a6 + a2a5 − a3a4           (M·rev(M) = normSq + 2·study·e0123)
valid(M,tol) = size=8 ∧ all finite ∧ tol finite ≥ 0 ∧ normSq finite ∧ 1/normSq finite
               ∧ normSq > tol ∧ |2·study| ≤ tol·normSq
normalize(M) = M · (1/√normSq)        ; inverse(M) = rev(M) · (1/normSq)
```

The ABI tolerance is `1e-12` (`cabi.h:40`). Oracle comparisons of these passed
27/27 (`ralph/progress.txt:130`).

### 4.9 The allocation-tight `FloatArray` loop idiom (`MV.lean:911-965`, `1003-1033`)

```lean
private def addAux (a b : @& FloatArray) (i : Nat) : Nat → FloatArray → FloatArray
  | 0, out => out
  | k+1, out => addAux a b (i+1) k (out.push (a.get! i + b.get! i))
def add (a b : @& MV sig p) : MV sig p :=
  let sz := storageSize n p; ⟨addAux a.coeffs b.coeffs 0 sz (FloatArray.emptyWithCapacity sz)⟩
```

The generated C showed:

* one `lean_mk_empty_float_array`;
* direct `lean_float_array_get` and `lean_float_array_push` calls;
* a `goto` tail loop;
* no RC traffic on the borrowed inputs.

The old port measured `Id.run do for … in [:n]` loops as creating closures and
per-iteration control objects (`MV.lean:938-941`) on v4.27. **Re-measure on
the new toolchain**, because the new code generator may have changed this.
Better still, use `uget`/`uset` with `USize` and in-bounds proofs to drop the
bounds checks in `get!`.

### 4.10 Conformal and projective example formulas (verified against Julia, §A.6)

* **`S"∞+++"`** (v∞² = +1, stereographic):
  `↑p = (2/(p²+1))·p + ((p²−1)/(p²+1))·v∞`. The Lean evaluator
  (`JuliaExamples.lean:73-83`) uses `↓ω = ω_vec / (1 − ω_∞)`; Julia prints
  `↑(v1) = 0.0v∞ + 1.0v₁ + 0.0v₂ + 0.0v₃`.
* **`S"∞∅+++"`**: v∞² = v∅² = 0 and `v∞*v∅ = −1 + v∞∅`. `↑p = p + (p²/2)v∞ + v∅`.
  Julia prints `↑(v1) = 0.5v∞ + 1.0v∅ + 1.0v₁ + …`.
* **Old CGA via e±**: `e∞ = e₊+e₋` and `e₀ = (e₋−e₊)/2`. Normalize by the
  origin weight `(coef_{e₋} − coef_{e₊})`, not by the e∞ coefficient (fix
  `776d584`, `CGA.lean`).

### 4.11 Versor inverse precondition (`VersorInverseTests.lean`)

`inv(m) = rev(m)/(m·rev(m))` is valid **only** if `m·rev(m)` is exactly scalar.
The counterexample is `(1+e1)(1+e1)† = 2 + 2e1`. Julia's `inv` handles this
generally, so port Julia's algorithm rather than the reverse shortcut.

---

## 5. Display: the old port versus Grassmann.jl

The old `PrettyPrint.lean:20-60` prints `e₁ - 2e₂` style with integer-looking
Floats rounded (`2` for `2.0`). It uses the `e` prefix, prints "scalar" for mask
0 in names, and sorts by grade and then by mask. **None of this matches Julia.**

These strings are verbatim Julia output (probes 1–5):

* `v₂` (a unit `Submanifold`)
* `1v₂₃` and `-1v₁₃` (a `Single` with coefficient ±1)
* `v` (the unit scalar blade)
* `𝟎` (`Zero`)
* `0v₁₂₃` (a zero `Single` in a degenerate hodge)
* `2.22045e-16v₁ - 1.0v₂ + 0.0v₃` (a `Chain`, which prints every slot including
  zeros)
* `1.0 + 2.0v₁ + 3.0v₂ + … + 16.0v₁₂₃₄` (a `Multivector`, printing all slots)
* `1.0 + 2.0v₁₂ + 3.0v₁₃ + 4.0v₁₄ + 5.0v₂₃ + 6.0v₂₄ + 7.0v₃₄ + 8.0v₁₂₃₄` (a
  `Spinor`)
* `1.0v₁ + 2.0v₂ + 3.0v₃ + 4.0v₄ + 5.0v₁₂₃ + 6.0v₁₂₄ + 7.0v₁₃₄ + 8.0v₂₃₄` (an
  `AntiSpinor`)
* `-1 + 1v∞∅ + 0v∞₁ + …` (a `Spinor` over `S"∞∅+++"` with Int coefficients,
  printing zeros)

Float formatting follows Julia's `show` shortest round-trip (`2.22045e-16` in
compact IO). The display spec should come from the Grassmann.jl-focused spec,
not from the old port.

---

## 6. Golden examples harvested

### 6.1 Anchors pinned by the old port that are CORRECT for Julia

These are exact, and they match Julia because they involve only Euclidean
metrics and the conventions of §4.3 and §4.4:

* R3 hodge (`AnchorTheorems.lean:262-310`): `⋆1 = e123`, `⋆e1 = e23`,
  `⋆e2 = −e13`, `⋆e3 = e12`, `⋆e123 = 1`, `⋆⋆e1 = e1`, `⋆⋆e12 = e12`. Julia
  agrees: `⋆v1 ⋆v2 ⋆v3 = 1v₂₃ -1v₁₃ 1v₁₂ ; ⋆v12 = 1v₃ ; ⋆1 = 1v₁₂₃ ; ⋆v123=1v`.
* Contractions (`JuliaOracle.lean` r10–r13): `e1⌋e12 = e2`,
  `e2⌋e12 = −e1`, `e1⌋e123 = e23`, `e12⌋e123 = e3`.
* PGA3 hodge anchors (`MVHodgeTests.lean:55-63`): `e4 ↦ −e123` and
  `e123 ↦ e4`. These are correct **for `!`**, but **wrong for Julia `⋆`**, which
  gives `0v₁₂₃` for `⋆e4`.
* Float non-associativity witness (`ralph/progress.txt:169-170`):
  `(1e20 + -1e20) + 3 = 3` while `1e20 + (-1e20 + 3) = 0`.

### 6.2 Fresh Julia goldens (probes run in `scratchpad/juliaenv`; copy verbatim)

```
R3 v12⋅v12 = v ; v12*v12 = -1v
R3 v1⋅v12 = 𝟎 ; v12⋅v1 = v₂
R3 v1<v12 = v₂ ; v12>v1 = v₂ ; v1>v12 = 𝟎
R3 v12<v123 = v₃ ; v123>v12 = v₃
R3 ⋆v1 ⋆v2 ⋆v3 = 1v₂₃ -1v₁₃ 1v₁₂ ; ⋆v12 = 1v₃ ; ⋆1 = 1v₁₂₃ ; ⋆v123=1v
R3 !v1 = 1v₂₃ complementleft(v1) = 1v₂₃
R3 v12 ∨ v23 = v₂ ; v1∨v23 = v
S-+++ ⋆v1 = -1v₂₃₄ ; !v1 = 1v₂₃₄ ; ⋆v2 = -1v₁₃₄ ; !v2 = -1v₁₃₄ ; ⋆v12 = -1v₃₄ ; !v12=1v₃₄
S-+++ v1*v1 = -1v ; v1⋅v1 = -1v v12⋅v12 = -1v v12*v12=1v
R4 ⋆v4 = -1v₁₂₃ ; ⋆v1 = 1v₂₃₄ ; ⋆⋆v1 = -1v₁ ; ⋆v12 = 1v₃₄ ; complementleft(v4) = 1v₁₂₃
R4 Multivector 1:16 = 1.0 + 2.0v₁ + 3.0v₂ + 4.0v₃ + 5.0v₄ + 6.0v₁₂ + 7.0v₁₃ + 8.0v₁₄ + 9.0v₂₃ + 10.0v₂₄ + 11.0v₃₄ + 12.0v₁₂₃ + 13.0v₁₂₄ + 14.0v₁₃₄ + 15.0v₂₃₄ + 16.0v₁₂₃₄
⟨1,1,1,0⟩: e4*e4 = 0v ; ⋆e4 = 0v₁₂₃ ; !e4 = -1v₁₂₃ ; ⋆(e1*e2*e3) = 1v₄ ; e1*e1=1v
⟨++++⟩ (from S"+++0" and S"0+++"): e4*e4 = 1v ; ⋆e4 = -1v₁₂₃ ...
R>>>v1 = 2.22045e-16v₁ - 1.0v₂ + 0.0v₃ ; R*v1*~R = 2.22045e-16v₁ - 1.0v₂ + 0.0v₃ + 0.0v₁₂₃   (R = exp(π/4*v12), R3)
2R >>> v1 = 8.88178e-16v₁ - 4.0v₂ + 0.0v₃
∅+++ : v∅*v∅ = -1v ; v1*v1 = 1v ; v∅*v1 = v∅₁
∞+++ : v∞*v∞ = 1v ; v1*v1 = 1v ; ↑(v1) = 0.0v∞ + 1.0v₁ + 0.0v₂ + 0.0v₃
∞∅+++ : v∞*v∞ = 𝟎 v∅*v∅=𝟎 v∞*v∅ = -1 + 1v∞∅ + 0v∞₁ + … ; v∅*v∞ = -1 - 1v∞∅ + … ; ↑(v1) = 0.5v∞ + 1.0v∅ + 1.0v₁ + 0.0v₂ + 0.0v₃
R4 v12 ∨ v134 = v₁ ; complementleft(!v12 ∧ !v134) = 1v₁ ; !( !v12 ∧ !v134) = -1v₁
R4 v123 ∨ v234 = v₂₃ ; v1234 ∨ v1 = v₁
R4 Spinor 1:8 = 1.0 + 2.0v₁₂ + 3.0v₁₃ + 4.0v₁₄ + 5.0v₂₃ + 6.0v₂₄ + 7.0v₃₄ + 8.0v₁₂₃₄
R4 AntiSpinor 1:8 = 1.0v₁ + 2.0v₂ + 3.0v₃ + 4.0v₄ + 5.0v₁₂₃ + 6.0v₁₂₄ + 7.0v₁₃₄ + 8.0v₂₃₄
R2 R = exp(π/4*v12) = 0.7071067811865476 + 0.7071067811865475v₁₂ ; v1 ⊘ R = 2.22045e-16v₁ + 1.0v₂ ; R >>> v1 = 2.22045e-16v₁ - 1.0v₂ ; v1 ⊘ (2R) = 8.88178e-16v₁ + 4.0v₂
inv(R)*v1*R = 2.22045e-16v₁ + 1.0v₂ ; ~R*v1*R = 2.22045e-16v₁ + 1.0v₂
helix S"∞∅+++" f(0.3) = 0.0 + 1.51762e-25v∞ + 1.41386v₁ - 0.0317322v₂ + 2.88496v₃ + 3.94358e-9v∞₁₂ + 4.33763e-11v∞₁₃ + 1.93267e-9v∞₂₃ - 1.11022e-16v₁₂₃
helix f(1.0) = 0.0 - 0.467085v₁ - 1.33485v₂ + 7.28319v₃ + 7.81343e-8v∞₁₂ + 1.43204e-8v∞₁₃ - 5.01091e-9v∞₂₃
torus S"∞+++" f(0.0) = 0.0v∞ + 1.0v₁ + 1.0v₂ + 1.0v₃ ; f(0.3) = 0.0v∞ + 1.04116v₁ - 0.0233676v₂ - 0.927916v₃
```

Takeaways:

* **`>>>` and `⊘`.** `R >>> x = R*x*~R` and `x ⊘ R = ~R*x*R`. Both use
  **reverse, not inverse**, so scaling R by 2 scales the result by 4. Both
  **project to the input's kind**, so no spurious `v₁₂₃` appears.
* **Julia's own `exp` of a non-simple bivector has error around 1e-8.** The
  helix residuals in the v∞₁₂ components show this. Golden tolerances for
  exp-based examples must be at least 1e-7. The helix matches the old closed
  form `(cos a + sin a, cos a − sin a, 1 + 2πt)` with `a = (6/7)πt`, which gives
  `(1.41386, −0.03173, 2.88496)` at t = 0.3.

### 6.3 The twelve documented plot examples (`docs/src/algebra.md:776-826`; reference PNGs in `paper/img/`)

| Name | Signature | Expression | Old Lean status |
|---|---|---|---|
| plane-1 | `basis"2"` | `streamplot(vectorfield(exp(π*v12/2)), -1.5..1.5, -1.5..1.5)` | hand-written field (approximate) |
| plane-2 | `basis"2"` | same with `exp((π/2)*v12/2)` | approximate |
| plane-3 | `basis"2"` | same with `exp((π/4)*v12/2)` | approximate |
| plane-4 | `basis"2"` | same with `v1*exp((π/4)*v12/2)` | approximate |
| plane-5 | `S"+-"` | same with `exp((π/8)*v12/2)` | approximate |
| plane-6 | `S"+-"` | same with `v1*exp((π/4)*v12/2)` | approximate |
| torus | `S"∞+++"` | `f(t)=↓(exp(π*t*((3/7)*v12+v∞3))>>>↑(v1+v2+v3)); lines(V(2,3,4).(points(f)))` | exact evaluator, oracle-checked |
| helix | `S"∞∅+++"` | same `f`; `lines(V(3,4,5).(points(f)))` | closed form, not Julia-checked |
| orb | `S"∞+++"` | `streamplot(vectorfield(exp((π/4)*(v12+v∞3)),V(2,3,4)),-1.5..1.5,-1.5..1.5,-1.5..1.5,gridsize=(10,10))` | approximate |
| wave | `S"∞+++"` | same, with an extra `V(1,2,3)` argument | approximate |
| orbit-2 | `S"∞+++"` | `f(t)=↓(exp(t*v∞*(sin(3t)*3v1+cos(2t)*7v2-sin(5t)*4v3)/2)>>>↑(v1+v2-v3))` | exact evaluator |
| orbit-4 | `S"∞+++"` | `f(t)=↓(exp(t*(v12+0.07v∞*(sin(3t)*3v1+cos(2t)*7v2-sin(5t)*4v3)/2))>>>↑(v1+v2-v3))` | 40-term Taylor |

Grassmann.jl definitions the new port must reproduce for these plots:

* `points(f, r=-2π:0.0001:2π) = vector.(f.(r))` (`~/chakravala/Grassmann.jl/src/Grassmann.jl:68`).
* `vectorfield = pointfield` (`:311`).
* `pointfield(t,V=Manifold(t),W=V) = p -> Point(V(vector(↓(↑((V∪Manifold(t))(Chain{W,1}(p.data))) ⊘ t))))`
  (`ext/GeometryBasicsExt.jl:30`). The field is therefore `↓(↑p ⊘ t)`, with
  `⊘` defined as `~t*x*t`. The old port's plane fields were hand-coded
  rotations and boosts, not derived from this definition, so re-derive them.
* `V(2,3,4)` selects basis indices 2..4 of the result.

The old oracle's sampling set for the exact curves was
`t ∈ [−2π, −π, −1, −0.5, 0, 0.5, 1, π, 2π]` (`JuliaExamplesVisualComparison.md:213-215`).
The old visual gates required a grayscale stddev ≥ 1200 and a normalized
RMSE ≤ 0.25. The observed RMSE ranged from 0.0926 to 0.1539
(`JuliaExamplesVisualComparison.md:154-169`).

---

## 7. Dependencies used by the old port (and lessons)

* **mathlib** (`lakefile.toml:13-16`). It was imported by core runtime files for
  trivial things, for example `BitMask.lean:19` imports
  `Mathlib.Data.Nat.Choose.Basic` just for `Nat.choose`. That made builds slow
  and blocked a small shared library, so the PGA3 kernel had to be isolated as
  Init-only (§8.7). There was also a comment that
  `Mathlib.Data.Fin.Basic` "causes runtime panic in v4.26.0-rc2"
  (`BitMask.lean:20`). **Lesson:** keep the runtime core free of mathlib, and
  put proofs needing mathlib in a separate library target.
* **Plausible** was used for property tests; its generators were weak.
* **SciLean, LeviCivita, and LeanPlot** were maintainer path dependencies,
  available only in the nested workspace (`G4/lakefile.toml:18-31`). LeanPlot
  was disabled "due to Verso dependency issues", so `CoffeeshopExamples` and
  `LeanPlotDemo` never built canonically (`ralph/progress.txt:65-69`). LeanPlot
  lives at `~/leanplot` on toolchain `v4.27.0-rc1`, with API calls `plotMany`,
  `scatterChart`, and `plot` (`G4/Grassmann/LeanPlotDemo.lean:47-76`). For
  co-development, depend on LeanPlot through a pinned git revision or a
  workspace member, never a path dependency in the canonical lakefile.
* **Julia-side symbols used by the old oracle**: `S"…"`, `D"…"`, `Λ(sig)`,
  `alg[i+1]` for basis access, `@basis`, `value`, `scalar`, `~`, `*`, `∧`, `<`,
  `>`, `⋅`, `>>>`, `exp`, `inv`, `↑`, `↓`, `⋆`, and the JSON package.

---

## 8. Porting notes: performance learnings, pitfalls, design recommendations

### 8.1 Measured numbers

All measurements were taken on an Apple Silicon Mac with release builds and
Lean `v4.27.0-rc1`.

| Operation | Old measurement | Source |
|---|---|---|
| R3 rotor compose (packed, straight-line quaternion) | 119–138 ns/iter, mostly harness overhead (§8.3) | `ralph/progress.txt:43,210,409,569-570` |
| R3 rotor compose (dense closure `Multivector`) | 37–38 µs | `README.md:213-219` |
| "R3 sandwich" packed | 97–107 ns. **Suspect**: the probe was likely dead-code eliminated (§8.3). | same |
| PGA3 motor×motor | 417–460 ns | `ralph/progress.txt:43,210,409,570` |
| PGA3 point transform, packed, before fusion | 4326.7 ns | `ralph/progress.txt:91,136` |
| PGA3 point transform, fused sandwich | 542.3 ns | `ralph/progress.txt:137` |
| PGA3 point transform, dense | 412–425 µs | same |
| PGA3 flat batch (Lean) | **10.53 ns/point** | `ralph/progress.txt:139` |
| C ABI boundary: construct and copy / packed in, extract, copy | 12.8–14.2 ns / 18.2–19.2 ns per call | `ralph/progress.txt:133-135,288,406,479,568` |
| C ABI batch of 4096 points vs repeated scalar calls | 31.4–32.5 µs vs 288–311 µs (about 9–10x) | `ralph/progress.txt:133-134,208,287,567,642` |
| CGA3 full add/neg/smul (32 coefficients), one-buffer version | 84–94 ns (vs about 300–340 ns boxed) | `G4/docs/PackedMVPerformance.md:185-190` |
| CGA3 full reverse/involute/conjugate | 327–396 ns (vs about 14.5 µs boxed) | `:203-213` |
| CGA3 Hodge with the UInt64 sign stream | 77–79 ns (vs 26.7–27.1 µs boxed) | `:226` |
| CGA3 grade and parity projection / widening | 149–333 ns / 158–164 ns | `:241-247` |
| CGA3 dense-closure ingress | 3.3–6.3 µs, dominated by the closure | `:264-266` |
| Full CGA3 multiply via a cached-table lookup | 4.18 µs → 3.05 µs after removing an index-array lookup | `ralph/progress.txt:370-373` |

**Interpretation.** Where it mattered, the fixed costs per call were allocation,
dispatch, and harness overhead of roughly 50–120 ns. Arithmetic was a few ns.
Hence:

1. A fused, straight-line kernel beats a generic loop by about 8x, and a batch
   beats per-element calls by about 50x.
2. The Lean-side unary loops at about 10 ns per coefficient (reverse at
   ~390 ns for 32 slots) are **slow**. Each iteration recomputes a
   popcount-based grade sign on `Nat`. A precomputed `UInt64` sign mask (as for
   Hodge) or codegen would bring them to about 1 ns per coefficient.

### 8.2 What was fast or slow in compiled Lean (v4.27; re-measure on v4.35)

* **Fast**:
  * `FloatArray` built with `emptyWithCapacity` and `push` in a unique,
    tail-recursive loop over `@&`-borrowed inputs, giving one allocation.
  * Straight-line `let` arithmetic on unboxed `Float` locals.
  * `UInt64` bit tricks, such as the Hodge sign stream.
  * Returning an input unchanged for identity operations (even involution:
    20 ns, which is essentially harness cost).
  * Small enum type indices (`Parity`).
* **Slow**:
  * **Boxed `Array Float`** plus `Array.range`/`map` followed by a copy into
    `FloatArray`: 3.5–350x slower (§8.1).
  * **Closure-typed storage** (`Fin (2^n) → F`), which costs about 1000x.
  * **`Nat` bit operations** (`<<<`, `|||`, `>>>`, `&&&`). These are
    arbitrary-precision calls, measured at 1.27 µs → 164 ns in one kernel, and
    the recursive `popcount` on `Nat` (`BitMask.lean:32-34`) adds to it.
  * `for` loops inside `Id.run do`, which lowered to closures and control
    objects in v4.27 (`MV.lean:938-941`).
  * **Typeclass dictionary dispatch in generic code**: the `MVMulKernel` path
    measured about +50% to +100% over direct dispatch, even with `@[inline]`,
    `@[always_inline]`, `@[specialize]`, `@[default_instance]`, and release
    builds (`G4/CLAUDE.md:22`, `:60-66`; `MV.lean:1217-1221`). The root cause
    is that `@[specialize]` only specializes **instance and function
    arguments** at concrete call sites. Generic code over `{sig : Signature n}`
    still passes the dictionary at runtime. Value parameters such as
    `n : Nat` and `sig : Signature n` are **never monomorphized**, so
    `storageSize n p = 2^(n-1)` is recomputed through `Nat.pow` at runtime in
    every kernel.
  * Runtime signature comparisons in the hot path, both
    `sig.metric.toNat == 0 && sig.degenerate.toNat == 8`
    (`MV.lean:798-818, 1302-1311`) and `sig == R3` (`SignTablesCore.lean:36-46`).
    They are cheap individually but prevent the kernel choice from happening at
    compile time.
* **Boxing at closure boundaries**: any `Nat → Float` or
  `Float → Float` closure call boxes the Float result, which is a heap
  allocation. That affects benchmark harnesses and any higher-order API such as
  a coefficient function.

### 8.3 Benchmark methodology pitfalls (fix these in the new harness)

1. **Dead-code-eliminated probe.** `Grassmann/Bench.lean:230,370` measures
   `MV.scalarPart (mvSandwich R v)` with `v : MV R3 .odd`. `scalarPart` on
   `.odd` returns the constant `0.0` (`MV.lean:357-360`). After inlining, the
   sandwich is dead pure code and probably eliminated. The "1100x sandwich
   speedup" in the README is therefore unreliable. **Probes must read computed
   data**, for example by summing several coefficients as `packedProbe` does in
   `RunPackedMVBench.lean:82-94`.
2. **`let _ := runN warmupIters f`** (`RunPackedMVBench.lean:211`) is a pure,
   unused `let`, so it is likely eliminated and the warmup never runs.
3. **The harness `runN (n) (f : Nat → Float)`** makes one closure call and
   **one Float box per iteration**. That puts a floor of roughly 20–50 ns under
   every number; for example, the 20 ns "even involution" is pure overhead.
   Instead:
   * benchmark `@[noinline]` kernels in explicit loops over input arrays inside
     `IO`;
   * write outputs to a `FloatArray` sink;
   * report ns per element with the empty-loop floor subtracted.
4. **The trick worth keeping**: `salt := Float.ofNat (start % 1024)` is added
   into the timed computation, so the pure work cannot be hoisted above the
   start timestamp (`RunPackedMVBench.lean:212-215`).
5. **Allocation-freedom needs a structural check, not timing (S11).** Lean's
   generated C names now carry the package prefix (`lp_Grassmann_…`), and
   private declarations get unstable ordinals, so match on suffixes
   (`packed_linear_codegen_guard.sh:117-120`).

### 8.4 Dependent-type lessons

* **What worked**: a small enum index for storage kind, with type-level result
  kinds (`MV sig p1 → MV sig p2 → MV sig (p1*p2)`) and proof-carrying buffer
  constructors (`ofDataArray` with `h : size = storageSize n p`). This costs
  zero or one byte at runtime. Generalize the enum to Grassmann.jl's kinds:
  `Chain G` (single grade), `Spinor` (even), `AntiSpinor` (odd), and
  `Multivector` (full), and possibly a `GradeSet` bitmask
  (`GradeSet.lean:81-120` has the product grade-set rules). Compute result
  kinds by `decide`/`rfl`-reducible functions.
* **What did not work**: using signature *values* as indices and hoping for
  specialization. Julia's speed comes from `@generated` functions specialized
  per `(V, G, B)` type parameter, plus compile-time caches in Leibniz and
  DirectSum. The Lean equivalent is **explicit code generation**:
  * An elaborator or command such as `grassmann_algebra PGA3 := D"1,1,1,0"`
    emits concrete `def`s for every product and input-kind pair (straight-line,
    zero terms pruned) and registers them as instances of per-operator classes
    for that concrete algebra.
  * Call sites that name the algebra concretely then resolve the instance at
    elaboration time, and `@[inline]` instances turn into direct calls.
  * Generic code (arbitrary `n`) uses loop kernels over `UInt64` masks with
    per-`n` cached tables, like Leibniz.
* **What to avoid**:
  * Proofs inside hot structures that are not erased. `Vector Float k` is fine,
    but a `Subtype` on every element is not.
  * Indexing by `Fin (2^n)` where `2^n` is computed at runtime.

### 8.5 Soundness and proof lessons

* `Proof.lean:28-32` declares `axiom sorryDataAxiom {α} : α` and
  `axiom sorryProofAxiom {P} : P`. Earlier versions also had a **fake
  `Ring Float`/`Field Float`** with 36 axiom-backed law fields
  (`ralph/progress.txt:185-195`). Never do either.
* `AnchorTheorems.lean:22-40` states `geometric_product_assoc` and similar
  results over `MultivectorS sig Float` with `sorry`. **These are false for
  IEEE Float**; see the witness in §6.1.
* **Pattern to keep**:
  * state laws over exact coefficients (`Int`, `Rat`, or a generic
    `[CommRing R]`) on the *same* kernel code, parameterized by a lawless ops
    class (`CoeffOps`);
  * pin small-algebra facts with `decide` or `native_decide` over `Rat`
    (`AnchorTheorems.lean:255-310`);
  * add a compile-time firewall that proves `Ring Float` cannot be synthesized
    (`ReferenceSoundnessTests.lean`).
  * For the new toolchain, prefer `decide +kernel`, `grind`, `bv_decide` (for
    `UInt64` mask identities), and `omega` (for index bounds;
    `MV.lean:169-201` shows the style).
* The core ring laws (associativity, `reverse_mul`, `wedge_assoc`) were **never
  proved** (`G4/CLAUDE.md:44-49`). If you attempt them, prove them once for the
  sign function: associativity of the twisted group-algebra 2-cocycle,
  `sign(a,b)·sign(a⊕b,c) = sign(b,c)·sign(a,b⊕c)`, on bitmasks with
  `bv_decide` for fixed n, or by induction. Kernels inherit the laws from that.

### 8.6 Notation and DSL pitfalls

* **Suffixed notations** proliferated because each representation had its own
  functions: `⋀ᵇ ⋀ᵐ ⋀ₛ ⌋ᵇ ⌋ₛ ⌋ᵐ ⌊ᵐ ⋁ᵇ ∨ₛ ⋅ₛ ⋅ᵐ †ₛ ▷ₛ`
  (`Notation.lean:31-43`, `SparseMultivector.lean:154-313`,
  `Multivector.lean:234-236,356-357`). Use **one heterogeneous class per
  operator** (`class Wedge (α β : Type) (γ : outParam Type)`, and likewise for
  contractions, hodge, and so on), mirroring Julia multiple dispatch, with
  exactly one notation each.
* **Lean-reserved symbols.** `∧`/`∨` are `And`/`Or`, `<`/`>` are `LT`/`GT`
  propositions, `!` is `Bool.not`, and `⟨…⟩` is the anonymous constructor. The
  old grade notation `⟨M⟩₀` collided and needed repair (`GANotation.lean:81-87`,
  `ralph/progress.txt:534`). Choose ASCII aliases and non-conflicting
  Unicode: `⋀`/`∧ᵍ` for wedge, `⋁` for vee, `⨼`/`⨽` (Julia's own symbols) for
  contractions, `⋆` for hodge, and a distinct symbol for Julia `!`, such as
  `complementright`.
* **Keyword tokens that break identifiers.** `syntax "e" subscriptDigits`
  (`DSL/Subscript.lean:97-101`) makes `e` a token. `syntax "R3" "{" term "}"`
  and similar lines (`DSL/Context.lean:42-49`) make `R3`, `PGA3`, and `STA`
  keywords, which breaks the identically named `abbrev`s wherever the DSL is
  imported. Also, `e₁₂` already lexes as one identifier in Lean. For a Julia
  `@basis` analogue, declare real constants in a namespace (a `basis!` command
  generating `v₁ v₂ v₁₂ …` definitions), or use an ident-based term elaborator.

### 8.7 Build, Lake, and FFI pitfalls

* **The C ABI shared library must link only modules whose import closure is
  tiny.** `grassmann_initialize_v1` runs
  `lean_initialize_runtime_module(); initialize_Grassmann_Grassmann_CABI(1); lean_io_mark_end_initialization();`
  (`c/grassmann_cabi.c:~119-139`). The module initializer transitively
  initializes **every imported module**, and each one's object must be linked.
  That is why `PGA3Kernel.lean` imports only `Init.Data.FloatArray` (:12).
  Design exported kernels as Init-only or Std-only modules.
* **Link recipe** (`scripts/cabi_smoke.sh:49-102`):
  * build `lake build 'Mod:o.export'` facets;
  * `cc -dynamiclib … Mod.c.o.export … -lInit_shared -lleanshared_2 -lleanshared_1 -lleanshared -Wl,-rpath,$(lean --print-prefix)/lib/lean`;
  * foreign threads must call `lean_initialize_thread`/`lean_finalize_thread`;
  * there is no process shutdown.
* **Lake's shared artifact cache** can replay trace metadata without producing
  the object or C file. The old port had to use
  `LAKE_CACHE_DIR='' lake --no-cache build …` for facet builds (commit
  `cbfb075`; `packed_linear_codegen_guard.sh:24-29`).
* `precompileModules = false` was needed for the bench executables
  (`G4/lakefile.toml:62-78`).
* The module initializer is named `initialize_<Pkg>_<Module path>`, which
  changes if the package or lib is renamed. Re-check it after the rename.

### 8.8 Oracle harness pitfalls

* **One Julia process per check** (`JuliaOracle.lean:81-122`) meant 188 checks
  × Julia startup plus `using Grassmann`, which took many minutes. Generate
  goldens in **one** Julia run and write versioned JSON files.
* **Spawn Julia with a scrubbed environment** (`env -i HOME PATH JULIA_DEPOT_PATH JULIA_PKG_PRECOMPILE_AUTO=0`).
  Lake and Lean child processes inherit `DYLD_*`/`LD_*` variables that conflict
  with Julia's LLVM (`JuliaOracle.lean:85-88`).
* **A first-run precompile of the repo root's dev dependencies** can exit
  nonzero, so the old harness retried once (`:119-129`). Using a dedicated
  project avoids this.
* **The oracle root was assumed from the working directory**, and a nested cwd
  silently produced wrong paths (`ralph/progress.txt:634-637`). Resolve roots
  explicitly and fail fast.
* **Coefficient extraction via `scalar(x*~B)/scalar(B*~B)`**
  (`oracle/grassmann_oracle.jl:71-80`) cannot read null blades such as v∞ or
  e4 in PGA. Dump `value(Multivector(x))` in `indexbasis` order together with
  the basis masks instead.
* **Tolerance.** `1e-9` was the default. `exp` of non-simple bivectors in Julia
  is only good to about 1e-8 (§6.2).

### 8.9 Other mistakes to avoid

* `geometricProductSingles` returns `a·b` on the scalar blade when the product
  is degenerate zero (`Products.lean:191-197`).
* A colex `combinations` ordering was used for "Julia" blade indices
  (`BitMask.lean:121-146`), which is wrong for n ≥ 4.
* `hodgeDual` and `regressiveProduct` in `MV` and `Multivector` compute
  `⋆(⋆a∧⋆b)` with the right complement three times. In R4 this gives the
  **wrong sign**: Julia gives `v12 ∨ v134 = +v₁`, but `!(!v12 ∧ !v134) = −v₁`
  (§A.4). Julia's `∨` is `complementleft(complementright(a) ∧ complementright(b))`
  (`~/chakravala/Grassmann.jl/src/algebra.jl:154,391`).
* `fatDot` (`⋅ᵐ`) is defined as left + right − scalar (`MV.lean:974-977`,
  `Multivector.lean:473-477`). **Julia's `⋅` is the right contraction**, so
  `v1⋅v12 = 𝟎`, while the old fatDot gives `v₂`.
* Hand-rolled Taylor series for `sin`, `cos`, `exp`, `sinh`, and `cosh`
  (`RotorExp.lean:18-75`), which also had indexing bugs.
* `#eval`s in library files (`Manifold.lean:474-541` and elsewhere) slow builds
  and spam output. Use `#guard` in test modules instead.
* Six representations and a `GAlgebra` class with 17 fields. Choose one runtime
  representation family (Julia's kinds) plus generated fixed-algebra kernels.
* Treating the working tree as sacred. The old loop repeatedly avoided touching
  "dirty experiments", which made builds brittle for months
  (`ralph/progress.txt:140-141` and others).

### 8.10 Suggested module decomposition for the new port

This decomposition is informed by the salvage. The core spec comes from the
Grassmann.jl, DirectSum, and Leibniz reports.

| Module | Role | Rough LOC |
|---|---|---|
| `Grassmann/Bits.lean` | `UInt64` masks, SWAR popcount, `swaps`, and the Leibniz `indexbasis`, `bladeindex`, `lowerbits`, and `expandbits` with per-`n` caches | 300 |
| `Grassmann/Sign.lean` | Geometric, wedge, and contraction signs (§4.3), `complementright`/`complementleft`/Hodge parities (§4.4), `DiagonalForm` factors, ∞/∅ rules. Proofs use `bv_decide`/`decide`. | 350 |
| `Grassmann/Kernel/Loops.lean` | One-buffer `FloatArray` kernels: linear ops, involutions from precomputed sign masks, projections, the 3ⁿ wedge, and generic products | 800 |
| `Grassmann/Codegen/Expand.lean` | Meta-level symbolic expansion of products for a registered algebra and input kinds, pruning zeros | 600 |
| `Grassmann/Codegen/EmitLean.lean` | `grassmann_algebra` command that emits `def`s and instances | 500 |
| `Grassmann/Codegen/EmitC.lean`, `EmitMetal.lean` | Straight-line C and Metal from the same expansion | 400 |
| `Grassmann/Algebras/{R2,R3,R4,STA,PGA3,CGA3,ProjInf3,Conf3}.lean` | Generated instances for common algebras | 50 each |
| `Grassmann/PGA3/Rigid.lean` | Study-condition checks, normalize, inverse, affine extraction, batch transforms (S2, S3), re-derived in Julia order | 300 |
| `Grassmann/FFI/CABI.lean` + `c/` + `include/` | Versioned caller-owned ABI (S8), Init-only imports | 150 Lean + 600 C |
| `GrassmannTest/Oracle.lean` | JSON golden loader and comparator (tolerance per case) | 400 |
| `oracle/gen_goldens.jl` + `oracle/Project.toml` | One-shot golden generator (§9) | 600 (Julia) |
| `GrassmannBench/*.lean` | Fixed harness (§8.3) and codegen shape checker (S11) | 500 |
| `GrassmannTest/Differential.lean` | Codegen kernels vs generic loops vs exact-`Rat` reference, with random coefficients | 600 |

Salvage-derived total: about 4.8k lines of Lean, plus about 0.6k of C and about
0.6k of Julia. This excludes the main Grassmann, DirectSum, and Leibniz type
and API surface, which the other specs estimate.

---

## 9. Oracle test plan (salvaged and redesigned)

**Architecture.**

* `oracle/gen_goldens.jl` runs once in a dedicated environment:

  ```
  julia --startup-file=no --project=oracle -e 'include("oracle/gen_goldens.jl")'
  ```

  Spawn it with a scrubbed environment (§8.8).
* It writes `goldens/<topic>.json`. Each record contains:
  * `algebra`: the signature string exactly as Julia writes it, for example
    `"D\"1,1,1,0\""`, `"S\"∞∅+++\""`, `"S\"+---\""`;
  * `basis`: the `indexbasis` mask list;
  * inputs: coefficient vectors in `indexbasis` order, plus the Julia kind
    (`Chain{G}`, `Spinor`, `AntiSpinor`, `Multivector`, `Submanifold`, or
    `Single`);
  * `op`;
  * outputs: coefficients, output kind, and `string(result)` for display
    goldens.
* Lean tests load the JSON with `Lean.Json` and compare. Regenerating goldens is
  an explicit command, and the goldens are committed.

**Cases carried over from the old 188 checks, with the conventions fixed:**

1. **Basis-blade tables.** For each algebra in
   {R2, R3, R4, `S"+---"`, `S"-+++"`, `D"1,1,1,0"`, `S"∞+++"`, `S"∞∅+++"`,
   `S"++++-"`, R5, R6}, and for every pair of basis blades (a, b), record the
   result of each of `*`, `∧`, `∨`, `<`, `>`, `⋅`, `⊛`, `>>>`, and `⊘`. Also
   record every unary `~`, `involute`, `clifford`, `⋆`, `!`, and
   `complementleft`. That is 4ⁿ pairs; skip pairs for n > 6. Record both the
   coefficient and the printed string.
2. **Random dense multivectors.** For each algebra, use 50 seeds with
   coefficients uniform in [−2, 2] plus some exact integers, for all binary
   products and unaries. Also include random `Chain{G}`, `Spinor`, and
   `AntiSpinor` inputs to pin the kind and grade rules. Tolerance 1e-12
   relative.
3. **Exponentials and logarithms.** Cover `exp` of simple bivectors (closed
   form), non-simple bivectors (tolerance 1e-7), and null bivectors (PGA,
   conformal); `log` of rotors; and `inv` of versors and non-versors.
4. **Geometry.** CGA point embedding and null check, distances, translators and
   their composition. PGA translators and rotors, checked motors (normalize,
   inverse, round trip), and point extraction. Rebuild these in Julia's native
   bases (`D"1,1,1,0"` null-last, **and** Julia's preferred PGA and conformal
   bases) rather than the old port's permuted channels.
5. **Plot witnesses.**
   * For torus, helix, orbit-2, and orbit-4, dump `f(t)` coefficients for
     t ∈ {−2π, −π, −1, −0.5, 0, 0.3, 0.5, 1, π, 2π}, plus 200 uniform samples in
     [−2π, 2π].
   * For the plane-*, orb, and wave fields, dump `pointfield(t)(p)` on a 21×21
     grid over [−1.5, 1.5]² (and 10³ for orb/wave).
   * These numeric goldens are the primary LeanPlot cross-test. Pixel
     comparison with the old gates (S10), using the local `paper/img/*.png`, is
     a secondary smoke test.
6. **Display strings.** Include `string(x)` for representative values of every
   kind, covering zero, one, ±1 coefficients, Float formatting, and ∞/∅ names.
7. **Linear-algebra anchors.** R3 cross via `⋆(a∧b)`, determinants via
   `v1∧v2∧v3`, and R4/R5 contraction and Hodge squares from the old
   `StressTests`.

**Input distributions.** Use exact small integers for sign and structure
tests, so results compare with `==`. Use uniform [−2, 2] Floats for numeric
tests, with a scale sweep over {1e-8, 1, 1e8} for conditioning. Use
adversarial inputs for checked operations: NaN, ±Inf, zero motors, and
Study-invalid motors (`ralph/progress.txt:116-117`).

---

## Appendix A: semantic disagreements between the old port and Grassmann.jl

| # | Topic | Old port | Grassmann.jl (verified) | Status in the old port |
|---|---|---|---|---|
| A.1 | Left and right contraction signs | Initially the plain geometric sign | `a<b = contraction(b,a)`: sign `rev(|a|)·g(a,b)`. `a>b = contraction(a,b)`: sign `rev(|b|)·g(b,a)`. Julia gives `v1<v12 = v₂`, `v12>v1 = v₂`, `v12<v123 = v₃`. | **Fixed**: `79902b3`, `3d8fd9a` |
| A.2 | The `⋅` operator | `⋅ᵐ`/`fatDot` = left + right − scalar (`MV.lean:974`) | `⋅` is the **right contraction**: `v1⋅v12 = 𝟎`, `v12⋅v1 = v₂`, `v12⋅v12 = v` | **Not fixed** |
| A.3 | Hodge `⋆` | Metric-free right complement, including nonzero values on degenerate blades (`MV.lean:859-902`), and documented as a "left complement" | `⋆` is metric-dependent: `S"-+++"` gives `⋆v1 = −v₂₃₄` where `!v1 = +v₂₃₄`, and `D"1,1,1,0"` gives `⋆e4 = 0v₁₂₃` where `!e4 = −v₁₂₃`. The old kernel equals Julia's `!` (`complementright`). | **Not fixed**. The name is also wrong. |
| A.4 | Regressive `∨` | `⋆(⋆a ∧ ⋆b)` using the right complement three times (`MV.lean:905-907`, `Multivector.lean:485-486`). The blade version was patched with ad hoc signs (`c7e01c8`). | `complementleft(complementright a ∧ complementright b)`. R4: `v12 ∨ v134 = v₁`, while `!(!v12∧!v134) = −v₁`. R3: `v12∨v23 = v₂`, `v1∨v23 = v`. | **Wrong in even n** |
| A.5 | Basis ordering | Mask order for full storage, `mask>>>1` for even and odd | `indexbasis` grade-major lex. Full order differs even at n=3, and even/odd orders differ for n ≥ 4 (§3.3). | Worked around in the oracle with manual permutations |
| A.6 | Conformal and projective bases | e₊, e₋, and the null vector placed **last**; no ∞/∅ semantics | `S"∞∅+++"`: v∞, v∅ first; v∞² = v∅² = 0; `v∞*v∅ = −1 + v∞∅`; `↑p = p + (p²/2)v∞ + v∅`. `S"∞+++"`: v∞² = +1, stereographic `↑`/`↓`. `S"∅+++"`: v∅² = −1. `S"0+++"` means **Euclidean ++++**. | Examples hand-translated. The helix was never oracle-checked, and it does work in the current Julia (§6.2). |
| A.7 | Sandwich operators | `mvSandwich R x = R x R†`, keeping full grades in the dense version | `R >>> x = R x ~R` and `x ⊘ R = ~R x R`. Both use reverse (not inverse), are unnormalized, and project to the input kind. | Partial (matches `>>>` only) |
| A.8 | Display | `e₁ - 2e₂`, `2` for `2.0` | `v₂`, `1v₂₃`, `-1v₁₃`, `𝟎`, `v`, dense printing for Chain, Spinor, and Multivector (§5) | Not attempted |
| A.9 | CGA point normalization | Normalized by the e∞ coefficient | Normalize by the origin weight, which is `(e₋ − e₊)` for the e± embedding | **Fixed**: `776d584` |
| A.10 | Versor inverse | `rev(m)/scalar(m·rev m)` for any m | Julia's `inv` is general. The reverse formula is valid only for versors. | **Fixed**: checked `versorInv?` (`ebdd0cf`) |
| A.11 | Exponential | Custom Taylor series, with a 40-term fallback | Closed form when the square is scalar, otherwise a series. Julia's result carries about 1e-8 residuals on non-simple bivectors. | Taylor indexing bug fixed in `14770a0` |
| A.12 | Metric in `Manifold` instance and `numPositive` | Always Euclidean / wrong when a bit is in both masks | n/a | Latent bugs |

## Appendix B: key old-port file index (for quick reference)

* Packed runtime: `G4/Grassmann/MV.lean`. Layout at :27-248, generic products
  at :429-660, dispatch at :676-830, Hodge at :852-907, linear ops at
  :908-965, unary ops at :990-1100, projection and widening at :1100-1215,
  instances at :1217-1269, sandwich at :1289-1311.
* PGA3 kernels: `G4/Grassmann/PGA3Kernel.lean`. Constructors at :16-95,
  `motorMul` at :104-141, reverse, norm, study, validity, normalize, and
  inverse at :143-244, even×odd and odd×even at :254-336, fused sandwich at
  :346-404, point extraction at :405-435, batch at :437-476.
* C ABI: `G4/include/grassmann/cabi.h`, `G4/c/grassmann_cabi.c`,
  `G4/Grassmann/CABI.lean`, `G4/scripts/cabi_smoke.sh`, `G4/c/cabi_smoke.c`.
* Oracle: `G4/oracle/grassmann_oracle.jl` (commands at :191-793, main at :795),
  `G4/Grassmann/JuliaOracle.lean`.
* Guards and benchmarks: `G4/scripts/{bench_guard,packedmvbench_guard,packed_linear_codegen_guard,mvdense_codegen_guard,compare_julia_examples}.sh`,
  `G4/RunPackedMVBench.lean`, `G4/Grassmann/Bench.lean`.
* History and specs: `ralph/PRD.md`, `ralph/progress.txt`, `G4/CLAUDE.md`,
  `G4/docs/PackedMVPerformance.md`, `G4/docs/JuliaExamplesVisualComparison.md`,
  `G4/docs/GrassmannJL_TypeHierarchy.md`. The last one is outdated: it uses the
  old `Simplex` and `SubManifold` names.
