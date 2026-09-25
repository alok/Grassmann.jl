# Performance log

Numbers are ns/op on Apple Silicon, Lean v4.35.0-rc3 (`lake build`, default -O3 C), Julia 1.13 with
Grassmann 0.8.46. Record new measurements at the bottom with date and commit.

## Lean vs Julia at a glance (2026-09-25, `uv run scripts/bench/run.py`)

Every suite of `lake exe bench` has a Julia twin (`oracle/bench/`) measured by the same harness;
the full table (131 cases, budgets, checks) is [`perf/latest.md`](perf/latest.md), the workflow
[`perf/README.md`](perf/README.md), the run history [`perf/history.jsonl`](perf/history.jsonl).
Minimum ns per operation, Apple M4 Max; ratio < 1 means Lean is faster. Every checksum agrees
with Julia's (almost all bit for bit) except `directsum/blade_show_R10`, a real printing
difference (below).

| suite | geomean Lean/Julia | representative case | Lean | Julia | ratio |
|---|---|---|---|---|---|
| math (Julia's own scalar kernels) | 1.8× | `exp` / `sin` / `atan` / `x^2.5` | 6.4 / 5.7 / 2.2 / 13 ns | 2.5 / 3.3 / 4.6 / 19 ns | 2.5× / 1.8× / 0.47× / 0.69× |
| juliabase (print, parse, sum, ranges, complex) | 11× | `show_float` / `parse_float` / `range_collect` | 149 ns / 2.2 µs / 41 ns | 40 / 29 / 0.57 ns | 3.7× / 75× / 71× |
| staticvectors (`Values` ops) | 18× | `dot3` / `add3` | 9.6 / 10 ns | 0.62 / 0.56 ns | 16× / 18× |
| directsum (blades, tables, plans) | 3.3× | `blade_mul_R5` / `plan_mul_R5` / `basis_index_n10` | 336 / 493 / 99 ns | 339 / 404 / 2.6 ns | 0.99× / 1.2× / 39× |
| unitsystems (conversions, dimensions) | 2.6× | `convert_pairs` / `dim_products` | 373 ns / 1.5 µs | 417 / 139 ns | 0.89× / 11× |
| geophysics (atmosphere, gravity) | 0.92× | `pressure` / `sonicspeed` | 19 / 76 ns | 13 / 174 ns | 1.5× / 0.44× |
| dendriform (trees, groves) | 0.036× | `grove_sum_4_3` | 29 µs | 748 µs | 0.039× |
| demorgan (truth values, tables) | 61× | `tv_formula_N6` | 669 ns | 0.43 ns | 1556× |
| wilkinson (parse, exprval, errval) | 0.54× | `errval_horner9` (3000 points) | 2.3 ms | 2.6 ms | 0.88× |
| meshtopology (stencils, simplices) | 0.79× | `ghost_sphere` / `simplex_topology` / `degrees` | 7.9 ns / 1.9 ms / 1.7 ms | 30 ns / 1.2 s / 89 µs | 0.26× / 0.0015× / 19× |
| fatou (escape-time rasters) | 1.1× | `mandelbrot_seq` / `mandelbrot_par` (16 threads) | 71 / 11 ms | 60 / 9.5 ms | 1.2× / 1.1× |
| grassmann (generated kernels; own harness, below) | — | `Multivector*Multivector` ℝ3 / CGA3 | 14.7 / 146 ns | 8.1 / 146 ns | 1.8× / 1.0× |

Where Lean loses, it is almost always one of four causes, each with a known fix (details in the
2026-09-25 section at the bottom): **heap-allocated small vectors** (`Values`/`FloatArray`
results: StaticVectors, Grassmann's small products), **`Nat`/`Int`/bignum arithmetic in hot
paths** (TruthValues as `BitVec (2^N)`, `2 ^ n` in Leibniz ranks, `Float.ofInt` in ranges,
`Rat` exponents in dimension groups), **runtime `Float.ofScientific` literals** (fixed in
`FieldConstants.JNum`: conversions 28× faster), and **no SIMD** (Julia's `sum`, reductions).

## 2026-09-24: storage / kernel spike (R3 full geometric product, Float)

| variant | ns/op |
|---|---|
| Julia `Multivector*Multivector` (ℝ3) | 19.8 |
| Julia `Spinor*Spinor` (ℝ3) | 15.8 |
| Lean: structure with 8 unboxed `Float` fields, unrolled | 13–15 |
| Lean: `FloatArray`, unrolled by hand | 24–29 |
| Lean: unrolled, generic over α via a storage class, specialized at Float | **26** |
| Lean: elaboration-time codegen (`gen_mul`), generic over α, @Float | **23** |
| Lean: generic struct with boxed fields, unrolled | 53 |
| Lean: boxed `Array Float`, unrolled | 61 |
| Lean: `FloatArray` table loop | 190–290 |
| Lean: flat term-list loop (`USize`, `uget`) | 400+ |
| Lean: boxed `Array Float` loop | 510–870 |

| full product, larger n | Julia | Lean codegen @Float |
|---|---|---|
| n = 5 (32×32) | 152 | 250 |
| n = 6 (64×64) | 8244 | 1189 |

Elaboration + compile cost of the generated kernels: n=3,4,5 together ≈1.3 s; n=6 ≈7 s.

Conclusions baked into DESIGN.md:
* Unrolling is mandatory; loops are 10–40× slower in compiled Lean.
* One generic kernel source serves every coefficient type. Specialization at Float yields unboxed code.
* Boxing costs ≈2×, so Float storage is `FloatArray`.
* `for … break` with `let mut` Floats boxes every Float through `ForInStep`. Measured 8× slower on a
  Mandelbrot escape loop (446 ms vs 54 ms with a tail-recursive loop). Hot Float loops must be tail-recursive.

## 2026-09-24: MeshTopology hot paths
## 2026-09-24: Julia's own scalar kernels (`JuliaBase.Math`, `lake exe bench math`)

Lean: `Tests/MeshTopology/Bench.lean` (compiled); Julia 1.13, MeshTopology 0.1.0 (one thread):
`oracle/meshtopology/bench.jl`. Best of 7. Ghost lookups are all one-step stencil queries
`m[Val(a), i ± e_a]` of the grid (precomputed query lists on both sides).
## 2026-09-24: Fatou escape-time kernel (Apple M4 Max, 12P+4E cores)
ns per call, 10⁷ calls over a sweep of arguments, results folded into an accumulator (Julia: the
same loop, `@elapsed`, after warm-up).

| operation | Julia | Lean |
|---|---|---|
| ghost lookup, Torus(61,61) | 1.9 ns | 7.8 ns (`ghost`, returns a `Vector`) |
| ghost lookup, Möbius(61,61) | 2.1 ns | 7.0 ns |
| ghost lookup, Sphere(61,61) (Julia `q` maps of mixed types: type-unstable) | 29.6 ns | 7.5 ns |
| ghost lookup, Hopf(7,60,61) | 26.4 ns | 14.5 ns |
| `NeighborTable` read (any of the above) | – | 1.0–1.1 ns (build: 0.17 ms 61×61, 3.8 ms Hopf) |
| `elementfuns` Torus(61,61) / Sphere(61,61) / Hopf(7,60,61) | 8.2 µs / 548 µs / 8.3 µs | 47 / 49 / 129 µs |
| `BilinearTopology` Sphere(61,61) | 658 µs | 1.3 ms |
| `SimplexTopology` of 79 202 triangles (Julia `vertices` is O(n²)) | 1.19 s | 1.9 ms |
| `edges` (Julia `vertices` of the edge list is O(E²)) | 1.21 s | 73 ms |
| `edgesindices` | 3.2 ms | 12 ms |
| `neighbors` | 104 ms | 30 ms |
| `incidence` / `degrees` | 2.4 ms / 85 µs | 5.1 ms / 1.7 ms |
| `facets(t, ones)` (Julia `findfirst` on a growing vector: O(F²)) | 8.4 s | 55 ms |
| `LagrangeTriangles{3}` node lists (Julia incl. `edgesindices`) | 7.0 ms | 24 ms (`getVec`: 20 ms) |
Wall times, best of 5–7. Julia 1.13 with Fatou 1.2.4; "handwritten" is a Julia kernel with
Fatou's exact grid and loop (counts checked equal), threaded over rows like `Fatou.Compute`
(`oracle/fatou/bench.jl`). Lean: `Tests/Fatou/Bench.lean` (`fatou K` / `fatou K (par := false)`).
| function | libm (`Float.exp`, …) | `JuliaBase` (Julia's kernel in Lean) | Julia 1.13 |
|---|---|---|---|
| `exp` | 1.8 | 6.6 | 2.6 |
| `log` | 2.0 | 8.2 | 3.1 |
| `expm1` | — | 12.4 | 3.5 |
| `log1p` | — | 9.3 | 3.3 |
| `x^2.5` | 4.7 | 22.1 | 8.6 |
| `x^7` (`pow_body`) | — | 9.0 | 2.9 |

Conclusions:
* Stencils should read a `NeighborTable`: one array read beats Julia's specialized branchy
  lookup and is 25× faster on topologies whose maps Julia cannot type-infer.
* One-shot mesh setup is dominated by Julia's quadratic `vertices`/`findfirst`; Lean's
  counting sorts, bucketed edge lookup and hash maps are linear or `n log n`.
* Per-element loops that Julia keeps in isbits tuples (`degrees`, Lagrange node lists) cost Lean
  3–20× (heap `Vector`s, boxed `Nat` arrays); acceptable for one-shot setup.
| raster | iterations | Lean seq | Lean par (Tasks) | Julia handwritten 1 / 16 thr | Fatou.jl 1 / 16 thr |
|---|---|---|---|---|---|
| Mandelbrot 1000², N=100 | 29.2 M | 67 ms | 10.7 ms | 62 / 8.8 ms | 2539 / 1760 ms |
| README filled Julia 1501×1001, N=80 | 30.0 M | 92 ms | 14.5 ms | 76 / 19 ms | 3123 / 2758 ms |
| README Newton z³−1 800² | 3.0 M | 71 ms | 7.9 ms | 69 / 8.9 ms | 405 / 349 ms |
| README generalized Newton sin z−1 500² | 2.8 M | 210 ms | 20 ms | 255 / 27 ms | 543 / 330 ms |

Findings:
* The fused tail-recursive sweep specialized on the map compiles to a 12-instruction inner loop
  (no loads, no allocation) at the latency bound of `z ↦ z² + c`. Per-pixel work (four array
  pushes, the colouring, the pixel lookup) is the rest.
* Loop-invariant parameters as separate scalar arguments, not a structure: a structure's fields
  are reloaded on every iteration (≈20% on Mandelbrot).
* Nothing shared between parallel chunks may be reference-counted per pixel: a boxed `seed`
  in the chunk parameters made the 16-thread run 8× slower than the sequential one (atomic
  RC contention).
* Pixel coordinates must reach the kernel as data (`Fatou.Source`), not inside a closure:
  specializing on a closed `Define` copied `Rectangle.xs` into the specialized loop and
  rebuilt the whole axis per pixel (a 800² raster took minutes).
* A decimal literal inlined into a specialized kernel can stay a runtime
  `Float.ofScientific` call with big-number arithmetic (`1.0` in the inlined Baudin–Smith
  division: Newton 255 → 69 ms once hoisted into top-level constants). Integer literals
  (`Float.ofNat`) are cheap. `JuliaBase.ComplexF64.div`/`inv` were not `@[inline]`, so
  `Fatou.C64.div`/`inv` restate them inlined (bit-identical, oracle-checked); since the
  consolidation below they are `@[inline]` with hoisted constants themselves.
* Concatenating the chunk outputs costs ≈3 ns per float (`FloatArray` has no bulk copy);
  the three float arrays are concatenated by parallel tasks.
* The same specializer hazard bites callers: a closed value (e.g. `let Z := fatou K` with a
  literal `K`) used inside a `for` body was copied into the specialized loop and recomputed
  on every iteration (a 10⁴-step loop took 3 s instead of 1 ms). Pass such values to a
  separate function, or make them depend on runtime input.
* The kernel's output sizes are proved (`sweep_sized`, `spawnChunks_sizes`), so `fatou`
  builds its `FilledSet rows cols` without a runtime check; the proof-carrying version
  (subtypes, a `List` of tasks) measured the same as the checked one.

## Rule: hoist Float literals out of hot loops (2026-09-24, Fatou port)

A decimal literal such as `0.5` or `2.0` inside a function that gets inlined into a specialized hot
loop can stay a runtime `Float.ofScientific` call. Measured 3.7× slower on Newton-basin rasters.
Bind such constants to top-level `def`s (closed terms, evaluated once) and refer to those.

* **Float literals can cost microseconds.** `0.9394130628134757` elaborates to
  `Float.ofScientific 9394130628134757 true 16`; the code generator normally hoists that into a
  closed term, but after inlining into a branch where the `Bool` argument is already a variable
  it leaves the call in place, and `Float.ofScientific` takes a bignum path for 17-digit mantissas
  or exponents past `10^22`. The first port of the kernels ran `F64.log` at 3 µs (exp 180 ns);
  decoding the constants at elaboration time (`f64!`/`f32!`, `JuliaBase.FloatLit`) brought it to
  8 ns. Grep the generated C for `l_Float_ofScientific` outside `_init_` functions to find
  others (`JuliaBase/Complex.lean` had about 50; since 2026-09-24 no JuliaBase function has one).
* `Int`/`Nat` arithmetic with `2 ^ 64`-style constants cost ~40 ns per conversion; the kernels use
  `Int64`/`UInt64` (`>>>` on `Int64` is arithmetic, as Julia's `>>`).
* Turning off closed-term extraction (`compiler.extract_closed false`) inlines the `f64!` bit
  patterns as immediates but is not faster: the remaining cost is the out-of-line
  `lean_float_to_bits`/`lean_float_of_bits` calls (`bl` in the disassembly), five or so per `exp`.
  Unboxed `FloatArray` tables save two of them (7.3 → 6.6 ns).

## Rule: `Nat.toFloat` is slow in hot loops (2026-09-24, LeanPlot recipes)

`Nat.toFloat` goes through `Float.ofScientific` and GMP on every call. In hot loops, convert through
`n.toUInt64.toFloat` (or keep a running Float counter). Float literals inside lambdas are also
re-parsed on every call: bind them to top-level constants or use `JuliaBase`'s `f64!` macro. These
two fixes alone halved some recipe kernels.



## 2026-09-24: Julia's own trig and hyperbolic kernels; literals as module globals

`lake exe bench math` (10⁷ calls, a sweep of arguments folded into an accumulator; Apple M4 Max)
against the same sweeps in Julia 1.13 (`sweep(f, x, dx, n)`, best of 3). `JuliaBase.Trig`,
`JuliaBase.Hyperbolic` and `ComplexF64` agree with Julia bit for bit (`Tests/JuliaBase/trig.json`
and 2·10⁶-row `fuzztrig` sweeps).

| function (ns) | libm (`Float.sin`, …) | JuliaBase | Julia 1.13 |
|---|---|---|---|
| `exp` | 1.8 | 6.5 (6.6 before) | 2.6 |
| `log` | 2.0 | 6.7 (8.2) | 3.1 |
| `x^2.5` | 4.7 | 13.1 (22.1) | 8.6 |
| `x^7` (`pow_body`) | — | 7.7 (9.0) | 2.9 |
| `sin`, `cos` on [-10, 10] | 2.2 | 5.8 | 3.4, 3.6 |
| `tan` | 2.9 | 10.4 | 4.9 |
| `sin` of `x ≈ 10¹⁰` (Payne–Hanek) | — | 62 (2 160 in `Nat` arithmetic) | 9.6 |
| `asin` | 2.8 | 5.3 | 2.7 |
| `atan` | 2.4 | 2.2 | 4.6 |
| `atan(y, 0.7)` | 4.3 | 11.0 | 5.5 |
| `sinh`, `tanh` | 2.8, 2.6 | 8.1, 8.6 | 3.2, 3.4 |
| `sinpi` | — | 7.0 | 3.4 |
| `ComplexF64` `/` | — | 2.9 | 2.4 |
| `ComplexF64` `exp`, `sin` | — | 30, 34 (38, 81 at first) | 7.1, 10.2 |

Findings:
* **Closed terms are atomic loads.** In Lean 4.35 a constant inside a function body (a hoisted
  literal, `Float.ofBits n`, `-c`, an `Int32`/`Int64` literal) becomes a closed term read through
  a once-cell whose state is `_Atomic(int)`: every use is a sequentially consistent load (`ldar`)
  and a branch. A top-level `def` is initialized with its module and read as a plain global.
  `f64!`/`f32!` therefore elaborate to a module-level constant per literal (`M._f64.x<bits>`),
  with the sign inside (`f64! -0.5`, not `-f64! 0.5`): `x^2.5` 22 → 13 ns, `atan` 9.9 → 2.2 ns,
  `log` 8.2 → 6.7 ns, with no source change beyond the macro. `Int32`/`Int64` literals are still
  closed terms (e.g. the shift counts in `atan2` and `exp`).
* `Float.isNaN`/`isInf`/`isFinite` and `Float.toBits`/`ofBits` are out-of-line runtime calls
  (a `toBits`+`ofBits` round trip ≈ 0.6 ns). `F64.isnan x` (`x != x`), `F64.isinf`, `F64.isfinite`
  (comparisons of `|x|` with `Inf`) are inline; take a sign from a comparison wherever the
  operand cannot be `±0`, and keep bit casts for the cases that need them.
* **A NaN's sign is unobservable in Lean**: `Float.toBits` canonicalizes NaNs (Float's logical
  model identifies them), so `copysign(·, NaN)` sees every NaN as positive and negating a NaN is
  invisible. Julia code that negates a NaN and reads its sign back needs the case written out
  (`ComplexF64.atan(±Inf + NaN·im)`).
* A tuple of `Float`s built in several branches or returned from a non-inlined function boxes
  both fields (three allocations): `sincos` has a continuation-passing form `F64.sincosK` for the
  complex functions, the kernels return single `Float`s (`atanPQ` returns `p + q`), and
  `exthorner` is written out rather than through a local step function.
* The remaining gap in `ComplexF64.exp`/`sin` is the result itself: `JuliaBase.Complex α` is
  polymorphic, so a `Complex Float` returned from a non-inlined function holds two boxed floats.
  `div` and `inv` are `@[inline]` and cancel their constructors inside specialized code.
* `a[i]!` on a `FloatArray` compiles to an out-of-line bounds-check lambda; `a.get! i` is the inline
  `lean_float_array_get` (`log` 7.8 → 6.8 ns).
* Payne–Hanek reduction (`|x| ≥ 2^20·π/2`) runs its 128-bit products on `UInt64` limbs; the
  first port used `Nat` and took 2.2 µs.



## 2026-09-24: generated product kernels (`grassmann_kernels`, DESIGN.md §5.2) vs Julia

Apple M4 Max, one thread. Lean: `lake exe bench grassmann` (`Bench/Grassmann/Products.lean`);
Julia 1.13.0 with Grassmann 0.8.46: `oracle/bench/grassmann_bench.jl`. Both run the same loop:
ns per call over 10⁷ calls (10⁶ for the CGA3 multivector product), operands drawn from a ring
of 1024 random `Float64` elements (nothing loop-invariant), every result's coefficients summed
into the accumulator (so every output is computed), best of 7 after a warm-up. Lean's call
sites are ordinary typed expressions at concrete types (`a * b`, `v ⊘ R`, `~m`), so their
dispatch folds to the generated kernels specialized at `Float`. "ref" is the reference kernel
(the interpreted plans every space used before code generation).

| op | ℝ3 Julia | ℝ3 Lean | STA Julia | STA Lean | PGA3 Julia | PGA3 Lean | CGA3 Julia | CGA3 Lean |
|---|---|---|---|---|---|---|---|---|
| harness: sum of an operand | 0.75 | 1.11 | 1.08 | 1.80 | 1.08 | 1.96 | 2.49 | 4.01 |
| harness: copy of an operand (one result) | 0.69 | 9.98 | 1.07 | 11.2 | 1.06 | 11.4 | 2.47 | 14.8 |
| `Multivector*Multivector` | 8.14 | **14.7** | 41.4 | **37.6** | 35.8 | **32.6** | 146 | **146** |
| `Spinor*Spinor` | 2.23 | 11.9 | 8.16 | 14.3 | 8.56 | 13.3 | 31.0 | **38.5** |
| `R*v*~R` | 4.11 | 27.8 | 27.5 | **30.3** | 42.5 | **30.1** | 54.6 | **58.5** |
| `v ⊘ R` (fused) | 2.80 | 11.6 | 6.99 | 14.6 | 8.32 | 13.7 | 17.1 | **24.2** |
| `R >>> v` (fused) | 2.80 | 11.7 | 7.27 | 14.6 | 8.31 | 15.3 | 17.3 | **24.2** |
| `Chain1∧Chain1` | 0.69 | 10.3 | 2.29 | 13.2 | 2.31 | 13.4 | 3.02 | 12.5 |
| `Chain2*Chain1` | 2.17 | 11.8 | 3.18 | 11.9 | 3.06 | 12.1 | 5.40 | 18.0 |
| `~m` (reverse) | 0.77 | 10.9 | 1.07 | 12.9 | 1.07 | 13.1 | 2.54 | 21.2 |
| `m := ~m` in place | 0.52 | 3.59 | 1.27 | 3.88 | 1.27 | 3.88 | 1.19 | 5.78 |
| `⋆m` (Hodge) | 0.74 | 10.8 | 1.13 | 13.2 | 1.53 | 13.0 | 40.2 | **21.1** |
| `⋆v` (Hodge of a vector) | 0.68 | 10.1 | 0.70 | 11.0 | 0.68 | 11.4 | 3.33 | 11.4 |
| ref `Multivector*Multivector` | | 158 | | 424 | | 346 | | 1496 |
| ref `Spinor*Spinor` | | 93.2 | | 161 | | 149 | | 430 |

Bold: within 1.5× of Julia (or faster).

Findings:
* **Where the arithmetic dominates, the generated kernels match Julia**: the multivector products
  of STA, PGA3 and CGA3 (0.91–1.0×), the CGA3 spinor product (1.24×), the rotor sandwich
  `R*v*~R` of STA, PGA3, CGA3 (0.71–1.1×), the fused CGA3 sandwiches (1.4×), and the conformal
  Hodge star (0.52×: Julia's conformal complement is not unrolled). Against the reference
  kernels the gain is 10× (ℝ3 158 → 14.7 ns, CGA3 1496 → 146 ns).
* **Everything small sits on an allocation floor of ≈ 9–13 ns.** Every Lean result is a fresh
  `FloatArray`: allocate, copy, free (the "copy of an operand" row). Julia's results are
  `isbits` tuples that live in registers, so its small operations cost 0.7–3 ns. ℝ3 `∧`,
  `~`, `⋆` are at the floor (the kernel itself is ≈ 1 ns), ℝ3 `Multivector*Multivector` is
  floor + 4.7 ns. Within the storage contract (DESIGN.md §2: bulk Floats in `FloatArray`)
  the floor is not avoidable per result; it is avoided by **updating in place**: a kernel
  writes its outputs into an operand of the output's size when that operand is exclusive,
  so `m := ~m` (or `m := m * n`) allocates nothing (3.6 ns vs 10.9 ns).
* `R*v*~R` is three typed products, hence three allocations; `⊘` and `>>>` are fused (one
  kernel per `(R, x)` layout pair keeping `(~R) x` in registers, one allocation).

Fixes made while profiling the generated C (`set_option trace.compiler.ir.result true`):
* Outputs written with unchecked `set` into a copy of an operand or of the zero vector, instead
  of a `FloatArray.push` per output: `lean_float_array_push` is an out-of-line runtime call
  (capacity and exclusivity checks, size update). ℝ3 `Multivector*Multivector` 21 → 14.7 ns.
* The fallback of a dispatch branch that does not fold receives the space as a `@[noinline]`
  constant. LCNF folds neither `Nat.mod` nor `Nat.beq`, so the parity layouts of the typed
  instances (`halfLayout ((G + H) % 2 == 1)`) stay closed `Bool` terms and their dispatch is a
  run-time branch (cheap); but the `abbrev` space in the fallback branch was inlined as a
  structure literal and allocated before the branch on every call (`lean_alloc_ctor(0, 6, 3)`
  in the loop): `R >>> v` 80 → 33 ns before fusion.
* Fused sandwiches (`SandwichKernels`): ℝ3 `v ⊘ R` 26.5 → 11.6 ns, `R >>> v` 32.4 → 11.7 ns,
  CGA3 38.9 → 24.2 ns. The typed layer reaches them through `SandwichKernels V`; code generic
  over the space must carry `[SandwichKernels V]` next to `[Kernels V]` to get them.
* Harness: `Values.foldl` is a structural loop with `Nat` arithmetic per element (≈ 2 ns per
  coefficient; the sum uses `FloatArray.foldl`), and `xs[i]!` built its `Inhabited` default (a
  zero multivector) on every iteration. Julia side: `@elapsed(run(N))` of a pure loop whose
  result is unused is deleted by Julia's effect analysis (it reported 0.0 ns for `~m`); every
  result now goes to a global sink.

Build cost of the pre-generated kernels (`Grassmann.Kernel.Generated`, one module per space;
elaboration and compilation to C, then clang `-O3` of the C file):

| space | kernels | entries | fused sandwiches (entries) | `Multivector*Multivector` entries | elaborate + compile | clang | C size |
|---|---|---|---|---|---|---|---|
| ℝ2 | 372 | 832 | 50 (296) | 16 | 2.0 s | 1.9 s | 2.2 MB |
| ℝ3 | 514 | 2624 | 72 (1120) | 64 | 3.2 s | 3.0 s | 3.9 MB |
| ℝ4 | 682 | 8800 | 98 (4320) | 256 | 5.8 s | 5.3 s | 7.4 MB |
| STA | 682 | 8800 | 98 (4320) | 256 | 5.6 s | 5.3 s | 7.3 MB |
| PGA2 | 514 | 2077 | 72 (864) | 48 | 3.1 s | 3.1 s | 3.7 MB |
| PGA3 | 682 | 6899 | 98 (3296) | 192 | 5.2 s | 5.0 s | 6.7 MB |
| CGA2 | 682 | 8800 | 98 (4320) | 256 | 6.0 s | 5.5 s | 7.3 MB |
| CGA3 | 876 | 30944 | 128 (16896) | 1024 | 13 s | 11 s | 16.9 MB |

52 s CPU (14 s wall on 16 cores) to elaborate, 39 s CPU (11 s wall) for clang; the `.olean`s
total 110 MB. The CGA3 multivector product stays generated. `basis!` of an `n = 6` space
(`S!"+++++-"`, dense families other than `Multivector*Multivector` dropped) emits 1002 kernels
with 64 873 entries and 162 fused sandwiches in about 20 s.

## 2026-09-25: benchmark harness, Julia twins for every package, first Lean-vs-Julia sweep

Commit `8d619251` (+ budgets); full table in `docs/perf/latest.md`, summary at the top of this
file. Infrastructure: `Bench/Harness.lean` (named cases, warm-up, adaptive batch size, min/median
ns per operation, checksum sinks, `--filter`, `--smoke`, `--json`), its twin
`oracle/bench/harness.jl`, one `oracle/bench/<suite>.jl` per Lean suite with identical case keys,
inputs and checksums, `scripts/bench/run.py` (build, run both, compare) and
`scripts/bench/compare.py` (report, `history.jsonl`, `--guard` against `docs/perf/budgets.toml`
and a 20% regression threshold). The old ad-hoc benches (`Bench.Math`, `Tests/*/Bench.lean`,
`oracle/*/bench.jl`) are ported onto it.

Harness pitfalls (details in `docs/perf/README.md`):
* **Arity reduction defeats a naive black box.** `@[noinline] def blackBox (_salt : Nat) (x : α) := x`
  loses its unused salt (`blackBox._redArg x`); `f (blackBox s 10)` then became a closed term
  computed once, and cases reported 0.005 ns. The harness's `blackBox` is implemented by a
  function whose result depends on the salt through an undecidable branch (`ptrAddrUnsafe`).
* **An opaque `Define` is not specialized**: `fatou (blackBox s K)` ran the generic, boxed kernel
  25× slower (1.59 s vs 67 ms); salt the size and inline the definition instead.
* **`Nat.toFloat` of a value ≥ 2^53 takes ~8 µs** (`Float.ofScientific` leaves its fast path for
  the `Float.Model` bignum path). Convert 64-bit values through `UInt64.toFloat`.

Fixed on the way:
* `FieldConstants.JNum.isApproxUnit` (UnitSystems' `unit` snapping, several per conversion
  chain) evaluated its tolerance literal `8.161992717227193e-15` at run time; the exponent is
  past `10^22`, so every call took the bignum model path (~1.3 µs). Decoded with `f64!`, and
  `JNum.toFloat` of an `Int64` uses `Int64.toFloat`: `unitsystems/convert_pairs` 10.4 µs → 0.37 µs
  per factor (Julia 0.42 µs), `natural_systems` 10 µs → 0.37 µs. All FieldAlgebra, UnitSystems,
  Similitude, MeasureSystems and Geophysics tests unchanged.

Open gaps (budgets record them with 30% headroom; each is a follow-up):

| case | Lean / Julia | diagnosis | fix |
|---|---|---|---|
| `demorgan/tv_formula_N6` | 669 ns / 0.43 ns | `TruthValues N` is a `BitVec (2^N)`; at `N = 6` every column ≥ 2^63 is a GMP bignum, each connective allocates | `UInt64` storage for `N ≤ 6` |
| `juliabase/parse_float` | 2.2 µs / 29 ns | `List Char` scan into a `Nat`, exact `ofDecimal` (bignum) for every input | Clinger fast path (mantissa < 2^53, \|e\| ≤ 22), `String.Iterator` |
| `juliabase/range_*` | 40 ns / 0.6 ns | `StepRangeLen.get` converts the index with `Float.ofInt` (Int → Nat → OfScientific) | `(i - r.offset).toInt64.toFloat` (same value for Julia `Int` indices) |
| `directsum/basis_index_n10` | 99 ns / 2.6 ns | `bladeRankImpl` computes `2 ^ n` (GMP `mpz_pow_ui`) per call; `binomsum` re-sums binomials | `b >>> n == 0`; read the tables' offsets |
| `staticvectors/*`, small Grassmann ops | 10–40 ns / 0.5–3 ns | every vector-valued result is a fresh `FloatArray`; reductions are Nat-indexed, bounds-checked loops | unrolled generated kernels for small `n`, or unboxed-field structs for `n ≤ 4` |
| `unitsystems/dim_products` | 1.5 µs / 139 ns | group products add `Rat` exponent vectors (a `gcd` per entry) | integer exponents in twelfths, as `UnitSystems.Dim` |
| `directsum/blade_mul_CGA3` | 1.7 µs / 230 ns | Gram product recomputed per call over `Rat` terms | read plan tables (DESIGN §5.3) |
| `directsum/blade_show_R10` | 310 ns / 10 ns, check ≠ | label strings built by `List`/`String` concatenation; **Lean prints `v₀` for generator 10, Julia `v10`** (label rule for `n ≥ 10`) | fix `Leibniz.printLabel`; build into one buffer |
| `juliabase/sum_f64` | 0.55 / 0.087 ns per element | bit-exact replay of the SIMD accumulator layout with bounds-checked reads; no vectorization | `USize`/`uget` loop that clang can vectorize |
| `math/*` (exp, log, expm1, sinh, tan) | 2–3× | Julia's kernels bit for bit; out-of-line `lean_float_to_bits`/`of_bits` calls and `Int` bookkeeping | runtime inline bit casts; `Int64` exponent arithmetic |
| `meshtopology/degrees`, `elementfuns_*`, `lagrange3_nodes` | 5–19× | per-element loops over boxed `Nat` arrays and heap `Vector`s (Julia: isbits tuples) | packed `ByteArray`/`UInt32` storage |

Where Lean already wins: Dendriform groves (25–35× faster: Julia's `Grove` arithmetic
allocates matrices), Wilkinson's `errval` as a whole (Julia generates and compiles a function
per call; with that function precompiled, `*_nocodegen`, Julia is 10–17× faster than Lean's AST
interpreter, a follow-up: compile the AST to a closure tree or plan), MeshTopology setup (Julia's quadratic `vertices`/`findfirst`), the
Geophysics viscosity and sonic-speed profiles (2–4×), `atan`/`x^2.5` and the cached `parity`
table lookups (3×).


## 2026-09-25: the dynamic layer `TA` dispatches to the generated kernels

`lake exe bench dynamic` (`Bench/Dynamic.lean`) against `oracle/bench/dynamic.jl`: `ℝ3`
(`Submanifold(3)`) elements with `Float64` coefficients, rings of 1024 random operands, every
result's stored coefficients summed (checksums equal to Julia's bit for bit). Julia keeps its
elements in a `Vector{Any}`, so every call dispatches on the runtime type, as `TA` dispatches
on its kind. Minimum ns per operation, Apple M4 Max.

| case | Julia (`Vector{Any}`) | Lean `TA` operators | Lean `TA` Julia loops (before) | ratio |
|---|---|---|---|---|
| `Multivector * Multivector` | 42.3 | 34.5 | 311 | 0.82 |
| `Chain{1} * Chain{1}` | 41.9 | 37.3 | 280 | 0.89 |
| `Chain{1} ∧ Chain{1}` | 51.1 | 37.9 | 207 | 0.74 |
| `Single * Single` | 255 | 99.4 | 498 | 0.39 |
| `Multivector + Multivector` | 35.0 | 33.8 | 98.9 | 0.97 |
| `~Multivector` | 39.2 | 21.3 | 2039 | 0.54 |

What changed (`Grassmann/Dynamic/Fast.lean`):
* The dynamic products evaluate Julia's generated loops through interpreted plans (so that
  `Float` results agree with Julia bit for bit, sign of zero included, in every space), found
  per call in a process-wide `HashMap` keyed by the space, and run generic in the coefficient
  type (boxed `Float`s). The unary maps computed every entry from DirectSum's blade rules (a
  `Rat` coefficient and a basis rank per entry: 2 µs for `~m`).
* `class DynKernels V` marks spaces whose `Kernels` instance is generated and whose metric is
  diagonal and non-degenerate (`ℝ2`, `ℝ3`, `ℝ4`, `STA`, `n ≤ 5`, not conformal, tangent or
  dyadic). There the generated kernel of a chain × chain or container × container product,
  and of a sign map or complement of a container, *is* Julia's loop (same contributions in the
  same order, first-term sums, `-x` negation), so the operator instances call it directly;
  `Single * Single` uses the blade sign (`parityjoin`) with `termProd`'s exact scaling; same-kind
  container sums are inline. `Tests/Dynamic/Fast.lean` checks 17602 fast results against the
  loops bit for bit. Every other case (and every space without `DynKernels`: PGA, CGA,
  runtime-built spaces) keeps the loops.
* At a call site with a literal space the `DynKernels.fast` test and the kernel dispatch fold,
  and the kernel is specialized at `Float`; the remaining cost is the result allocation and
  the kind match.

Open: the plan lookup of the loop path (hashing the `TensorBundle` per call) and the generic
coefficient code are what `PGA3`/`CGA3` and runtime spaces still pay (≈200-300 ns for small
products); a per-space `DynKernels` carrying precomputed loop plans would remove the lookup.
