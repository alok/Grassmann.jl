# Performance log

Numbers are ns/op on Apple Silicon, Lean v4.35.0-rc3 (`lake build`, default -O3 C), Julia 1.13 with
Grassmann 0.8.46. Record new measurements at the bottom with date and commit.

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
