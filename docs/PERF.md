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

Lean: `Tests/MeshTopology/Bench.lean` (compiled); Julia 1.13, MeshTopology 0.1.0 (one thread):
`oracle/meshtopology/bench.jl`. Best of 7. Ghost lookups are all one-step stencil queries
`m[Val(a), i ± e_a]` of the grid (precomputed query lists on both sides).

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

Conclusions:
* Stencils should read a `NeighborTable`: one array read beats Julia's specialized branchy
  lookup and is 25× faster on topologies whose maps Julia cannot type-infer.
* One-shot mesh setup is dominated by Julia's quadratic `vertices`/`findfirst`; Lean's
  counting sorts, bucketed edge lookup and hash maps are linear or `n log n`.
* Per-element loops that Julia keeps in isbits tuples (`degrees`, Lagrange node lists) cost Lean
  3–20× (heap `Vector`s, boxed `Nat` arrays); acceptable for one-shot setup.
