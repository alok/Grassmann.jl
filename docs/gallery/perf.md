# GrassmannPlot performance against Cartan/Makie

`lake exe plotbench` (gallery package, `gallery/PlotBench.lean`) runs the `plot` suite on the
root harness (`Bench/Harness.lean`, [`../perf/README.md`](../perf/README.md)); its Julia twin is
`oracle/gallery/bench.jl` (Cartan 0.4.16, Makie 0.24 `streamplot_impl`, CairoMakie 0.15). Same
fields as the gallery figures, same inputs, same checks (all `=`).

```
cd gallery && lake exe plotbench --json lean.json
julia --startup-file=no --project=oracle oracle/gallery/bench.jl --json julia.json
uv run scripts/bench/compare.py --lean gallery/lean.json --julia julia.json --no-record --no-latest
```

2026-09-25, Apple M4 Max, one thread, minimum over 7 samples.

| case | what | Lean before | Lean | Julia | Lean/Julia |
|---|---|---|---|---|---|
| `plot/speed_riemann` | Cartan `speed` of the 125 664-point Riemann-sphere curve, per point | 62.8 ns | 13.7 ns | 10.2 ns | 1.3× |
| `plot/eval2_bivector` | `t(x, y)` of the 31×31 grid field (bilinear), per evaluation | 385 ns | 24.9 ns | 27.1 ns | 0.92× |
| `plot/stream2_bivector` | `streamplot` of that field (32×32 cells) | 2.83 ms | 0.875 ms | 0.576 ms | 1.5× |
| `plot/stream3_conformal` | `streamplot` of the 31³ conformal field (10³ cells) | 13.4 ms | 3.75 ms | 1.99 ms | 1.9× |
| `plot/figure_riemann` | `lines(curve)` in an `Axis3`, rendered to PNG bytes (600×500) | 54.7 ms | 49.5 ms | 428 ms | 0.12× |
| `plot/figure_bivector` | `streamplot(field)` rendered to PNG bytes (600×450) | 28.2 ms | 27.3 ms | 51.4 ms | 0.53× |

What changed ("before" is the first version of the library):

* **Grid evaluation.** Streamplots call the interpolated field at every Euler step.
  `Cartan.TensorField.eval` is general (any dimension, any gluing): per call it builds index
  vectors, a bracket pair per axis and a fiber value. `GrassmannPlot.Eval` prepares the field once
  (`Grid2Eval`/`Grid3Eval`: axes, flat fibers, width, division rule) and computes the first three
  components of the same multilinear combination directly (same operations, same order: the
  streamlines stay bit-identical with Julia's), falling back to `eval` outside the grid. The
  bracket search returns a plain index (`cellIndex`), not a pair or an `Option`; no local
  closures capture floats. 385 → 25 ns.
* **`Stream.run` directly.** `Stream.streamplot2` wraps a `Vec2 → Vec2` field into `Vec3 → Vec3`,
  allocating two more structures per step; the 2-D streamplot calls `Stream.run 2` with the
  `Vec3` evaluator.
* **`speed`.** The five-point stencil is evaluated at fixed offsets for interior points and the
  norm accumulated component by component (Grassmann fibers, whose norm is the Euclidean norm of
  the flat encoding), without building a fiber per point; no closure in the stencil. 63 → 14 ns.
* **Whole figures** are 2–9× faster than CairoMakie: LeanPlot's rasterizer against Cairo, and
  no plot-object graph.

Remaining gap: `stream3_conformal` (1.9×, `stream2` 1.5×). LeanPlot's `Stream.trace` passes the
field a boxed `Vec3` and receives one back at every step; Makie's loop keeps `Point3` values in
registers. A continuation-passing field signature in LeanPlot (`Float → Float → Float → (Float →
Float → Float → α) → α`) would remove both allocations; that is a LeanPlot change.
