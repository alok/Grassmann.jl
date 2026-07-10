# Packed MV Performance Evidence

This note records the repeatable checks for the packed `MV` backend's PGA3
motor-point path, basic linear kernels, and unary involutions. These paths
exercise the port's hot native representation: projective transforms over
`MV PGA3 .even` and `MV PGA3 .odd`, plus full/even/odd arithmetic over
contiguous `FloatArray` storage.

## Reproducible Guard

From `Grassmann4`:

```bash
scripts/packedmvbench_guard.sh
```

The guard builds and runs:

```bash
lake exe packedmvbench all "$PACKED_MV_BENCH_SMOKE_ITERS"
lake exe packedmvbench pga-motor-point "$PACKED_MV_BENCH_MOTOR_ITERS"
lake exe packedmvbench subtraction "$PACKED_MV_BENCH_SUBTRACTION_ITERS"
lake exe packedmvbench linear-arithmetic "$PACKED_MV_BENCH_LINEAR_ITERS"
lake exe packedmvbench unary-involutions "$PACKED_MV_BENCH_UNARY_ITERS"
```

Default thresholds:

| Metric | Threshold |
| --- | ---: |
| PGA3 motor-point L1 diff | `<= 1e-6` |
| Packed PGA3 motor-point time | `<= 20000 ns/iter` |
| Packed-vs-dense speedup | `>= 5x` |
| Direct packed subtraction | `<= 500 ns/iter` |
| Direct-vs-add-neg subtraction speedup | `>= 1.5x` |
| Direct packed add, neg, and smul | `<= 500 ns/iter` each |
| Direct-vs-boxed add, neg, and smul speedup | `>= 2.5x` each |
| Full reverse, involute, and conjugate | `<= 750 ns/iter` each |
| Even/odd reverse and conjugate | `<= 500 ns/iter` each |
| Even involute identity | `<= 100 ns/iter` |
| Odd involute negation | `<= 150 ns/iter` |
| Direct-vs-boxed unary speedup | `>= 20x` each |

The subtraction comparator is intentionally the current optimized
`MV.add a (MV.neg b)` composition. Its relative threshold is lower than the
linear kernels' boxed baselines because both composed operations now use their
own one-buffer loops; direct subtraction still avoids one traversal and one
temporary result.

Unary preflight compares all stored coefficients of 16 varied CGA3 values in
all three layouts before timing. Full reverse, involute, and conjugation use one
result buffer. Even involution returns the immutable input, and odd involution
delegates to the one-buffer negation kernel. Their separate ceilings preserve
those stronger parity fast paths instead of hiding them behind one loose unary
threshold.

## Generated-C Structure Guard

Timing is not an allocation counter. Run the compiler-structural gate as a
separate acceptance check:

```bash
scripts/packed_linear_codegen_guard.sh
```

After Lake establishes a current `Grassmann.MV` artifact, the script extracts
only the non-boxed linear loops, the five full/packed unary loops, and the
public constructors or parity branches that own their result. It requires:

- one final `lean_mk_empty_float_array` in each nontrivial public constructor;
- direct `lean_float_array_get`, one unboxed Float operation, and one
  `lean_float_array_push` per coefficient;
- a generated tail jump rather than C stack recursion;
- no callback application, boxed coefficient array, second collection pass,
  or input-array reference-count churn in the hot loop;
- an unboxed C `double` scalar through `smulAux`.
- a retained direct return for even involution, and exactly one result
  allocation feeding `negAux` or `involuteFullAux` for odd or full storage.

The audit does not scan the whole generated module. Typeclass dictionaries may
legitimately allocate closures, and boxed wrappers may legitimately unbox and
decrement their owned adapter arguments.

## Quiet Profiling Commands

The benchmark executable also exposes quiet runners for external profilers:

```bash
lake build packedmvbench
./.lake/build/bin/packedmvbench pga-motor-point-packed 200000
./.lake/build/bin/packedmvbench pga-motor-point-dense 20000
```

On macOS, process-level timing and footprint can be captured without benchmark
text noise:

```bash
/usr/bin/time -l ./.lake/build/bin/packedmvbench pga-motor-point-packed 200000
/usr/bin/time -l ./.lake/build/bin/packedmvbench pga-motor-point-dense 20000
```

`hwatch` is useful for watching those commands over repeated local runs, but use
a bounded wrapper or manual stop; batch mode behaves like `watch` and keeps
running.

## 2026-06-05 Audit

The packed guard passed from `Grassmann4` with zero numerical drift:

| Metric | Observed |
| --- | ---: |
| PGA3 motor-point L1 diff | `0.000000` |
| Packed PGA3 motor-point time | `10671.741600 ns/iter` |
| Dense PGA3 motor-point time | `214258.633400 ns/iter` |
| Packed-vs-dense speedup | `20.1x` |

The quiet `/usr/bin/time -l` runs gave the same process-level peak footprint for
packed and dense loops:

| Runner | Iterations | Real time | User time | Max RSS | Peak memory footprint |
| --- | ---: | ---: | ---: | ---: | ---: |
| `pga-motor-point-packed` | `200000` | `2.07s` | `2.07s` | `80986112` | `23560648` |
| `pga-motor-point-dense` | `20000` | `4.13s` | `4.12s` | `80969728` | `23560648` |

The `time -l` footprint is process-level evidence, so it should be treated as a
smoke check for gross allocation or memory regressions rather than a per-iteration
allocator proof. The timing guard remains the primary repeatable performance
gate.

## 2026-07-09 Packed Linear Audit

The thresholded guard passed with zero L1 drift in the linear preflight and the
following CGA3 full-storage results over 32 coefficients:

| Operation | Direct | Comparator | Speedup |
| --- | ---: | ---: | ---: |
| Add | `93.865084 ns/iter` | `339.517418 ns/iter` boxed | `3.617x` |
| Neg | `84.626166 ns/iter` | `299.504500 ns/iter` boxed | `3.539x` |
| Float smul | `84.537666 ns/iter` | `294.006500 ns/iter` boxed | `3.478x` |
| Sub | `91.165830 ns/iter` | `161.609580 ns/iter` optimized add-neg | `1.773x` |

The same run measured the packed PGA3 motor-point path at
`573.658200 ns/iter` versus `356053.991600 ns/iter` dense (`620.673x`) with
zero L1 drift. The generated-C structure guard independently passed all four
linear operations and the unboxed scalar ABI.

## 2026-07-09 Packed Unary Audit

The thresholded guard compared every stored coefficient of every unary result
with the pre-optimization boxed shape before timing 100,000 iterations. All
nine comparisons had zero L1 drift:

| Operation/layout | Direct | Boxed comparator | Speedup |
| --- | ---: | ---: | ---: |
| Reverse full | `388.240830 ns/iter` | `14558.060000 ns/iter` | `37.497x` |
| Reverse even | `206.378330 ns/iter` | `7295.566670 ns/iter` | `35.350x` |
| Reverse odd | `204.964580 ns/iter` | `7235.700840 ns/iter` | `35.302x` |
| Involute full | `327.273750 ns/iter` | `14364.854590 ns/iter` | `43.892x` |
| Involute even | `20.438340 ns/iter` | `7178.073750 ns/iter` | `351.206x` |
| Involute odd | `51.632500 ns/iter` | `7211.798330 ns/iter` | `139.676x` |
| Conjugate full | `395.760000 ns/iter` | `14448.023340 ns/iter` | `36.507x` |
| Conjugate even | `216.921250 ns/iter` | `7253.701250 ns/iter` | `33.439x` |
| Conjugate odd | `214.406250 ns/iter` | `7251.296670 ns/iter` | `33.820x` |

Generated C independently showed one native output loop for each nontrivial
path, no boxed range/map callbacks in those helpers, an allocation-free retained
return for even involution, and one output allocation for odd/full involution.
