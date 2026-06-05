# Packed MV Performance Evidence

This note records the repeatable checks for the packed `MV` backend's PGA3
motor-point path. The path is important because it exercises the port's current
hot representation for projective transforms: `PGA.Motor.transformPoint` over
`MV PGA3 .even` and `MV PGA3 .odd`.

## Reproducible Guard

From `Grassmann4`:

```bash
scripts/packedmvbench_guard.sh
```

The guard builds and runs:

```bash
lake exe packedmvbench all "$PACKED_MV_BENCH_SMOKE_ITERS"
lake exe packedmvbench pga-motor-point "$PACKED_MV_BENCH_MOTOR_ITERS"
```

Default thresholds:

| Metric | Threshold |
| --- | ---: |
| PGA3 motor-point L1 diff | `<= 1e-6` |
| Packed PGA3 motor-point time | `<= 20000 ns/iter` |
| Packed-vs-dense speedup | `>= 5x` |

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
