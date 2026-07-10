# Grassmann

A Lean 4 port of [Grassmann.jl](https://github.com/chakravala/Grassmann.jl) - a Clifford/Geometric Algebra library.

This directory contains the Lean sources. The authoritative Lake workspace is
the repository root (`../lakefile.toml`), which pins Lean `v4.27.0-rc1` and
mathlib commit `32d24245c7a12ded17325299fd41d412022cd3fe`. Run the commands in
this README from that outer repository root.

The nested `Grassmann4/lakefile.toml` is an experimental, noncanonical
workspace with maintainer-local path dependencies. Those dependencies are not
required by the supported outer build.

## Features

- **Compile-time dimension checking**: Uses `BitVec n` for basis blade representation
- **Arbitrary metric signatures**: Euclidean, Minkowski, conformal, projective, and custom signatures
- **All fundamental products**: Geometric, wedge, dot, contractions, regressive
- **Involutions**: Reverse (†), involute (ˆ), conjugate (‡), Hodge dual (⋆)
- **Geometric models**: Conformal (CGA) and Projective (PGA) geometric algebras
- **Spinors/Rotors**: Efficient rotation representation with slerp
- **Linear algebra**: Generic determinants, linear maps, Cramer's rule, outermorphism
- **Calculus**: Gradient, divergence, curl, Laplacian via finite differences
- **Unicode notation**: Clean syntax with operators like `⋀`, `⊛`, `⌋`
- **Computable packed runtime**: `MV` uses native Float storage and does not
  import the project's placeholder proof axioms

## Runtime Architecture

The performance-oriented and reference-oriented APIs have an explicit import
boundary:

```lean
-- Proof-free packed Float runtime.
import Grassmann.MV

-- Optional conversions/coercions to the dense reference representation.
-- This import reaches Multivector and its proof-oriented infrastructure.
import Grassmann.MVDense
```

`Grassmann.SignTablesCore` supplies cached sign tables to the packed runtime;
`Grassmann.SignTables` adds dense `Multivector` integration. The supported
`import Grassmann` root is also proof-free and includes the packed PGA3 API;
use `import Grassmann.Reference` for the broad dense/extended surface. For
canonical development builds that also compile the broad validation suites,
use `import Grassmann.All` or run `lake build Grassmann.All` from the outer root.
Application experiments and optional-dependency modules are deliberately not
part of that aggregate.

Packed linear arithmetic uses borrowed inputs and one final `FloatArray` for
`MV.add`, `MV.sub`, `MV.neg`, and `MV.smul`. Standard `Zero`, `Inhabited`, and
`SMul Float` instances work for full, even, and odd storage. `One` exists only
for even and full storage; an odd packed value cannot contain the scalar
identity. These are executable interfaces and do not assert exact Float ring or
module laws.

## Quick Start

The examples below opt into the dense/reference surface because they mix blade
notation, dense `Multivector`, and spinor APIs. Use `import Grassmann` for a
packed-runtime application.

```lean
import Grassmann.Reference

open Grassmann

-- Euclidean 3-space basis
#check (e1 : Blade R3)  -- grade 1 vector
#check (e12 : Blade R3) -- grade 2 bivector
#check (e123 : Blade R3) -- grade 3 pseudoscalar

-- Products
#eval (e1 : Blade R3) ⋀ (e2 : Blade R3)  -- wedge: e12
#eval (e1 : Blade R3) ⊛ (e1 : Blade R3)  -- geometric: scalar 1
#eval (e1 : Blade R3) ⌋ (e12 : Blade R3) -- contraction: e2

-- Multivector operations
#eval let v := (Multivector.ofBlade (e1 : Blade R3) : Multivector R3 Int)
      let w := (Multivector.ofBlade (e2 : Blade R3))
      (v * w).coeff e12  -- 1 (anticommutative)

-- Rotations via spinors
#eval let R := rotorZ (3.14159 / 2)  -- 90° around z
      let e1v : Multivector R3 Float := Multivector.ofBlade (e1 : Blade R3)
      R.rotate e1v  -- rotates e1 towards e2
```

## Modules

| Module | Description |
|--------|-------------|
| `BitMask` | BitVec utilities: popcount, grade, indices |
| `Manifold` | Metric signatures: R1-R4, STA, CGA3, PGA3, Cl(p,q,r) |
| `Blade` | Basis blades with BitVec representation |
| `Parity` | Sign computation via the parityjoin algorithm |
| `Products` | Geometric, wedge, dot, and contraction products for blades |
| `Notation` | Unicode operators: `⋀`, `⊛`, `⌋`, `⌊`, `⋁` |
| `DataArray` | Native unboxed Float storage used by packed kernels |
| `MV` | Proof-free parity-packed Float multivectors and direct-dispatch kernels |
| `SignTablesCore` | Proof-free cached tables for standard signatures |
| `EvenKernelTables` | Shared packed even-grade lookup tables |
| `PGA3Kernel` | Init-only fixed PGA3 kernels shared by Lean and C callers |
| `PGA3Packed` | Proof-free packed PGA3 constructors and transformations |
| `MVDense` | Opt-in packed/dense conversion and coercion layer |
| `Multivector` | Dense 2^n reference and proof-oriented representation |
| `SparseMultivector` | Sparse reference representation |
| `TruncatedMV` | Grade-truncated representation for larger dimensions |
| `Versor` / `Spinor` | Rotor construction, sandwich products, and interpolation |
| `CGA` | Conformal GA: points, lines, circles, spheres, meet |
| `PGA` / `PGATransforms` | Projective GA entities and rigid transformations |
| `LinearAlgebra` | Generic determinant, linear maps, Cramer's rule |
| `Calculus` | Gradient, divergence, curl, Laplacian |
| `PropertyTests` | Focused dense/packed/sparse/truncated reference gates |
| `MVArithmeticTests` | Exact packed linear-arithmetic layout regressions |
| `JuliaOracle` | Automated comparisons against Grassmann.jl |
| `CABI` | Internal exports behind the versioned, caller-owned C API |

## Development aggregate and experiments

`Grassmann.All` imports `Grassmann.Reference` plus the dependency-free stress,
unit, exact packed-arithmetic, oracle-anchor, DSL, and property-test modules.
It is designed to build in the authoritative outer workspace without local
SciLean, LeanPlot, or LeviCivita checkouts.

These application modules remain explicit entry points:

- `Grassmann.CurveShortening` is an in-repository geometric-flow experiment.
- `Grassmann.CoffeeshopExamples` and `Grassmann.LeanPlotDemo` require a
  separately compatible LeanPlot package profile.

The experimental nested Lake workspace does not currently provide a supported
LeanPlot profile; use the outer workspace for canonical build results.

## Signatures

```lean
-- Standard Euclidean spaces
R1, R2, R3, R4 : Signature n

-- Complex numbers as Cl(0,1)
ℂ_sig : Signature 1

-- Quaternions as Cl(0,2)
ℍ_sig : Signature 2

-- Spacetime algebra Cl(1,3)
STA : Signature 4

-- Conformal geometric algebra Cl(4,1)
CGA3 : Signature 5

-- Projective geometric algebra Cl(3,0,1)
PGA3 : Signature 4

-- Custom signatures
Signature.cl p q  -- Cl(p,q) with p positive, q negative
```

## Products

| Operator | Name | Description |
|----------|------|-------------|
| `⋀` / `⋀ᵐ` | Wedge | Antisymmetric, grade-increasing |
| `⊛` / `*` | Geometric | Full Clifford product |
| `⌋` / `⌋ᵐ` | Left contraction | Projects a into b |
| `⌊` / `⌊ᵐ` | Right contraction | Projects b into a |
| `⋁` | Regressive | Dual to wedge (meet) |
| `⋅ᵐ` | Fat dot | Left + right contraction |

## Involutions

| Notation | Name | Grade k factor |
|----------|------|----------------|
| `†` | Reverse | (-1)^(k(k-1)/2) |
| `ˆ` | Involute | (-1)^k |
| `‡` | Conjugate | (-1)^(k(k+1)/2) |
| `⋆ᵐ` | Hodge dual | Maps grade k to n-k |

## Conformal Geometric Algebra (CGA)

```lean
open Grassmann.CGA

-- Embed 3D point into CGA
let p := point (1 : Float) 2 3

-- Geometric objects as blades
let l := line p1 p2           -- grade-3 line
let c := circle p1 p2 p3      -- grade-3 circle
let π := plane p1 p2 p3       -- grade-4 plane
let s := sphere p1 p2 p3 p4   -- grade-4 sphere

-- Intersections via meet
let intersection := meet obj1 obj2
```

## Projective Geometric Algebra (PGA)

```lean
open Grassmann.PGA

-- Points, lines, planes as blades
let p := point (1 : Float) 2 3    -- grade-3 trivector
let π := plane 1 0 0 5            -- grade-1 (x = 5)
let l := joinPoints p1 p2         -- line through two points

-- Intersections
let pt := meetPlaneLine π l       -- point where line meets plane

-- Rigid transformations via motors
let T := translator 1 0 0         -- translate by (1,0,0)
let R := rotor 0 0 1 (π/2)        -- rotate 90° around z
let p' := applyMotor (T * R) p    -- combined transform
```

## Spinors and Rotations

```lean
-- Create rotor from axis-angle
let R := Spinor.fromAxisAngle bivector angle

-- Convenient R3 rotors
let Rx := rotorX angle
let Ry := rotorY angle
let Rz := rotorZ angle
let R := rotorFromEuler roll pitch yaw

-- Apply rotation
let v' := R.rotate v

-- Interpolate rotations
let Rmid := Spinor.slerp R1 R2 0.5
```

## Linear Algebra via GA

```lean
open Grassmann.LinearAlgebra

-- Generic determinant (works for any dimension!)
let d := det [v1, v2, v3]  -- R3
let d := det [v1, v2, v3, v4]  -- R4

-- Linear maps
let L : LinearMap R3 Float := LinearMap.id
let v' := L.apply v
let d := L.det

-- Solve systems via Cramer's rule
let x := cramer L b
```

## Calculus

```lean
open Grassmann.Calculus

-- Numerical derivatives
let grad := gradient f x h        -- ∇f
let div := divergence F x h       -- ∇·F
let rot := curl F x h             -- ∇×F (⋆(∇∧F))
let lap := laplacian f x h        -- ∇²f

-- Geometric measurements
let v := volume [v1, v2, v3]      -- parallelepiped volume
let a := signedArea2D v1 v2       -- 2D signed area
```

## Building

From the outer repository root:

```bash
lake update
lake build
lake build Grassmann.MV Grassmann.MVDense
```

The root workspace fetches its pinned mathlib revision and has no required local
path dependencies. Do not use the nested experimental Lake workspace as the
normal build entrypoint.

## Benchmarks

Use the benchmark guards for repeatable local correctness and performance
checks:

```bash
Grassmann4/scripts/bench_guard.sh
Grassmann4/scripts/packedmvbench_guard.sh
Grassmann4/scripts/packed_linear_codegen_guard.sh
```

`Grassmann4/scripts/bench_guard.sh` runs the core `lake exe bench` suite, checks
that the packed `MV` rotor and sandwich paths still match dense `Multivector`, and
enforces conservative local latency and speedup thresholds for rotor,
sandwich, PGA3 motor, and compile-time gradient kernels. Override defaults with
`MAX_MV_ROTOR_NS`, `MAX_MV_SANDWICH_NS`, `MAX_MV_MOTOR_NS`,
`MAX_KERNEL_GRAD_NS`, `MIN_ROTOR_SPEEDUP`, `MIN_SANDWICH_SPEEDUP`, and
`MIN_GRADIENT_SPEEDUP`.

Packed `MV` point-transform checks live in `packedmvbench`:

```bash
lake exe bench verify
lake exe packedmvbench all 200
lake exe packedmvbench pga-motor-point 5000
lake exe packedmvbench subtraction 250000
lake exe packedmvbench linear-arithmetic 500000
```

`Grassmann4/scripts/packedmvbench_guard.sh` runs a small correctness smoke test,
then checks the packed PGA3 motor-point transform, direct subtraction, addition,
negation, and Float scalar multiplication against conservative local absolute
and relative thresholds. The linear kernels are compared with their former
boxed-array shape; subtraction is compared with the now-optimized two-buffer
`add`/`neg` composition. Iteration counts and thresholds have corresponding
`PACKED_MV_BENCH_*`, `MAX_PACKED_*`, and `MIN_PACKED_*` overrides in the script.

`Grassmann4/scripts/packed_linear_codegen_guard.sh` builds `Grassmann.MV` and
audits only the exact non-boxed generated-C bodies for the four linear kernels.
It requires one final result allocation, direct unboxed Float arithmetic,
borrowed inputs, a single push per coefficient, and tail-loop codegen. It
deliberately excludes typeclass dictionary closures and boxed ABI adapters.

A local `Grassmann4/scripts/bench_guard.sh` run on 2026-06-05 passed with zero
checked correctness drift, `156.632080 ns/iter` MV rotor composition versus
`37116.177920 ns/iter` dense composition (`237.0x`), `100.820830 ns/iter` MV
sandwich versus `110933.791250 ns/iter` dense sandwich (`1100.3x`),
`868.634160 ns/iter` PGA3 motor multiplication, and `793.880420 ns/iter`
compile-time gradient versus `8043.472080 ns/iter` finite-difference gradient
(`10.1x`).

A local `Grassmann4/scripts/packedmvbench_guard.sh` run on 2026-06-05 passed
with `0.000000` PGA3 motor-point correctness drift, `6641.300000 ns/iter` packed
motor-point transforms versus `211530.158400 ns/iter` dense transforms
(`31.9x`).

The 2026-07-09 port acceptance run also passed with zero rotor, sandwich, and
PGA3 point-transform drift. It measured `122.529580 ns/iter` for packed rotor
composition versus `38096.199170 ns/iter` dense (`310.9x`), `99.087500 ns/iter`
for packed sandwich transforms versus `114705.108330 ns/iter` dense (`1157.6x`),
`438.934170 ns/iter` for packed PGA3 motor multiplication, and
`4340.383400 ns/iter` for packed PGA3 motor-point transforms versus
`412131.550000 ns/iter` dense (`95.0x`).

The 2026-07-09 packed-linear acceptance run had zero L1 drift and measured
`93.865084 ns/iter` addition versus `339.517418 ns/iter` boxed (`3.617x`),
`84.626166 ns/iter` negation versus `299.504500 ns/iter` boxed (`3.539x`), and
`84.537666 ns/iter` scalar multiplication versus `294.006500 ns/iter` boxed
(`3.478x`). Direct subtraction measured `91.165830 ns/iter` versus
`161.609580 ns/iter` for optimized `add`/`neg` composition (`1.773x`). The
generated-C shape guard passed add, sub, neg, and smul, including an unboxed
`double` scalar through the smul loop.

See `docs/PackedMVPerformance.md` for the focused PGA3 motor-point profiling
commands and a current process-level `time -l` footprint snapshot.

## Correctness Gates

The main property-test executable exposes focused gates for the core
representations:

```bash
lake exe propertytests packed-reference
lake exe propertytests mv-dispatch
lake exe propertytests pga-point-cloud
lake exe propertytests sparse-reference
lake exe propertytests truncated-reference
lake exe propertytests repr
lake exe propertytests stress
lake exe propertytests
lake exe fixedkerneltests
lake exe fatdottests
lake exe pga3kerneltests
```

Local runs on 2026-06-05 passed the sparse, truncated, representation
conversion, and high-dimensional stress gates. The sparse gate checks R3,
PGA3, and CGA3 `MultivectorS` operations against dense references for
arithmetic, products, involutions, grade projections, grade-projector
identities, and `GAlgebra` helpers. The truncated gate checks PGA3 null-basis
squares and R3/PGA3/CGA3 grade-2 truncated `GAlgebra` operations against dense
references. The representation gate checks dense/sparse round-trips for all
three signatures. The stress gate runs exact R4/R5 basis, wedge, rotor,
contraction, Hodge, determinant, composition, and R3 cross-product anchors.

## Testing Against Grassmann.jl

Run the automated oracle guard from the outer repository root:

```bash
lake exe oracletests
```

This is optional and requires Julia plus the repository's Grassmann.jl
environment. The launcher uses the current outer repository root and inherited
environment; override `GRASSMANN_REPO_ROOT`, `JULIA`, or `JULIA_DEPOT_PATH` for
nonstandard launch locations.

## Native C ABI

`include/grassmann/cabi.h` defines the versioned PGA3 ABI using caller-owned
fixed `double` buffers. It does not expose Lean objects. From the outer root,
build the shared library and run the C/C++ headers, runtime initialization,
foreign-thread, layout, transform, ownership-stress, symbol, and timing smoke:

```bash
Grassmann4/scripts/cabi_smoke.sh
```

Call `grassmann_initialize_v1` once before use. Foreign worker threads must pair
`grassmann_thread_initialize_v1` and `grassmann_thread_finalize_v1`. The Lean
runtime remains alive for the process lifetime; there is deliberately no
process-global shutdown API. Packed mask order and semantic channel aliases are
documented in the header.

The 2026-07-09 ABI acceptance run passed both header probes, the exported-symbol
audit, a foreign-thread call, layout checks, and 100,000 iterations / 500,000
consuming calls of ownership stress. Informational boundary timings were
`14.2 ns/call` for construction/result copies and `18.8 ns/call` for packed
input/extract/result copies.

The underlying oracle checks can also be explored directly in Julia:

```julia
using Grassmann
@basis V"+++"  # R3 Euclidean

# Verify: e1*e1 = 1, e1*e2 = e12, e12*e12 = -1
v1 * v1        # 1
v1 * v2        # v12
v12 * v12      # -1

# Rotations
R = 1 + v12    # unnormalized 45° rotor
R * v1 * ~R    # rotates e1
```

## References

- David Hestenes, *New Foundations for Classical Mechanics*
- Alan Macdonald, *Linear and Geometric Algebra*
- Leo Dorst et al., *Geometric Algebra for Computer Science*
- [Grassmann.jl](https://grassmann.crucialflow.com/)

## License

MIT
