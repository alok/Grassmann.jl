import Cartan.Fiber
import Cartan.Axis
import Cartan.ProductSpace
import Cartan.Local
import Cartan.Bundle
import Cartan.Field
import Cartan.Kernel
import Cartan.Algebra
import Cartan.Parameters
import Cartan.Slice
import Cartan.Show

/-!
# Cartan: tensor fields over discretized manifolds

Lean port of the core of Michael Reed's Cartan.jl 0.4.16 (`src/Cartan.jl`, `src/topology.jl`,
`src/quotient.jl`, `src/fiber.jl`): sections of trivial bundles whose base is a structured grid
(with boundary gluings from MeshTopology) or a simplex mesh, and whose fibers are Grassmann
algebra elements. Semantics, citations and the Julia defect list: `docs/port-notes/cartan-core.md`;
the Julia oracle is `oracle/cartan/gen.jl` (`Tests/Cartan`).

```lean
open Cartan Grassmann
-- Julia: t = TensorField(0:0.25:2); sin(t) + t
def t := TensorField.ofAxis (Axis.colon 0 0.25 2)
#eval (t.sin + t).get 2
-- Julia: v = (x -> Chain(x[1], x[2], 1.0)).(TensorField(ProductSpace(0:0.5:1.5, 0:0.25:1)))
def g := GridBundle.ofSpace (.ofAxes #v[Axis.colon 0 0.5 1.5, Axis.colon 0 0.25 1])
def v : TensorField g (Chain ℝ3 1 Float) :=
  .tabulatePoint g fun x => Chain.ofFn fun i => #[x.get! 0, x.get! 1, 1.0][i.1]!
#eval toString ((v ∧ ⋆v).localAt 5)
-- Julia: TorusParameter(60, 60)
def T := Cartan.Parameter.torus #v[60, 60]
```

## Map

| module | contents |
|---|---|
| `Cartan.Fiber` | `FlatFiber` (unboxed fiber storage), `LinearFiber`, `ShowFiber`, `FiberNorm`, `Induced` |
| `Cartan.Axis` | Julia's 1-D point vectors (`a:s:b`, `LinRange`, integer ranges, vectors), bit-exact, with Julia's lazy range arithmetic |
| `Cartan.ProductSpace` | `ProductSpace N` (lazy tensor-product grids), `AffinePoint N` |
| `Cartan.Local` | `Coordinate`, `LocalTensor` (`b ↦ f`), `LocalPrincipal` |
| `Cartan.Bundle` | `FrameBundle`/`Coordinates` classes; `GridBundle N P G` (with `QuotientTopology N`), `PointCloud`, `SimplexBundle`, `FaceBundle` |
| `Cartan.Field` | `TensorField m F` (indexed by its base `m`), constructors C1-C16, maps, coordinates, components |
| `Cartan.Algebra` | the lifted algebra: `+ - * /`, `∧ ∨ ⋅ × ⊘ ⋆ ~`, grade projections, scalar functions, norms, reductions |
| `Cartan.Parameters` | `TorusParameter` and the other parameter domains |
| `Cartan.Slice` | slices, `leaf`, `boundaryComponents`, `extract`, `variation`, re-gluing |
| `Cartan.Show` | display of fields and bases |

## Design (port notes §8)

* **The base is a type index.** `TensorField m F` stores only its fibers; binary operations
  need both operands over the same `m`, which replaces Julia's O(n) runtime `checkdomain` by
  type checking, and fibers always have the base's length (a proof field, erased).
* **Fibers are flat**: `width F` floats per point in one `FloatArray` (Julia's `Vector{Chain}`
  layout), so `+`, `-` and scaling are single loops, and Grassmann products run the fiber
  kernels point by point.
* **Julia's lazy ranges are followed**: the identity field of a range and its range arithmetic
  keep Julia's `TwicePrecision` elements, bit for bit.
* **Grid dimensions, fiber algebras and grades are types**; sizes, topology tables and metric
  values are data. Real 1-D points (`GridBundle 1 Float`) and affine grid points
  (`AffinePoint N`) are distinct types, as Julia dispatches on them.
* **No global state**: Julia's point caches and id counters are plain `id` fields.

## Julia defects fixed (port notes §8.6)

B1 (multi-dimensional `XParameter`s throw), B2/B3 (quotient `resample`), B7 (`ProductSpace` show
of a `LinRange`), B8/B9 (`Global` eltype and size: here `MetricStore`), B11 (`LocalTensor × LocalTensor`
throws), B12 (5-D `boundarycomponents`), B18 (2-D `HopfParameter`), B19 (`BallParameter()`/
`SphereParameter()` are tubes), B25 (`angle` of a complex field).

## Not modelled

Metric extensors other than the fiber algebra's own (Julia `Outermorphism` metrics) in the
Grassmann operations; integer-valued points (Julia `ProductSpace(0:2)` has `Int` points, here
`Float`); non-product N-D point arrays (Julia `TensorField(a, b)` with a matrix-valued `a`);
`MultilinearBundle`, `VolumeBundle`, `FiberProductBundle`, `HomotopyBundle` and `TimeParameter`;
`PrincipalFiber`; `orbit`/`Limit`/`SequenceArray` integration; interpolation (`t(x)`), which
belongs to the grid stage.
-/
