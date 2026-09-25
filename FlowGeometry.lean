import FlowGeometry.Param
import FlowGeometry.Solve
import FlowGeometry.Types
import FlowGeometry.Eval
import FlowGeometry.Base
import FlowGeometry.Airfoil
import FlowGeometry.NACA
import FlowGeometry.Mesh
import FlowGeometry.Plot

/-!
# FlowGeometry

Lean port of `chakravala/FlowGeometry.jl` (v0.1.5, `395ab65`): geometry for computational fluid
dynamics with Grassmann and Cartan elements. Airfoil profiles (NACA 4-, 5-, 6-, 6A-series camber
lines, the 4-digit and modified thickness families, circular and parabolic arcs), their assembly
into airfoils (American and British conventions, symmetric and double arcs, the Joukowski map),
the `NACA"…"` designation grammar, and the meshing helpers (structured triangulations, the Rakich
stretched C-mesh, polyhedra and sphere subdivision, a convex hull, the 3-D wing surface). See
`docs/port-notes/applied-misc.md` §1.2, §2.2, §3.2, §4.2, §8.

| module | Julia | contents |
|---|---|---|
| `Param` | type parameters | `Num`: Julia's `Int`-or-`Float64` parameters (they print differently) |
| `Types` | `Profile{P}`, `Airfoil{p}` | `Profile`/`Airfoil` (mutual: `UpperArc` wraps an airfoil), `Joukowski`, Julia type strings |
| `Solve` | Grassmann `\` | Cramer's rule with wedge products (`composite.jl:706-736`) |
| `Eval` | `profiles.jl` | coefficient fits, `Eval` (a profile's precomputed coefficients), values and slopes |
| `Base` | `interval`, Cartan `gradient` | sample axes, range slicing, the 1-D gradient of arcs |
| `Airfoil` | `airfoils.jl` | sampled profiles, surfaces, the closed outline, points, Joukowski |
| `NACA` | `@NACA_str` | the four designation patterns, `NACA!"2412"` |
| `Mesh` | `FlowGeometry.jl` | triangulations, Rakich, polyhedra, sphere, `rectcirc`, edge loops, hull, wing, `decsg` data |
| `Plot` | `ext/` | the data of the Makie/UnicodePlots recipes and gallery figures W1-W4 |

```lean
open FlowGeometry
-- Julia: N = NACA"2412"; fiber(complex(N))            (299 samples, LE → TE → LE)
#eval (NACA!"2412").complex.get 1
-- Julia: profile(ClarkY{12,150}()), profileslope(NACA4{24,150}(), 0.3)
#eval (Profile.clarkYDefault 12 150).field.get 75
#eval (Profile.naca4 24 150).slope 0.3
-- Julia: wing(NACA"6511"), initrakich()
#eval (wing (NACA!"6511")).data.size
#eval (initrakich).1.top.elements
```

## Design

* **Parameters are data, samples are types.** Julia keeps every shape parameter in the type and
  lets `@pure`/`@generated` fold the coefficient fits at compile time. Here the parameters are
  constructor arguments (`Num` keeps `12` and `12.0` apart for Julia's type strings), and
  `Profile.eval` computes the coefficients once into an `Eval` whose constructors hold them as
  unboxed floats. Sampled results are `Cartan.TensorField`s over the base Julia uses
  (`profile(p)` over `interval(p)`; the outline over `doubleinterval` with the 1-D torus gluing),
  so their sizes are those of their bases by construction.
* **Bit for bit.** Every expression replays Julia's operation order: `x^2`/`x^3` as products,
  `x^4` as Julia's compensated `pow_body` (unrolled), Julia's own `atan`/`sincos`/`acos`/`log`/`exp`
  (`JuliaBase`), `Complex{Bool}` arithmetic (`false * y = copysign(0, y)`), the lazy
  `TwicePrecision` ranges and their slices, and the Cramer solves through the Grassmann port's
  wedge kernels. 253 354 oracle checks in `Tests/FlowGeometry` agree exactly.
* **Hot loops** are top-level `@[specialize]` tail-recursive functions over `FloatArray`s (a `where`
  helper taking a closure is not specialized and boxes every float), write in place where the size
  is known, and use hoisted `f64!` literals.

## Julia defects (`oracle/flowgeometry/defects.toml`)

Fixed or replaced by the evident intent: `complex(::Airfoil)` needs `TorusTopology` (FG-B1);
`British` surfaces throw (FG-B2: thickness laid off perpendicular to the chord); `NACA6A` throws
below `x = 0.87437` (FG-B3: the scalar `naca6(x, 0.8, 0, 0)`); `addbound`/`airfoilbox` use
undefined globals (FG-B5: explicit bounds); `SymmetricArc`/`DoubleArc`/`British` have no
`interval` (FG-B6); `initedges(::Profile)` throws (FG-B7: Cartan's `initedges(interval(N))`);
`edgeslist!` cannot push into a `PointCloud` (FG-B8); `UpperArc` is not callable (FG-B9: `NaN`);
`wing` evaluates an unused camber field (FG-B10). Reproduced on purpose: the `ParabolicArc` slope
`t/400`, the `Modified` leading-edge row `(1,1,1,1)`, the reflexed `NACA5` fits and its slope
without `/6`, `NACA6`'s value-path `g`/`h` swap and `log(a - x)` domain error, the parser's
1- and 6A-series parameter mapping, `upper`/`lower` forcing `1 + 0im` for every `c`, `x0`, and
`rectcirc` without centre offsets.

Not ported: the MATLAB call of `decsg` (its geometry matrix is `decsgGeometry`), the
MiniQhull/TetGen stubs `cubesphere`, `spheresurf`, `spheremesh`, `cubemesh` (no Delaunay or
tetrahedral mesher in Lean yet), the unused `Chord{p,c,x0}` type, and the undefined exports `arc`,
`arcslope`, `chordedges`. UnicodePlots' braille rendering belongs to LeanPlot.

## Performance (`Tests/FlowGeometry/Bench.lean` vs `oracle/flowgeometry/bench.jl`, Apple M4 Max)

Time per call, best of 7, one thread; Julia 1.13 with FlowGeometry 0.1.5.

| per call | Julia | Lean |
|---|---|---|
| `NACA"2412"` parse (Julia: the macro body) | 4.2 µs | 0.48 µs |
| `profile(ClarkY{12,150})` | 0.79 µs | 0.86 µs |
| `profile(Thickness{12,4,150})` | 0.79 µs | 0.98 µs |
| `profile(Modified{12,64,150})` | 0.47 µs | 0.91 µs |
| `profile(NACA4{24,150})` | 0.27 µs | 0.74 µs |
| `profile(NACA6{2,150})` | 1.97 µs | 2.49 µs |
| `upper(NACA"2412")` | 3.70 µs | 3.59 µs |
| `complex(NACA"2412")` | 4.96 µs | 5.30 µs |
| `points(NACA"2412")` | 5.67 µs | 5.83 µs |
| `complex(Joukowski{1.1,0.1,0.1,1.0,75})` | 1.68 µs | 3.40 µs |
| `initrakich()` (101 × 51) | 20.4 ms | 1.31 ms |
| `wing(NACA"6511")` (150 × 299) | 122 µs | 245 µs |
| `convhull` (25 points) | 2.9 µs | 11.4 µs |
| sphere subdivision × 2 (20 → 320 faces) | 8.2 µs | 22.2 µs |
| `ClarkY{12}(x)` per point | 4.1 ns | 5.1 ns |

Julia folds the coefficient fits into the code; the port fits the `NACA4` cambers once per
process (a table of the 100 digit pairs) and caches the `Thickness`/`Modified` solves
(`cachedFit`). The remaining gap on the cheap profiles is the field's base: a
`Cartan.GridBundle` materializes its coordinates (about 0.5 µs for 150 points, `grid1`), where a
Julia field over a range is a thin wrapper. The Joukowski map and the airfoil surfaces are bound by
`JuliaBase`'s `sincos`/`atan`, which are slower than Julia's (docs/PERF.md). Measured lessons:
a `where` helper taking a closure is not specialized (every `Float` boxed through it: 16 → 2.5 ns
per sample once the loop is a top-level `@[specialize]` function); a `FloatArray.push` is an
out-of-line call (2.2 ns), so outputs of known size are zero arrays filled with `set!`; the general
`JuliaBase.range` spends about 1-2 µs in `rat`, so `range(0, 1, n)`, its `doubleinterval` and
`range(0, 2π, n)` are built directly (checked against it).
-/
