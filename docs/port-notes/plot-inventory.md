# Cross-package PLOT inventory: the chakravala ecosystem gallery, for the Lean port and LeanPlot

Paths are relative to `/Users/alokbeniwal/chakravala/` unless they are absolute.
`S/` is `/private/tmp/claude-502/-Users-alokbeniwal-Grassmann/c6cc2308-bfca-4b9a-ad33-d89b110132a8/scratchpad/`.
Oracle artifacts produced for this report live in `S/notes/plot_inventory_oracle/`:
* `goldens/` holds 118 files: JSON plus raw `.bin` rasters.
* `plots/` holds 95 CairoMakie reference PNGs.
* The runners are `gallery_*.jl` and `ir_helpers.jl`.

This report reuses the following sibling reports and does not repeat them:
* `S/notes/cartan-element-spectral-plot.md`: Cartan MakieExt dispatch table (§5.2), plot helpers (§4.10), UnicodePlotsExt (§2.4, §5.3).
* `S/notes/grassmann-docs.md`: Grassmann README plot examples, with goldens in `S/notes/grassmann-docs-goldens/plots/`.
* `S/notes/adapode_oracle/`: Adapode spectral, ODE and FEM goldens and plots.
* `~/leanplot-next/docs/AUDIT.md`: the LeanPlot backend plan, including Makie tick, colormap, contour and arrow algorithms.

---

## 1. Purpose and scope

This report enumerates **every figure, plot and animation** that the chakravala repositories ship or document:
* the 24 cloned repos: AbstractAnalysis, AbstractLattices, AbstractTensors, Adapode, Cartan, Clifford, DeMorgan, Dendriform, DirectSum, Fatou, FieldAlgebra, FieldConstants, FlowGeometry, Geophysics, Grassmann, Heisenberg, Leibniz, MeasureSystems, MeshTopology, PrimitiveBits, Similitude, StaticVectors, UnitSystems, Wilkinson;
* the parts scanned in each: READMEs, `docs/src/*.md`, `docs/src/assets`, `img/`, `paper/img`, `examples/`, `test/`, and every plotting extension in `ext/`.

For each figure it records:
* the source file and line, and the image path or URL;
* the **verbatim Julia code** that produces it;
* the plot kind and the numeric data it consumes;
* the **LeanPlot marks and features** it needs;
* whether it runs **today** under the Julia oracle, and which upstream bugs block it.

It then ranks the gallery by visual impact and feasibility, and gives the oracle plan for cross-testing LeanPlot against Julia/Makie.

### Scan result by repository

| Repo | Figures found | Where |
|---|---|---|
| Grassmann.jl | 16 PNGs in `paper/img/`, 13 of them referenced by the README and `docs/src/algebra.md`; 15 YouTube embeds | `README.md:63-67, 271-316`; `docs/src/algebra.md:1265-1316`; `paper/paper.tex:320-617`; `docs/src/videos.md:21-49` |
| Cartan.jl | about 25 documented interactive examples in `fiber.md`; 32 Makie and about 20 UnicodePlots blocks in `plot.md`; 16 YouTube embeds | `docs/src/fiber.md:440-962`; `docs/src/plot.md:1-534`; `docs/src/videos.md:20-50` |
| Adapode.jl | about 30 documented plot calls; `examples/chaos.jl` (17 attractor plots) | `README.md:52-368`; `examples/chaos.jl:1-46` |
| Fatou.jl | 5 PNGs in `img/`; 4 LaTeX basin images (codecogs URLs) | `README.md:58-116` |
| FlowGeometry.jl | no figures in its README; plot recipes in `ext/MakieExt.jl` and `ext/UnicodePlotsExt.jl`. Its geometry appears in the Cartan and Adapode airfoil figures. | `ext/MakieExt.jl:19-42` |
| Dendriform.jl | 1 external PNG (Tamari associahedron, from the Fatou.jl wiki), made by an external gist; plus LaTeX codecogs images | `README.md:37-41` |
| Wilkinson.jl | 1 PyPlot figure function, `plot(::PolynomialComparison)` | `src/polynomial.jl:96-133` |
| MeshTopology.jl | none (README and docs only have logos and badges). Its topologies are drawn indirectly through Cartan. | – |
| Geophysics, UnitSystems, MeasureSystems, Similitude, DirectSum, AbstractTensors, Leibniz, StaticVectors, FieldAlgebra, FieldConstants, AbstractAnalysis, AbstractLattices, DeMorgan, Clifford, Heisenberg, PrimitiveBits | **none**. `rg` over all `*.md` and `*.jl` for `makie`, `unicodeplots`, `pyplot`, `lineplot`, `heatmap`, `streamplot` and `plot` finds nothing; only logos and badges. | – |
| `test/` of all repos | no plotting calls. Adapode's tests exercise `initmesh`, `refinemesh` and `adaptpoisson` without plotting (`Adapode.jl/test/runtests.jl:12-27`). | – |

Out of scope:
* **Videos.** There are 21 unique YouTube talk embeds (16 in Cartan, 15 in Grassmann, 10 shared) with no source code (§6.9). They cannot be reproduced; see the animation protocol in §4.9.
* **LaTeX formula images.** Fatou's basin sets and Dendriform's formulas are codecogs SVG renders of LaTeX, not plots. They are only reproducible as strings (Fatou `basin`, §5.2).

---

## 2. Public plotting API inventory (every plot-producing symbol in the ecosystem)

"Weak" means the method exists only when the named package extension loads. The Unicode name is the API; none of these functions have ASCII aliases, except that `vectorfield` is a `const` alias of `pointfield`.

### 2.1 Grassmann.jl

| Symbol | Signature | Semantics | file:line |
|---|---|---|---|
| `points` | `points(f::Function, r=-2π:0.0001:2π) = vector.(f.(r))` | Samples a multivector-valued curve and keeps its grade-1 part. The default gives **125,664 samples**. | `src/Grassmann.jl:68` |
| `pointfield` / `vectorfield` | `vectorfield(t, V=Manifold(t), W=V) = p -> Point(V(vector(↓(↑((V∪Manifold(t))(Chain{W,1,ptype(p)}(p.data))) ⊘ t))))` | Versor outermorphism field for Makie `streamplot`. `W` is the subspace in which the input point is read; `V` is the output restriction. `vectorfield` is `const` = `pointfield` (Grassmann.jl:311). Weak on GeometryBasics or Meshes. | `ext/GeometryBasicsExt.jl:30`, `ext/MeshesExt.jl:29`, `src/Grassmann.jl:309-311` |
| `pointfield(t, ϕ::AbstractVector)` | – | Piecewise-linear interpolation of the nodal values ϕ on a simplex mesh `t`: locate `Pi ∋ P`, then `(Pi\P)⋅ϕ[ti]`. Returns `Point(0,0)`/`Point(0,0,0)` outside the mesh. **Bug G-B2**: the 2-D fallback calls the module `GeometryBasics(0.0,0.0)`. | `ext/GeometryBasicsExt.jl:31-44` |
| `chainfield` | `chainfield(t, V=Manifold(t), W=V) = p -> V(vector(↓(↑((V∪Manifold(t))(p)) ⊘ t)))`; `chainfield(t, ϕ)` is the mesh-interpolation variant | Same as `pointfield` but returns a `Chain`. | `src/Grassmann.jl:314, 327-339` |
| `scalarfield(t, ϕ)` | – | Scalar piecewise-linear mesh interpolation. | `src/Grassmann.jl:315-326` |
| `rectanglefield(t, ϕ, nx=100, ny=nx)` | – | Evaluates `chainfield(t,ϕ)` on a regular `nx×ny` grid covering the mesh bounding box. `rectangle` builds `Chain(1.0, x, y)` points from `x' .+ im*y`. | `src/Grassmann.jl:341-348` |
| `Makie.convert_arguments(::PointBased, ::Vector{<:Chain})` | – | Converts a vector of Chains to `Point`s. | `ext/MakieExt.jl:19` |
| `Makie.lines(p::Vector{<:TensorAlgebra})` / `lines!` | – | `lines(Point.(p))`, i.e. the grade-1 coordinates. | `ext/MakieExt.jl:23-24` |
| `Makie.lines(p::Vector{<:TensorTerm})`; `lines(p::Vector{<:Chain{V,G,T,1}})` | – | `lines(value.(p))` (scalar series); 1-component Chains are plotted as scalars. | `ext/MakieExt.jl:25-28` |
| `Makie.arrows(p::Vector{<:Chain{V}}, v)` / `arrows!` | – | `arrows(Point.(↓(V).(p)), Point.(value(v)))`: origins are projected down from homogeneous coordinates. | `ext/MakieExt.jl:21-22` |
| `Makie.convert_single_argument(a::Chain)` | – | **Bug G-B3**: references an undefined `P`. | `ext/MakieExt.jl:20` |
| `LightGraphs.SimpleDiGraph(x::TensorTerm / Chain / Multivector, g=SimpleDiGraph(rank(V)))` | – | Converts the grade ≥ 2 blades of a multivector to directed edges (§4.4). The paper's graph figures use it. | `ext/LightGraphsExt.jl:19-48` |
| `graph(x, n="simplex.pdf", l=GraphPlot.circular_layout)` and `Compose.draw(img, x, l)` | – | **Commented out.** Drew `gplot(SimpleDiGraph(x), layout=l, nodelabel=1:mdims)` to a 16 cm × 16 cm PDF. The paper's `triangle-tetrahedron.png` came from this path. | `src/Grassmann.jl:430-445` |
| `vandermonde(x, y, V, grid)` (UnicodePlots) | – | Least-squares polynomial fit. Prints a UnicodePlots scatter of `(x,y)`, overlays `lineplot!` of the fitted polynomial on `grid+1` points, prints `‖ϵ‖`, and returns the coefficients. | `ext/UnicodePlotsExt.jl:19-26`; the fit is `src/composite.jl:862-885` |

### 2.2 Cartan.jl (the main plotting surface)

The full Makie dispatch table is in `cartan-element-spectral-plot.md` §5.2. The following names are the ones the gallery uses.

| Symbol | Where | Notes |
|---|---|---|
| Exported recipe stubs `linegraph, tangentbundle, normalbundle, planesbundle, arrowsbundle, spacesbundle, scaledbundle, scaledfield, scaledarrows, scaledplanes, scaledspaces, planes, spaces` (and their `!` forms), plus `graylines` | `src/Cartan.jl:911-920`; implemented in `ext/MakieExt.jl` | `scaledarrows(M, t)` scales so that arrows fill the sample spacing (§4.7). |
| `graylines(x, lw=3)`, `graylines(x, f, lw)` and `!` forms | `ext/MakieExt.jl:32-58` | `lines(x; colormap=:grays, linewidth=lw)`, then `lines!(x; color=:black, linestyle=:dash)`. |
| Makie methods on TensorFields: `lines, linesegments, scatter, text, mesh, wireframe, surface, contour, contourf, contour3d, heatmap, volume, voxels, volumeslices, streamplot, arrows, arrows2d, arrows3d` | `ext/MakieExt.jl:60-893` | Key lines: 1-D curve `lines`, colored by `speed` by default (`:171-176`); `scaledarrows` (`:371-386`); tangent-space `streamplot(M, m)` (`:520-557`); `mesh` of grid and simplex fields (`:822-874`); `surface(ScalarMap)` (`:876-891`); VolumeGrid `volume`/`contour` (`:443-451`). |
| `variation, alteration, modification` and `!` forms; `Variation` | `src/Cartan.jl:663-858` | Animation and overlay protocol (§4.9). |
| `boundarycomponents` | `src/Cartan.jl:610-661` | Used by `lines`/`mesh`/`wireframe` of 2-D and 3-D grid maps. |
| `raster(ga::Vector, R=_rectangle(3))` (weak on ColorTypes) | `ext/ColorTypesExt.jl:19-35` | Point-set rasterization to a `GrayA` image (§4.10). No documented figure. |
| UnicodePlots: `lineplot, scatterplot, polarplot, densityplot, contourplot, surfaceplot, isosurface, histogram, boxplot, spy, heatmap`, and `Base.display` overrides | `ext/UnicodePlotsExt.jl:19-78` | Terminal plots (`plot.md:417-534`). |

### 2.3 Adapode.jl (`ext/MakieExt.jl:19-80`)

The following methods are defined for `fun ∈ {Makie.lines, Cartan.graylines}` and their `!` forms:
* `fun(X::Function|VectorField, xi::Vector{<:Chain}, t=1)` builds `FlowIntegral(X, t)`. Calling `fun(ϕ::FlowIntegral, xi)` then plots the first flow line `ϕ(xi[1])` and overlays the rest. Each `ϕ(x0)` is `odesolve(InitialCondition(Flow(X,t), x0), ExplicitIntegrator{4}(2^-11))` (`src/Adapode.jl:143-203`).
* `fun(X, t::AbstractCurve, n=7)` uses `Flow(X, 0.2)` to plot the curve `t` together with n successive flow-mapped curves (`ϕt = ϕ(ϕt)`). This is a "curve transported by a flow" figure.
* `fun(X, t::Components, n)` does the same for each component.

These are not documented by an example. **Bug**: `FlowIntegral(::Vector{<:Chain})` has the typo `typoef` and an undefined `n` (`src/Adapode.jl:195-203`). The MakieExt path loops element-wise, so it avoids that method.

### 2.4 Fatou.jl

| Symbol | Signature (all keywords with defaults in `src/Fatou.jl:93-118, 203-318`) | Semantics |
|---|---|---|
| `juliafill(E; Q=:(abs2(z)), C=:((angle(z)/(2π))*n^p), ∂=π/2, n=176, N=35, ϵ=4, iter=false, p=0, x0=nothing, orbit=0, depth=1, cmap="", plane=false, disk=false)` | `:203-222` | Julia-set `Define`: the map is `(z,c)->E` and z0 is the pixel. |
| `mandelbrot(E; …C=:(exp(-abs(z))*n^p), seed=0.0+0.0im, m=0…)` | `:250-271` | Mandelbrot mode: z starts at `seed` and `c` is the pixel. `m≠0` switches on Newton mode. |
| `newton(E; C=:((angle(z)/(2π))*n^p), ϵ=0.01, m=1, …)` | `:299-318` | Newton mode. The map is `z - m f/f'`, built with symbolic REDUCE (`newton_raphson`, `src/internals.jl:9-12`). The escape test is `|f(z)| > ϵ`, i.e. iterate while not converged. |
| `fatou(K::Define[, Z])` → `FilledSet` | `:169-177` | Computes the per-pixel `(iter::UInt16, z_final)`, then `mix = C.(z_final, iter./N, p)`. |
| `basin(K, j)` → `LaTeXString` | `:335` | The j-th preimage set as LaTeX (§5.2). |
| `orbit(K::Define)` | `src/orbitplot.jl:17-21` | Cobweb plot (§4.2). The backend is PyPlot, UnicodePlots or Makie. |
| `plot(K::FilledSet; c="", bare=false)` (PyPlot) = `imshow(K; cmap, bare)` | `ext/PyPlotExt.jl:19-28` | `imshow(iter or mix, cmap, extent=bounds)` + `tight_layout`. Unless `bare`, it also calls `title(K)`, which draws the title **and the colorbar** (`:30-40`). `bare=true` therefore has no colorbar, as in the README filled-Julia image. |
| `Makie.heatmap/contour/contourf/surface/arrows(K::FilledSet; bare=false)` | `ext/MakieExt.jl:6-48` | **Dead code** (`:6-78`; orbit at `:50-78`): the weakdep is commented out in `Project.toml`, and the code uses the removed `Makie.layoutscene`. The transposes and reverses are documented in §3.3. |
| `Base.show(io, K::FilledSet)` (ImageInTerminal) | `ext/ImageInTerminalExt.jl:20-24` | Shows the ColorScheme image (default `:balance`) and prints `String(K)`. |
| `(C::ColorSchemes.ColorScheme)(K::FilledSet)` | `src/Fatou.jl:376-390` | Discrete colormap indexing (§4.1). |
| `Fatou.orbit(K::Define, z0)` (GrassmannExt) | `ext/GrassmannExt.jl:19-30` | The same iteration, over `Grassmann.Couple{V,B}` numbers. `B=im` gives complex numbers; other `B` (e.g. a Grassmann bivector) give split or dual numbers. This is a latent "hyperbolic/dual Mandelbrot" feature with no example. |

### 2.5 FlowGeometry.jl

| Symbol | file:line | Semantics |
|---|---|---|
| `Makie.lines(N::Profile)` / `lines!` | `ext/MakieExt.jl:19-20` | `lines(profile(N))` (a RealFunction, colored by speed). |
| `Makie.lines(N::Airfoil)` | `ext/MakieExt.jl:29-30` | `lines(complex(N))`: the closed outline as a 1-D complex map. **Needs** a `TorusTopology` shim (bug FG-B1). |
| `Makie.lines(N::DoubleArc)` | `ext/MakieExt.jl:31-42` | Upper surface, mean line `(real U, (imag U + imag L)/2)`, then lower surface. |
| UnicodePlots `lineplot` for the same types, plus `Base.display(::Airfoil / ::Profile)` | `ext/UnicodePlotsExt.jl:19-40` | Terminal airfoil display. |
| Geometry producers used in figures: `NACA"…"`, `upper/lower/upperlower`, `profile`, `wing`, `rectcirc`, `initrakich`, `sphere`, `icosahedron`, `cube`, `cubesphere`, `decsg` | `src/*.jl` | §4.8. |

### 2.6 Wilkinson.jl

`plot(x::PolynomialComparison)` (`src/polynomial.jl:96-133`) draws, in one PyPlot figure:
* series drawn as solid lines (`lw=0.7`) are the "(bound)" series; series with `marker="o", ms=1, ls="--"` are the "(actual)" series;
* colors: yellow for the rounded factor (only if `rxtra`), red for expand, blue for horner, green for factor, black for the original (only if `extra`);
* legend order: `["approx (bound)"?, "orignal (bound)"?, "expand (bound)", "horner (bound)", "factor (bound)", …, "expand (actual)", "horner (actual)", "factor (actual)"]` (the typo "orignal" is upstream);
* x-label: `$\log|x|,\,\Delta=%.2e$`; y-label: a long LaTeX fraction.

The package **cannot be loaded** in the oracle env: PyCall/Conda precompile fails. It also needs REDUCE and BigFloat.

---

## 3. Data representations that the figures consume

### 3.1 Cartan TensorFields

The base types and fibers are defined in the cartan-core report. Plot-relevant layout facts:

* **Grid order.** A `TensorField` over a `ProductSpace` or `GridBundle` of size `(n₁,…,n_d)` stores fibers in a Julia column-major array: index 1 varies fastest.
  * `Makie.mesh(GridBundle)` builds `Tesselation(Rect(0,0,1,1), size)`.
  * GeometryBasics quad faces `(a,b,c,d)` decompose to triangles `(a,b,c), (a,c,d)`.
  * Vertices are `vec(points)`, also column-major (GeometryBasicsExt.jl `_mesh`).
* **Parameter domains** used by the gallery (MeshTopology `src/quotient.jl:87-126`, Cartan `src/quotient.jl:19-100`):
  * `TorusParameter(n,m)`: `LinRange(0,2π,n)×LinRange(0,2π,m)`.
  * `SphereParameter(n,m)`: `LinRange(-π/2,π/2,n)×LinRange(-π,π,m)`.
  * `KleinParameter(n,m)`: `(0,2π)²`.
  * `HopfParameter()`: `(7,60,61)`, i.e. `LinRange(7π/16/7, 7π/16, 7)×LinRange(0,2π,60)×LinRange(0,4π,61)`. θ values: 0.19635, 0.392699, 0.589049, 0.785398, 0.981748, 1.178097, 1.374447.
  * `OpenParameter(n,m)`: `(0,1)²`.
  * `TorusParameter(180)` (1-D): `LinRange(0,2π,180)` with `CompactTopology`.
  * All ≥ 2-D `XParameter` constructors **throw** in current Cartan unless the oracle shim `MT.XTopology(p::ProductSpace) = MT.XTopology(PointArray(p))` is installed (cartan-core bug B1).
* **Curves** are `IntervalMap`s. `lines(curve)` colors each vertex by `speed(curve)`, a per-vertex scalar through **viridis** (`ext/MakieExt.jl:171-176`). This is the single most common styling in the ecosystem.
* **Mesh coloring**: `mesh(M, f)` with `f::Function` means `color = vec(fiber(Real(f(M))))`, a per-vertex scalar through viridis (`:844-851`).
* **Surface coloring**: `surface(SurfaceGrid)` uses `color = z` (`cartan-element-spectral-plot.md` §5.2).

### 3.2 Streamplot output (Makie `streamplot_impl`, `Makie/src/basic_recipes/streamplot.jl:134-222`)

`(arrow_pos::Vector{Point{N,Float32}}, arrow_dir::Vector{Vec{N,Float32}}, line_points::Vector{Point{N,Float32}}, arrow_colors, line_colors)`:
* `line_points` concatenates traces. For each seed and each direction `d ∈ (-1, +1)`, it pushes `NaN-point, seed`, then the traced points. Every seed therefore contributes exactly two NaN separators.
* Colors are `norm(f(x))` at each point, mapped through the colormap (default viridis) by the child `lines`.
* The arrowheads are a `scatter` with marker `:utriangle` (2-D, `markersize=15` px, rotated by `atan(dir) - π/2` in screen space). In 3D they are a `meshscatter` of a cone with `markersize = 0.2·min(widths)/min(gridsize)`.

### 3.3 Fatou raster layout

* `Rectangle(∂, n)`:
  * a scalar ∂ gives `[-∂, ∂, -∂, ∂]`, and a 2-vector gives `[a, b, a, b]`;
  * `size = (round(UInt16, (∂[4]-∂[3])/(∂[2]-∂[1])*n), n)`, i.e. (rows = y count, cols = x count) (`src/Fatou.jl:29-46`).
  * **`n` is the horizontal count.** The README's "vertical grid points" (README:35) is wrong.
* `ranges` (`:149-154`):
  * `x = range(∂[1]+0.0001, ∂[2], length=xn)`. The **+0.0001 offset** on the first x is deliberate upstream (it avoids z=0 for Newton maps). Keep it.
  * `y = range(∂[4], ∂[3], length=yn)`, i.e. **top to bottom**.
* Grid: `Ω[j,k] = x[k] + im*y[j]` (`:174-177`). Row 1 is the top edge (y = ∂[4]) and column 1 is the left edge.
* `FilledSet` fields:
  * `iter::Matrix{UInt16}` (rows × cols), with values `0..N`;
  * `set.Ω`, the final z per pixel (Complex{Float64});
  * `mix = C.(z_final, iter./N, p)` as Float64. Newton-mode NaN is possible: generalized Newton has 6 NaN pixels.
* Rendering conventions:
  * PyPlot `imshow(M, extent=[∂1,∂2,∂3,∂4])` puts row 1 at the top, so the matrix is used as is.
  * The (dead) Makie heatmap uses `reverse(transpose(M), dims=2)`, so y increases upward (`ext/MakieExt.jl:24`).
  * Contour uses `transpose(M)` with y descending.
* **Golden binary format**:
  * `goldens/<name>_iter_u16.bin` is raw little-endian UInt16, row-major (row = y from top, col = x from left);
  * `…_mix_f64.bin` is Float64 in the same layout.

### 3.4 Graph figures

* `SimpleDiGraph(rank(V))` has vertices `1..n` with `n = mdims(V)`. Edges are de-duplicated directed pairs, kept in insertion order in the goldens.
* Layout is `GraphPlot.circular_layout`: `θ_k = 2π(k-1)/n` and `pos_k = (cos θ_k, sin θ_k)`, rendered **y-down** (Compose). Vertex 1 is at the right and vertex 2 is clockwise below it (verified against `paper/img/graph-*.png`).
* Style: nodes are filled gray disks (≈ `#A9A9A9`) with centered black labels `"1".."n"`. Edges are light-gray lines (≈ `#D3D3D3`, width ≈ 4 px) with an open V arrowhead at the target.

### 3.5 Airfoil data (FlowGeometry)

* `Profile{p}` samples `interval(p) = range(0, 1, length=p)`; the NACA macro uses p = 150.
* `upper(z, r) = z + r` and `lower(z, r) = z - r` are complex vectors with the last entry forced to exactly `1+0im` (`src/airfoils.jl:47-54`).
* `complex(N)` produces **299 points**: `[U; reverse(L)[2:end]]` over `doubleinterval`. It starts at the leading edge (0,0), goes along the upper surface to the trailing edge (1,0), and returns along the lower surface to (0,0).

---

## 4. Algorithms needed to regenerate the figures

### 4.1 Fatou escape-time iteration (`src/Fatou.jl:341-364`)

```
orbit(K, z0):                       # type params M=mandel, N=newt, P=plane, D=disk
  z  := M ? K.seed : (P ? plane(z0) : z0)
  zn := 0 :: UInt16
  while (N ? Q(z,z0) > ϵ : Q(z,z0) < ϵ) && zn < K.N:
      z := F(z, z0); zn += 1        # F(z,c); c = z0 (pixel) in every mode
  return (zn, D ? disk(z) : z)
Q = abs2(z) (non-Newton); Q = abs(E(z)) (Newton, i.e. |f(z)|)
mix[j,k] = C(z_final, iter/N, p)
  C default = (angle(z)/(2π))*n^p   (juliafill, newton)
  C default = exp(-abs(z))*n^p      (mandelbrot)
  with p = 0 ⇒ n^0 = 1
plane(z) = 2x/(x²+(1-y)²) + i(1-x²-y²)/(x²+(1-y)²)
disk(z)  = 2x/(x²+(1+y)²) + i(x²+y²-1)/(x²+(1+y)²)
```

* **Title type** (`typeplot`, `:367`):
  * `"iter."` if `iter=true`;
  * otherwise `"roots"` if `m==1`, else `"limit"`.
* **Newton map** (REDUCE `factor` of `z - m f/f'`, current output):
  * `z^3-1`, m=1 gives `(2z^3+1)/(3z^2)`;
  * `sin(z)-1`, m=1-1im gives `((sin z - 1)(i-1) + z cos z)/cos z`.
  * Lean should hard-code these closed forms, or differentiate a small expression AST. Bit-exactness needs the same operation order (§8.4).
* **ImageInTerminal/ColorScheme coloring** (`:376-390`):
  * iteration mode: `C[ceil(Int, len(C)/(max(iter)+1) * (iter+1))]` (1-based index into the scheme);
  * otherwise `get(C, nonan(mix))`, which clamps to [0,1] and maps NaN to 0.
* **PyPlot coloring**: matplotlib `imshow` with vmin/vmax = data extrema, linear normalization, and the named cmap:
  * `gnuplot` (filled Julia), `gist_earth` (Mandelbrot), `jet` (Newton), `cubehelix` (generalized Newton);
  * default is `viridis`.

### 4.2 Cobweb orbit (`src/orbitplot.jl:23-54`, plotting in `ext/PyPlotExt.jl:42-72`)

```
x      = range(bi[1], bi[2], length=incr)          # incr = n (147 in README)
N[:,1] = x;  N[:,t+1] = f.(N[:,t]) for t=1..depth # f = z -> F(z, 0)
N2[1]  = x0; N2[t+1] = f(N2[t]) for t=1..orb
cobweb (3·orb rows): for each k:
  (N2[k], N2[k]), (N2[k], N2[k+1]), (N2[k+1], N2[k+1])   # rows 1:3:end, 2:3:end, 3:3:end
xlim = bi[1:2]; ylim = [min(1.07·min(N[:,2]), 0), max(1.07·max(N[:,2]), 0)]
```

Series, in legend order:
1. `y=x`: black dashed.
2. `ϕ(x)`: C0 blue.
3. `(x_n, ϕ(x_n))`: red cobweb.
4. `ϕ^k(x)` for k = 2..depth: `lw=1`, colors C1, C2, ….
5. `ϕ(x_{0:orb})`: N2 plotted against `range(bi[1], bi[2], length=orb+1)`, gray dotted with x markers, `lw=1`. Note that this is a time series stretched across the x range.

### 4.3 Grassmann conformal curves and versor fields

The math is in grassmann-docs.md §README. Summary:
* A curve is `f(t) = ↓(exp(bivector(t)) >>> ↑(v1+v2±v3))`, i.e. an up-projection, a sandwich (`>>>`), then a down-projection. It is sampled by `points(f)` over `-2π:0.0001:2π` and restricted by `V(2,3,4)` or `V(3,4,5)`.
* The streamplot field is `x ↦ V(vector(↓(↑x ⊘ t)))`.

### 4.4 Multivector to digraph (`ext/LightGraphsExt.jl:19-48`)

```
edges(x::TensorTerm):  ind = signbit(value(x)) ? reverse(indices(basis x)) : indices(basis x)
                        rank(x)==2 ? add_edge!(ind...) : edges(∂(x))      # recurse through the boundary
edges(x::Chain{V,G}):  for k in 1:binom(N,G) with x.v[k]≠0: B = symmetricmask(V,ib[k],ib[k])[1];
                        count_ones(B)≠1 && edges(x.v[k]*getbasis(V,B))
edges(x::Multivector):  same for grades 2..N (offset binomsum(N,i))
```

Results (golden `grassmann_paper_graphs.json`):

| Figure | Input | Edges |
|---|---|---|
| graph-1 | `v12+v34` | 1→2, 3→4 |
| graph-2 | `v14+v24+v34` | 1→4, 2→4, 3→4 |
| graph-3 | `∂v124+v34 = v12 - v14 + v24 + v34` | 1→2, **4→1**, 2→4, 3→4 |
| triangle-tetrahedron | `v123 + !v123 = v123 + v4567` | 1→2, 3→1, 2→3, then all 12 ordered pairs of {4,5,6,7}, rendered as double-headed arrows |

These match the paper PNGs exactly.

### 4.5 Makie streamplot (exact port target, `streamplot.jl:134-222`)

```
res  = to_ndim(gridsize, last)                 # (10,10) on a 3-D Rect → (10,10,10)
mask = trues(res); r_i = LinRange(min_i, max_i, res_i+1); dt = Float32(stepsize)
φ = (golden 1.618…, 1.324717957244746, 1.2207440846057596)[N]; a_i = φ^(-i)
ind = 0; n_points = 0
while n_points < prod(res)·min(1, density):
  c_i = clamp(ceil(Int, ((0.5 + a_i·ind) mod 1)·res_i), 1, res_i); ind += 1
  if mask[c]:
     x0 = r_i[1] + (c_i - 0.5)·step(r_i); v = f(x0)
     push arrow (x0, v/|v|, color(v)); mask[c]=false; n_points+=1
     for d in (-1, +1):
        x = x0; n = 1; push NaN, x0
        while x ∈ rect && n < maxsteps:
           v = f(x); x = x + d·dt·v/|v|       # fixed-length normalized Euler step (Float32 dt)
           x ∉ rect → break
           idx = searchsortedlast.(r, x); if idx ≠ current cell: (mask[idx] false → break); mask[idx]=false; n_points+=1
           push x (color |v|); n += 1
```

* Defaults: `gridsize=(32,32,32)`, `stepsize=0.01`, `maxsteps=500`, `density=1`, `color=norm`, `arrow_size = 15` px in 2-D.
* `f` receives `Point{N,Float64}` built from Float64 ranges; `line_points` are converted to Float32.
* Goldens hold the exact outputs for the ecosystem's own fields (§9).

**Tangent-space streamplot** (`Cartan ext/MakieExt.jl:520-557`), called as `streamplot(M, m)` for a surface M and a parameter-space field m:
* If M is embedded in 3-D, it streamplots `p ↦ Point(m(p)₁, m(p)₂, 0)` over the parameter box × `[-1e-15, 1e-15]`, with `arrow_size = 0.2·√(surfacearea(M)/∏w)·min(w)/min(gs)`. It then sets `transform_func = p ↦ Point(M(p))`, so every traced point is pushed through the embedding.
* LeanPlot needs a **transform hook** on the stream polyline, i.e. `map M` over the points.

### 4.6 Contour levels (Makie `contours.jl:124-128, 137-212`)

* `levels::Int = n` gives levels `zmin + k·dz` for k = 1..n, with `dz = (zmax-zmin)/(n+1)`. The default is n = 5.
* 2-D isolines use Contour.jl marching squares in `canonical_line_order`, with NaN separators.
* 3-D `contour(volume)` is a **volume render**:
  * `isorange = 0.1·min level gap` (or `0.1·(max-min)` for a single level);
  * a transfer colormap of N = clamp(ceil(2.5(max-min)/isorange), 100, 4096) entries is transparent except within ±isorange of a level;
  * `alpha` applies there.
  * **CairoMakie draws nothing for volume and 3-D contour**; the goldens' PNGs are empty axes.
  * LeanPlot should use **marching cubes**: one triangle mesh per level with the level's color at `alpha`. This is a deliberate redesign, validated by data, not pixels.

### 4.7 `scaledarrows` / `spacing` (Cartan)

* `s = spacing(M) / mean‖t‖`, where `spacing` is the mean sample-to-sample distance of the *embedded* points (`src/Cartan.jl:324-329`). For a TensorOperator, each column's mean norm is used, taking the max.
* It draws `arrows2d` or `arrows3d` with `lengthscale = s/3` (`ext/MakieExt.jl:371-386`; `argarrows(t, s/3, s/17)` forwards only the lengthscale).
* Oracle values:
  * plane-curve frames: lengthscale **0.7703017906928418** with `gridsize=(50,)`;
  * Bishop frame: **0.08885800219533839** with `gridsize=(25,)`.
* `gridsize` resamples by interpolation (`gridargs`, `src/Cartan.jl:956-982`). **Broken for 1-D curves upstream** (§8.3, bugs P1-P3).

### 4.8 FlowGeometry airfoil geometry

* **NACA macro** (`src/airfoils.jl:150-167`, p = 150): regexes are tried in the order 5-digit, 4-digit, 1-series, 6A.
  * `"6511"`: the 5-digit pattern needs a third digit 0 or 1 followed by 2 digits, so it fails. It parses as 4-digit: `American(NACA4{65}, ClarkY{11})`, i.e. 6% camber at 50% chord with 11% thickness.
  * `"4412-63"` gives `American(NACA4{44}, Modified{12,63})`.
  * `"16-012"` gives `American(NACA6{0.0}, Modified{6,12})`.
  * `"23012"` (British) and `"65A010"` **throw** (bugs FG-B2, FG-B3).
* **American convention** (thickness perpendicular to the camber line). For `x = interval`, `yc = camber(x)`, `yc' = camberslope(x)`, `yt = thickness(x)`:
  `U = x + i·yc + i·cis(atan yc')·yt` and `L = x + i·yc - i·cis(atan yc')·yt`; then `U[end] = L[end] = 1`.
* **NACA4 camber** (`src/profiles.jl:194-219`): `m = M/100`, `p = P/10`. The camber is the quadratic `C(x)·coef` whose coefficients solve `[C(p); C'(p); C(0 or 1)]ᵀ coef = (m, 0, 0)`. Coefficients with the C(0) row apply for x < p and those with the C(1) row for x ≥ p. This is the standard NACA 4-digit camber.
* **ClarkY thickness**: `5t·(Y(x)⋅a)` with `Y = (√x, x, x², x³, x⁴)` and `a = (0.2969, -0.1260, -0.3516, 0.2843, te-0.1036)`, `te = 0.0021`.
  Oracle maxima: 0012 thickness 0.06001619691023314; 4412-63 (Modified) 0.059999354156812436.
* **Joukowski** (not in docs): `z = R·cis(θ) - (f - g i)`, `w = z + b²/z`, θ ∈ `range(0, 2π, length=2p-1)` (`src/airfoils.jl:171-183`).
* **`wing(N, λ=0.7, σ=0.5)`** (`src/FlowGeometry.jl:195-217`): a 150 × 299 surface grid of a swept, tapered wing built from the upper and lower surfaces.
* **`initrakich()`** (`src/FlowGeometry.jl:103-142`): a structured C-mesh around `CircularArc{6,61}` with Rakich geometric stretching toward the wall. The stretch factor κ solves `RakichNewton` in 10 Newton steps. The mesh is 101 × 51 points with `rectangletriangles` split pattern. It needs the MeshTopology `Grassmann` patch to run.

### 4.9 Animation protocol (`src/Cartan.jl:663-858`)

* `variation(v, t, fun, fun!)` draws `fun(leaf(v,1))`, `display`s it, then for each next leaf runs `empty!(ax)` (only when `Val(true)`), `fun!(leaf)`, and `sleep(t)`.
* `variation!` / `alteration!` / `modification!` use `Val(false)`, i.e. **overlay without clearing**. This is how the Hopf figure draws 7 nested tori.
* The leaves iterate the last dimension (`variation`), dim 1 (`alteration`) or dim 2 (`modification`). With an Int `n`, the leaves are resampled at n interpolated coordinates.
* LeanPlot equivalent: `Figure → Array Figure` frame sequences (`frame_0001.png…`). The PDE solution fields (`wave*`, `heat*`, `leapfrog`) are exactly the inputs the videos animate over `t`.

### 4.10 `raster` (ColorTypesExt)

For each pixel of a 100 × 100 grid on [-3,3]² (the argument is ignored), let P = `Chain(1,x,y)`. Count the elements g with `‖P∧g‖ < δ`, where δ = ½·(pixel diagonal). Write the pixel as `GrayA(c,c)` at `out[1+ny-y, x]` (y flipped). This renders lines and points of projective geometric algebra as an implicit raster, and maps to LeanPlot's `image` DrawOp.

---

## 5. Display, labels and strings

### 5.1 Fatou titles and labels (golden `fatou_*.json` field `title`)

* The format is `String(K)` = `"f : z ↦ $(E), m = $(m), $(t)"` in Newton mode, else `"f : z ↦ $(E), $(t)"` (`src/Fatou.jl:369-372`). Oracle strings:
  * `f : z ↦ z ^ 2 + (-0.06 + 0.67im), iter.` (README interpolates `$c`)
  * `f : z ↦ z ^ 2 + c, limit`
  * `f : z ↦ z ^ 3 - 1, m = 1, iter.`
  * `f : z ↦ sin(z) - 1, m = 1 - 1im, iter.`
  * defaults: `f : z ↦ (z ^ 2 - 0.06) + 0.67im, limit`; `f : z ↦ z ^ 3 - 1, m = 1, roots`
* The PyPlot versions use LaTeX (`ext/PyPlotExt.jl:30-40`): `f:z\mapsto <latex(E)>,\, m = …, <t>`. The Newton y-label is `Fatou\,set:\,z\,↦\,z-m\,×\,f(z)\,/\,f\,'(z)`; the Makie equivalent is `"Fatou set: z ↦ z-m×f(z)/f'(z)"`. There is also a colorbar.
* Orbit title: `"x ↦ $E, IC: x₀ = $(x0), n∈0:$orb"`, e.g. `x ↦ z ^ 2 - 0.67, IC: x₀ = 1.25, n∈0:17`. The legend is shown in §4.2.
* The README PNGs render the PyPlot LaTeX, e.g. `x ↦ x² - 0.67`. LeanPlot should render plain text with Unicode superscripts; exact matching is not required.

### 5.2 Fatou `basin` LaTeX (goldens `fatou_newton_basins.json`, `fatou_generalized_newton_basins.json`)

* `j = 0`: `$D_0(\epsilon) = \left\{ z\in\mathbb{C}: \left|\,z - r_i\,\right|<\epsilon,\,\forall r_i(\,f(r_i)=0 )\right\}$`.
* `j ≥ 1`: `$\displaystyle D_j(\epsilon) = \left\{z\in\mathbb{C}:\left|\,<latex of j-fold composition> - r_i\,\right|<\epsilon,…\right\}$`.
* Current REDUCE output for j = 1 of `z^3-1` is `\left(2 z^{3}+1\right)/\left(3 z^{2}\right)`. **The README image (README:90) shows the older unfactored form** `z - (z^3-1)/(3z^2)`.
* Non-Newton sets use the suffix `\,\right|>\epsilon\right\}`.

### 5.3 Graph labels

Node labels are `"1".."n"` (`nodelabel=collect(1:mdims)`), with no title.

### 5.4 Cartan

* Figures have no titles.
* The UnicodePlots `display` override prints `typeof(t)` and then the terminal plot (`ext/UnicodePlotsExt.jl:73-78`).
* 3-D data automatically gets an `LScene` with an `axis3d` child. Every 3-D plot IR in the goldens starts with an `axis3d[text/linesegments]` entry.

---

## 6. Gallery catalogue (verbatim code, data needs, LeanPlot needs, oracle status)

### Mark and feature vocabulary

**Marks**:

| Mark | Meaning |
|---|---|
| `LINE2`/`LINE3` | Solid polyline, 2-D or 3-D. |
| `CLINE2`/`CLINE3` | Per-vertex colormapped polyline, lowering to `DrawOp.segments`. |
| `SEG` | Line segments. |
| `SCAT` | Scatter markers. |
| `TEXT` | Text. |
| `ARR2`/`ARR3` | Arrows, 2-D or 3-D. |
| `STREAM2`/`STREAM3` | Streamplot per §4.5. |
| `STREAMT` | Streamplot with an embedding transform. |
| `HEAT` | Heatmap / image. |
| `CONT` | Isolines. |
| `CONTF` | Isobands. |
| `CONT3` | Isolines placed at z = level in 3-D. |
| `ISO` | Marching-cubes isosurfaces. |
| `VOX` | Voxels. |
| `MESH2` | 2-D triangle mesh with per-vertex color. |
| `MESH3` | Shaded 3-D mesh with per-vertex colormap. |
| `SURF` | Grid surface. |
| `WIRE` | Wireframe. |
| `GRAPH` | Graph nodes plus directed edges. |

**Features**:

| Feature | Meaning |
|---|---|
| `AX2` | 2-D axis. |
| `AX3` | 3-D axis box and camera. |
| `CBAR` | Colorbar. |
| `LEG` | Legend. |
| `TITLE` | Title text. |
| `CMAP:x` | Named colormap. |
| `DASH`, `DOT` | Line styles. |
| `MK:x`, `MK:utri` | Marker shapes (x, up-triangle). |
| `SCALE` | Log or ReversibleScale axes. |
| `ASPECT` | DataAspect. |
| `LIM` | xlims!/ylims!. |
| `FACET` | Multiple axes in one figure. |
| `ANIM` | Frame sequence. |
| `HIDE` | Hidden decorations. |

The status column says **OK** if the documented code runs in the oracle env (with the XParameter shim), **OK\*** if it needs an additional oracle shim or workaround, and **BROKEN** if it fails upstream. Images marked (Makie-GL) are GLMakie screenshots and cannot be reproduced headless.

### 6.1 Grassmann.jl

**G1: plane-1..6, versor vector fields** (`README.md:271-285`; `docs/src/algebra.md:1265-1279`; `paper/paper.tex:457-506`; images `paper/img/plane-{1..6}.png`, 382×384 gray)

```julia
using Grassmann, Makie
basis"2" # Euclidean
streamplot(vectorfield(exp(π*v12/2)),-1.5..1.5,-1.5..1.5)
streamplot(vectorfield(exp((π/2)*v12/2)),-1.5..1.5,-1.5..1.5)
streamplot(vectorfield(exp((π/4)*v12/2)),-1.5..1.5,-1.5..1.5)
streamplot(vectorfield(v1*exp((π/4)*v12/2)),-1.5..1.5,-1.5..1.5)
@basis S"+-" # Hyperbolic
streamplot(vectorfield(exp((π/8)*v12/2)),-1.5..1.5,-1.5..1.5)
streamplot(vectorfield(v1*exp((π/4)*v12/2)),-1.5..1.5,-1.5..1.5)
```

* Kind: 2-D streamplot.
* Data: an analytic field on [-1.5,1.5]² evaluated by `streamplot_impl` (32 × 32 cells).
  * Arrows per figure: 202, 178, 171, 162, 201, 193.
  * Points: about 9k per figure.
* LeanPlot: `STREAM2`, `CMAP:viridis` (the paper images are grayscale), `AX2`, `HIDE` (the paper crops the axes).
* Status: OK.
* Goldens:
  * `grassmann-docs-goldens/plots/readme_plot_goldens.json` (7×7 samples of the field);
  * `streamplot_impl_plane-{1..6}.json` (exact streamlines);
  * PNGs in `grassmann-docs-goldens/plots/`.

**G2 torus / G3 helix: Riemann-sphere curves** (`README.md:287-296`; `algebra.md:1281-1290`; `paper.tex:588-602`; `paper/img/torus.png` 344×250, `helix.png` 180×255)

```julia
using Grassmann, Makie
@basis S"∞+++"
f(t) = (↓(exp(π*t*((3/7)*v12+v∞3))>>>↑(v1+v2+v3)))
lines(V(2,3,4).(points(f)))
@basis S"∞∅+++"
f(t) = (↓(exp(π*t*((3/7)*v12+v∞3))>>>↑(v1+v2+v3)))
lines(V(3,4,5).(points(f)))
```

* Kind: 3-D polyline with **125,664** points.
* LeanPlot: `LINE3`, `AX3`.
* Status: OK.
* Goldens: `readme_plot_goldens.json` keys `torus` and `helix` (41 samples). Spot values: torus(0) = (1,1,1); helix(2π) = (-1.28784, 0.58435, 40.47842).

**G4 orb / G5 wave: conformal 3-D streamplots** (`README.md:63-67, 298-302`; `algebra.md:1292-1302`; `paper.tex:533-547`; `paper/img/orb.png`, `wave.png`, the README hero image)

```julia
using Grassmann, Makie; @basis S"∞+++"
streamplot(vectorfield(exp((π/4)*(v12+v∞3)),V(2,3,4)),-1.5..1.5,-1.5..1.5,-1.5..1.5,gridsize=(10,10))
streamplot(vectorfield(exp((π/4)*(v12+v∞3)),V(2,3,4),V(1,2,3)),-1.5..1.5,-1.5..1.5,-1.5..1.5,gridsize=(10,10))
```

* Kind: 3-D streamplot. `gridsize=(10,10)` is extended to (10,10,10).
* Data: orb has 293 arrows and 24,908 points; wave has 301 arrows and 25,632 points.
* LeanPlot: `STREAM3` (cone heads → projected triangles), `AX3`.
* Status: OK.
* Goldens: `streamplot_impl_orb.json`, `streamplot_impl_wave.json`, `readme_plot_goldens.json` key `orb`.

**G6 orbit-2 / G7 orbit-4** (`README.md:304-316`; `algebra.md:1304-1316`; `paper.tex:604-617`; `paper/img/orbit-2.png` 507×550, `orbit-4.png` 675×395)

```julia
using Grassmann, Makie; @basis S"∞+++"
f(t) = ↓(exp(t*v∞*(sin(3t)*3v1+cos(2t)*7v2-sin(5t)*4v3)/2)>>>↑(v1+v2-v3))
lines(V(2,3,4).(points(f)))
f(t) = ↓(exp(t*(v12+0.07v∞*(sin(3t)*3v1+cos(2t)*7v2-sin(5t)*4v3)/2))>>>↑(v1+v2-v3))
lines(V(2,3,4).(points(f)))
```

* Kind: 3-D polyline with 125,664 points.
* LeanPlot: `LINE3`, `AX3`.
* Status: OK.
* Goldens: `readme_plot_goldens.json` keys `orbit-2`, `orbit-4`.

**G8 graph-1..3** (`paper.tex:566-586`; `paper/img/graph-{1,2,3}.png` 302×302). No code is in the paper. The intended code (from `src/Grassmann.jl:430-445` and `ext/LightGraphsExt.jl`) is:

```julia
using Grassmann, LightGraphs, GraphPlot, Compose; @basis ℝ^4
draw(PDF("g.pdf",16cm,16cm), gplot(SimpleDiGraph(v12+v34), layout=circular_layout, nodelabel=1:4))
# (b) v14+v24+v34, (c) ∂(v124)+v34
```

* Kind: directed graph drawing.
* Data: n = 4 vertices on the unit circle, with edges per §4.4.
* LeanPlot: `GRAPH` (disks + labels + arrowed edges shortened by the node radius), `HIDE`.
* Status: OK\* (edges computed by emulation; LightGraphs and GraphPlot are not installed).
* Golden: `grassmann_paper_graphs.json`. Reference PNGs are `plots/grassmann_graph-*.png`.

**G9 triangle-tetrahedron** (`paper.tex:320-329`; `paper/img/triangle-tetrahedron.png` 605×605)

```julia
using Grassmann, Compose
x = Grassmann.Algebra(ℝ^7).v123     # today: Λ(ℝ^7).v123
Grassmann.graph(x+!x)               # commented out in src/Grassmann.jl:430-445
draw(PDF("simplex.pdf",16cm,16cm),x+!x)
```

* Data: 7 vertices and 15 directed edges. The edges within {4,5,6,7} run both ways, so they are drawn as double-headed arrows.
* LeanPlot: `GRAPH`.
* Status: BROKEN as written (the API was removed). OK\* via emulation.
* Golden: `grassmann_paper_graphs.json` key `triangle-tetrahedron`.
* Note: the Multivector construction must happen at **top level**; inside a closure, compiling it hung Julia for more than 9 minutes.

**G10 vandermonde terminal plot** (`ext/UnicodePlotsExt.jl:19-26`). API only; there is no documented call. LeanPlot: `SCAT` + `LINE2`.

### 6.2 Cartan.jl `docs/src/fiber.md` interactive examples

**C1: plane curve with unit frames** (`fiber.md:442-451`)

```julia
t = TensorField(0:0.01:4*pi)
lin = Chain.(cos(t)*t,sin(t)*11+t)
lines(lin); scaledarrows!(lin,unitframe(lin),gridsize=50)
lines(arclength(lin)); lines(speed(lin)); lines(curvature(lin))
```

* Data: 1257 samples. The frames are resampled to 50 points with 2 columns each.
* LeanPlot: `CLINE2` (speed → viridis), `ARR2` (two arrow sets), `AX2`.
* Status: **BROKEN** (P1: `gridsize=50` hits `MeshTopology.resample(::AbstractVector,::Int)`, giving the `LinRange(LocalTensor)` MethodError). OK\* with `gridsize=(50,)` plus shims P2 and P3.
* Oracle values: `totalarclength = 113.54675623570898`; `arclength(lin)` at sample index 1251 (the golden keeps every 10th sample) is 112.82190703932899; `speed[1] = 12.041594612922752`.
* Goldens: `cartan_planecurve_frames.json`, `cartan_planecurve_{arclength,speed,curvature}.json`.

**C2: planecurve from curvature** (`fiber.md:452-457`)

```julia
lines(planecurve(cos(t)*t)); lines(planecurve(cos(t*t)*t)); lines(planecurve(cos(t)-t*sin(t)))
```

* LeanPlot: `CLINE2`.
* Status: OK.
* Endpoints: (3.551604065768503, 1.8623094048012847), (11.818222224682877, 0.2904720806275356), (0.898721774157712, -2.1356366584856104).
* Goldens: `cartan_planecurve_{1,2,3}.json`.

**C3: Lorenz vector field** (`fiber.md:460-468`; Adapode `README.md:54-62`)

```julia
Lorenz(s,r,b) = x -> Chain(s*(x[2]-x[1]), x[1]*(r-x[3])-x[2], x[1]*x[2]-b*x[3])
p = TensorField(ProductSpace(-40:0.2:40,-40:0.2:40,10:0.2:90))
vf = Lorenz(10.0,60.0,8/3).(p)
streamplot(vf,gridsize=(10,10))
```

* Data: the grid is **401³ = 64,481,201 samples** (about 1.5 GB of Chains in Julia). Lean should keep the field **lazy/analytic**.
* LeanPlot: `STREAM3`, `AX3`.
* Status: OK (rendered in `adapode_oracle/plots/lorenz_streamplot.png`).
* Golden: `streamplot_impl_lorenz60_analytic.json` (analytic field; 647 arrows, 640,795 points; the golden stores a prefix and checksums).

**C4: Lorenz and other ODE attractors** (`fiber.md:470-474` uses r=60; Adapode `README.md:64-68` uses **r=28**; `examples/chaos.jl`)

```julia
fun,x0 = Lorenz(10.0,60.0,8/3),Chain(10.0,10.0,10.0)
ic = InitialCondition(fun,x0,2pi)
lines(odesolve(ic,MultistepIntegrator{4}(2^-15)))
```

* LeanPlot: `CLINE3` (speed-colored), `AX3`.
* Status: OK.
* Goldens: `adapode_oracle/goldens/chaos.json` and `ode_*.json`; `plots/lorenz_{rk4,abm4}.png`.

**C5 = G2/G6/G7 variants: Riemann sphere** (`fiber.md:477-493`). The same curves over `TensorField(-2π:0.0001:2π)` via `f.(pts)`. Covered by G2-G7.

**C6: Cartan bivector streamplots over grid fields** (`fiber.md:495-509`)

```julia
basis"2"; vdom = TensorField(ProductSpace{V}(-1.5:0.1:1.5,-1.5:0.1:1.5))
streamplot(tensorfield(exp(pi*v12/2)).(vdom))     # … same 6 versors as G1
```

* Data: 31 × 31 grid fields. Streamplot evaluates them by **interpolation**, so the result differs slightly from G1.
* LeanPlot: `STREAM2`.
* Status: OK.
* Goldens: `cartan_bivector_{1..6}.json`.

**C7: conformal 3-D stream over grids** (`fiber.md:511-523`)

```julia
vdom1 = TensorField(ProductSpace{V(1,2,3)}(-1.5:0.1:1.5,-1.5:0.1:1.5,-1.5:0.1:1.5))
tf1 = tensorfield(exp((pi/4)*(v12+v∞3)),V(2,3,4)).(vdom1); streamplot(tf1,gridsize=(10,10))
# vdom2 over V(2,3,4) likewise
```

* LeanPlot: `STREAM3`.
* Status: OK.
* Goldens: `cartan_conformal_stream_{1,2}.json`.

**C8: Lie bracket fields** (`fiber.md:552-563`)

```julia
f1(x) = Chain(cos(3x[1]),sin(2x[1])); f2(x) = sin(x[1]/2)*sin(x[2])
f3(x) = Chain(cos(x[1])*cos(x[2]),sin(x[2])*sin(x[1]))
vf1 = f1.(TorusParameter(100,100)); vf2 = gradient(f2.(TorusParameter(100,100))); vf3 = f3.(TorusParameter(100,100))
lie1 = Lie[vf1,vf2]; lie2 = Lie[vf1,vf2,vf3]; streamplot(lie1); streamplot(lie2)
```

* Data: 100 × 100 torus grid.
* LeanPlot: `STREAM2`.
* Status: OK.
* Oracle: `Lie[vf1,vf2]+Lie[vf2,vf1]` = 0 exactly.
* Goldens: `cartan_lie{1,2}.json` (field sampled every 11).

**C9: circle and sphere** (`fiber.md:602-613`)

```julia
t = TensorField(0:0.001:2pi); circ = Chain.(cos(t),sin(t))
spher(x) = Chain(cos(x[2])*sin(x[1]), sin(x[2])*sin(x[1]), cos(x[1]))
sph = spher.(SphereParameter(60,60))
lines(circ); wireframe(sph)
```

* LeanPlot: `CLINE2`; `WIRE` in 3-D.
* Status: OK.
* Oracle: `surfacearea(circ) = 6.283000000652752`, matching the docs. `surfacearea(sph) = 12.538186337430929` (docs: 12.533742943601457); `sectorintegrate(sph) = 6.3e-17` (docs: 4.17791). Both follow from P19: SphereParameter's latitude domain puts the sphere on one hemisphere.
* Goldens: `cartan_circle.json`, `cartan_sphere_wireframe.json`.

**C10: link curves and linkmap meshes** (`fiber.md:649-656`)

```julia
t = TensorField(0:0.01:2pi); f(t) = Chain(cos(t[1]),sin(t[1]),0); g(t) = Chain(0,1+cos(t[1]),sin(t[1]))
lines(f.(t)); lines!(g.(t)); (linknumber(f.(t),g.(t)), 1.0)
mesh(linkmap(f.(t),g.(t)),normalnorm); mesh(unit(linkmap(f.(t),g.(t))),normalnorm)
```

* Data: the linkmap is **629 × 629 = 395,641 vertices** (about 788k triangles), so LeanPlot must rasterize or decimate for SVG.
* LeanPlot: `CLINE3`, `MESH3`.
* Status: OK.
* Oracle: `linknumber = 0.9995732313191671`.
* Goldens: `cartan_link_curves.json`, `cartan_linkmap{,_unit}_mesh.json`.

**C11: torus curvature coloring** (`fiber.md:669-680`)

```julia
torus(x) = Chain((2+0.5cos(x[1]))*cos(x[2]), (2+0.5cos(x[1]))*sin(x[2]), 0.5sin(x[1]))
tor = torus.(TorusParameter(60,60)); mesh(tor,normalnorm); mesh(tor,meancurvature); mesh(tor,gausssign)
```

* Data: 60 × 60 vertices, 3481 quads, 6962 triangles.
* LeanPlot: `MESH3` with a per-vertex scalar through viridis, default Makie shading.
* Status: OK.
* Oracle color ranges:
  * normalnorm [0.7475219940278309, 1.2452816756788567], i.e. about the area element r(R + r cos u) ∈ [0.75, 1.25];
  * meancurvature [0.6673, 1.2];
  * gausssign ±1 with sum 0.
* Goldens: `cartan_torus_{normalnorm,meancurvature,gausssign}.json`.

**C12: wiggle** (`fiber.md:682-695`)

```julia
wobble(x) = (1+0.3sin(3x[1])+0.1cos(7x[2])); wumble(x) = (3+0.5cos(x[2]))
wiggle(x) = Chain((wumble(x)+wobble(x)*cos(x[1]))*cos(x[2]), (wumble(x)+wobble(x)*cos(x[1]))*sin(x[2]), wobble(x)*sin(x[1]))
wig = wiggle.(TorusParameter(60,60)); mesh(wig,normalnorm); mesh(wig,gaussextrinsic); mesh(wig,gaussintrinsic)
```

* LeanPlot: `MESH3`.
* Status: OK.
* Oracle: gaussintrinsic range [-5.662028245059032, 5.273845754609879].
* Goldens: `cartan_wiggle_*.json`.

**C13: torus geodesic and metric curves** (`fiber.md:709-730`; Adapode `README.md:86-107`)

```julia
tormet = surfacemetric(tor); torcoef = secondkind(tormet)
ic = geodesic(torcoef,Chain(1.0,1.0),Chain(1.0,sqrt(2)),10pi)
sol = geosolve(ic,ExplicitIntegrator{4}(2^-7)); lines(torus.(sol))
@basis MetricTensor([1 1; 1 1]); solm = TensorField(tormet(sol),Chain{V}.(value.(fiber(sol))))
lines(solm); lines(arclength(solm)); lines!(arclength(sol))
```

* Data: 4022 steps, `t_last = 31.4140625`.
* Oracle arclengths: `totalarclength(sol) = 73.9785216659852`, `(solm) = 101.87550126477599`, `(torus.(sol)) = 102.0783293707203`. The metric estimate is close to the 3-D value, which is the point of the example.
* LeanPlot: `CLINE3`, `CLINE2`.
* Status: OK.
* Goldens: `adapode_torus_geodesic_{3d,param_metric,arclengths}.json`.

**C14: Klein bottle geodesic** (`fiber.md:732-750`; Adapode `README.md:109-127`)

```julia
kle = klein.(KleinParameter(100,100)); klecoef = secondkind(surfacemetric(kle))
ic = geodesic(klecoef,Chain(1.0,1.0),Chain(1.0,2.0),2pi)
lines(geosolve(ic,ExplicitIntegrator{4}(2^-7)));wireframe(kle)
```

(`klein(v,u)` is the degree-7 trigonometric Klein bottle; its full formula is in the source.)

* Data: 805 steps.
* LeanPlot: `CLINE2` (parameter path), `WIRE` in 3-D.
* Status: OK.
* Goldens: `adapode_klein_geodesic_param.json`, `adapode_klein_wireframe.json`.

**C15: upper half-plane geodesics** (`fiber.md:752-763`; Adapode `README.md:129-140`)

```julia
halfplane(x) = TensorOperator(Chain(Chain(Chain(0.0,inv(x[2])),Chain(-inv(x[2]),0.0)),Chain(Chain(-inv(x[2]),0.0),Chain(0.0,-inv(x[2])))))
z1 = geosolve(halfplane,Chain(1.0,1.0),Chain(1.0,2.0),10pi,7)   # z2..z5 with other ICs
lines(z1); lines!(z2); lines!(z3); lines!(z4); lines!(z5)
```

* LeanPlot: `CLINE2` × 5.
* Status: OK.
* Goldens: `adapode_oracle/goldens/geodesic_halfplane.json`, `plots/halfplane_geodesics.png`.

**C16: Hopf fibration** (`fiber.md:765-775`)

```julia
function stereohopf(theta,phi,psi)
    a = cos(theta)*exp((im/2)*(psi-phi)); b = sin(theta)*exp((im/2)*(psi+phi))
    Chain(imag(a),real(b),imag(b))/(1-real(a))
end
stereohopf(x) = stereohopf(x[1],x[2],x[3])
hs = stereohopf.(HopfParameter()); alteration!(hs,wireframe,wireframe!)
```

* Data: a 7 × 60 × 61 field, drawn as 7 nested tori (one wireframe per θ leaf) in the Wong palette cycle.
* LeanPlot: `WIRE` × 7 with the palette cycle, `AX3`.
* Status: OK.
* The function must be defined at top level: inside a local closure, the two-method definition overflowed the stack.
* Golden: `cartan_hopf_wireframes.json` (leaves sampled every 10).

**C17: tangent-space streamplots** (`fiber.md:778-797`)

```julia
sph = spher.(SphereParameter(60,60)); f2(x) = sin(x[1]/2)*sin(x[2]); vf2 = gradient(f2.(TorusParameter(100,100)))
streamplot(sph,vf2)
tor = torus.(TorusParameter(60,60)); f3(x) = Chain(cos(x[1])*cos(x[2]),sin(x[2])*sin(x[1])); vf3 = f3.(TorusParameter(100,100))
streamplot(tor,vf3)
```

* LeanPlot: `STREAMT` (a parameter-space streamplot mapped through the embedding, §4.5).
* Status: OK. The sphere result covers **only the z ≥ 0 hemisphere** (P19).
* Goldens: `cartan_{sphere,torus}_tangent_stream.json`.

**C18: da Rios vortex filament** (`fiber.md:800-811`; Adapode `README.md:142-149`)

```julia
start(x) = Chain(cos(x),sin(x),cos(1.5x)*sin(1.5x)/5); x1 = start.(TorusParameter(180))
darios(t,dt=tangent(fiber(t))) = hodge(wedge(dt,tangent(dt)))
sol = odesolve(darios,x1,1.0,2^-11); mesh(sol,normalnorm)
```

* LeanPlot: `MESH3` (a swept-curve surface over curve × time).
* Status: **BROKEN** (P9: `odesolve` fails with a `convert` MethodError between TensorField topology types).
* Also missing in `adapode_oracle/plots`.

**C19: Bishop frame** (`fiber.md:813-820`)

```julia
x1 = start.(TorusParameter(180)); scaledarrows(x1,bishopunitframe(x1),gridsize=25); lines!(x1,linestyle=:dash)
```

* LeanPlot: `ARR3` × 3 columns, `LINE3` + `DASH`.
* Status: **BROKEN** (P1-P3). OK\* with `gridsize=(25,)` plus shims.
* Golden: `cartan_bishop_frame.json` (lengthscale 0.08885800219533839).

**C20: eigenmodes of the disk** (`fiber.md:823-834`; Adapode `README.md:242-252`)

```julia
pt,pe = initmesh("circleg","hmax"=>0.1)           # MATLAB PDE toolbox
A,M = assemble(pt,1,1,0); using KrylovKit; yi,xi = geneigsolve((A,M),10,:SR;krylovdim=100)
amp = TensorField.(Ref(pt),xi./3); mode = TensorField.(amp,xi)        # Adapode README: TensorField.(graphbundle.(amp),xi)
mesh(mode[7]); wireframe!(pt)   # figure modes are 4,5,7,8,6,9
```

* LeanPlot: `MESH3` + `WIRE`.
* Status: needs MATLAB, so it is not reproducible as written.
* OK\* with the substitute disk mesh: `squaremesh(20)` elliptically mapped to the disk, then a dense generalized eigen-solve.
  * Eigenvalues: [-3.3e-13, 3.39900, 3.40301, 9.40589, 9.45847, 14.86744, 18.02172, 18.14709, 28.89580, 29.33791].
  * These are ≈ the Neumann values j'² = 0, 3.39 (×2), 9.33 (×2), 14.68, 17.65 (×2), 28.3.
* Goldens: `adapode_disk_eigenmode{4..9}.json`.

**C21: heat flow around an airfoil** (`fiber.md:874-895`; Adapode `README.md:333-354`)

```julia
pt,pe = initmesh(decsg(NACA"6511"),"hmax"=>0.1)
tf = solvepoisson(pt,pe,1,0,x->(x[2]>3.49 ? 1e6 : 0.0),0,x->(x[2]<-1.49 ? 1.0 : 0.0))
gtf = -gradient(tf); kf = kappa.(gtf(immersion(pe)))
tf2 = solvetransportdiffusion(gtf,kf,0.01,1/50,x->(sqrt((x[2]-0.5)^2+x[3]^2)<0.7 ? 1.0 : 0.0))
wireframe(pt); streamplot(gtf,-0.3..1.3,-0.2..0.2); mesh(tf2)
```

* LeanPlot: `WIRE` (2-D), `STREAM2` over a simplex-interpolated field, `MESH2` colored.
* Status: needs MATLAB `decsg` and `initmesh`. Not reproducible without an in-Lean triangulator. `FlowGeometry.decsg` itself only builds the geometry matrix (`src/FlowGeometry.jl:282-289`).

**C22: Poisson on a sphere-in-cube tetrahedral mesh** (`fiber.md:898-910`; Adapode `README.md:356-368`)

```julia
ps = sphere(sphere(∂(delaunay(PointCloud(sphere())))))
pt,pe = tetrahedralize(cubesphere(),"vpq1.414a0.1";holes=[TetGen.Point(0.0,0.0,0.0)])
tf = solvepoisson(pt,pe,1,0,x->(x[2]>1.99 ? 1e6 : 0.0),0,x->(x[2]<-1.99 ? 1.0 : 0.0))
streamplot(-gradient(tf),-1.1..1.1,-1.1..1.1,-1.1..1.1,gridsize=(10,10,10)); wireframe!(ps)
```

* LeanPlot: `STREAM3` + `WIRE`.
* Status: needs MiniQhull and TetGen, so it is not reproducible.

**C23: Stokes theorem on a paraboloid** (`fiber.md:932-962`)

```julia
square = TensorField(ProductSpace(-3:0.003:3,-3:0.003:3)); cube = TensorField(ProductSpace(-4:0.1:4,-4:0.1:4,-1:0.2:10))
disk = (x->float(abs(x)<3)).(square); paraboloid(x) = 9-x[1]*x[1]-x[2]*x[2]; S = graph(disk*paraboloid.(square))
F(x) = Chain(2x[3]-x[2],x[1]+x[3],3x[1]-2x[2])
mesh(S,normalnorm); scaledarrows!(S,disk*unitnormal(S),gridsize=(22,22)); streamplot!(F.(cube),gridsize=(11,11,11))
integrate(disk*(curl(F.(cube)).(S) ⋅ normal(S))); fluxintegrate(S,curl(F.(cube)),disk)
t = TensorField(0:0.001:2pi); f(t) = Chain(3cos(t[1]),3sin(t[1]),0.0); integrate(F.(f.(t)) ⋅ tangent(f.(t))); integrate(f.(t),F)
```

* Data: the documented surface has **2001² ≈ 4.0 M vertices**. The oracle coarsens it to step 0.03 (201²).
* LeanPlot: `MESH3` + `ARR3` + `STREAM3` in one axis.
* Status: the plot is OK\* (coarsened). The **flux integrals are BROKEN** (P10: `MethodError tangent(::Int,::Int,::Int)` at both h = 0.03 and h = 0.01).
* The line integral works: 56.546999999998114 ≈ 18π = 56.5487; the exact value is ∮F·ds = ∫₀^{2π} 9 dt.
* Goldens: `cartan_stokes.json`, `cartan_stokes_integrals.json`.

### 6.3 Cartan.jl `docs/src/plot.md` (Makie gallery ported to TensorFields; status from `plotmd_status.json`, 29 of 32 OK)

All blocks were run verbatim in order. Globals persist across blocks, as they do on the docs page.

| id | lines | Code essence | Kind | Status | LeanPlot |
|---|---|---|---|---|---|
| arrows2d | 15-28 | `xy = TensorField(OpenParameter(xs,ys),Chain.(us,vs))` with us = sin x cos y, vs = -cos x sin y on a 20×20 grid; black background; `arrows2d!(xy, lengthscale=0.2, color=strength)` | quiver | OK | `ARR2` color-mapped, background color |
| arrows3d | 31-38 | `ps = OpenParameter(-5:2:5,…)`, `ns = 0.1*Chain(p2,p3,p1)`; `arrows3d(…, shaftcolor=:gray, tipcolor=:black, align=:center)` | 3-D quiver | OK | `ARR3` |
| arrows3d_lengths | 40-46 | `color = norm.(ns), lengthscale=1.5` | 3-D quiver | OK | `ARR3` |
| contour | 52-65 | `cos(x)sin(y)` on 100×100; `contour!(xyz)`; `contour!(xyz, levels=-1:0.1:1)` | isolines | OK | `CONT` |
| contour_himmelblau | 66-76 | Himmelblau, `levels = 10.0.^range(0.3,3.5,length=10)`, `labels=true`, `colormap=:hsv`, `ReversibleScale(x^(1/10))` | labeled isolines | OK | `CONT` + labels + `SCALE` + `CMAP:hsv` |
| contour_curvilinear | 77-98 | `mesh(TensorField(GridBundle(Chain.(xs,ys)),zs); shading=NoShading)` + orange labeled `contour!` | curvilinear | **BROKEN** (`Mesh(::GridBundle{PointMatrix})` has no method) | `MESH2` + `CONT` |
| contour3d | 104-118 | `√(x²+y²)` cone; `contour3d!(±xyz, linewidth=2, color=:blue2/:red2)` | 3-D isolines | OK | `CONT3` |
| contour3d_levels | 119-125 | explicit levels ±(.025:0.05:.475) | 3-D isolines | OK | `CONT3` |
| contour_volume_and_contour3d | 127-143 | `contour!(TensorField(rrr, cos x+cos y+cos z))` (21³) + `contour3d!(2-D, levels=10)` | volume contour + 3-D isolines | OK (volume is blank in CairoMakie) | `ISO` + `CONT3`, `FACET` |
| contour_isorange_alpha | 144-153 | `contour!(…, isorange=0.04)`; `contour!(field, data3d, alpha=0.05)` | volume | **BROKEN** (Makie compute-graph `:converted_3`) | `ISO` |
| contourf | 159-170 | `contourf!(TensorField(ProductSpace(x,y)), xyz; levels)` | isobands | **BROKEN** (FieldError: Array has no field v) | `CONTF` |
| heatmap_centers | 176-188 | `ProductSpace([1,2,4,7,11],[6,7,9,12,16])`, values `reshape(1:25,5,5)` + white scatter at the centers | irregular heatmap | OK | `HEAT` (center→edge rule) + `SCAT` |
| heatmap_colorbar | 190-201 | `sin(x*y)` 100×100 + `Colorbar(fig[:,end+1], hm)` | heatmap | OK | `HEAT` + `CBAR` |
| heatmap_logscale | 202-214 | `x = 10.0.^(1:0.1:4)`, asinh ReversibleScale on colors and x axis | heatmap | OK | `HEAT` + `SCALE` |
| linesegments | 224-236 | `ys = sin(TensorField(1:0.2:10))`; three copies with `linewidth=5`, color range | segments | OK | `SEG` |
| mesh_polar3d | 242-252 | `rs=1:10`, `thetas=0:10:360`, `(r cosθ, r sinθ, sin r cosθ)`; `mesh(xyz, TensorField(xyz,zs))` | 3-D mesh | OK | `MESH3` |
| mesh_polar2d | 253-256 | same, 2-D positions | 2-D mesh | OK | `MESH2` |
| scatter | 266-272 | `TensorField(xs, 0.5 sin xs)`, 30 points | scatter | OK | `SCAT` |
| scatter_colored | 273-280 | `color=1:30, markersize=range(5,30,length=30), colormap=:thermal` | scatter | OK | `SCAT` + `CMAP:thermal` |
| streamplot_point2 | 290-293 | `v(x)=Point2f(x[2],4x[1])` on (-2..2)² | stream | OK | `STREAM2` |
| streamplot_fitzhugh_nagumo | 294-310 | FHN `(e,s,y,b) = (0.1,0,1.5,0.8)` on `OpenParameter(-1.5:0.1:1.5,…)`, `colormap=:magma` | stream | OK | `STREAM2` + `CMAP:magma` |
| streamplot_colorfunction | 311-313 | `color = p -> RGBAf(p..., 0, 1)` | stream | OK | `STREAM2` with a color function |
| surface | 319-327 | `cos(x)sin(y)` 100×100 | surface | OK | `SURF` |
| surface_mesh_polar | 328-339 | the docs reuse `xy` from the mesh section | mesh | OK | `MESH2` |
| surface_mesh_polar_noshading | 340-344 | `shading=NoShading` | mesh | OK | `MESH2` |
| volume_contour_abs2 | 350-356 | `contour(abs2(OpenParameter(r,r,r)), alpha=0.5)`, `r=LinRange(-1,1,100)` | volume contour | OK (blank) | `ISO` |
| volume_iso | 357-360 | `volume(cube*(cube.>1.4), algorithm=:iso, isorange=0.05, isovalue=1.7)` | isosurface | OK (blank) | `ISO` |
| volume_indexedabsorption | 361-371 | `1+min(|x|,|y|,|z|)` on (-5:5)³, 6-color colormap, `absorption=5` | volume | OK (blank) | out of scope, or `VOX` approximation |
| voxels_cube_with_holes | 377-388 | `voxels(cube_with_holes, is_air = x -> !(1.65<=x<=1.75))` | voxels | OK | `VOX` |
| voxels_chunk3 | 389-393 | `OpenParameter(3,3,3)`, values 1:27, `gap=0.33` | voxels | OK\* (needs the XParameter shim, B2) | `VOX` |
| voxels_chunk8 | 394-403 | 8³, `colorrange=(65,448)`, `colorscale=log10`, `lowclip=:red`, `highclip=:orange`, `colormap=[:blue,:green]` | voxels | OK\* | `VOX` + clip colors |
| wireframe_sinc | 409-415 | `sinc(√(X²+Y²)/π)` on (-8:0.5:8)²; `wireframe(graph(xyz), color=:black)` | wireframe | OK | `WIRE` |

The UnicodePlots section (`plot.md:417-534`) has about 20 terminal plots: lineplot, scatterplot with log scales and markers, histogram, boxplot, densityplot, contourplot, polarplot, heatmap, surfaceplot and isosurface. UnicodePlots is not in the env, so none of them was run. Optional LeanPlot targets: histogram, boxplot and polar axes (none is in the current LeanPlot plan).

### 6.4 Adapode.jl README and examples

| id | Source | Code | Kind | Status / golden |
|---|---|---|---|---|
| A1 chaos | `examples/chaos.jl:10-45` | `lines(odesolve(F(params...), Chain(10.0,10.0,10.0)))` for Lorenz(10,28,8/3), Lorenz(10,60,8/3), DiskDynamo(14.625,1,5), and Rössler(1/5,1/5,c) with c ∈ {2.4,3.5,4.0,4.23,4.3,5.0,5.7}; also (0,0,12), (0,0,25), (0.343,1.82,9.75); plus ChemicalKinetics and Rossler4 | `CLINE3` | 13 OK: `adapode_oracle/goldens/chaos.json` (default `odesolve` = RK4, h = 2^-15, tmax = 2π). **ChemicalKinetics BROKEN** (undefined `k5`; 8 arguments passed to a 7-parameter constructor, `:34-38`). **Rossler4 BROKEN for plotting** (4-D chain, `:40-45`). |
| A2 leapfrog 2-D | `README.md:151-169` | `leapfrog(ex,41,4,1/30)` with `ex = exp(-40((X-0.4)^2+Y^2))` on `Chebyshev(41)²`; `contour(lf,alpha=0.03)`; `surface(lf[:,:,10])` | x,y,t volume contour; surface | OK: `adapode_oracle/plots/leapfrog_{contour,surface10}.png`, `goldens/leapfrog.json` |
| A3 leapfrog 3-D | `:170-178` | `Chebyshev(31)³`, `leapfrog(ex,31,2,1/30)`, `contour(lf[:,:,:,10],alpha=0.02,levels=5)` | `ISO` | OK: `adapode_leapfrog3d_frame10.json` (size 31×31×31×61; frame 10 range [-0.5287, 0.5595]) |
| A4 1-D wave | `:184-192` | `x=TensorField(0:0.01:pi)`; `lines/surface` of `wave{dirichlet,neumann,periodic}(0*x, x*(1+cos(x)), 0.4 or 0:0.01:2pi)` | `CLINE2`, `SURF` (x × t) | OK: `adapode_oracle/plots/wave*_t0.4.png`, `wavedirichlet_surface.png`, `goldens/spectral.json` |
| A5 2-D rest wave | `:193-202` | `XY` over `(0:0.01:π)²`, `fun = exp(-100((x-1)^2+(y-0.7)^2))`, `surface(restwave{…}(2fun.(XY), 2.1 or 3.1))` | `SURF` | OK: `restwavedirichlet_2.1.png` |
| A6 3-D rest wave | `:203-212` | `(0:0.05:π)³`, `contour(restwave…(2fun.(XYZ),2.1),alpha=0.2,levels=5)` | `ISO` | OK: `adapode_restwavedirichlet3d_t2.1.json` (63³; range [-0.05943, 0.07703]) |
| A7 1-D heat | `:213-221` | `x = TensorField(-1:0.01:1)`; `lines/surface` of `heat{dirichlet,neumann,periodic}(box.(x) or sin(pi*x)+2, 0.001 or 0:0.01:1)` | `CLINE2`, `SURF` | OK: `heatdirichlet_box.png`, `heatneumann_surface.png`, `heatperiodic_sin.png` |
| A8 2-D heat | `:222-226` | `surface(heatdirichlet(box.(XY),0.01/0.1))` over `(-1:0.01:1)²` | `SURF` | OK (not yet rendered; covered by the spectral goldens) |
| A9 3-D heat | `:227-231` | `contour(heatdirichlet(box.(XYZ),0.05/0.5),alpha=0.03)` over `(-1:0.05:1)³` | `ISO` | OK: `adapode_heatdirichlet3d_t0.05.json` (41³; center 0.49895944079103866) |
| A10 L2 projector | `:235-240` | `L2Projector(t,f)=mesh(t,color=\(assemblemassload(t,f)...))`; `L2Projector(initmesh(0:1/5:1)[3], x->x[2]*sin(x[2]))` | 1-D mesh → colored line | OK: `adapode_oracle/plots/l2proj.png`. The README indexes `[3]`, but the oracle used `[1]`. |
| A11 eigenmodes | `:242-252` | see C20 | | |
| A12 airfoil, A13 tetra | `:333-368` | see C21, C22 | | |

### 6.5 Fatou.jl README (`README.md:58-116`; images `img/*.png`, PyPlot)

**F1: cobweb orbit** (`README.md:58-64`, `img/orbit.png` 630×470)

```julia
juliafill(:(z^2-0.67),∂=[-1.25,1.5],x0=1.25,orbit=17,depth=3,n=147) |> orbit
```

* Data: x has 147 points; N is 147 × 4; N2 has 18 entries; the cobweb has 51 × 2 entries.
  * N2 = [1.25, 0.8925, 0.126556, -0.653984, -0.242306, -0.611288, -0.296327, -0.58219, -0.331054, -0.560403, -0.355949, -0.543301, -0.374824, -0.529507, -0.389623, -0.518194, -0.401475, -0.508818].
  * ylim = [-0.7168498029649091, 1.6906].
* LeanPlot: `LINE2` × 5, `DASH`, `DOT`, `MK:x`, `LEG`, `TITLE`, `LIM`.
* Status: OK.
* Golden: `fatou_orbit.json`. Reference render: `plots/fatou_orbit.png` (matches the README image).

**F2: filled Julia set** (`README.md:66-74`, `img/filled-julia.png` 630×413)

```julia
c = -0.06 + 0.67im
nf = juliafill(:(z^2+$c),∂=[-1.5,1.5,-1,1],N=80,n=1501,cmap="gnuplot",iter=true)
plot(fatou(nf), bare=true)
```

* Data: a **1001 × 1501** UInt16 raster (1.50 M pixels). The iteration sum is 30,001,428; 177,598 pixels hit N = 80.
* LeanPlot: `HEAT` (`image`) with `CMAP:gnuplot` and extent axes, `AX2`, no title and no colorbar (`bare=true`).
* Status: OK.
* Goldens: `fatou_filled_julia.json` (+ 41×61 reduced grid), `filled_julia_{iter_u16,mix_f64}.bin`.

**F3: Mandelbrot** (`README.md:76-82`, `img/mandelbrot.png` 546×470)

```julia
mandelbrot(:(z^2+c),n=800,N=20,∂=[-1.91,0.51,-1.21,1.21],cmap="gist_earth") |> fatou |> plot
```

* Data: 800 × 800. The **mix** (iter=false) is `exp(-|z_final|)`, range [0.00283, 0.99916]; 190,154 pixels are in the set (iter = 20).
* LeanPlot: `HEAT` + `CMAP:gist_earth` + `CBAR` + `TITLE`.
* Status: OK.
* Goldens: `fatou_mandelbrot.json`, `mandelbrot_*.bin`.

**F4: Newton fractal of z³−1** (`README.md:96-104`, `img/newton.png` 564×470)

```julia
nf = newton(:(z^3-1),n=800,ϵ=0.1,N=25,iter=true,cmap="jet"); nf |> fatou |> plot; basin(nf,3)
```

* Data: 800 × 800 iteration counts. The iteration sum is 3,003,400; 748 pixels are at N and 660 at 0.
* LeanPlot: `HEAT` + `CMAP:jet` + `CBAR` + `TITLE` + y-label.
* Status: OK (the REDUCE-derived map works).
* Goldens: `fatou_newton.json`, `newton_*.bin`, `fatou_newton_basins.json`.

**F5: generalized Newton for sin(z)−1** (`README.md:106-116`, `img/generalized-newton.png` 568×470)

```julia
nf = newton(:(sin(z)-1),m=1-1im,∂=[-2π/3,-π/3,-π/6,π/6],n=500,N=33,iter=true,ϵ=0.05,cmap="cubehelix")
nf |> fatou |> plot; basin(nf,2)
```

* Data: 500 × 500; the iteration sum is 2,799,500; 6 NaN mix pixels.
* LeanPlot: `HEAT` + `CMAP:cubehelix` + `CBAR`.
* Status: OK.
* Goldens: `fatou_generalized_newton*.json`, `generalized_newton_*.bin`.

**F6: basin LaTeX** (`README.md:84-94, 101, 111, 116`). Text only; see §5.2. Default-keyword grids are in `fatou_defaults.json` (41×41 for juliafill, mandelbrot and newton).

### 6.6 FlowGeometry.jl (API-level figures, no documented images)

| id | Code | Status | Golden |
|---|---|---|---|
| W1 NACA outlines | `lines(NACA"6511")`, and likewise `"2412"`, `"0012"`, `"4412"`, `"4412-63"`, `"16-012"` | OK\* (TorusTopology shim, FG-B1). `"23012"` BROKEN (FG-B2); `"65A010"` BROKEN (FG-B3). | `flowgeometry_airfoils.json` (299 outline points each, camber, thickness), `flow_naca_*.json` |
| W2 DoubleArc, Joukowski | `lines(DoubleArc(CircularArc{6,61}(), ParabolicArc{3,61}()))`; `lines(complex(Joukowski{1.1,0.1,0.1,1.0,75}()))` | OK | `flow_doublearc.json`, `flow_joukowski.json` |
| W3 wing | `mesh(FlowGeometry.wing(NACA"6511"))`: 150 × 299 grid | OK | `flow_wing_mesh.json` |
| W4 Rakich C-mesh | `pt,pe = initrakich(); wireframe(pt); linesegments!(pe)` | OK\* (MeshTopology `Grassmann` patch) | `flow_rakich_mesh.json` |

### 6.7 Dendriform.jl

**D1: Tamari associahedron colored by grove sums** (`README.md:37-41`). The image is `https://raw.githubusercontent.com/wiki/chakravala/Fatou.jl/dendriform/grove-sum-1.png` and the code is an external gist (`fbc1b1a34adaeb7fdac93b3d488c57a4`), which is not in the repos.
* It needs the Hasse diagram of the Tamari lattice Y₄ (14 binary trees), with vertices colored by membership in `[1,2]+[2,1]` sums.
* LeanPlot: `GRAPH` (layered layout).
* Status: not reproducible from the repos; low priority.

### 6.8 Wilkinson.jl

**K1** `plot(PolynomialComparison(j))` (§2.6). The package cannot be loaded in the env (PyCall), so this is not reproducible. LeanPlot: `LINE2` × 8, `MK:circle`, `DASH`, `LEG`.

### 6.9 Videos (not reproducible)

* `Cartan.jl/docs/src/videos.md:20-50`: GOKfTbExD_Q, worMICG1MaI, hwOd6ctv67o, ltx1D0K6Nqg, EUYpqdcRGq0, 2gE0Gvw_88M, 4PH1WIRozhk, 7hlDRLEhc8o, t84X5OBb89g, C3Nlq-cuAws, E5cvRClsPwQ, 2ofvi5Wq6So, C-nGcQvWSPE, eQjDN0JQ6-s, yv3SCHdRg0c, cchGLYOphkg.
* `Grassmann.jl/docs/src/videos.md:21-49`: worMICG1MaI, hwOd6ctv67o, 7hlDRLEhc8o, t84X5OBb89g, eQjDN0JQ6-s, Anc0TBa2vJM, Z8XiFRcDNYc, 14Rf2r6i5xA, wxAHAe7qpgQ, 0ipBtidZ-F8, yv3SCHdRg0c, cchGLYOphkg, 2ofvi5Wq6So, C-nGcQvWSPE, GOKfTbExD_Q.

These are talks, with no titles or code in the repos. Animation capability is provided by §4.9.

---

## 7. Ranking: (visual impact I, feasibility F), priority = I·F

* **I** (1-5): how striking the figure is and how central it is to the ecosystem's identity.
* **F** (1-5) combines three things:
  * whether the math is portable in Lean without external solvers or mesh generators;
  * how complex the LeanPlot marks are (2-D lines/heatmap are easy; 3-D shaded mesh or streamplot is medium; volume/isosurface is hard);
  * whether the Julia oracle can produce a golden today.

| Rank | ID | Figure | I | F | P | Blocking Lean pieces | New LeanPlot pieces beyond the AUDIT plan |
|---|---|---|---|---|---|---|---|
| 1 | F2 | Filled Julia set | 5 | 5 | 25 | complex arithmetic only | `image` heatmap + gnuplot LUT (gallery LUTs dumped) |
| 2 | F3 | Mandelbrot | 5 | 5 | 25 | hypot/exp | gist_earth LUT |
| 3 | A1/C4 | Lorenz, Rössler and dynamo attractors | 5 | 5 | 25 | Adapode RK4/ABM4 on Chains | per-vertex colored 3-D polyline |
| 4 | F4 | Newton z³−1 | 5 | 4 | 20 | closed-form Newton map (or a tiny symbolic derivative) | jet LUT |
| 5 | F5 | Generalized Newton sin | 5 | 4 | 20 | complex sin/cos, Julia complex division | cubehelix LUT |
| 6 | G1/C6 | plane-1..6 versor streamplots | 4 | 5 | 20 | Grassmann exp, sandwich, 2-D | exact `streamplot_impl` |
| 7 | G2 | Riemann-sphere torus curve | 4 | 5 | 20 | conformal ↑/↓, bivector exp in ⟨∞+++⟩ | 125k-point `LINE3` |
| 8 | G6/G7 | orbit-2 / orbit-4 | 4 | 5 | 20 | same | – |
| 9 | C11 | torus colored by curvature | 5 | 4 | 20 | Cartan grid derivatives, shape operator | `MESH3` Gouraud + viridis + depth sort |
| 10 | C12 | wiggle curvature | 5 | 4 | 20 | same | – |
| 11 | C16 | Hopf fibration | 5 | 4 | 20 | complex exp; `alteration!` overlay | `WIRE` + Wong palette cycle |
| 12 | A4/A5 | spectral wave/rest-wave surfaces | 4 | 4 | 16 | FFT (Lean FFT needed) | `SURF` over (x,t) |
| 13 | F1 | cobweb orbit | 3 | 5 | 15 | trivial | legend, markers, dash/dot |
| 14 | C2 | planecurve from curvature | 3 | 5 | 15 | cumulative trapezoid integral | – |
| 15 | W1 | NACA airfoil outlines | 3 | 5 | 15 | FlowGeometry port (small) | – |
| 16 | M-fhn/M-sinc/M-heat | plot.md: FitzHugh-Nagumo stream, sinc wireframe, sin(xy) heatmap | 3 | 5 | 15 | none | – |
| 17 | G4/G5/C7 | orb and wave 3-D streamplots | 4 | 3 | 12 | Grassmann 4-D conformal | `STREAM3` (cone heads) |
| 18 | C3 | Lorenz 3-D vector-field streamplot | 4 | 3 | 12 | lazy analytic field | `STREAM3` |
| 19 | C13 | torus geodesic | 4 | 3 | 12 | Christoffel symbols + RK4 | – |
| 20 | C14 | Klein geodesic + wireframe | 4 | 3 | 12 | KleinTopology quotient | – |
| 21 | C15 | half-plane geodesics | 3 | 4 | 12 | geosolve | – |
| 22 | C10 | link number + linkmap mesh | 4 | 3 | 12 | 629² mesh | mesh decimation / raster for SVG |
| 23 | C23 | Stokes paraboloid (coarse) | 4 | 3 | 12 | graph, unitnormal, curl | multi-mark 3-D axis |
| 24 | A7/A8 | heat lines and surfaces | 3 | 4 | 12 | FFT | – |
| 25 | A2 | leapfrog 2-D surface (+ volume contour) | 4 | 3 | 12 | Chebyshev FFT Laplacian | `ISO` for the (x,y,t) contour |
| 26 | W3/W4 | wing surface, Rakich mesh | 3 | 4 | 12 | FlowGeometry port | – |
| 27 | C1 | curve with unit frames | 3 | 4 | 12 | frames + resample (fix P1-P3) | `ARR2` sets |
| 28 | C9 | circle + sphere wireframe | 2 | 5 | 10 | – | – |
| 29 | G8/G9 | paper graphs | 2 | 5 | 10 | ∂ on blades | `GRAPH` recipe |
| 30 | C8 | Lie bracket streamplots | 3 | 3 | 9 | gradient on torus grids | – |
| 31 | C19 | Bishop frame | 3 | 3 | 9 | bishopunitframe (Cartan bug noted in cartan-diffgeo) | `ARR3` |
| 32 | C17 | tangent-space streamplots | 4 | 2 | 8 | interpolation on the surface | `STREAMT` transform hook |
| 33 | C20 | disk eigenmodes (substitute mesh) | 4 | 2 | 8 | FEM assembly + generalized symmetric eigen | – |
| 34 | C18 | da Rios | 4 | 2 | 8 | fix P9 | – |
| 35 | A10 | L2 projector | 2 | 4 | 8 | 1-D FEM | – |
| 36 | M-rest | other plot.md blocks | 2-3 | 3-5 | 6-12 | – | labels on contours, log colorscale, voxels |
| 37 | A3/A6/A9 | 3-D PDE isosurfaces | 3 | 2 | 6 | FFT; marching cubes | `ISO` |
| 38 | D1 | Tamari lattice | 3 | 2 | 6 | Dendriform port + layered layout | layered graph layout |
| 39 | C21 | airfoil heat flow | 5 | 1 | 5 | 2-D mesh generator (Triangle-like) + transport FEM | – |
| 40 | C22 | sphere-cube tetra Poisson | 4 | 1 | 4 | TetGen-like mesher | – |
| 41 | K1 | Wilkinson error curves | 2 | 1 | 2 | REDUCE + BigFloat | – |

**Suggested gallery phases.**
* **Phase 1** (2-D only; no 3-D camera needed): F1-F5, G1, C2, W1, the plot.md 2-D blocks, and C9 circle.
* **Phase 2** (3-D lines and wireframes, which only need camera projection plus polyline painting): G2, G3, G6, G7, A1, C13-C16.
* **Phase 3** (shaded meshes and surfaces): C10-C12, A4, A5, A7, A8, W3, C20, C23.
* **Phase 4** (3-D streamplots, tangent-space streamplots, isosurfaces): G4, G5, C3, C17, A3, A6, A9.

---

## 8. Lean porting notes (gallery and LeanPlot co-development)

### 8.1 What becomes a type index vs a runtime value

* **Gallery identity**: `inductive GalleryId` with one constructor per figure in §6, plus a total `GalleryId.spec : GalleryId → FigureSpec`. `decide` then checks that every figure has a source citation and a golden path, the metadata being a `structure` of string literals. This costs nothing at runtime.
* **Raster sizes**: `structure Raster (rows cols : Nat) where iter : ByteArray; h : iter.size = 2*rows*cols` (UInt16 little-endian), with a `mix : FloatArray` having `mix.size = rows*cols`. The proof fields are erased. A Fatou `Rectangle` computes `rows` at runtime (it depends on ∂), so use a Σ-type `(rows cols : Nat) × Raster rows cols`.
* **Iteration counts**: `Fin (N+1)` in the spec. The implementation uses `UInt16` with the invariant `≤ N` proved once, using `omega` on the loop bound.
* **Graph vertices**: `Fin n × Fin n` edges, with `n = mdims V` taken from the Grassmann manifold index, which is a type index in the Grassmann port. Duplicate-free edge lists: `List.Nodup` proved by construction (insert-if-absent).
* **Streamplot**: stay runtime. Dimension N ∈ {2,3} can be an index (`Vec N`). Termination of the seed loop is Makie's density argument and is not easily provable; use explicit fuel `prod(res)·16`, which is never hit in practice, and record a `theorem` that the output arrays have `2·n_arrows` NaN separators.
* **Grids**: LeanPlot's `Grid2 nx ny` (size proof) matches Cartan's `TensorField` over `ProductSpace{2}` with sizes as indices. Where the Cartan port already indexes by dimension, conversion is a zero-copy reinterpretation of the FloatArray.

### 8.2 Performance hot paths and how Julia gets its speed

* **Fatou rasters** do about 30 M complex iterations for F2. Julia compiles the user expression with `SyntaxTree.genlatest` into a native closure and uses `@threads` per row (`src/Fatou.jl:357-364`); the oracle measured 3.1 s single-threaded including compilation.
  * Lean equivalent: a small expression AST (`z`, `c`, `+ − × ÷ ^n`, `sin cos exp abs abs2 angle`) compiled to a closure. Better, write the six README maps as hand-written `@[inline]` functions over unboxed `Float` pairs.
  * Use tail-recursive loops per the LeanPlot rules and `Task.spawn` per row block.
  * Expected cost is under 0.5 s.
* **`points(f)`** evaluates 125,664 conformal sandwiches in 16-dimensional (⟨∞+++⟩) or 32-dimensional (⟨∞∅+++⟩) multivector algebras. Julia relies on generated, fully unrolled products. The Grassmann Lean port must supply a specialized `exp(bivector)` and sandwich for these signatures.
* **Streamplot** needs fewer than 30k f-evaluations per 2-D figure. 3-D Lorenz needs 640k evaluations and must not materialize the 64 M-sample grid.
* **Big meshes**: linkmap has 395k vertices; Stokes at the documented resolution has 4 M. SVG output must fall back to raster (`image` DrawOp), or decimate by a step parameter.
* **ODE**: Lorenz ABM4 with h = 2^-15 over 2π takes 205,887 steps and one f-evaluation per step. The default RK4 takes 4 evaluations per step. Cheap.

### 8.3 Tricky semantics and upstream bugs (numbered; the oracle scripts install shims for the starred ones)

| # | Where | Symptom | Port decision |
|---|---|---|---|
| P1\* | `Cartan src/Cartan.jl:956-982` (`gridargs`), `MeshTopology src/MeshTopology.jl:46` | `gridsize=n` (Int) on 1-D curves calls `resample(::AbstractVector,::Int)`, which does `LinRange(LocalTensor…)` and throws MethodError. Documented calls fiber.md:447 and 818 are broken. | Resample curves by interpolation to n points (the intent). |
| P2\* | `MeshTopology.jl:45` vs typed `NTuple` methods | A 1-tuple `gridsize=(n,)` is ambiguous at every level (TensorField, GridBundle, Open/CompactTopology). | The oracle deletes the generic method. Lean has no issue. |
| P3\* | `MeshTopology src/quotient.jl:380-392` | `@generated resample(::QuotientTopology)` references `Grassmann.combo`, but MeshTopology never imports Grassmann. On Julia ≥ 1.12 the generator runs in its definition world, so a later injection cannot fix it. Every periodic-grid resample fails. | The oracle re-implements it non-generated. |
| P4\* | Cartan ≥ 2-D `XParameter` (cartan-core B1) | `TorusParameter(60,60)` etc. throw. | Shim: `XTopology(::ProductSpace)`. Implement the intended semantics. |
| P5\* | `FlowGeometry src/airfoils.jl:58` | `complex(::Airfoil)` uses `TorusTopology`, which Cartan no longer exports. | Shim `const TorusTopology = Cartan.TorusTopology`. |
| FG-B2 | `airfoils.jl:49-51, 122` (British, NACA 5-digit) | `Vector{ComplexF64} * TensorField` MethodError. | Fix: broadcast. |
| FG-B3 | `profiles.jl:329-330` (NACA6A) | `Float64 + Values{1}`, because `sum.` is applied to a scalar-returning `naca6`. | Fix. |
| FG-B4 | `airfoils.jl:114, 137` | `British{n,p}()` / `American{n,p}()` reference an undefined `Camber`. | Use `NACA4`. |
| FG-B5 | `FlowGeometry.jl:52-53` | `airfoilbox` uses undefined globals `xn,xm,yn,ym`. | Take explicit parameters. |
| P9 | fiber.md:800-811 | da Rios `odesolve` has a `convert` mismatch between TensorField topology types. | Port the intent: an ODE on curve fields. |
| P10 | fiber.md:950-951 | `integrate(disk*(curl(F.(cube)).(S) ⋅ normal(S)))` and `fluxintegrate` throw MethodError `tangent(::Int,::Int,::Int)`. | Port `curl` of a 3-D grid field and evaluation on S. The expected value is 18π. |
| P11 | plot.md:77-98, 144-153, 159-170 | Curvilinear `mesh(GridBundle{PointMatrix})` has no method; `contour!(…, data3d, alpha)` fails in the compute graph; `contourf!` hits a FieldError. | Implement the intent. |
| P12 | `Adapode examples/chaos.jl:34-45` | ChemicalKinetics: undefined `k5` and an arity mismatch. Rossler4: a 4-D curve cannot be plotted. | Fix k5 and project Rossler4 to 3-D. |
| P13 | Fatou README:35 vs `Fatou.jl:46`; `ranges:151` | `n` is horizontal; x starts at ∂[1]+0.0001. | Keep the offset for goldens. |
| P14 | `Fatou Project.toml` weakdeps; `ext/MakieExt.jl` | The Makie extension is disabled and uses the removed `layoutscene`. | PyPlot conventions (§3.3) are the reference. |
| P15 | Fatou README basin images | These show pre-`factor` REDUCE output. | Compare against current strings only if the port has a symbolic layer. |
| P16 | paper.tex:320-325 | `Grassmann.Algebra(ℝ^7)` and `graph` no longer exist. | Use `Λ(ℝ^7)` and the emulated digraph. |
| P17 | `Grassmann ext/GeometryBasicsExt.jl:21, 34` | Typo `GeometryBasis.Point`; the module is called as a function. | Fix in the port. |
| P18 | `Grassmann ext/MakieExt.jl:20` | Undefined `P` in `convert_single_argument`. | Drop. |
| P19 | `SphereParameter(n,m)`, latitude `[-π/2, π/2]` with `spher` using `sin(x[1])` | Only the z ≥ 0 hemisphere is covered, twice. `surfacearea` is 12.538186 instead of the docs' 12.533743; `sectorintegrate` ≈ 0 instead of 4.17791; tangent streamplots cover a hemisphere. | Decide: faithful mode keeps it; "doc-intent" mode uses colatitude `[0,π]`. |
| P20 | `Adapode.jl:195-203` | `typoef`, undefined `n`. | Fix. |
| P21 | Lorenz r | The Adapode README ODE uses r=28; fiber.md uses r=60. Both are documented. | Gallery includes both. |
| P22 | Eigenmodes | fiber.md `TensorField.(amp,xi)` vs Adapode `TensorField.(graphbundle.(amp),xi)`. | Use the Adapode form. |
| P23 | Wilkinson | Cannot load (PyCall). | Skip. |
| P24 | README wave/orb | 2-tuple gridsize on a 3-D streamplot is extended with its last element. | Mirror `to_ndim`. |

Oracle notes. Neither is an upstream bug, but both change oracle procedure:
* The 7-D Multivector (G9) and a two-method `stereohopf` both misbehave inside Julia closures: a compile hang and a stack overflow respectively. The oracle scripts keep them at top level.
* CairoMakie renders **volume and 3-D contour** as empty axes. Their goldens are the scalar volumes plus levels, not pixels.

### 8.4 Bit-exactness of the numerics behind the goldens

* **Polynomial Fatou maps.** `z^2+c` uses `z*z = (x*x - y*y, x*y + y*x)`; `z^3` uses `literal_pow`, i.e. `z*z*z`. `abs2 = x*x + y*y`. These are bit-exact in Lean `Float` if the same operation order is used. **Require exact equality** of the iteration rasters.
* **Newton maps** use complex division. Julia's `/(::Complex,::Complex)` is the robust Baudin-Smith scaled algorithm (`base/complex.jl`). Port it to get bit-exact results, or allow a pixel-mismatch fraction ≤ 1e-3 on boundaries.
* `abs(z)` is Julia's `hypot`, which scales with a correction. `angle` is `atan(y,x)`, and `sin`/`cos`/`exp` of Float64 are pure-Julia implementations, whereas Lean `Float.sin` calls the system libm. Use ≤ 2 ulp tolerance on `mix` values, and a pixel-mismatch tolerance for escape-time maps that use transcendentals (F5).
* **Streamplot**: Makie mixes Float64 field evaluation with Float32 `dt` and stored points. The golden stores Float32-rounded values. Comparisons:
  * exact arrow counts and NaN-separator counts;
  * points within 1e-5 absolute;
  * a trace may flip at a cell boundary, so allow ≤ 1% of seeds to differ, and compare arrow positions as sets.

### 8.5 Julia-specific material to skip or redesign

* **Skip**: PyPlot/LaTeX titles (use plain Unicode text); ImageInTerminal and UnicodePlots terminal output (optional later); GLMakie interactivity; MATLAB `decsg`/`initmesh`/`refinemesh`; KrylovKit (use a dense symmetric generalized eigen-solver, or Lanczos); TetGen and MiniQhull; the GraphPlot/Compose PDF path.
* **Redesign**:
  * volume rendering becomes marching-cubes isosurfaces;
  * `display` + `sleep` animations become frame sequences;
  * the `LScene` auto-camera becomes `Axis3` defaults (azimuth 1.275π, elevation π/8);
  * Makie `transform_func` for tangent streamplots becomes an explicit `map` over polyline points.

### 8.6 Suggested module decomposition (gallery side, depending on LeanPlot core, the Grassmann port and the Cartan port)

| Module | Content | Rough LOC |
|---|---|---|
| `Fatou/Core.lean` | `Rectangle`, ranges (with the +1e-4 offset), `Define`/`FilledSet`, escape loop, coloring functions, `typeplot`, `String` title | 350 |
| `Fatou/Expr.lean` | tiny complex-expression AST, compiler to closures, symbolic derivative for Newton (optional) | 250 |
| `Fatou/Orbit.lean` | `realOrb` cobweb data + figure builder | 120 |
| `FlowGeometry/{Profiles,Airfoils,Meshes}.lean` | NACA4/5/6/6A camber, ClarkY/Thickness/Modified thickness, American/British, Joukowski, wing, Rakich mesh | 700 |
| `Gallery/GrassmannFigs.lean` | `points`, `pointfield`/`chainfield`, G1-G7 specs | 200 |
| `Gallery/Graph.lean` | multivector → digraph (§4.4), circular layout, `GRAPH` recipe lowering to paths and text | 200 |
| `Gallery/CartanCurves.lean`, `CartanSurfaces.lean`, `CartanStream.lean` | C1-C23 figure builders, including the tangent-streamplot transform | 700 |
| `Gallery/Adapode.lean` | chaos systems, geodesics, spectral PDE figures, eigenmodes (substitute mesh) | 400 |
| `Gallery/PlotMd.lean` | the 32 plot.md ports | 450 |
| `Gallery/Main.lean` (+ `lake exe gallery`) | render everything to `docs/gallery/{id}.svg,png` + JSON IR | 150 |
| `GalleryTest/*` | load `plot_inventory_oracle/goldens`, compare per §9 | 600 |
| LeanPlot additions not in the AUDIT plan | `STREAMT` transform hook, `GRAPH` recipe, marching cubes `ISO`, `VOX`, palette-cycled `WIRE`, contour labels | 900 |
| **Total** | | **≈ 5,000** |

---

## 9. Oracle test plan

### 9.1 Runners (reproducible)

All runners are in `S/notes/plot_inventory_oracle/`:
* `julia --startup-file=no --project=S/juliaenv gallery_a_fatou_graphs.jl`: Fatou (5 README figures, defaults, orbit, basins) and paper graphs. About 2 min.
* `… gallery_b_cartan_flow.jl [ids…]`: fiber.md non-Adapode examples and FlowGeometry. It includes shims P1-P5 and the MeshTopology `Grassmann` patch.
* `julia --startup-file=no --project=S/fftenv gallery_d_adapode.jl`: geodesics, eigenmodes, 3-D PDE contours, Stokes integrals. It needs FFTW, which is only in `fftenv`.
* `… gallery_e_plotmd.jl`: all 32 plot.md blocks and `plotmd_status.json`.
* `… gallery_f_streamplot_colormaps.jl`: exact `streamplot_impl` outputs and gallery colormap LUTs.
* `ir_helpers.jl`: shared encoders. `plotir` dumps every Makie plot object (type, converted-argument summaries with min/max/sum/sample, attributes).

### 9.2 Golden files and comparison rules

| Golden | Contents | Lean comparison |
|---|---|---|
| `fatou_{filled_julia,mandelbrot,newton,generalized_newton}.json` + `.bin` | full rasters (UInt16 iter, Float64 mix, row-major, row 1 = top), ranges, histogram, center row, 61-column reduced grid, title | F2/F3: **exact** iter equality; mix within 2 ulp. F4/F5: histogram L1 ≤ 1e-3·pixels; the reduced grid must match exactly except for ≤ 3 pixels. |
| `fatou_defaults.json` | 41×41 default-keyword grids for juliafill, mandelbrot and newton | exact iter; mix within 1e-12 |
| `fatou_orbit.json` | x, N columns, N2, cobweb, xlim, ylim, legend, title | abs ≤ 1e-15 (polynomial) |
| `fatou_*basins.json` | LaTeX strings | only if a symbolic layer exists |
| `grassmann_paper_graphs.json` | edges (ordered), layout | exact |
| `streamplot_impl_*.json` (11 fields) | arrow_pos, arrow_dir, line_points (NaN = "NaN"), colors, counts | §8.4 streamplot tolerances |
| `colormaps_gallery.json` | LUTs for viridis, magma, inferno, plasma, thermal, hsv(101), twilight(510), grays(2), jet(9), gnuplot(100), gist_earth(101), cubehelix, balance, RdBu(11), turbo, plus `interpolated_getindex` probes | abs ≤ 1e-6 |
| `cartan_*.json`, `adapode_*.json`, `flow_*.json`, `plotmd_*.json` | field samples (every k-th point) + plot IR (plot types, child types, per-argument min/max/sum, sampled points, attributes such as lengthscale, colorrange and markersize) | field samples: rel 1e-9 (1e-6 after ODE/FFT); IR: same plot-type tree, same argument sizes, min/max/sum rel 1e-6 |
| scalars in goldens | linknumber, surfaceareas, totalarclengths, eigenvalues, Stokes line integral, lengthscales | rel 1e-9, except eigenvalues (substitute mesh; rel 1e-9 against the same mesh) |
| `plots/*.png` | CairoMakie references (volume and 3-D contour are blank) | SSIM ≥ 0.8 for 2-D figures (catches gross errors); no pixel test for 3-D |

### 9.3 More to dump (not done yet; suggested next oracle pass)

1. **Marching-squares isolines** of the gallery fields, via Makie `contourlines`: Himmelblau, cos·sin, and the Newton iteration raster at levels 5, 10 and 15. Compare as polyline sets (Hausdorff ≤ 1e-9).
2. **Marching-cubes references** for the `ISO` figures. Makie computes none on the CPU, so dump the volume and levels (already done). Optionally add `Meshing.jl` to a new env and dump triangle counts and areas per level.
3. **Axis3 camera** matrices for each 3-D gallery figure (AUDIT §9 row 13), so projected 2-D polylines can be compared exactly.
4. **Full-resolution Grassmann curves** (125,664 points) as `.bin` Float64 triplets, for G2, G3, G6 and G7. The existing JSON holds 41 samples.
5. **Adapode spectral surfaces** A8 (2-D heat) and all six rest-wave variants, as reduced-grid JSON.
6. **Input distributions**, beyond the documented parameters:
   * Fatou: a random c in the unit disk; N ∈ {1, 2, 35, 255}; n ∈ {1, 2, 17}; degenerate ∂ with a == b (expect a zero-size grid); `plane=true` and `disk=true` variants (the Möbius maps are untested today).
   * Streamplot: density ∈ {0.5, 1, 2} and gridsize (8,8) on the plane-k fields.
