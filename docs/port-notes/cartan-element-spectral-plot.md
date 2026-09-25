# Cartan.jl porting spec: finite elements (`element.jl`), spectral tools (`spectral.jl`), plotting and other extensions (`ext/`)

Scope: `Cartan.jl/src/element.jl` (855 LOC), `Cartan.jl/src/spectral.jl` (1105 LOC), all of `Cartan.jl/ext/` (18 files, of which `MakieExt.jl` is 893 LOC), the plotting helpers in `Cartan.jl/src/Cartan.jl:324-329,606-982`, and `docs/src/plot.md`, `docs/src/library.md`, `docs/src/videos.md`.

Source snapshot: `/Users/alokbeniwal/chakravala/Cartan.jl` at commit `02a105dcc6556b7a832cbbbd4e018a5d0399a88c` (2026-09-23), `Project.toml` version 0.4.16. The registered Cartan 0.4.16 and MeshTopology 0.1.0 in `~/.julia/packages` are byte-identical to the master clones (`diff -rq` was empty). Unless stated otherwise, a path like `element.jl:123` means `Cartan.jl/src/element.jl:123`, and `MT/element.jl:123` means `MeshTopology.jl/src/element.jl:123`.

The oracle behavior was checked in a Julia 1.13 environment. The FFT probes ran in a copy of that environment with FFTW and ToeplitzMatrices added offline (`scratchpad/fftenv`); the base environment was not changed. Probe scripts that can be reused for goldens are in the scratchpad: `probe_fem.jl`, `probe_fem2.jl`, `probe_spec.jl`, `probe_fft.jl`, `probe_fft2.jl`, `probe_makie.jl` and its output `probe_makie.out`. In this document, **[probe]** marks a value that was actually printed by Julia, not inferred from reading the code.

---

## 1. Purpose and scope

* **`element.jl`** is the finite-element layer on top of `SimplexBundle`/`FaceBundle`, which are defined in `fiber.jl` and share topology with MeshTopology.jl. It provides simplex geometry (volumes, determinants, affine frames), P1 hat-function gradients (`gradienthat`), element-to-node and node-to-element transfer (`interp`, `pretni`, `means`), a lumped load vector (`assembleload`), graph and topology queries (edges, facets, boundary, neighbors, adjacency), point location and linear interpolation on meshes, mesh construction from point/edge/triangle matrices (the MATLAB/Triangle/Delaunay formats), 1D refinement, Crouzeix-Raviart interpolation, and placement of Lagrange P_M node coordinates. The stiffness, mass and convection assemblies (`assemble`, `assemblestiffness`, and so on) are **not** here. They live in Adapode.jl and consume `volumes` and `gradienthat` from this file.
* **`spectral.jl`** contains the spectral tools on `TensorField`s over grids:
  * frequency-axis domains (`FourierSpace`, `fftspace`, `rfftspace`, `r2rspace`);
  * AbstractFFTs wrappers that swap the domain to and from frequency space;
  * discrete Laplace and Gabor transforms (`flt`, `fgt` and variants);
  * orthogonal-series transforms (`OrthogonalTransform`: Fourier cosine and sine, Chebyshev first and second kind);
  * Chebyshev collocation (points, differentiation matrix, integration vector, FFT-based derivatives);
  * periodic spectral calculus (`gradient_fft`, `integral_fft`, impulses, Toeplitz differentiation matrices);
  * Lagrange barycentric and sinc resampling;
  * Clenshaw-Curtis weights and wavenumber vectors.
* **`ext/`** holds the weak-dependency extensions:
  * **MakieExt** is the plotting semantics: which Makie primitive each field type maps to, with which colors and scale factors. It is the key input for co-developing LeanPlot.
  * **UnicodePlotsExt** provides terminal plots and overrides REPL `display`.
  * **FFTWExt** adds `dct` and `r2r` domain wrappers plus `dst`/`idst`. **ToeplitzMatricesExt** provides `derivetoeplitz`.
  * **GeometryBasicsExt** builds quad meshes for `GridBundle`s. **MeshesExt**, **DelaunayExt**, **QHullExt**, **MiniQhullExt**, **TriangulateExt**, **TetGenExt** and **MATLABExt** are mesh-ingest adapters.
  * **ColorTypesExt** is a projective-geometry rasterizer.
  * **SpecialFunctions, Elliptic, EllipticFunctions, FewSpecialFunctions and JacobiElliptic** exts are pure pointwise lifts of scalar special functions onto `TensorField`/`LocalTensor`.
* **Docs:** `plot.md` holds Makie and UnicodePlots usage examples (golden plot-IR candidates, §6). `library.md` is just `@autodocs` for module Cartan (`library.md:1-9`). `videos.md` is 16 YouTube embeds and has no technical content (`videos.md:19-51`).

---

## 2. Public API inventory

Notation: `SB` = `SimplexBundle`, `FB` = `FaceBundle`, `EB` = `ElementBundle` (the abstract supertype of SB and FB), `TF` = `TensorField`, `ST` = `SimplexTopology` (MeshTopology). The field aliases are defined at `Cartan.jl:118-148`:
* `SimplexMap` = TF over SB; `FaceMap` = TF over FB; `ScalarMap` = real TF over SB.
* `RealFunction` = real TF over a 1D interval. `PlaneCurve` and `SpaceCurve` = TF of 2- or 3-component `Chain` over an interval.
* `SurfaceGrid` and `VolumeGrid` = real TF over a 2D or 3D `RealSpace`. `ComplexMap` = complex-valued TF. `GradedField{G}` = TF of `Chain{V,G}`. `VectorField` = `GradedField{1}`.

Unicode operators in scope: `∂` (ASCII `boundary`), `∧` (ASCII `wedge`, Grassmann), `⋅` (ASCII `contraction`/`dot`), `⊕` (fiber product of domains), `↓` (drop the first basis vector, removing the homogeneous coordinate), `→` (the TF constructor), `↦` (LocalTensor constructor/show).

### 2.1 `element.jl` exports and methods

`element.jl:15-20` exports:

```
assembleload, edges, edgesindices, neighbors, gradienthat, gradientCR, gradient, interp,
submesh, detsimplex, iterable, callable, value, edgelengths, laplacian, weights, boundary,
interior, trilength, trinormals, incidence, degrees, faces, facets, adjacency, antiadjacency,
facetsigns, refinemesh, refinemesh!, select, rms, unbundle, initmeshes, totalmesh, totalmeshes
```

`element.jl:436` exports `mean, means, centroid, centroids, barycenter, barycenters, curl, curls` (from a loop). `element.jl:560` exports `interpCR`, and `element.jl:677` exports `LagrangeBundle, LagrangeBundle!`.

**Exported but undefined in Cartan [probe]:** `gradientCR`, `edgelengths`, `trilength`, `trinormals`. They are defined in Adapode (`Adapode.jl/src/element.jl:35-48`). Port them with Adapode, or drop them from Cartan's export list.

| Name | Signature(s) | Semantics | file:line |
|---|---|---|---|
| `iterpts` (internal) | `(t, f)`, `(t, f::Number)` | Values of `f` at every full point of `t`. A Number becomes a constant vector of length `totalnodes(t)`. | 24-25 |
| `iterable` | `(p::Int, f::Number)` → `range(f,f,length=p)`; `(p, f::Number)` → by `length(p)`; `(p, f::Function)` → `f.(p)`; `(p, f::AbstractVector)` → `f` | Coerces a field specification into per-point values | 26-29 |
| `callable` | `(c::Function)` → `c`; `(c)` → `x->c` | Coerces a value into a function | 30-31 |
| SB/SimplexMap call | `(m::SimplexBundle)(t::Chain)`, `(m::TF over SB)(t::Chain)` → `sinterp` | Evaluates a piecewise-linear field at an arbitrary point (§4.4) | 33-42 |
| `edgelength` (internal) | `(v)` = `value(abs(v[2]-v[1]))` | Length of a 2-point simplex | 44 |
| `volumes` | `(t::TF)`, `(t::SB)`, `(t::FB)` → FaceMap of Float64 | Unsigned simplex measure per element (§4.1) | 45-54 |
| `unbundle` | `(te::Tuple)`, `(t)` → `(fullcoordinates(t), immersion(t))`; `(t,e)` → `(fullcoords(t), immersion(e), immersion(t))`; `(g,t,e)` → `(g, …)` | Unpacks bundles into raw data | 56-59 |
| `initedges` (internal) | `(n::Int)` → ST of `[i,i+1]` for i=1..n-1; `(r::AbstractVector)` → SB | Chain topology of a 1D mesh | 61-62 |
| `initmesh` | `(r::AbstractVector)` → `(pt, pe)` | 1D mesh plus 0-simplex boundary `{1},{n}` | 63-67 |
| `initpoints`, `initpoint` (internal) | `(P::AbstractArray)`; `(P::Real)`; `@generated (P, Val(n))`; `@generated (P::Chain)` | Lift raw coordinates to homogeneous `Chain{varmanifold(n+1),1}(1.0, x...)` | 69-78 |
| `initpointsdata` (internal) | `(P, E, Val(n))` | Point matrix plus edge matrix → edge SB | 80-83 |
| `initmeshdata` (internal) | `(P, E, T, Val(n))` → `(pt, pe)` | Point, edge and element matrices (MATLAB/Triangle layout) → SB pair | 85-88 |
| `initmeshes`, `totalmesh`, `totalmeshes` | stubs | Implemented only in MATLABExt | 89-91 |
| `totalmeshdata`, `edgemeshdata` (internal) | `(P,E,T,Val(n))`; `(pt::SB, E, Val(n))` | Like `initmeshdata`, but `pe` becomes a sub-immersion of the full edge set | 92-118 |
| `argmax`, `argmin`, `rms` | `(η::TF)` | Applied to the fiber array | 120-122 |
| `maximum`, `minimum` | `(η::TF)` → `η[argmax(η)]` (a LocalTensor) | | 123-124 |
| `rms` | `(η)` = `norm(η)/sqrt(length(η))` | | 125 |
| `select` | `(η, ϵ=rms(η))` → `sort!(findall(x->x>ϵ, fiber(η)))` | Refinement marker indices | 126 |
| `refinemesh` | `(g::AbstractRange, args...)` → `(g, refine(pt), refine(pe))` | Other `g` types go through MATLABExt | 127-130 |
| `refinemesh!` | `(::AbstractRange, pt::SB, pe, η, _=nothing)` | 1D bisection of the elements in `η`, in place (§4.5) | 131-157 |
| `reducedcolumns` | `(m::FrameBundle)` | Forwards to MT | 161 |
| `SparseArrays.sparse` | `(t::FrameBundle, cols=reducedcolumns(t), np=nodes(t))` | Forwards to MT (§4.3) | 167 |
| `edges` | `(t::EB)` → `t(edges(immersion(t)))`; `(t::EB, adj)` | Unique edges (§4.3) | 179-180 |
| `faces` | `(t::EB, v::Val)`; `(t::EB, h, v::Val, g=identity)` | k-faces | 222-223 |
| `∂` / `boundary` | `(t::Tuple{EB,Vector{Int}})`, `(t::Tuple{ST,Vector{Int}})`, `(t::SB, u::Vector{Int})`, `(t::ST, u)`, `(t::EB)`, `(t::ST{N})` | Boundary complex (§4.3) | 293-308 |
| `complement` | `(t::EB)` | Elements not in the sub-immersion | 314 |
| `skeleton` | `(t::SB)` | All k-faces for k = 1..N | 318 |
| `array`, `array!` (internal) | Vector{Chain}; Vector{Values}; SubArray; SB; ST; DiscontinuousTopology; PointCloud | Dense np×mdims point matrix / nt×N index matrix, cached by bundle id (§3.4) | 324-377 |
| `submesh`, `submesh!` | `(m)`; `(m::SB)`; `(m::PointCloud)` | Point matrix **without** the homogeneous column, cached | 379-398 |
| `findfirst`, `findlast` | `(P::GradedVector{V}, M::SB)` → element index or 0 | Linear-scan point location (§4.4) | 400-413 |
| `affineframe` | `(t::SB)`; `@generated (t::FB, c=columns(topology(t)))` | Per element, edge vectors `p_i - p_1` as a TensorOperator | 415-426 |
| `detsimplex` | `(m::EB)` = `∧(m)/factorial(sdims(m)-1)` | Signed simplex volume as a pseudoscalar | 428 |
| `∧` | `(m::SB)`, `(m::FB)` | Per-element exterior product of vertices, or of edge vectors when embedded | 429-432 |
| `means`/`centroids`/`barycenters`/`curls` | `(m::EB, u)`, `(m::SB)`, `(m::FB)`, `(m::SimplexMap)` | Per-element reductions of vertex data (§4.1) | 433-451 |
| `revrot` (internal) | `(hk::TensorOperator)`, `(hk::Chain{V,1})` = `Chain{V,1}(-hk[2], hk[1])` | +90° rotation in 2D | 453-454 |
| `gradienthat` | `(t::TF, m=volumes(t))`, `(t::SB, m)`, `(t::FB, m)` → FaceMap of TensorOperator | P1 barycentric gradients per element (§4.1) | 456-471 |
| `gradient` | `(t::SimplexMap, m, g)` → nodal SimplexMap; `(t::FaceMap, m, g)` → FaceMap | P1 gradient (§4.2) | 479-487 |
| `gradient_2` (internal) | `(t::SimplexMap, m, g)`; `(t::EB, u, m, g)`; `(t::EB, u::AbstractVector{<:Chain}, m, g)` | Elementwise gradient (scalar) or Jacobian (vector) | 488-501 |
| `Laplacian` call `Δ(t::ST)` | `Diagonal(degrees(t)) - adjacency(t)` | "Graph Laplacian" in Cartan's convention (§4.3, bug B7) | 505-506 |
| `weights` | `(t::FrameBundle)` = `inv(degrees(t))`; `(t, B::SparseMatrixCSC)` | 1/degree per node | 507-508 |
| `degrees` | `(t::FB, f=nothing)`, `(t::SB, f=nothing)` → SimplexMap{Int} | Number of elements incident to each node | 512-513 |
| `assembleincidence` | `(t, f, B::SparseMatrixCSC)` = `Diagonal(iterpts(t,f))*B`; `(t, f, m=volumes(t), v=Val(false))`; `(X::FrameBundle, f, m, v)` | Scatter-add of element×node products (§4.2) | 522-526 |
| `incidence` | `(t::FrameBundle)` | **Broken:** references undefined `cols` (bug B5) | 536 |
| `assembleload` | `(t, f=1, m=volumes(t))` | Lumped P1 load vector (§4.2). **Upstream crash**, bug B1. | 546 |
| `interp` | `(t::FaceMap)` → SimplexMap; `(t::FB, args...)` | Element→node averaging (§4.2) | 550-552 |
| `pretni` | `(t::SimplexMap)` = `means(t)` | Node→element averaging | 556 |
| `interpCR` | `(pt, crfun::Function)`, `(pt, m)`, `(pt, ed, m)`, `(pt, dt::DiscontinuousTopology, ed, m::TF)` | Crouzeix-Raviart edge DOFs → discontinuous P1 nodal values (§4.6) | 560-585 |
| `edgesindices` | `(t::SB)`, `(t::SB, ed::SB)`, `(t::SB, e::FB)` | Per-element global edge ids, on a PointCloud of edge midpoints (§4.3) | 597-605 |
| `neighbors` | `(t::EB, args...)` | Forwards to MT (§4.3) | 647 |
| `facetsigns` | `(t::SB, args...)` | Forwards to MT (§4.3) | 663 |
| `LagrangeBundle`, `LagrangeBundle!` | `(pt)`, `(p,t)`; `!(p::PointCloud, t::LagrangeEdges{2})`, `{M}`, `LagrangeTriangles{2}`, `{M}`, `LagrangeTetrahedra{M}` | Places high-order node coordinates (§4.7) | 675-784 |
| imports only | `refinement, refinetriangle, refinetetrahedron` from MT | | 853 |

These are re-exported or imported from MeshTopology and used unchanged: `columns`, `vertices`, `pointset`, `antiadjacency`, `adjacency`, `edgetopology`, `facetsinterior`, `facets`, `faces`, `isedge`, `discontinuousboundary`, `assemblelocal!`, `invmap`, `findmissing`, `interior`, `facesindices`, `localedge`, `neighbor`, `facetsign`, `edgesigns`. Their semantics are in §4.3. The commented-out blocks in `element.jl` (165-174, 181-289, 309-312, 474-478, 509-520, 527-544, 589-595, 606-628, 632-673, 786-851) are verbatim copies of the MT implementations and document them.

### 2.2 `spectral.jl` exports and methods

Exports: `FourierSpace` (15); `fftspace, rfftspace, r2rspace` (31); `dst, dst!, idst, idst!` (96); `flt, bflt, rflt, brflt, iflt, irflt` (109); `fgt, bfgt, rfgt, brfgt` (164); `OrthogonalTransform, seriestransform` (202, but **`seriestransform` is undefined**); `FourierCosine, FourierSine, ChebyshevFirst, ChebyshevSecond` (203); `Chebyshev, ChebyshevMatrix, ChebyshevVector, chebyshevfft, chebyshevifft, unitpoints` (317); `resample_sinc, resample_lagrange, resample_roots` (612); `LagrangeWeights, lagrangepoints, lagrangeweights` (613); `lagrangepolynomial, rootspolynomial` (614); `fftwavenumber, rfftwavenumber, r2rwavenumber` (769); `derivetoeplitz, derivetoeplitz2` (1073); `gradient_chebyshev, gradient_chebyshevfft, laplacian_chebyshevfft` (1075); `gradient2_chebyshevfft, gradient2_toeplitz, gradient_toeplitz` (1076).

`grid.jl:17-23,1078-1082` exports these, although they are defined in `spectral.jl`: `gradient_fft, gradient_rfft, integral_fft, integral_rfft, gradient_impulse(+_fft,_rfft), integral_impulse(+_fft,_rfft), convolve, clenshawcurtis`.

The `fft`, `ifft`, `rfft`, `fftshift` and similar method extensions are **not** exported by Cartan. Users call `AbstractFFTs`/`FFTW` names. [probe: `isexported(Cartan,:fft) == false`]

| Name | Signature(s) | Semantics | line |
|---|---|---|---|
| `FourierSpace{T,F<:AbstractVector{T},G}` | fields `f::F` (frequencies), `v::G` (original physical domain) | AbstractVector of frequencies that remembers the source domain for inversion | 16-19 |
| `size`, `getindex` | on FourierSpace | Delegate to `f` | 21-22 |
| `invdim` (internal) | `(f::FourierSpace, dims=1)` = `length(f.v)`; `(f::ProductSpace, dims)` = `invdim(f.v[dims])`; `(f::AbstractVector)` = `length(f)` | Original length, needed for irfft | 23-25 |
| `isfourier` | FourierSpace → true; ProductSpace → all components; FiberBundle → of points; otherwise false | | 26-29 |
| `fftspace`, `r2rspace` | `(t::TF)`, `(x::GridBundle)`, `(x::ProductSpace{V})` | Lifts to fields, bundles and product domains | 33-39 |
| `rfftspace` | `(t::TF)`, `(x::GridBundle)`, `(x::ProductSpace{V})` = `ProductSpace{V}(rfftspace(x.v[2]), fftspace.(x.v[2:end])...)` | **Bug B11:** uses `x.v[2]` twice instead of `x.v[1]` | 40-42 |
| `r2rspace` | `(t::TF, kind)`, `(x::GridBundle, kind)`, `(x::ProductSpace, kind)` | | 43-45 |
| `GridBundle(x::FourierSpace)` | = `GridBundle(x, ClampedTopology(size(x)))` | Frequency grids are clamped/compact | 47 |
| `rfftspace` | `(N::Real, ω=1/N)` = `rfftfreq(N, N*ω)` → `ω*(0:N÷2)`; `(x::AbstractRange)` = `FourierSpace(rfftspace(length(x), 2π/(x[end]-x[1])), x)`; `(x::FourierSpace)` = `x.v`; `(x::Frequencies)` = `OneTo(length(x))` | | 48-51 |
| `fftspace` | `(x::AbstractRange)` = `FourierSpace(fftspace(length(x), 2π/(x[end]-x[1])), x)`; `(N::Real, ω=1/N)` → `ω*(0:N-1)` (§4.9.1); `(x::FourierSpace)` = `x.v`; `(x::Frequencies)` = `OneTo` | | 52-58 |
| `r2rspace` | `(N::Real, ω::Float64=1/N)` = `fftspace(N,ω)`; `(x::AbstractRange)` uses `ω = π/(x[end]-x[1])`; `(x::FourierSpace)` = `x.v`; `(N::Real, kind::Int, fs=1)` → shifted by one step when `kind ∈ (9,6,10)`; `(x::AbstractRange, kind)` → `FourierSpace(r2rspace(N, kind, (x[end]-x[1])/π), x)`; `(x::FourierSpace, kind)`; `(x::Frequencies, kind)` | | 60-71 |
| `fftshiftalias` (internal) | `(x)` = `fftshift(x) .- x[ceil(N/2)]` | Recentred frequency axis (bug B12 for even N) | 73 |
| `fftshift`, `ifftshift` | `(x::FourierSpace)`; `(t::TF)` → shifts domain **and** fiber; `(x::GridBundle)`; `(x::ProductSpace)` | | 74-82 |
| `fft, fft!, ifft, ifft!, bfft, bfft!` | `(t::TF, args...)` = `TF(fftspace(base(t)), f(fiber(t), args...))` | Domain swap, involutive (§4.9.2) | 83-85 |
| `rfft` | `(t::TF, args...)` = `TF(rfftspace(base(t)), rfft(fiber(t), args...))` | | 86-88 |
| `irfft, brfft` | `(t::TF)` = `TF(rfftspace(base(t)), f(fiber(t), invdim(points(t))))`; `(t::TF, dims)` | Recovers the original length from the FourierSpace | 89-94 |
| `dst, dst!, idst, idst!` | stubs | Implemented in FFTWExt | 97-100 |
| `flt, bflt, rflt, brflt, iflt, irflt` | `(f::TF, σ::Number)` | `flt = fft(exp(-σ t) f)`; `iflt = ifft(exp(σ t) f)`; the other variants follow the same pattern | 102-107 |
| `flt, bflt, rflt, brflt` | `(f::TF, σ::AbstractVector)` → TF over `σ ⊕ fftspace(base(f))` of size (length σ, N) | One row per σ | 110-142 |
| `iflt, irflt` | `(f::TF)` over a 2D (σ, ω) product | Average over σ of `exp(σ_i t) .* ifft(row_i)` | 144-162 |
| `fgt, bfgt, rfgt, brfgt` | `(f::TF, σ::Int, g)` → `σ = resample(points(f), σ)`; `(f::TF, σ::AbstractVector, g)` | Windowed FFT (Gabor): row i = `fft(g(t - σ_i) * f)` | 165-200 |
| `OrthogonalTransform{F,T}` | fields `f::F` (basis function `(n,x)->…`), `a::T`, `b::T` (canonical interval) | | 205-209 |
| `FourierCosine` | `OT((n,x)->cos(n*x), 0.0, π)` | | 211 |
| `FourierSine` | `OT((n,x)->sin((n+1)*x), 0.0, π)` | Note the `n+1` shift | 212 |
| `ChebyshevFirst` | `OT((n,x)->cos(n*acos(x)), -1.0, 1.0)` | | 213 |
| `ChebyshevSecond` | `OT((n,x)->(θ=acos(x); iszero(θ) ? one(θ) : sin((n+1)θ)/sin θ), -1.0, 1.0)` | **Bug B15:** returns 1 at x=1 instead of n+1 | 214 |
| OT call | `(ot)(n::Int, x)` = `ot.f(n,x)`; `(ot)(n::Int, x::TF)` = pointwise | | 216-217 |
| OT transform | `(f::OT)(g::AbstractVector, N=length(g))`; `(g::AbstractMatrix, N, M)`; 3D; 4D; 5D | Series coefficients or restoration (§4.9.6) | 219-307 |
| `FourierSpace` | `(f::OT, x::ProductSpace)`; `(f::OT, x::ProductSpace{V}, args...)`; `(f::OT, x::AbstractVector, N=length(x))` = `FourierSpace(((b-a)/interval_scale(x))*(0:N-1), x)` | Coefficient-index axis | 309-315 |
| `Chebyshev{T,A}` | fields `v::Vector{T}` (points, **ascending**), `a::A` (angles θ) | DenseVector of Chebyshev-Lobatto points | 319-322 |
| `Chebyshev` | `(N::Int)`: θ = `(π/(N-1))*(0:N-1)`, x = `-cos.(θ)`; `(x::AbstractVector)`: affine map onto `[x[1], x[end]]` | | 324-333 |
| `points`, `unitpoints`, `angle`, `getindex`, `size` | on Chebyshev | `unitpoints` maps back to [-1,1] | 335-342 |
| `ChebyshevVector` | `(x::FiberBundle)`, `(x::ProductSpace)` componentwise, `(x::AbstractVector, N=length(x))` = `vcat(0, reverse(inv(ChebyshevMatrix(x)[1:N-1,1:N-1])[1,:]))`, `(N::Int)` | Spectral quadrature weights on [-1,1] (§4.9.7) | 348-351 |
| `ChebyshevMatrix` | `(x::TF)`, `(x::Chebyshev)` = `ChebyshevMatrix(-points(x))`, `(N::Int)` (N=0 → `[0;;]`), `(x)` generic | Barycentric differentiation matrix (§4.9.7). Sign convention: bug B13. | 352-361 |
| `chebyshevfft` | `(v::TF)`, `(v::TF, i)`, `(v::AbstractVector)`, `(v::AbstractMatrix, i)`, `(v::Array3, i)` | FFT of the even extension (§4.9.7). **Bug B16:** the 3D i=3 branch uses `dims=2` in `reverse` | 363-383 |
| `chebyshevifft` | `(V::AbstractVector, U, N)`, `(V::AbstractMatrix, U, i, N, M)`, 3D | Trefethen `chebfft` back half | 385-453 |
| `chebyshevifft2` (internal) | 1D/2D/3D | Second-derivative back half (bug B14) | 455-521 |
| `resample_sinc` | `(v::AbstractVector, n)`; `(v::AbstractMatrix, n, m)`; 3D; 4D; 5D; `(v::Array{T,N}, n, Val(q))` | Whittaker-Shannon resampling (§4.9.10). **Bug B17:** typo `l.m` at line 602 in the 5D q=5 branch | 523-610 |
| `LagrangeWeights{T,W,V}` | fields `v::V` (nodes), `w::Vector{W}` (barycentric weights) | AbstractVector that shows as its nodes | 616-619 |
| `LagrangeWeights` | `(v::LagrangeWeights)`, `(v::AbstractVector)`, `(v::ProductSpace)`, `(t::PointArray)`, `(t::GridBundle)`, `(t::TF)` | Attaches weights to a domain | 621-626 |
| `lagrangepoints` | `(v)`, `(v::LagrangeWeights)`, `(v::FiberBundle)` | | 628-630 |
| `lagrangeweights` | `(v::LW)`, `(v::LW, j)`, `(v::FiberBundle[, j])`, `(v)`, `(v, j)` = `inv(prod(v_j - v_i, i≠j))` | | 632-640 |
| `resample` | `(v::LagrangeWeights, n::Int)` | | 647 |
| `lagrangepolynomial` | `(t::TF, x::AbstractVector)`, `(t::TF, x::AbstractMatrix)`, `(t::TF, x::Number)`, `(L::LW, y, x::AbstractArray)`, `(L::LW, y, x::Number)`, `(v, wy, x)` = `prod(x-v) * sum(wy ./ (x-v))` | First-form barycentric interpolation. The NaN at a node falls back to `t(x)` (§4.9.9). | 649-667 |
| `size_new` (internal) | `(Val(q), n, sizes...)` | Replaces dimension q of the size tuple by n | 675-676 |
| `resample_lagrange` | `(t::AbstractVector, n)`; `(v::AbstractMatrix, n, m::Int)`; 3D-5D; `(v::Array{T,N}, n, Val(q))` | Tensor-product Lagrange resampling | 678-754 |
| `resample_roots`, `rootspolynomial` | `(t, n)`; `(t::TF, x::AbstractArray)`; `(t::TF, x::Number)`; `(v, x::AbstractArray)`; `(v, x::Number)` = `prod(x .- v)` | Nodal polynomial ω(x) | 756-760 |
| `size`, `getindex` | on LagrangeWeights | | 762-763 |
| `convolve` | `(f::ScalarField...)` = `irfft(*(rfft.(f)...))` | Circular convolution | 767 |
| `fftwavenumber` | `(N::AbstractArray)`, `(N...)` → ProductSpace, `(N::Int)` = `vcat(0:Int((N-isodd(N))/2)-1, -Int((N+isodd(N))/2):-1)` | **Bug B10:** wrong for odd N | 770, 774, 776 |
| `rfftwavenumber` | `(N::AbstractArray)`, `(N...)`, `(N::Int)` = `0:Int((N-isodd(N))/2)` | | 771, 775, 777 |
| `r2rwavenumber` | `(N::AbstractArray[, kind])`, `(N::Int)` = `0:N-1`, `(N::Int, kind)` = `kind ∈ (9,6,10) ? 1:N : 0:N-1` | | 772-773, 778-779 |
| `spectral_diff_fft`, `_rfft`, `spectral_sum_fft`, `_rfft` (internal) | `(N::Int)` | `i·k`, or `1/(i·k)` with 0 at k=0 (§4.9.4) | 781-784 |
| same four | `(t, i, N[, M, O, P, Q])` | Multiply array dimension i by the vector (1D to 5D) | 785-805 |
| `gradient_fft` | `(t::RealFunction, d)` = `real(ifft(d .* fft(t)))`; `(t::AbstractCurve, d)` componentwise; `(t::AbstractMatrix, i)`; `(t::Array3, i)`; `(t::TF)` → Chain over all dims; `(t::VectorField, i)` | Periodic spectral derivative **in radians per sample index** (§4.9.4) | 807-853 |
| `gradient_rfft` | analogous via rfft/irfft. **Bug B18:** 3D signature `AbstractArray{3,T}` (parameters swapped) | | 854-900 |
| `gradient_impulse` | `(t::TF)` = `real(irfft(gradient_impulse_rfft(t)))` | Spatial kernel of d/dx | 901 |
| `gradient_impulse_fft`, `_rfft` | `(N::Int)`, `(t::TF)` = `TF(fftspace(…), spectral_diff_…(N))` | | 902-905 |
| `integral_fft`, `integral_rfft` | `(t::RealFunction, d=spectral_sum_…)`, `(t::AbstractCurve, d)`. **Bug B19:** the curve default uses `spectral_diff`. | Periodic antiderivative plus a mean-slope term (§4.9.4) | 907-918 |
| `integral_impulse(_fft,_rfft)` | as for gradient | | 919-923 |
| `integrate_fft`, `integrate_rfft` | final value of `integral_*` | | 925-928 |
| `spectral_sum_impulse` (internal) | `(N)` = `(b/-x).*(0:N-1) .+ b`, where `x=N/2`, `b=(π/2)/x` | Line-impulse kernel | 930-934 |
| `integral_impulse_line` | `(t::TF)` | | 935 |
| `gradient_chebyshev` | `(v, D=ChebyshevMatrix(v))` = `D*v` | **Bug B13:** gives −dv/dx on Chebyshev domains | 937 |
| `gradient_chebyshevfft` | `(v::AbstractVector, d)`, `(v::AbstractMatrix, i)`, `(v::Array3, i)` | Correct derivative on ascending Chebyshev nodes, in unit coordinate u∈[-1,1] | 939-989 |
| `gradient2_chebyshevfft` | 1D/2D/3D | **Bug B14:** wrong formula | 991-1051 |
| `LocalTensor` forwards | `laplacian_chebyshevfft, gradient, gradient_fft, …, gradient_back` on `LocalTensor` → fiber | | 1053-1055 |
| `laplacian_chebyshevfft` | 1D = `gradient2`; 2D/3D = sum over dims | | 1056-1058 |
| `spectral_diff_chebfft` | `(v)`, `(N)` = `im*vcat(0:N-2, 0, 2-N:-1)` (length 2N-2) | | 1060-1061 |
| `spectral_diff_chebfft2` | `(v)`, `(N)` = `-vcat(0:N-2, 0, 2-N:-1).^2` | | 1063-1064 |
| `gradient_toeplitz`, `gradient2_toeplitz` | `(v, D=derivetoeplitz(v))` = `D*v` | | 1066-1067 |
| `toeplitz1`, `toeplitz2` (internal) | `(N, h=2π/N)` | First columns of the periodic D and D² (§4.9.5) | 1069-1070 |
| `derivetoeplitz`, `derivetoeplitz2` | `(v)` → by length; `(N::Int, …)` in ToeplitzMatricesExt | | 1071-1072 |
| `clenshawcurtis` | `(t::AbstractVector)` = `clenshawcurtis(length(t))*(interval_scale(t)/2)`; `(t::FiberBundle)`; `(t::ProductSpace)`; `(n::Int)` | CC-like weights (bug B9) | 1078-1104 |

### 2.3 Plot API (the Cartan stubs are implemented only by MakieExt)

`Cartan.jl:911-920` declares empty generic functions:
* `unorientedpoly, orientedpoly, makietransform, graylines, graylines!, raster` (not exported except `graylines`, `graylines!`, exported at `Cartan.jl:70`);
* `linegraph, tangentbundle, normalbundle, planesbundle, arrowsbundle, spacesbundle, scaledbundle, scaledfield, scaledarrows, scaledplanes, scaledspaces, planes, spaces`, each with its `!` form, all exported.

Helpers in `Cartan.jl`:
* `spacing` (324-329);
* `Components{T<:TF} = AbstractVector{T}` (608) and `boundarycomponents` (610-661);
* `Variation/variation/alteration/modification` and their `!` versions, plus `_alteration` (663-858);
* `_unorientedplane/_orientedplane/unorientedplane/orientedplane` (906-909);
* `point2chain/point3chain` (922-923), `polytransform` (925), `argarrows/argarrows2/argarrows3` (926-933), `streamargs` (935-954), `gridargs` (956-982).

The full Makie dispatch table is in §4.10 and §5.2. For every Makie function listed below, Cartan also adds methods for `Components` (a vector of fields: plot the first, `display`, then `!`-plot the rest), for `Limit` (plot `last(t)`), and for `LocalTensor` (plot `fiber(t)`) (`MakieExt.jl:60-84`):
* `linegraph, scaledarrows, planes, scaledplanes, spaces, scaledspaces, scaledfield, scaledbundle, arrowsbundle, planesbundle, spacesbundle, tangentbundle, normalbundle` (the Cartan names);
* `wireframe, mesh, lines, linesegments, streamplot, volume, contour, contourf, contour3d, heatmap, voxels, volumeslices, surface, scatter, text, arrows, arrows2d, arrows3d` (the Makie names).

### 2.4 UnicodePlotsExt (`UnicodePlotsExt.jl:19-78`)

* `scatterplot` accepts SB, FB, TF over SB, RealFunction, generic TF, and arrays of 2-component Chains.
* `lineplot` accepts ScalarMap, PlaneCurve, RealFunction, a 1D ComplexMap, and a 1D GradedField.
* `polarplot` accepts RealFunction. `densityplot` accepts TF and arrays of 2-Chains.
* `contourplot` accepts a 2D ComplexMap or SurfaceGrid. `surfaceplot` accepts the same two. `isosurface` accepts VolumeGrid.
* `histogram` and `boxplot` accept ScalarField. `boxplot` also accepts Chain fields and vectors or arrays of Chains.
* `spy` accepts SurfaceGrid and SB. `heatmap` accepts SurfaceGrid and a 2D ComplexMap.
* `Base.display` is overridden for PlaneCurve, RealFunction, 1D and 2D ComplexMap, 1D GradedField, and SurfaceGrid (§5.3).

### 2.5 Other extensions

* **FFTWExt** (`FFTWExt.jl:19-29`):
  * `dct, dct!, idct, idct!(t::TF, args...)` → TF over `r2rspace(base(t))`;
  * `r2r, r2r!(t::TF, kind, args...)` → TF over `r2rspace(base(t), kind)`;
  * `Cartan.dst(t) = r2r(t, RODFT10)/prod(2 .* size(t))`, and `dst!` likewise;
  * `idst(t) = r2r(t, RODFT01)`, and `idst!` likewise.
* **ToeplitzMatricesExt** (`:19-20`): `derivetoeplitz(N, h=2π/N, c=toeplitz1(N,h)) = Toeplitz(c, -c)` and `derivetoeplitz2(N, h, c=toeplitz2(N,h)) = Toeplitz(c, c)`.
* **GeometryBasicsExt** (`:19-66`):
  * GridBundle{1..5} and TF{…,1..5} can be called with a `Point`;
  * `unorientedpoly`/`orientedpoly` return `Point.(polytransform(_…plane(p,v1,v2)))`;
  * `convert(Point, ::LocalFiber) = Point(base(t))`;
  * `GeometryBasics.Mesh(m::TF{Couple,2,GridBundle}) = Mesh(vectorize(m))`;
  * `GeometryBasics.Mesh(m::TF{Chain,2,GridBundle})` attaches normals `normal(m)` iff `mdims(fibertype(m)) ≠ 2`;
  * `_mesh(m::GridBundle{2})` builds `Tesselation(Rect(0,0,1,1), size)` quad faces, uv on `Chain(0,0):inv.(size-1):Chain(1,1)`, points = `Point.(vec(points(m)))` in column-major order;
  * `SimplexBundle(m::GeometryBasics.Mesh)` ingests coordinates plus faces, adding the homogeneous 1.0.
* **MeshesExt** (`:19-25`): `SimplexBundle(m::Meshes.SimpleMesh{N})`. Uses `Submanifold(ℝ^(N+1))`, not `varmanifold`, so the metric signature differs.
* **DelaunayExt** (`:19-21`): `delaunay(::PointCloud)`, `delaunay(::Vector{Chain})` → `initmesh(Triangulation)` = `initmeshdata(t.points', t.convex_hull', t.simplices')`.
* **QHullExt** (`:19-27`): `chull(::Vector{Chain}|::PointCloud, n=1:length(p))` → an SB of hull facets with global indices remapped through `n`; `SimplexBundle(::Chull)`.
* **MiniQhullExt** (`:19-27`): `delaunay(p, n=1:length(p), args...)` → an SB of N-vertex simplices (`N = mdims(p)`) remapped through `n`.
* **TriangulateExt** (`:19-62`): per-bundle-id caches of Triangle-format arrays; `TriangulateIO(e::SB, h=nothing)` (the pointlist drops the homogeneous row; segmentlist is `Cint` 1-based); `triangulate(switches, e::SB; holes)`; `initmesh(::TriangulateIO) = initmeshdata(pointlist, segmentlist, trianglelist, Val(2))`.
* **TetGenExt** (`:19-40`): `JLTetGenIO(mesh::SB; marker, holes)`; `initmesh(tio, command="Qp")` → `(tets SB, trifaces SB)` over `Submanifold(ℝ^4)`; `tetrahedralize(mesh::SB, command="Qp"; …)`.
* **MATLABExt** (`:18-125`):
  * `initmesh(g, args...)` calls MATLAB PDE Toolbox `[P,E,T] = initmesh(g, …)` → `initmeshdata(P,E,T,Val(2))`;
  * `initmeshes` also returns subdomain labels `T[end,:]` as a FaceMap{Int};
  * `totalmesh(es)`; `refinemesh(g, …)` and `refinemesh!(g, pt, pe, …)` through MATLAB `refinemesh`, rewriting points, topology and caches in place.
  * Not portable. Keep only the P/E/T **data format** (§3.3).
* **ColorTypesExt** (`:19-35`): `raster(ga::Vector, R=_rectangle(3))`. For each pixel, P = `Chain{M}(1, x, y)`. The pixel's count c is the number of `g ∈ ga` with `norm(P∧g) < δ`, where δ = `sqrt(δx²+δy²)/2`. The output is `GrayA(c,c)` at `out[1+ny-y, x]` (y flipped). `_rectangle` ignores its argument and uses a 100×100 grid on [-3,3]².
* **Special-function extensions** (SpecialFunctions, Elliptic, EllipticFunctions, FewSpecialFunctions, JacobiElliptic): mechanical lifts `F(x::TF) = TF(base(x), F.(fiber(x)))` and `F(x::LocalTensor) = LocalTensor(base(x), F(fiber(x)))` over every argument position. Some lifts are buggy:
  * `SpecialFunctionsExt.jl:39-40` uses undefined `k`;
  * `EllipticFunctionsExt.jl:65` returns `LocalTensorField`, which is undefined;
  * the `EllipticFunctionsExt.jl:35-43` group (`ljtheta1..4, am`) omits the broadcast dot for vector arguments.

  Port these as a generic `liftField : (α → β) → TensorField α → TensorField β`, not one method per function.

---

## 3. Data representations

### 3.1 Homogeneous (affine) coordinates

Every simplicial mesh point is stored as a **homogeneous** Grassmann vector `Chain{V,1,Float64,d+1}(1.0, x₁, …, x_d)` with `V = varmanifold(d+1) = Submanifold(d+2)(1,…,d+1)` (`fiber.jl:825`). This is the ⟨11…1_⟩ signature: d+1 Euclidean basis vectors, with the extra basis vector reserved.

[probe] `varmanifold(3)` shows as `⟨111_⟩`, and a 1D mesh uses `⟨11_⟩`.

* `initpoint(P::Real) = Chain{varmanifold(2),1}(1.0, P)` (`element.jl:70`).
* The generated `initpoints(P, Val(n))` builds `Chain{varmanifold(n+1),1}(1.0, P[1,k], …, P[n,k])` for every column k of the n×np matrix P (`element.jl:71-74`).
* `↓(V)` drops the first basis vector, which maps homogeneous coordinates to Euclidean ones (a `Submanifold` of dimension d, shown as `⟨_11_⟩`).
* `submesh(m)` returns the np×d matrix of columns `2:mdims` (`element.jl:380`). `array(m)` returns the np×(d+1) matrix including the leading 1 (`element.jl:326`).

Consequences:
* `∧` of d+1 homogeneous points in d dimensions is the (d+1)×(d+1) determinant `det[1 p_i]`, which equals d!·(signed volume).
* Barycentric coordinates solve `[p₁ … p_{d+1}] λ = P` in homogeneous coordinates, which enforces Σλ = 1 automatically.

**Lean:** do not store the leading 1. Store `FloatArray` with stride d and make the 1 implicit in the kernels. Record `d` (ambient dimension) and `n = sdims` (vertices per simplex) as type indices (§8).

### 3.2 Topology (MeshTopology, as used here)

* `ImmersedTopology{N,M} = AbstractArray{Values{N,Int},M}`. `SimplexTopology{N,…}` stores:
  * `id` (bundle cache id);
  * `t::Vector{Values{N,Int}}` (**1-based** vertex indices of each element, called the full topology);
  * `i` (vertices, the subspace vertex list: `OneTo(n)` or `Vector{Int}`);
  * `p` (totalnodes, often a `Ref`, shared between the element and boundary topologies: `refnodes`);
  * `f` (subelements);
  * `v` (verticesinv).
* Predicates:
  * `isfull`: no element subset;
  * `istotal`: vertices cover all nodes;
  * `iscover`: both.
  * [probe] a fresh `SimplexTopology([…], 4)` has type parameter `(true, true)`.
* `sdims(t) = N` is the number of vertices per simplex (3 for triangles). `mdims` of the bundle is the homogeneous dimension (3 for planar triangles, 4 for tets or surface triangles in 3D).
* `DiscontinuousTopology` gives every element private copies of its vertices. `isdisconnected` means fully disconnected.
* Element vertex **order is significant**. Cartan never reorients elements: it uses unsigned volumes but orientation-dependent gradients (bug B3).

### 3.3 Bundles and mesh file formats

* `SimplexBundle{N,C,PA,TA}` has fields `p::PointCloud` (called `PA`) and `t::ImmersedTopology`. `N = mdims(pointtype(p)) - 1` (`fiber.jl:572-576`).
* `FaceBundle` has the same fields. The difference is that its "points" are element **means** (centroids) and its length is the number of elements (`fiber.jl:686-715`). `SimplexBundle(fb)` and `FaceBundle(sb)` convert by re-tagging (`fiber.jl:696-697`).
* A `TensorField{B,F,1,P,A}` over SB has fiber length = number of vertices (nodal values). Over FB it has one value per element.
* **Ingest format** (MATLAB PDE Toolbox, Triangle, Delaunay.jl):
  * P is a d×np Float64 matrix of coordinates;
  * E is a k×ne matrix whose rows 1..d are boundary-simplex vertex ids (for 2D, rows 1-2 are edge endpoints; MATLAB adds rows 3-7 with parameters and subdomain labels);
  * T is a k×nt matrix whose rows 1..d+1 are element vertex ids (MATLAB row 4 is the subdomain label).
  * All ids are **1-based**. `initmeshdata(P,E,T,Val(d))` returns `(pt, pe)` sharing one PointCloud: `pt` = elements with vertices `OneTo(np)`, `pe` = boundary simplices (`element.jl:80-88`).
* **1D meshes:** `initmesh(r)` builds the points `(1, r_i)`, elements `[i, i+1]`, and boundary `[[1], [n]]` with vertices `[1, n]`. [probe] See §6.

### 3.4 Julia-specific caches (redesign in Lean)

`array_cache`, `array_top_cache` and `submesh_cache` (`element.jl:324-398`), plus the Triangle and MATLAB caches in the extensions, are **global** vectors indexed by the integer bundle id `bundle(m)`. They hold dense matrices, so repeated plotting and assembly skip the conversion. Id 0 means "do not cache". `refinemesh!` has to invalidate them with `array!` and `submesh!`.

**Lean:** the canonical storage is already dense (`FloatArray` or `Array UInt32`), so there is no cache. The views are O(1) and no global mutable state is needed.

### 3.5 Spectral types

* `FourierSpace` is a pair (frequency vector, original domain). The frequency vector is often an `AbstractFFTs.Frequencies{Float64}`, which is lazy: `n_nonnegative`, `n`, `multiplier`.

  **Invariant:** `fftspace(fftspace(x)) == x` whenever x is a range, and likewise for `rfftspace` and `r2rspace`. The involution replaces the domain on both the forward and the inverse transform.

  [probe] For x=0:1.0:7, `fftspace(x).f::Frequencies{Float64}` equals `(2π/7)·(0:7)`.
* A multi-dimensional domain is a `ProductSpace{V,T,N}` holding a tuple of 1D vectors `v`. Its fields are stored **column-major** with the first index fastest, exactly like Julia arrays. The FFT along dimension i acts on axis i.
* A `GridBundle` over a FourierSpace gets `ClampedTopology`; [probe] it shows as `CompactTopology{1,0,2,…}`. A GridBundle over a `ProductSpace` gets the default `OpenTopology`.
* `Chebyshev` holds ascending Chebyshev-Lobatto points `x_j = -cos(πj/(N-1))`, j=0..N-1, affinely mapped to `[x₀, x₁]` when it is built from a vector, plus the angle range θ.
* `LagrangeWeights` holds nodes `v` and weights `w_j = 1/∏_{i≠j}(v_j - v_i)`.
* `OrthogonalTransform` holds a basis function `f(n,x)` and a canonical interval [a,b].

### 3.6 Plot-side representations

* `Components` (a vector of TFs) is produced by `boundarycomponents(f, n=1)`. It returns a `FixedVector` of `2·ndims` leaves:
  * 1D: `[f[n], f[end-n+1]]`;
  * 2D: `[leaf(f,n,1), leaf(f,s₁-n+1,1), leaf(f,n,2), leaf(f,s₂-n+1,2)]`;
  * up to 5D. The 5D case mislabels the container as `FixedVector{8}` with 10 entries (`Cartan.jl:651`, bug B21).

  `boundarycomponents(f, ::Colon)` peels the layers `1:min(size)÷2` (`Cartan.jl:610-661`).
* The keyword-argument protocol consumed by Cartan (removed before forwarding to Makie):
  * `gridsize` (resample the domain),
  * `arcgridsize` (arc-length resample),
  * `poly` (draw polygons instead of meshes),
  * `lengthscale` (for `planes`/`spaces`).
  * `gridargs` strips them (`Cartan.jl:956-982`).

---

## 4. Algorithms

### 4.1 Simplex geometry kernels

Let an element have vertices p₁…p_n (n = sdims), each point Euclidean in ℝ^d, stored homogeneously as P_i = (1, p_i).

1. **`detsimplex(m)`** (`element.jl:428-432`) = `∧(FaceBundle(m)) / (n-1)!`.
   * When the mesh is not embedded (`mdims(m) ≤ sdims(m)`, i.e. n = d+1), it is `P₁ ∧ P₂ ∧ … ∧ P_n`, a pseudoscalar of the homogeneous space with value `det[P₁ … P_n]`.
   * When embedded (`mdims > sdims`, for example surface triangles in 3D), it is `(p₂-p₁) ∧ … ∧ (p_n-p₁)` in ↓V, a grade-(n-1) blade. `Grassmann.vectors = affineframe` builds the edge vectors.
   * [probe] Unit right triangle: `detsimplex = 0.5v₁₂₃` and `∧ = 1.0v₁₂₃`. A 3D surface triangle with legs 2,2: `∧ = 4.0v₂₄`.
2. **`volumes(t)`** (`element.jl:45-54`):
   * If `sdims(immersion(t)) ≠ 2`: `Real.(abs.(detsimplex))`. Here `abs` of a blade is its norm.
   * If n = 2 (edges): `edgelength = value(abs(v₂ - v₁))`, the Euclidean length (the homogeneous components cancel).
   * The result is always **unsigned**. [probe] Values: two unit triangles give [0.5, 0.5], a clockwise triangle gives [0.5], a unit tet gives [1/6], the surface triangle gives [2.0], and the 1D mesh 0:0.25:1 gives [0.25×4].
3. **`affineframe(t::FaceBundle)`** (`element.jl:417-426`, `@generated` on sdims): per element, `TensorOperator(Chain{V(2..n),1}(↓(p_i - p₁) for i=2..n))`, i.e. the columns are the edge vectors from vertex 1. [probe] Triangle (0,0),(1,0),(0,1) gives columns (1,0),(0,1). Triangle (1,0),(1,1),(0,1) gives (0,1),(-1,1).
4. **Per-element reductions** (`element.jl:433-451`, `Grassmann composite.jl:935-945`): `means` = arithmetic mean of the vertex points, `barycenters` = sum, `centroids` = sum divided by its first (homogeneous) component (equal to `means` for affine points), `curls` = the cyclic differences `curl_i = p_{i+2} − p_{i+1}` (1-based, indices mod n). [probe] For (1,2,3): curls = [p₃−p₂, p₁−p₃, p₂−p₁], as homogeneous chains with first component 0. `means(m::SimplexMap)` gives the element averages of the nodal fiber values.
5. **`gradienthat(t, m=volumes(t))`** (`element.jl:456-471`) returns ∇λ_i, the gradients of the P1 barycentric hat functions, per element, packed as `TensorOperator(Chain{V,1}(∇λ₁, …, ∇λ_n))` with each ∇λ_i ∈ ↓V. It has three branches on `N = mdims(Manifold(t))` (the homogeneous dimension):
   * **N = 2 (1D intervals):** `c = 1/h` with h the **unsigned** length, and the result is `(−c, +c)`. This assumes p₂ > p₁. [probe] h = 0.25 gives `(-4.0v₂)v₁ + (4.0v₂)v₂`.
   * **N = 3 (planar triangles):** `∇λ_i = revrot( ↓(curl_i) ) / (2·|A|)`, where `revrot(x,y) = (−y, x)` and |A| is the **unsigned** area. For a counter-clockwise triangle this is exact. For a clockwise triangle **every gradient is negated** (bug B3). [probe] For CW (0,0),(0,1),(1,0), the gradient of u = x comes out as (−1, 0).
   * **Otherwise** (tets, surface triangles, higher): `Grassmann.grad(affinehull element)` (Grassmann `composite.jl:814-831`), a Cramer's-rule inverse or pseudo-inverse that is orientation-correct. For M < mdims (embedded) it computes `ct·inv(Tᵀ·ct)` (a Moore-Penrose-style tangential gradient). [probe] The unit tet gives (−1,−1,−1),(1,0,0),(0,1,0),(0,0,1). The surface triangle gives (−.5,0,−.5),(.5,0,0),(0,0,.5).

   Correct orientation-free formula for Lean:
   ```
   E = [p₂-p₁ … p_n-p₁]            (d × (n-1))
   G = (EᵀE)⁻¹                      ((n-1)×(n-1) Gram inverse)
   ∇λ_{2..n} = E·G  (columns);  ∇λ₁ = -Σ_{i≥2} ∇λ_i
   ```
   This matches branch 3 exactly and branches 1-2 for positively oriented elements.

### 4.2 Transfer, assembly and gradients

* **`degrees(t::ST)`** (MT/element.jl:303-309): `b[k] = #{elements containing node k}`, length `totalnodes`. [probe] Two triangles (1,2,3),(2,4,3) give [1,2,2,1]. `weights = 1 ./ degrees` gives [1, .5, .5, 1].
* **`assembleincidence(t, f, m, Val(T))`** (MT/element.jl:311-319): `b = zeros(totalnodes)`, then for each element k with vertices t_k, `b[t_k] += f[t_k] .* m[k]` (f nodal, m per element). The element type follows `m` if T else `f`, with Int promoted to Float64.
* **`assembleload(t, f=1, m=volumes(t))`** (`element.jl:546`): `b_i = Σ_{k ∋ i} f(x_i) |T_k| / n`. This is a mass-lumped (vertex-quadrature) load vector, with f evaluated at the **node**, not at quadrature points.
  * [probe, with the fibertype patch] Two unit triangles, f=1: [1/6, 1/3, 1/3, 1/6]. f=x: [0, 1/3, 0, 1/6]. 1D 0:0.25:1: [.125, .25, .25, .25, .125]. Unit tet: [1/24]×4.
  * **Upstream crash:** `MeshTopology.assembleincidence` calls `fibertype`, which is not defined in MeshTopology, so it raises `UndefVarError` (bug B1). Oracles must monkey-patch: `@eval MeshTopology fibertype(x::AbstractArray)=eltype(x)` and `fibertype(x::TensorField)=Cartan.fibertype(x)`.
* **`interp(t::FaceMap)`** (`element.jl:550` → MT/element.jl:332): nodal value `u_i = w_i · Σ_{k∋i} b_k`, the average of the incident element values. [probe] Element values [1, 3] give nodes [1, 2, 2, 3]. For a `DiscontinuousTopology` it is `view(b, discontinuousvertices(t))`.
* **`pretni(t::SimplexMap) = means(t)`** (`element.jl:556`). [probe] Nodes [1,2,3,4] on (1,2,3),(2,4,3) give [2, 3].
* **`gradient_2(t, u)`** (`element.jl:491-501`): per element k, with scalar u: `∇u|_k = Σ_i u[t_k[i]] ∇λ_i` (the dot of the Values of nodal values with the gradient chains). With vector-valued u (Chains): `∇u|_k = g_k ⋅ transpose(TensorOperator(u[t_k]))`, the Jacobian as a TensorOperator. [probe] u = x+2y on two triangles gives (1,2),(1,2).
* **`gradient(t::SimplexMap)`** (`element.jl:479-483`): `interp` of `gradient_2`, giving nodal averages of the element gradients. [probe] 1D x² on 0:0.25:1: the elements give [.25, .75, 1.25, 1.75] and the nodes give [.25, .5, 1.0, 1.5, 1.75].
* **`gradient(t::FaceMap)`** (`element.jl:484-487`): first interpolates the element values to nodes, then `gradient_2`, giving a FaceMap.
* **`Δ(t::ST) = Diagonal(degrees) − adjacency`** (`element.jl:505-506`). Here `degrees` counts incident *elements* and `adjacency` counts *edge multiplicity* (§4.3), so the rows do **not** sum to zero (bug B7). [probe] A single triangle gives `[1 -1 -1; -1 1 -1; -1 -1 1]`.

### 4.3 Topology operations (MeshTopology semantics as reached through Cartan)

* **`sparse(t, cols, np)`** (MT/element.jl:51-57): `A = Σ_{(a,b) ∈ combo(N,2)} sparse(cols[a], cols[b], 1, np, np)`, where `cols[a]` is the a-th vertex column over all elements. So `A[t_k[a], t_k[b]] += 1` for every a<b in **local** order, and A is not symmetric.
  * `adjacency = A + Aᵀ` (edge multiplicity: interior edges of a triangle mesh give 2).
  * `antiadjacency = A − Aᵀ`.
  * [probe] (1,2,3),(2,4,3): adjacency `[0 1 1 0; 1 0 2 1; 1 2 0 1; 0 1 1 0]`, antiadjacency `[0 1 1 0; -1 0 2 1; -1 -2 0 -1; 0 -1 1 0]`.
* **`edges(t)`** (MT/element.jl:59-70): `findall(!iszero, triu(adjacency))`. It returns `Values(i,j)` with i<j in **column-major order of the upper triangle**: sorted by j, then i.
  * [probe] Two triangles: `[1,2],[1,3],[2,3],[2,4],[3,4]`. Tet: `[1,2],[1,3],[2,3],[1,4],[2,4],[3,4]`.
  * `edges(ST{2}) = t` (identity).
  * For `DiscontinuousTopology{3}`: per element `(t1,t2),(t2,t3),(t3,t1)` (MT:71-82).
* **`edgesindices(t, et=edges(t))`** (MT/element.jl:344-366): builds a symmetric map (vertex pair → edge id), then per element:
  * triangle (v1,v2,v3): `(e(v2,v3), e(v1,v3), e(v1,v2))`, i.e. **edge i is opposite vertex i**;
  * tet: `(e12, e13, e14, e23, e24, e34)`;
  * 5-simplex: all pairs in lexicographic order.

  Cartan's `edgesindices(t::SB, e::FB)` wraps the result on a PointCloud of edge midpoints (`element.jl:601-605`). [probe] Two triangles give [[3,2,1],[5,3,4]]. Tet gives [[1,2,4,3,5,6]].
* **`facetsinterior(t)`** (MT:84-96): for each element, for each `(n-1)`-combination of the **sorted** vertices in lexicographic order, the facet is either appended to `out` or its index is pushed to `bnd` (it was seen twice). The implementation uses linear `findfirst` and is O(F²).
* **`∂(t::ST{N})`** (`element.jl:301-308`):
  * N ≠ 3: the facets not in `bnd` (appearing once), in first-appearance order. [probe] Tet gives [1,2,3],[1,2,4],[1,3,4],[2,3,4].
  * N = 3: `edges(t, adjacency(t) .% 2)`, the edges with odd multiplicity, in `edges` order. [probe] [1,2],[1,3],[2,4],[3,4].
  * The oriented `∂(t, u::Vector{Int})` (`element.jl:295-299`) uses `faces(t, h, Val(N-1))` (MT:142-166). It sorts each element with `indexparity!` (tracking permutation parity), enumerates the (n-1)-combinations of the sorted vertices, and gives each the coefficient `h[i]·(±val[k])`, where `val = value(∂(Submanifold(n)(I)))` are the alternating boundary signs of the unit n-blade and the sign flips on odd parity. It accumulates coefficients on duplicate facets and returns the facets with a nonzero sum.
* **`faces(t, Val(k))`** (MT:101-114): k = n returns t, k = 2 returns edges, k = 1 returns singletons of the vertices; otherwise the unique sorted k-combinations in first-appearance order. `facets(t) = faces(t, Val(n-1))`. [probe] Two triangles: facets = edges = 5.
* **`neighbors(t)`** (MT:368-393): uses the node→element incidence transposed. Neighbor i of element k is the unique other element sharing all vertices except local vertex i: `setdiff(∩_{j≠i} elems(t_k[j]), k)`, or 0 if there is none. This runs `@threads` over elements. [probe] (1,2,3),(2,4,3) gives [[2,0,0],[0,1,0]].
* **`facetsigns(t)`** (MT:395-397): `sign_i = (nbr_i < k) ? +1 : −1`. A boundary (0) always gives +1. [probe] [[-1,1,1],[1,1,1]].
* **`incidence(t)`** (MT:320-327): an np×nt sparse matrix with `A[i,k] = 1` iff i ∈ t_k. [probe] `[1 0; 1 1; 1 1; 0 1]`.
* **`interior(e) = interior(totalnodes(e), vertices(e))` → `setdiff(1:neq, fixed)`**: **the arguments are swapped** (MT:339-340), so it crashes with `Colon(::Int, ::OneTo)` (bug B6). The intended semantics are all nodes except the boundary vertices, sorted.
* **Local-facet tables** (MT:399-407):
  * `edgesigns(Values{3})` = `(i2<i3, i3<i1, i1<i2) ? 1 : -1`;
  * `facets(Values{3})` = `((i2,i3),(i3,i1),(i1,i2))`;
  * `facets(Values{4})` = `((2,3,4),(4,3,1),(1,2,4),(3,2,1))` as oriented local facets.

### 4.4 Point location and evaluation (`sinterp`, `findfirst`)

`element.jl:33-42, 400-413`:

```
sinterp(m, t::Chain):
  V  = Manifold(pointtype(m)); P = Chain{V}(value(t))   # t must already be homogeneous (1,x,y)
  j  = findfirst(P, base(m))       # linear scan over elements: P ∈ simplex(p[t[i]])
  j == 0 → return zero(fibertype(m))
  i  = immersion(m)[j]             # vertex ids
  λ  = simplex(points[i]) \ P      # barycentric coordinates (Cramer's rule, Grassmann composite.jl:723-734)
  return Chain{V}(fiber(m)[i]) ⋅ λ  # Σ u_i λ_i
```

* Containment `P ∈ simplex` (Grassmann `composite.jl:736-749`) is the sign test on the sub-determinants: all must share the sign of the full determinant.
* Complexity is O(nt) per query. Streamplots on simplex fields call this per integration step (a performance hot path, §8).
* [probe] u = x+2y on two triangles at (0.25, 0.25) gives 0.75. `findfirst((.75,.75))` gives 2. For 1D x² at 0.3 the value is 0.1 (linear).

### 4.5 Mesh construction and refinement

* `initedges(n)` gives `ST(Values{2}.(1:n-1, 2:n), OneTo(n))`. `initmesh(r)` gives `(t, t(ST([[1],[n]], vertices, refnodes(t))))` (`element.jl:61-67`).
* `totalmeshdata(P,E,T,Val(n))` (`element.jl:92-98`) builds the element topology `t` and the full `edgetopology(t)`. For each boundary edge in E it finds the matching edge index. If the edge is present only reversed, it **overwrites** that edge in the full list with the boundary orientation (`edgemeshdata`, `element.jl:99-118`, O(ne·E)). It returns `pe` as a sub-immersion: `SimplexTopology(new_id, ed, vertices(view(ed,ind)), refnodes(t), ind, vertices(ed))`. **Note:** `global top_id += 1` mutates a global counter.
* `refinemesh!(::AbstractRange, pt, pe, η)` (`element.jl:131-157`) does 1D bisection:
  1. for each element index i ∈ η, push the point `(1, (x_i + x_{i+1})/2)`, where `x_i` is the i-th **point** (so this assumes element i = [i, i+1], valid only for an unrefined sorted mesh);
  2. sort the points by x;
  3. set total nodes to np;
  4. rebuild the elements as consecutive `[i-1, i]`;
  5. set the last boundary vertex to np and fix `verticesinv`.

  [probe] Refining elements [2,4] of 0:0.25:1 gives points [0, .25, .375, .5, .75, .875, 1], 6 elements, boundary [1],[7], volumes [.25, .125, .125, .25, .125, .125].
* `refinemesh(g::AbstractRange)` = `(g, refine(pt), refine(pe))`. [probe] It leaves the 1D mesh unchanged.

### 4.6 Crouzeix-Raviart interpolation `interpCR` (`element.jl:561-585`)

Input: a triangle mesh `pt`, its edges `ed`, and per-edge values m (from `crfun` evaluated on edge midpoints, or given as a TF). Output: a discontinuous P1 field. Per triangle k with discontinuous nodes `dk` (3 private ids), global vertices `tk`, and local edge ids `nk = edgesindices[k]` (edge j is opposite local vertex j):

```
b = zeros(totalnodes(dt))
for j in 1:3:
   e   = ed[nk[j]]                      # global endpoints
   loc = invmap.(tk, e)                 # local indices (1..3) of both endpoints
   b[dk[loc]] += m[nk[j]]               # both endpoints of edge j
   b[dk[findmissing(loc)]] -= m[nk[j]]  # vertex opposite edge j
```

So `u(v_i) = Σ_{e ∋ v_i} m_e − m_{e opposite v_i}`, the exact P1 values of the CR function whose edge-midpoint values are m. Here `invmap(t, n)` is the position of n in t (MT:336) and `findmissing(v::Values{2})` is the element of {1,2,3} not in v (MT:337).

### 4.7 Lagrange P_M node coordinates `LagrangeBundle!` (`element.jl:683-784`)

The topology comes from MeshTopology's `LagrangeTopology{M}`. Each element's `Values` lists the corner nodes first, then the edge nodes, (facet nodes), and interior nodes. Coordinates are written into a resized point cloud `c`. With corners c_i, c_j, c_k, c_l of the element (from `columns(cornertopology(t))`) and `c_ab = (c_b − c_a)/M`:

* **LagrangeEdges{2}:** node 3 = (c_i + c_j)/2. **LagrangeEdges{M}:** node 3 = c_j + c_ij (**suspect**: `printlagrange` says c_i + c_ij), and nodes x = 4..M+1 are c_i + (x−2)c_ij. **Both methods reference undefined `pt` (bug B8), so they are unreachable as written.**
* **LagrangeTriangles{2}:** node 4 = (c_j+c_k)/2, node 5 = (c_i+c_k)/2, node 6 = (c_i+c_j)/2 (edge nodes opposite vertices 1, 2, 3).
* **LagrangeTriangles{M}:**
  * **Edge nodes** use *global* edges for conformity. With `(x,y) = columns(edges(t))` and Δe = (c_y − c_x)/M, the x-th interior node of global edge e (`getedge(t,e)[x]`) = c_x + x·Δe, for x = 1..M−1.
  * **Interior nodes**, starting at local index `3M+1`: for rows x = 1..M−2, with `ls = lagrangesimplex(3, x−2) = binomial(x,2)` and `Y = start+ls : start+ls+x−1`, local node `Y[y] = c_i + (x+1−y)·c_ik + y·c_ij` for y = 1..x. For P3 this gives node 10 = the centroid.
* **LagrangeTetrahedra{M}:**
  * **Edge nodes** are interleaved per step x = 1..M−1: local `4+6(x−1)+{1..6}` = `c_i+x c_ij, c_i+x c_ik, c_i+x c_il, c_j+x c_jk, c_j+x c_jl, c_k+x c_kl`. These use *element-local* orientation, so two tets that disagree on an edge's orientation write inconsistent coordinates for M ≥ 3 (last write wins).
  * **Face nodes:** `start = 4+6(M−1)+1`. For x = 1..M−2, `Y = start+4ls : 4 : start+4ls+4x`, and the four faces (jkl, ikl, ijl, ijk) get `c_j+bw c_jk+y c_jl`, `c_i+bw c_ik+y c_il`, `c_i+bw c_il+y c_ij`, `c_i+bw c_ik+y c_ij` (bw = x+1−y).
  * **Interior nodes:** `start += 4·facetsimplex(4,M)`, then triple loops z = 1..M−3, x = 1..z, y = 1..x give `c_i + (M−2−z)·c_ij + (x+1−y)·c_ik + y·c_il`. The offsets `ls1 + lagrangesimplex(4,x−2)` are **unverified**.

  **Oracle must dump coordinates before porting.**

Helper numbers (MT/lagrange.jl:20-49): `simplexnumber(N,n) = binomial(n+N−1, N)`, `lagrangesimplex(N,M) = simplexnumber(N−1, M+1)`, `centersimplex(N,M) = simplexnumber(N−1, M−N+1)`, `facetsimplex(N,M) = centersimplex(N−1, M)`.

### 4.8 Miscellaneous

`rms(η) = ‖fiber‖₂/√len`. `select(η, ϵ)` gives the sorted indices with `fiber > ϵ`. [probe] [0.1, 2.0] gives [2]; `rms([3,4])` = 3.5355. `maximum(η)` returns the LocalTensor `base ↦ value`. [probe] `1.0v₁ + 0.666667v₂ + 0.666667v₃ ↦ 4.0`.

### 4.9 Spectral algorithms

#### 4.9.1 Frequency axes (`spectral.jl:47-71`)

For a physical range x with N samples and span `L = x[end] − x[1] = (N−1)h`:

| function | ω (step) | values | length |
|---|---|---|---|
| `fftspace(x)` | 2π/L | `ω·(0:N−1)` (not wrapped to negatives) | N |
| `rfftspace(x)` | 2π/L | `ω·(0:N÷2)` | N÷2+1 |
| `r2rspace(x)` | π/L | `ω·(0:N−1)` | N |
| `r2rspace(x, kind)` | π/L | `ω·(0:N−1)`, or `ω·(1:N)` if kind ∈ {9 = RODFT10, 6 = REDFT11, 10 = RODFT11} | N |

**Convention warning (B20):** the step uses `(N−1)h`, not the period `Nh`. So on a periodic grid 0:2π/8:7·2π/8 the axis step is 8/7, not 1. [probe] fft axis `[0.0, 1.142857, 2.285714, …, 8.0]`; rfft axis `[0.0, …, 4.571429]`.

The `fftspace(N, ω)` implementation is `(n/N)·rfftfreq(n, N·ω)` with `n = 2(N−1) + iseven(N)`, which reduces exactly to `ω·(0:N−1)` [probe: `fftspace(8) = [0, .125, …, .875]`].

The FFTW r2r kind codes are R2HC=0, HC2R=1, DHT=2, REDFT00=3, REDFT01=4, REDFT10=5, REDFT11=6, RODFT00=7, RODFT01=8, RODFT10=9, RODFT11=10 [probe].

#### 4.9.2 Transform wrappers

* `fft(t) = TF(fftspace(base(t)), fft(fiber(t)))`.
  * FFTW conventions: forward `X_k = Σ_j x_j e^{−2πijk/N}` (unnormalized), `ifft` = (1/N)·Σ e^{+…}, `bfft` is unnormalized backward, `rfft` returns the first N÷2+1 bins, and `irfft(X, n)` needs the original length n (from `invdim`).
  * The data bins stay in **standard FFT order** (0, 1, …, −1), while the axis is labeled `ω·(0:N−1)`. This is consistent only modulo aliasing: bin k ≥ N/2 represents k−N.
  * `ifft(fft(t))` restores the original domain exactly. [probe]
* `fftshift(t::TF)` shifts the fiber by the standard `circshift(N÷2)`. The axis becomes `(0:N−1)ω − (⌈N/2⌉−1)ω`. For **odd N** this matches the data. For **even N** the axis is off by one bin (bug B12). [probe] N=8 axis: [−3,…,4]ω, but the data after the shift is ordered [−4,…,3].
* FFTWExt:
  * `dct(t)` uses FFTW.jl's orthonormal DCT-II: `Y_0 = Σx/√N`, `Y_k = √(2/N) Σ x_j cos(π(2j+1)k/(2N))`. [probe] `dct([1,2,3,4])[1] = 5.0`.
  * `r2r(t, kind)` uses unnormalized FFTW kinds (REDFT10 gives 2Σ…).
  * `dst(t) = RODFT10/(2N)`, where RODFT10 is `Y_k = 2Σ x_j sin(π(j+½)(k+1)/N)`.
  * `idst = RODFT01` (unnormalized), so `idst(dst(x)) = x`. [probe]

#### 4.9.3 Laplace and Gabor transforms (`spectral.jl:102-200`)

* `flt(f, σ::Number) = fft(e^{−σ t}·f)`, where t is the identity field of the domain. `flt(f, σ::Vector)` stacks the rows `fft(e^{−σ_i t} f)` into an `(length σ) × N` complex matrix over the product domain `σ ⊕ fftspace(x)`. [probe] σ = [0, .5] on sin with N=8 gives size (2,8) over a ProductSpace, and row 2 equals `flt(s, .5)`.
* `iflt(F)` over (σ, ω): `(1/|σ|) Σ_i e^{σ_i t} ⊙ ifft(F[i,:])`. `irflt` is analogous, using irfft with length `length(t)`.
* `fgt(f, σ, g)`: row i = `fft(g(t − σ_i)·f)`. With `σ::Int` the centers are `resample(points(f), σ)`, i.e. σ equally spaced centers over the domain.

#### 4.9.4 Periodic spectral calculus (`spectral.jl:767-935`)

Wavenumbers are **integers k** (unitless). The derivative is taken with respect to the sample phase θ = 2πj/N, not x:

```
spectral_diff_fft(N)  = i·[0,1,…,⌊N/2⌋−1, −⌈N/2⌉, …, −1]      (length N)
spectral_diff_rfft(N) = i·(0:⌊N/2⌋)
spectral_sum_fft(N)   = −i·[0, 1/1, …, 1/(⌊N/2⌋−1), 1/(−⌈N/2⌉), …, 1/(−1)]
spectral_sum_rfft(N)  = −i·[0, 1/1, …, 1/⌊N/2⌋]
gradient_fft(t)  = real(ifft(d ⊙ fft(t)))
gradient_rfft(t) = real(irfft(d ⊙ rfft(t)))
```

* **Bug B10 (odd N):** the negative half is `−(N+1)/2 … −1`, so N=7 gives `[0,1,2,−4,−3,−2,−1]`, where the correct values are `[0,1,2,3,−3,−2,−1]`. `fftwavenumber` has the same bug. [probe] The N=7 derivative of sin(3θ) is wrong (`[-0.5, 0.45, …]` against `3cos3θ = [3.0, −2.70, …]`); sin(θ) is fine.
* **Scaling:** on a domain [0,1) the derivative of sin(2πx) comes out as cos(2πx), missing the factor 2π. [probe]
* The multidimensional variants (`gradient_fft(t::AbstractMatrix, i)`, 3D) multiply along dimension i and return a **complex** TF (no `real`). `gradient_fft(t::TF)` returns a Chain of complex partials over all dims. [probe] The eltype is `Chain{⟨11⟩,1,ComplexF64,2}`.

`integral_fft(t, d=spectral_sum_fft(N))`:

```
m   = mean(fiber(t))
out = real(ifft(d ⊙ fft(t − m)))          # periodic antiderivative (in θ units), zero-mean
return out + m·(x − (x₀ + out[1]/m))        # = out − out[1] + m·(x − x₀)
```

This mixes units: the periodic part is in θ and the mean term is in physical x. If `m == 0.0` exactly, the result is 0·∞ = NaN (edge case B19b). [probe] `cos+1` on the 2π grid gives `sin x + x`, e.g. `[0.0, 1.492505, 2.570796, …]`. `integrate_fft` returns the last value: `4.79068036259559` for N=8.

Other helpers:
* `gradient_impulse(t) = real(irfft(i·(0:N/2)))`, the circulant derivative kernel. [probe] N=8 gives `[0, −1.207107, .5, −.207107, 0, .207107, −.5, 1.207107]`.
* `convolve(f,g) = irfft(rfft f ⊙ rfft g)`, a circular convolution.

#### 4.9.5 Toeplitz periodic differentiation (`spectral.jl:1069-1072`, ToeplitzExt)

```
toeplitz1(N,h=2π/N) = [0; ½(−1)^k cot(k h/2) for k=1..N−1]          # first column c
derivetoeplitz(N)   = Toeplitz(c, −c)    # first column c, first row −c
toeplitz2(N,h)      = [−π²/(3h²) − 1/6; ½(−1)^{k+1}/sin²(k h/2) for k=1..N−1]
derivetoeplitz2(N)  = Toeplitz(c, c)
```

These are Trefethen's periodic D_N and D_N² for **even** N. For odd N the cot/csc formula differs, and Cartan's matrices are then not exact (document or fix). [probe] `derivetoeplitz(4) = [0 .5 0 −.5; −.5 0 .5 0; 0 −.5 0 .5; .5 0 −.5 0]`, D·sin = cos and D²·sin = −sin for N = 8.

#### 4.9.6 Orthogonal series `(f::OrthogonalTransform)(g, N)` (`spectral.jl:219-315`)

**Forward** (g is not over a FourierSpace):

```
L   = x[end] − x[1]                               # interval_scale
ωx  = ((b−a)/L)·x + a                             # **assumes x[1] = 0** (bug B15b)
c_n = (2/L)·∫ g(x) f(n, ωx) dx,  n = 0..N−1       # ∫ = trapezoid (grid.jl:1226 integrate=trapz)
return TF(FourierSpace(((b−a)/L)·(0:N−1), x), c)
```

In 2D the prefactor is `4/(L₁L₂)` and the integrand is `f(i,ωx)f(j,ωy)`. The prefactors for 3D, 4D and 5D are 8, 16 and 32.

**Restore** (g is over a FourierSpace): `Σ_{n=1}^{N} c_n · f(n−1, ωx)` on the original domain. The cosine a₀ is therefore **not halved**: a restore of `cos(2t)+0.5` gives `2.0` at t=0 instead of 1.5 (B15c). [probe] Coefficients for `cos(2t)+.5` on 0:π/64:π: `[1.0, ~0, 1.0, ~0, ~0]`; restore at t=0 gives 2.0.

Further bugs:
* The 4D and 5D restore index `fiber(g)[i,j,k]` only, dropping l and o (B15d).
* For ChebyshevFirst and ChebyshevSecond, no weight `1/√(1−x²)` is used, so the coefficients are *not* Chebyshev coefficients.
* A domain that does not start at 0 maps outside [−1,1], which gives a DomainError. [probe] `ChebyshevFirst(t², 4)` on −1:0.01:1 raises `acos(-2.0)`.

#### 4.9.7 Chebyshev collocation (`spectral.jl:319-393, 937-1064`)

* **Points:** `Chebyshev(N)` gives `x_j = −cos(πj/(N−1))`, ascending. [probe] N=5: `[−1, −.707107, −6.1e−17, .707107, 1]`. `Chebyshev(x::Vector)` maps these to `(x_j+1)(x[end]−x[1])/2 + x[1]`, and `unitpoints` maps back.
* **`ChebyshevMatrix(x)`**, generic over any node vector (`spectral.jl:355-361`):
  ```
  N = length(x)−1;  c = [2, 1…1, 2] .* (−1).^(0:N)
  D = (c ⊗ c⁻¹) ./ (X − Xᵀ + I);   D −= Diagonal(rowsum(D))
  ```
  `ChebyshevMatrix(c::Chebyshev)` uses **`−points`** (descending cos nodes), giving Trefethen's `cheb(N−1)`. [probe] `ChebyshevMatrix(3) = [1.5 −2 .5; .5 0 −.5; −.5 2 −1.5]`.

  Applying it to data sampled on the ascending points gives **−dv/dx** (B13). [probe] `gradient_chebyshev(x³)` on Chebyshev(9) gives `−3x²`.
* **`ChebyshevVector(x, N)`** = `[0; reverse(first row of inv(D[1:N−1,1:N−1]))]`. It is an integration weight vector: `w·v ≈ ∫_{−1}^{1} v`. [probe] `ChebyshevVector(9)·x² = 0.6666…` (exact 2/3); `ChebyshevVector(4) = [0, 1.1111, .6667, .2222]`. `ChebyshevQuadrature` in grid.jl:1119 uses it.
* **`chebyshevfft(v)`** = `fft([v; reverse(v[2:N−1])])` (length 2N−2, even extension).
* **`gradient_chebyshevfft(v)`** is Trefethen's `chebfft` (Program 18) adapted to ascending nodes:
  ```
  N = length(v);  U = −real(chebyshevfft(v));   d = i·[0:N−2, 0, 2−N:−1]
  W = real(ifft(d ⊙ U))
  w[2:N−1] = −W[2:N−1] / sqrt(1 − cos²(π(1:N−2)/(N−1)))
  w[1] = Σ_{k=0}^{N−2} k² U[k+1]/(N−1) + ½(N−1)U[N]
  w[N] = Σ_{k=0}^{N−2} (−1)^{k+1} k² U[k+1]/(N−1) + ½(N−1)(−1)^N U[N]
  ```
  The result is correct for the derivative in the unit coordinate u ∈ [−1,1]. It does not rescale by 2/(x_end − x₀). [probe] x³ gives 3x² exactly.
* **`gradient2_chebyshevfft`** uses `u = W2/√(1−x²) − x·W1/(1−x²)^{3/4}`, with the endpoints left at 0. The correct formula is `W2/(1−x²) − x·W1/(1−x²)^{3/2}`, with endpoint formulas. This is bug B14. [probe] x⁴ gives `[0, 1.0154, 4.0176, 1.62, 0, …]` against the exact `12x² = [12, 10.24, 6, 1.76, 0, …]`. `laplacian_chebyshevfft` inherits the bug.

#### 4.9.8 Clenshaw-Curtis `clenshawcurtis(n)` (`spectral.jl:1081-1104`)

```
N = n−1; θ_k = πk/N; v = ones(N−1) over interior k=1..N−1
if N even: w[1] = 1/(N²+1)   (standard: 1/(N²−1));  w[N+1] = 0 (standard: same as w[1])
           v −= Σ_{k=1}^{N/2−1} 2cos(2kθ)/(4k²−1);  v −= cos(Nθ)/(N²−1)
else:      w[1] = 1/N²;  w[N+1] = 0 (standard: 1/N²)
           v −= Σ_{k=1}^{(N−1)/2} 2cos(2kθ)/(4k²−1)
w[2:N] = (2/N)·v;  return reverse(w)
```

The interior weights are standard; the **end weights are not** (B9). The sum is < 2. [probe] `clenshawcurtis(7) = [0, .253968, .457143, .520635, .457143, .253968, .027027]` with sum 1.96988. `clenshawcurtis(8)` has sum 1.97959, and `clenshawcurtis(9)·x²` = 0.6503 (against 2/3). `clenshawcurtis(t::Vector)` multiplies by L/2.

#### 4.9.9 Lagrange barycentric interpolation (`spectral.jl:616-760`)

```
w_j = 1 / ∏_{i≠j}(v_j − v_i)
p(x) = ∏_i (x − v_i) · Σ_j w_j y_j / (x − v_j)      # first barycentric form
```

At a node, 0·∞ gives NaN, and the TF methods fall back to `t(x)` (the field's own interpolation, which returns the nodal value). [probe] On nodes 0:.25:1: `w = [10.6667, −42.6667, 64, −42.6667, 10.6667]`. For `x³−x`: p(0.3) = −0.273 (exact), p(0.5) = −0.375.

* **`lagrangepolynomial(t, x::AbstractMatrix)`**, bug B17b: the fallback condition is `iszero(j) && isnan(...)`, which never fires, and the result uses `out[i]` instead of `out[i,j]`.
* **`resample_lagrange(v, n, Val(q))`** resamples dimension q to n equispaced points (`resample(range, n)` = same endpoints, n points), keeping the other dims. It uses precomputed `wxv = ∏(xi−xh)·(w./(xi−xh))` dotted along axis q, with the same NaN fallback. [probe] `x³−x` resampled to 9 points reproduces the cubic exactly.
* **`rootspolynomial(v, x) = ∏(x − v_i)`**. [probe] 0.3 gives −0.000945. `resample_roots(f, 3)` gives [0,0,0].

#### 4.9.10 Sinc resampling (`spectral.jl:523-610`)

`p(x) = Σ_i y_i · sinc((x − x_i)/h)`, where `sinc(z) = sin(πz)/(πz)` (Julia's normalized sinc) and h = step. In N-D it is applied dimension by dimension through `Val(q)`. [probe] `x³−x` on 0:.25:1 resampled to 9 points gives `[0, −.111408, −.234375, −.318310, −.375, −.397887, −.328125, −.159155, 0]`, exact at the nodes. `resample_sinc(v::Vector)` requires `points(v)` to be a range (it uses `step`).

#### 4.9.11 N-D wavenumber products

`fftwavenumber(N,M)` = `ProductSpace(fftwavenumber(N), fftwavenumber(M))`, a lazy grid of `Chain(k₁, k₂)`. [probe] (4,5) gives entries `(k₁ ∈ [0,1,−2,−1], k₂ ∈ [0,1,−3,−2,−1])`. The `spectral_diff_*(t, i, N, M, …)` variants multiply `fiber(t)[n,m,…]` by `ω[(n,m,…)[i]]`.

### 4.10 Plotting algorithms (Cartan.jl helpers and MakieExt)

* **`spacing(x)`** (`Cartan.jl:324-329`). 1D: `Σ‖x_{i+1} − x_i‖/(n−1)`, using the **fiber** values, i.e. the embedded points. N-D: `min over dims d of mean‖Δ_d x‖`.
* **`argarrows(t, s, siz)`** returns only `(; lengthscale = s)`. The tip and shaft sizes are commented out (`Cartan.jl:926-933`).
* **Scale factors** used by the helpers (M = base points as a field, t = the field). "mean col norm" means `value(Σ_points map(norm, columns(t_p)) / n)`, one value per column:

| function | s | Makie lengthscale | primitives |
|---|---|---|---|
| `scaledarrows(M, t::VectorField)` | `spacing(M) / (Σ‖t_p‖/n)` | s/3 | `arrows(M,t)` → arrows2d, or arrows3d if the fiber is 3D (`MakieExt:375-379`) |
| `scaledarrows(M, t::TensorOperator)` | `spacing(M) / max(mean col norm)` | s/3 | one `arrows2d/3d` per column (`MakieExt:380-384, 387-428`) |
| `arrowsbundle(M, t::VectorField)` | `spacing/(Σ‖t‖/n)` | s/2 | `scatter(points)` + `arrows!(M, t)` + `arrows!(M, −t)` (`MakieExt:290-299`) |
| `arrowsbundle(M, t::TensorOperator)` | `spacing/min(mean col norm)` | s/2 | as above, per column |
| `planesbundle(M, t)` | `spacing/min(mean col norm)` | half-extent s/2 | `arrows(M, Σcols)` plus, per point, a `mesh!` of the unoriented parallelogram (or `poly!` if `poly=true`) (`MakieExt:247-264`); **bug B4: undefined `M` at line 249** |
| `spacesbundle` | same | s/2 | arrows of Σcols plus 3 unoriented planes (v1v2, v1v3, v2v3) per point (`MakieExt:266-288`) |
| `planes(M, t; lengthscale=1)` | — | — | per point, `mesh(orientedplane(p, v1·ls, v2·ls))` or `poly`, then `scatter!(M, color=:black)` (`MakieExt:329-346`) |
| `spaces(M, t)` | — | — | arrows of Σcols plus 3 oriented planes (`MakieExt:348-369`) |
| `scaledplanes`/`scaledspaces` | `spacing/min(mean col norm)` | `lengthscale = s/2` | → planes/spaces (`MakieExt:321-327`) |
| `scaledfield`/`scaledbundle` | — | — | dispatch on `mdims(fibertype(t))`: 1 → arrows, 2 → planes, else spaces (`MakieExt:311-319`) |
| `tangentbundle(M 1D, t=gradient(M))` | — | — | arrowsbundle; 2D M with `t=jacobian(M)` → planesbundle (broken, B4) (`MakieExt:234-239`) |
| `normalbundle(M, t=normalframe(M))` | — | — | same routing. [probe] 2D fails with MethodError because `normalframe` returns a VectorField, not a TensorOperator. |

[probe] lengthscales:
* `scaledarrows` on a 5×5-per-unit 2D field: 0.25098;
* on the unit circle with 26 points and `unitframe`: 0.08311648892348515 (= spacing 0.2493/3);
* `tangentbundle` of the same circle: 0.12467854345810114.

* **Plane geometry** (`Cartan.jl:906-909, 925`):
  * `_orientedplane(p, v1, v2) = p .+ [0 v1+v2; v1 v2]`, a 2×2 grid, so `vec` (column-major) gives the polygon order `[p, p+v1, p+v1+v2, p+v2]`;
  * `_unorientedplane(p, v1, v2) = p .+ [−v1−v2 v1+v2; v1−v2 v2−v1]`, giving the polygon `[p−v1−v2, p+v1−v2, p+v1+v2, p−v1+v2]` (centered, half-extents v1 and v2).
  * `orientedplane` wraps the grid as a TF over `OpenParameter(2,2)`, which **fails** because `OpenParameter(::Int...)` for ≥ 2 dims calls a nonexistent `OpenTopology(::ProductSpace)` (bug B2). [probe] `planes(...)` and `scaledfield(curve, unitframe)` throw.
* **`gridargs(M, t, args)`**:
  * with `gridsize = n`: `resample(M, n)` and `resample(t, n)`. `resample(TF, sizes)` = `TF(resample(base), t.(points(resample(base))))` evaluates by interpolation;
  * with `arcgridsize`: `arcresample(M, n)` and `t` evaluated at the new points;
  * the key is always stripped.
* **`streamargs`:**
  * 3D field: default `gridsize = (11,11,11)`;
  * `streamargs(dim::Bool, args)`: `(32,32,1)` if dim (a tangent-space stream on a 3D-embedded surface), else `(32,32)`;
  * a user `gridsize` is extended with `1` when dim.
* **Variation traversal** (`Cartan.jl:663-858`), with `leaf(v, i, k)` defined in grid.jl:147-259 (slice at index i, or at a float coordinate, along dim k):
  * `variation` iterates the **last** dim, `alteration` dim 1, `modification` dim 2.
  * `!` forms: `fun` is called first and `fun!` for the rest. `Val(true)` empties the axis before each frame, for animation with `sleep(t)`.
  * `linegraph(M::TF{Chain,2,Grid}, f=speed)`: `variation!` draws leaves `v[:, i]` for all i along dim 2, then `_alteration` draws `v[i, :]` for all i. Each line is colored by `f(leaf)`, using `lines(curve, f)` → `color = f(curve)`.
  * With `gridsize = (n₁, n₂)`: the first loop resamples dim 2 to n₁ coordinates and draws `leaf(v, 1)`, `leaf(v, float(x_i))` for i = 2..n₁−1, then `leaf(v, size[end])`. The second loop draws `leaf(v, float(x_i), 1)` for all n₂ coordinates.
  * [probe] A 10×13 polar surface gives 13 lines of 10 points followed by 10 lines of 13 points.
  * `linegraph(v::TF{Chain,2}, f::TensorField)`: `colorrange = extrema(Real(f))`, plots `leaf(v,1,1)` then all leaves in both directions (the first one twice), colored by the leaf of f.
  * 3D `linegraph`: every axis-parallel line `leaf2(v, i, j, k)` for k = 1,2,3, with the other two indices ranging over `c = ((2,3),(1,3),(1,2))`.
* **Tangent-space streamplot** `streamplot(M::VectorField, m::VectorField 2D)` (`MakieExt:536-557`):
  * When the surface M is embedded in 3D (`mdims(fibertype(M)) ≠ 2`): streamplot the 2D parameter field lifted to 3D, `p ↦ Point(m(p)₁, m(p)₂, 0)`, over `points(m).v..., ClosedInterval(−1e−15, 1e−15)`. `arrow_size = 0.2·√(surfacearea(M)/∏w)·min(w)/min(gs₁, gs₂)`, where w = `widths` of the parameter domain. Then `makietransform(M, st, Val(3))` sets the plot's `transform_func` to `p ↦ Point(M(p))`, so the curves are pushed through the embedding.
  * When M is 2D: set the axis limits to the extrema of M's x and y, and use `makietransform(M, st, Val(2))`.
  * The same transform trick is used for `volume/contour(M, m 3D)`, `contour/contourf(M, m 2D|3D)` and `contour3d(M, m)` (`MakieExt:134-158`).
* **Makie's `heatmap(x, y, z)`** receives cell **centers** (`points(t).v...`) and converts them to edges: [probe] 7 centers become 8 edges. The rule is midpoints between centers, extended by half a step at each end. LeanPlot must replicate this.

---

## 5. Display and printing

### 5.1 REPL output of the types in scope (Cartan core, `topology.jl:63,269,316-333`)

* A `LocalTensor` / `LocalFiber` prints as `base ↦ fiber` (compact: `base↦fiber`). If the fiber type is `InducedMetric` (a Coordinate), only the base is printed.
* A `TensorField` is an `AbstractArray{LocalTensor}` and prints as `N-element TensorField{…full type…}:` followed by one `base ↦ fiber` line per element. [probe]
  ```
  4-element TensorField{…}:
                  0.0 ↦ 0.0
    0.5 ↦ 0.479425538604203
   1.0 ↦ 0.8414709848078965
   1.5 ↦ 0.9974949866040544
  ```
  The padding is Julia's pair alignment. Lean goldens should compare the data (`base`, `fiber`) and **not** the whitespace or type header.
* FFT output [probe]: `0.0 ↦ 2.318391510016154 + 0.0im`, `4.1887902047863905 ↦ -0.8414709848078965 + 0.5180694479998514im`, …
* `FourierSpace`, `Chebyshev` and `LagrangeWeights` print as plain numeric column vectors: the frequencies, the points, and the nodes respectively.
* A `RealRegion` built from ranges prints as `(x0-chain):(step-chain):(xend-chain)`. [probe] `ProductSpace(0:0.5:1, 0:1.0:2)` prints as `(0.0v₁ + 0.0v₂):(0.5v₁ + 1.0v₂):(1.0v₁ + 2.0v₂)`. `text/plain` shows the 3×3 matrix of `0.5v₂+1.0v₃`-style entries.
* Grassmann Chains in containers print with 6 significant digits, e.g. `1.0v₁ + 0.333333v₂ + 0.333333v₃`. A TensorOperator prints as `(col₁)v₁ + (col₂)v₂ + …`, e.g. `(-1.0v₂-1.0v₃)v₁ + (1.0v₂-0.0v₃)v₂ + (-0.0v₂+1.0v₃)v₃`. This belongs to Grassmann's printer, which another report covers.
* `Global{N}` prints as `Global{N}(value)`.

### 5.2 Plot dispatch table (MakieExt): what each field type becomes

All rows were confirmed by [probe] against CairoMakie (see `probe_makie.out`) unless marked (src). "color by f" means `color = Real.(vec(fiber(f)))`.

| Call | Resulting Makie plots (function, args, key attributes) | line |
|---|---|---|
| `lines(t::RealFunction, f=speed)` | `lines(x, y; color = f(t))`. The default colors by `speed` = \|f'\|. [probe] ex = (0.0124, 1.00003) for sin | 173 |
| `lines(t::PlaneCurve / SpaceCurve, f=speed)` | `lines(Point2/3.(fiber); color = speed)` in an Axis or LScene. [probe] unit circle color ≈ 1, helix ≈ √2 | 171-174 |
| `lines(t::ComplexMap 1D, f=speed)` | `lines(re, im; color = f(t))` | 175-176 |
| `lines(t::ScalarMap)` | if discontinuous: `lines(base(graphbundle(t)))`; else `lines(TF(GridBundle{1}(base), fiber))`, i.e. a RealFunction line over the node x-coordinates (1D meshes) | 164-170 |
| `lines(t::RectangleMap / HyperrectangleMap)` | `lines(boundarycomponents(t))`: 4 (or 6) boundary leaves, each a line colored by its speed. [probe] SurfaceGrid gives 4 `lines` | 162-163 |
| `lines(t::IntervalMap{TensorOperator}, f)` | one `lines` per column curve `getindex.(t,i)`; `lines(M, t)` draws `M + t_i` | 207-232 |
| `lines(p::SimplexBundle)` | `lines(Vector(points))` (homogeneous points, so the leading 1 becomes a coordinate) (src) | 618-619 |
| `linegraph(t::RealFunction)` | `lines(x, y)` with no color | 189-190 |
| `linegraph(t::GradedField 1D)` | one `lines(x, y_i)` per component, i = 1..binomial(mdims, G). [probe] 2 lines, default cycle colors | 191-206 |
| `linegraph(t::SurfaceGrid)` | `linegraph(graph(t))`: a 3D grid of iso-lines colored by speed | 184-185 |
| `linegraph(M::TF{Chain,2|3,GridBundle})` | variation grid lines (§4.10) | 627-797 |
| `linesegments(t::RealFunction …)` | same forms as `lines` → `linesegments` with speed color. [probe] | 160-178 |
| `linesegments(e::SimplexBundle)` | edges (n = 2): `linesegments(pointpair.(e[immersion(e)], ↓V))`; otherwise `linesegments(edges(e))`. [probe] 5 edges → 10 points | 799-806 |
| `wireframe(t::SimplexBundle)` | `linesegments(edges(t))` | 810-811 |
| `wireframe(M::GridBundle)` | `wireframe(GeometryBasics.Mesh(M))` | 814 |
| `wireframe(M::TF)` | `wireframe(base(M))` | 815 |
| `wireframe(M::TF{Chain,2,Grid})` | `wireframe(GridBundle(fiber(M)))`; 3D → `wireframe(boundarycomponents(M))` | 822-825 |
| `wireframe(t::SurfaceGrid)` | `wireframe(graph(t))` → 3D mesh wireframe in an LScene [probe] | 496 |
| `scatter(p::RealFunction)` | `scatter(x, y)` | 604 |
| `scatter(p::TF)` | `scatter(vec(fiber(p)))`. A real fiber is treated as y over the index; Chain fibers become Points. [probe] | 606 |
| `scatter(p::SimplexBundle)` | `scatter(submesh(p))` (vertices) | 608 |
| `scatter(p::FaceBundle)` | `scatter(submesh(means))` (element centroids). [probe] 2 points | 610 |
| `scatter(t::ComplexMap)` | `scatter(vectorize(t))` | 107-109 |
| `text(p::SimplexBundle)` | `text(submesh(p); text=string.(vertices(p)))`. [probe] text = `["1","2","3","4"]` | 613 |
| `text(p::FaceBundle)` | text at centroids, labeled with `string.(subelements(p))` | 615 |
| `mesh(M::SimplexBundle)` | if mdims = 2 (1D): `lines(sm, args[:color]); plot!(sm, args[:color])`, which **requires** a `color` kwarg. Otherwise `mesh(submesh(M), array(immersion(M)); args...)` (vertices np×d, faces nt×n). [probe] default shading | 856-874 |
| `mesh(t::ScalarMap)` | `mesh(base(t); color = fiber)` per-vertex colors. [probe] ex = (0, 3) | 854 |
| `mesh(M::FaceMap)` | `mesh(interp(M))`: nodal averages first. [probe] ex = (1, 2) | 852 |
| `mesh(M::GridBundle)` | `mesh(GeometryBasics.Mesh(M); shading = mdims(M) ≠ 2, backlight = 1)` | 819 |
| `mesh(M::TF{Chain,2,Grid})` | `mesh(GridBundle(fiber(M)))`: quad mesh of the embedded surface, normals if 3D. [probe] shading=true, backlight=1.0; plane → shading=false | 826-831 |
| `mesh(M::TF{Chain,3,Grid})` | `mesh(boundarycomponents(M))`, the 6 faces | 832-837 |
| `mesh(M::TF{Chain,2,Grid}, f::TF)` | same plus `color = vec(fiber(Real(f)))`. [probe] 130 = 10·13 colors | 844-849 |
| `mesh(M, f::Function)` | `mesh(M, f(M))`. If ndims ≠ 2: `mesh(boundarycomponents(M), f)` (drops kwargs) | 850-851 |
| `mesh(t::SurfaceGrid)` | `mesh(Makie.Mesh(base(M)); color)`. **Broken:** `Makie.Mesh` is the *plot type*, not `GeometryBasics.Mesh` (B22). [probe] MethodError | 838-843 |
| `mesh(t::ComplexMap 2D)` | `mesh(vectorize(t))`, the image of the grid under z ↦ (Re, Im). [probe] 2D mesh, shading=false | 116-121 |
| `mesh(M complex, t complex)` | `mesh(vectorize(M), Real(angle(t)))` | 124-129 |
| `surface(t::SurfaceGrid)` | `surface(xs, ys, Z; color = Z)` in an LScene. [probe] | 454 |
| `surface(t::SurfaceGrid, f)` | `color = abs.(f(Real(t)))`. [probe] ex = (0, .997) for `abs` | 455 |
| `surface(t::ComplexMap 2D)` | `surface(xs, ys, abs.(z); color = angle.(z), colormap = :twilight)`. [probe] color ex = ±π | 456 |
| `surface(t::GradedField 2D, f=gradient_fast)` | one surface per component, `color = abs(f(x → y_i))` | 458-467 |
| `surface(M::ScalarMap, f=identity)` | `mesh(hcat(submesh, z), array(immersion); color = f(M))` (the discontinuous case maps colors). [probe] mesh in an LScene | 876-885 |
| `surface(M::FaceMap real)` | `surface(interp(M), f)` | 886-891 |
| `contour / contourf / contour3d / heatmap (t::SurfaceGrid)` | `f(xs, ys, Z)`. [probe] contour args (7,), (9,), (7,9) | 480-482 |
| same on `TF{Chain{V,G},2,RealSpace{2}}` | one plot per component (binomial(mdims, G)). [probe] 2 heatmaps / 2 contours for a 2D vector field | 484-491 |
| `contour/contourf/contour3d (t::ComplexMap 2D)` | `f(xs, ys, abs.(z))` | 470-473 |
| `heatmap(t::ComplexMap 2D)` | `heatmap(xs, ys, angle.(z); colormap = :twilight)` | 475-478 |
| `contour/contourf/contour3d/heatmap/wireframe/streamplot/surface (t over FiberProductBundle)` | convert to `TF(GridBundle(base), fiber)` then plot (several of these drop the kwargs) | 186, 457, 483, 497, 535 |
| `volume / contour / voxels (t::VolumeGrid)` | `f(x₀..x₁, y₀..y₁, z₀..z₁, Real.(fiber(resample(t))))`, using interval endpoints. [probe] | 443-448 |
| `volumeslices(t::VolumeGrid)` | `volumeslices(xs, ys, zs, data)` | 449-451 |
| `arrows(t::VectorField)` | `arrows2d(t)`, or `arrows3d` if the fiber mdims is 3 | 563-565 |
| `arrows2d/3d(f::VectorField over AlignedRegion{2}, 2-comp)` | `arrows2d(xs, ys, u, v)` | 575-578 |
| `arrows2d/3d(f over RealSpace{2})` | `arrows2d(Point.(vec(points)), Point.(vec(fiber)))`. [probe] 63 origins, 63 directions, lengthscale 1, color black | 579-582 |
| `arrows2d/3d(f over GridBundle)` | same with `vec(Point.(points))` | 583-586 |
| `arrows2d/3d(M::VectorField, f::VectorField)` | origins = `fiber(M)` (embedded points), directions = `fiber(f)` | 587-590 |
| `arrows(M, f::TensorOperator over GridBundle)` | `arrows(TF(fiber(M), fiber(t)))` → one plot per column | 387-428 |
| `arrows(t::TF over SimplexBundle)` | `arrows(Point.(↓V.(points)), Point.(fiber))`. [probe] arrows2d | 596-597 |
| `streamplot(m::VectorField over RealSpace)` | if `isrange(m)`: `streamplot(m, xs, ys[, zs])` → `streamplot(p ↦ Point(m(Chain(p...))), dims...)`; else over `to_interval` of each axis. The 3D default is gridsize (11,11,11); 2D uses Makie's default (32,32,32). The default color is Makie's `norm`. [probe] | 524-534 |
| `streamplot(m::ScalarField over RealSpace)` | `streamplot(gradient_fast(m))`. [probe] | 524 |
| `streamplot(m::ScalarMap, dims...)` | `streamplot(gradient_fast(m), dims...)` | 525 |
| `streamplot(m::VectorField over SimplexBundle, dims::ClosedInterval...)` | `streamplot(p ↦ Point(m(Chain(1, p...))), dims...)`, using `sinterp` per evaluation | 526 |
| `streamplot(M::VectorField, m::VectorField 2D)` | tangent-space streamlines (§4.10) | 536-557 |
| `streamplot(t::TF{TensorOperator,2,RealSpace{2}}, m)` | one streamplot per column | 429-441 |
| `streamplot / arrows(t::ComplexMap)` | `vectorize` first. [probe] **Broken for a bare complex 2D field** (no matching method: the complex→`vectorize` overload is shadowed or ambiguous, B23) | 110-121 |
| `graylines(x, lw=3)` | `lines(x; colormap = :grays, linewidth = lw)` + `lines!(x; color = :black, linestyle = :dash)`. [probe] | 32-58 |
| `Makie.convert_arguments(P::PointBased, a::SimplexBundle)` | `Vector(points(a))`, homogeneous | 599 |
| `Makie.convert_single_argument(a::LocalFiber)` | references undefined `P`, broken (B24) | 600 |

Axis choice (Makie's automatic behavior, observed in the probes): 2D point data gets an `Axis`. 3D points, `surface`, `volume`, `mesh` with 3D vertices, and `wireframe` of a graph get an `LScene` with an `axis3d` plot added first.

### 5.3 UnicodePlots display override (`UnicodePlotsExt.jl:73-78`)

When UnicodePlots is loaded, `Base.display(t)` prints `typeof(t)` **then** a Unicode plot:
* PlaneCurve → `lineplot(x, y)`; RealFunction → `lineplot(points, fiber)`;
* 1D ComplexMap → `lineplot(re, im)`; 2D ComplexMap → `heatmap(angle; colormap = :twilight, xfact = step(x), yfact = step(y), xoffset = x₀, yoffset = y₀)`;
* 1D GradedField → `lineplot(points, Grassmann.array(fiber))` (one series per component);
* SurfaceGrid → `heatmap(Real.(fiber); xfact = step(x), yfact = step(y), xoffset = x₀, yoffset = y₀)`.

Other conversions:
* `contourplot`, `surfaceplot` and `isosurface` sample the **interior** grid (`v[2:end−1]`) through the field's interpolating call `t(Chain(x,y))`.
* `surfaceplot(ComplexMap)` uses `radius` with `colormap = :twilight`.
* `spy(p::SB)` = `spy(antiadjacency(p))`.
* `boxplot(Vector{Chain{V,G}})` labels groups with `string.(chainbasis(V,G))`.

---

## 6. Examples and golden candidates

### 6.1 From `docs/src/plot.md` (verbatim code; LeanPlot IR goldens can be produced by running `probe_makie.jl`-style dumps)

`plot.md:15-28` (arrows2d):
```julia
xs = LinRange(0, 2pi, 20)
ys = LinRange(0, 3pi, 20)
us = [sin(x) * cos(y) for x in xs, y in ys]
vs = [-cos(x) * sin(y) for x in xs, y in ys]
xy = TensorField(OpenParameter(xs,ys),Chain.(us,vs))
strength = vec(fiber(norm(xy)))
arrows2d!(xy, lengthscale = 0.2, color = strength)
```

`plot.md:31-38` (arrows3d; note `OpenParameter(-5:2:5,…)` works because the arguments are ranges):
```julia
ps = OpenParameter(-5:2:5,-5:2:5,-5:2:5)
ns = map(p -> 0.1 * Chain(p[2], p[3], p[1]), ps)
arrows3d(TensorField(ps, ns), shaftcolor = :gray, tipcolor = :black, align = :center, axis=(type=Axis3,))
```

The remaining examples, with their line ranges:
* contour: `plot.md:56-62` (with `levels=-1:0.1:1`), the Himmelblau log-levels example (`67-75`), and the curvilinear `mesh(xyz; shading=NoShading)` example (`78-97`);
* contour3d: `109-116, 123-124`; 3D contour: `128-137`; contourf: `159-169`;
* heatmap: irregular centers `[1,2,4,7,11]×[6,7,9,12,16]` (`180-187`), `sin(x*y)` (`190-200`), log x-scale (`203-213`);
* linesegments: `228-235`, `ys = sin(TensorField(1:0.2:10))`;
* mesh: `243-256`, the polar `TensorField(ProductSpace(rs,thetas),Chain.(xs,ys,zs))` with `mesh(xyz,TensorField(xyz,zs))`;
* scatter: `266-280`; streamplot: FitzHugh-Nagumo `fun.(OpenParameter(-1.5:0.1:1.5,-1.5:0.1:1.5))` (`295-312`);
* surface: `319-344`; volume: `350-371`; wireframe: `410-415`, `wireframe(graph(xyz))` of `sinc(√(X²+Y²)/π)`.

**Voxels** (`plot.md:390-402`) uses `OpenParameter(3,3,3)` and `OpenParameter(8,8,8)`. [probe] **These raise MethodError** (bug B2), so the documented example is broken upstream.

UnicodePlots examples:
* `plot.md:421-534`, e.g. `lineplot(TensorField([-1, 2, 3, 7], [-1, 2, 9, 4]), title="Example", name="my line", xlabel="x", ylabel="y")`;
* the four-series `lineplot(TensorField(1:10, Chain.(0:9,3:12,reverse(5:14),fill(4, 10))), color=[:green :red :yellow :cyan])`;
* `boxplot(TensorField(1:6, [1, 3, 3, 4, 6, 10]))`;
* `polarplot(TensorField(range(0, 2π, length=20), range(0, 2, length=20)))`;
* `surfaceplot(TensorField(OpenParameter(-8:.5:8,-8:.5:8),sombrero),colormap=:jet)`;
* `isosurface(TensorField(rrr,torus), cull=true, zoom=2, elevation=50)`.

FEM examples from `fiber.md:823-869`, for context. They need Adapode and MATLAB:
```julia
pt,pe = initmesh("circleg","hmax"=>0.1) # MATLAB circleg mesh
A,M = assemble(pt,1,1,0)
...
function solvepoisson(t,e,c,f,k,gD=0,gN=0)
    m = volumes(t)
    b = assembleload(t,f,m)
    A = assemblestiffness(t,c,m)
    R,r = assemblerobin(e,k,gD,gN)
    return TensorField(t,(A+R)\(b+r))
end
```
and `fiber.md:445-448`: `lines(lin); scaledarrows!(lin,unitframe(lin),gridsize=50)`.

### 6.2 Oracle-probe goldens (Julia printed; exact up to float formatting)

FEM, two-triangle mesh: points (0,0),(1,0),(0,1),(1,1); elements (1,2,3),(2,4,3):
```
volumes         [0.5, 0.5]
gradienthat[1]  ∇λ = (-1,-1), (1,0), (0,1)
gradienthat[2]  ∇λ = (0,-1), (1,1), (-1,0)
degrees         [1, 2, 2, 1]        weights [1.0, 0.5, 0.5, 1.0]
assembleload    f=1 → [1/6, 1/3, 1/3, 1/6];  f=x → [0, 1/3, 0, 1/6]
assembleincidence(pt, 1.0, m) → [0.5, 1.0, 1.0, 0.5]
edges           [1,2],[1,3],[2,3],[2,4],[3,4]
adjacency       [0 1 1 0; 1 0 2 1; 1 2 0 1; 0 1 1 0]
antiadjacency   [0 1 1 0; -1 0 2 1; -1 -2 0 -1; 0 -1 1 0]
∂ (boundary)    [1,2],[1,3],[2,4],[3,4]
edgesindices    [3,2,1],[5,3,4]
neighbors       [2,0,0],[0,1,0]      facetsigns [-1,1,1],[1,1,1]
incidence       [1 0; 1 1; 1 1; 0 1]
means           (1/3,1/3), (2/3,2/3)   barycenters (sum) (1,1),(2,2) with homogeneous 3
interp([1,3])   [1, 2, 2, 3]            pretni([1,2,3,4]) [2, 3]
gradient_2(x+2y) (1,2),(1,2)            u(0.25,0.25) = 0.75, findfirst((.75,.75)) = 2
submesh         [0 0; 1 0; 0 1; 1 1]    array(immersion) [1 2 3; 2 4 3]
```

Other FEM cases:
```
CW triangle (0,0),(0,1),(1,0):  volumes [0.5];  gradient_2(u=x) = (-1, 0)   ← orientation bug B3
Laplacian single triangle:      [1 -1 -1; -1 1 -1; -1 -1 1]
1D 0:0.25:1:  elements [1,2],[2,3],[3,4],[4,5]; boundary [[1],[5]], vertices [1,5]
              volumes .25×4; gradienthat (-4, 4); load [.125,.25,.25,.25,.125]
              gradient_2(x²) [.25,.75,1.25,1.75]; gradient (nodal) [.25,.5,1.0,1.5,1.75]
              u(0.3) for x² = 0.1; affineframe 0.25
unit tet: volumes [1/6]; gradienthat (-1,-1,-1),(1,0,0),(0,1,0),(0,0,1); load [1/24]×4
          edges [1,2],[1,3],[2,3],[1,4],[2,4],[3,4]; ∂ [1,2,3],[1,2,4],[1,3,4],[2,3,4]
          edgesindices [1,2,4,3,5,6]; neighbors [0,0,0,0]
surface tri (0,0,0),(2,0,0),(0,0,2) in 3D: volumes [2.0]; ∧ = 4.0v₂₄;
          gradienthat (-.5,0,-.5),(.5,0,0),(0,0,.5)
```

Spectral goldens:
```
fftwavenumber(8) = [0,1,2,3,-4,-3,-2,-1];  fftwavenumber(7) = [0,1,2,-4,-3,-2,-1]   (B10)
rfftwavenumber(8) = 0:4;  rfftwavenumber(7) = 0:3
fftspace(8) = 0:0.125:0.875 ; fftspace(7) = (0:6)/7 ; rfftspace(8) = 0:0.125:0.5
r2rspace(8,9,1) = 1:8 ; r2rspace(8,5,1) = 0:7
fftspace(0:0.5:3.5) = (2π/3.5)·(0:7) = [0, 1.7951958020513104, …, 12.566370614359172]
r2rspace(0:0.5:3.5, 9) = (π/3.5)·(1:8)
fftshift(fftspace(0:1:7))/(2π/7) = [-3,…,4] ; N=7 → [-3,…,3]
spectral_sum_fft(8) = -i·[0,1,1/2,1/3,-1/4,-1/3,-1/2,-1]
spectral_diff_chebfft(7) = i·[0,1,2,3,4,5,0,-5,-4,-3,-2,-1]
toeplitz1(8) = [0,-1.2071067811865475,0.5,-0.20710678118654754,3.06e-17,0.2071067811865475,-0.5,1.2071067811865472]
toeplitz2(8) = [-5.5,3.414213562373095,-1.0,0.585786437626905,-0.5,0.585786437626905,-1.0,3.414213562373093]
spectral_sum_impulse(8) = 0.39269908169872414:-0.09817477042468103:-0.2945243112740431
clenshawcurtis(7) = [0.0,0.2539682539682542,0.4571428571428573,0.5206349206349206,0.45714285714285713,0.2539682539682539,0.02702702702702703]
clenshawcurtis(8) = [0.0,0.19014100721820837,0.3522424237181591,0.43720840579832637,0.4372084057983263,0.3522424237181591,0.19014100721820837,0.02040816326530612]
Chebyshev(5) = [-1,-0.7071067811865476,-6.123233995736766e-17,0.7071067811865475,1]; angle 0:π/4:π
Chebyshev(0:0.5:2) = [0,0.2928932188134524,0.9999999999999999,1.7071067811865475,2]
ChebyshevMatrix(4) = [3.1667 -4 1.3333 -0.5; 1 -0.3333 -1 0.3333; -0.3333 1 0.3333 -1; 0.5 -1.3333 4 -3.1667]
ChebyshevVector(4) = [0,1.1111111111111112,0.666666666666666,0.22222222222222238]
ChebyshevVector(9) = [0,0.177965,0.247619,0.393464,0.361905,0.393464,0.247619,0.177965,0]
lagrangeweights(0:0.25:1) = [10.666666666666666,-42.666666666666664,64.0,-42.666666666666664,10.666666666666666]
FourierSpace(FourierCosine, 0:0.25:1, 4) = [0, π, 2π, 3π]
FourierCosine(2, TensorField(0:0.25:1)) = [1.0,0.8775825618903728,0.5403023058681398,0.0707372016677029,-0.4161468365471424]
N=8 grid 0:2π/8:7π/4:  fft(sin) = [0, -4i, 0, 0, 0, 0, 0, 4i]; axis (8/7)·(0:7)
  dct(sin) = [0,1.599647,-0.765367,-0.906127,0,-0.18024,0,-0.04229]; axis (4/7)(0:7)
  dst(sin) = [0.079547,0.46194,-0.151364,0,-0.067437,0,-0.053152,0]; axis (4/7)(1:8)
  gradient_impulse = [0,-1.207107,0.5,-0.207107,0,0.207107,-0.5,1.207107]
  convolve(sin,sin) = [-4,-2.828427,0,2.828427,4,2.828427,0,-2.828427]
  integral_fft(cos+1) = [0,1.492505,2.570796,3.063301,3.141593,3.219884,3.712389,4.79068]
Chebyshev(9): gradient_chebyshevfft(x³) = 3x² = [3,2.56066,1.5,0.43934,0,…]
              gradient_chebyshev(x³) = −3x²  (B13);  gradient2_chebyshevfft(x⁴) = [0,1.015356,4.017634,1.619984,0,…]  (B14)
```

---

## 7. Dependencies on other chakravala packages

* **Grassmann.jl** (with DirectSum and Leibniz underneath):
  * types: `Chain, Values, Variables, TensorOperator, Submanifold, Manifold, GradedVector, Single`;
  * operators: `∧` (wedge, n-ary and broadcast over vectors), `⋅` (contraction), `\` on `Values{M,Chain}` (Cramer solve for barycentric coordinates, `composite.jl:723-734`), `∈` (simplex containment, `composite.jl:736-749`), `↓`;
  * functions: `value, vector, mdims, abs/norm, detsimplex, volumes, affineframe/vectors, grad/gradient` (`composite.jl:814-831`), `mean/means, centroid(s), barycenter(s), curl(s)` (`composite.jl:935-958`), `list`, `combo`, `binomial`, `pointpair` (GeometryBasics ext), `vectorize` (complex → Chain), `radius, angle, realvalue, imagvalue, Leibniz.combinations, Leibniz.indexparity!`, and `∂` for the boundary signs.
* **MeshTopology.jl**:
  * types: `SimplexTopology, DiscontinuousTopology, LagrangeTopology{Edges,Triangles,Tetrahedra}, ImmersedTopology`;
  * all of `MT/element.jl` (§4.3);
  * accessors: `columns, reducedcolumns, vertices, verticesinv, refnodes, totalnodes, nodes, elements, subelements, fulltopology, fullimmersion, subimmersion, topology, sdims, iscover, isfull, isdiscontinuous, isdisconnected, continuous, discontinuous, disconnect, discontinuousvertices, getimage, cornertopology, getedge, lagrangesimplex, facetsimplex, refine, resample`.
  * **Broken symbol resolution in MT 0.1.0:** `fibertype`, `fiber`, `means`, `Grassmann`, `Leibniz`, `∂`, `Submanifold` and `Variables` are used but never imported. This breaks `assembleincidence`, `assembleload`, `interp`, `gradient`, `∂`, `facets`, `edgesindices` and `interior` at runtime. The oracle monkey-patch (in `probe_fem.jl` line 2) is:
    ```julia
    import MeshTopology; @eval MeshTopology begin; const Grassmann = Main.Grassmann; const Leibniz = Main.Grassmann.Leibniz; const ∂ = Main.Grassmann.∂; const Submanifold = Main.Grassmann.Submanifold; const Variables = Main.Grassmann.Variables; fiber(x)=Main.Cartan.fiber(x); means(a...)=Main.Cartan.means(a...); end
    @eval MeshTopology fibertype(x::AbstractArray) = eltype(x)
    @eval MeshTopology fibertype(x::$(Cartan.TensorField)) = $(Cartan.fibertype)(x)
    ```
* **AbstractAnalysis.jl:** `Limit` (for plotting `last(t)`); nothing else in scope.
* **Adapode.jl** (a downstream consumer): the assembly functions (`assemblestiffness, assembleconvection, assemblerobin, assembleSD, solvepoisson`, …) and `gradientCR, trilength, trinormals` consume `volumes`, `gradienthat` and `means`.
* **Other Cartan files** used by this scope: `fiber.jl` (bundle types, `affinehull` `fiber.jl:540-553`, `varmanifold` `:825`), `topology.jl` (`ProductSpace`, `resample`, `widths`, `isrange`, `LocalFiber` show), `grid.jl` (`leaf`, `leaf2`, `integrate` = trapz `:1226`, `gradient_fast`, `ChebyshevQuadrature` `:1117-1126`), `diffgeo.jl` (`speed :544`, `graph`, `normal`, `unitnormal`, `jacobian`, `normalframe`, `surfacearea :469-471`, `arcresample :1296`), and `quotient.jl` (`OpenParameter :19-24`, `ClampedTopology`).

---

## 8. Lean 4 porting notes

### 8.1 Type design: indices vs runtime values

| Julia | Lean | Compile-time index? |
|---|---|---|
| ambient dimension d (from `varmanifold(d+1)`) | `(d : Nat)` index on `PointCloud d` | **yes**: all kernels are specialized per d (`@[specialize]`) |
| vertices per simplex `sdims = n` | `(n : Nat)` index on `SimplexTopology n` | **yes**: element loops unroll over `Fin n` |
| number of nodes and elements | runtime `Nat` fields | no |
| vertex id arrays | flat `Array UInt32` of length `n·nt`, plus an erased proof `∀ i, ids[i] < nNodes` | proof only; use `arr[i]'h`-style access for bounds-check-free hot loops |
| homogeneous coordinate | **drop it**: store `FloatArray` stride d | — |
| grid rank N and per-axis sizes | `(N : Nat)` index; `shape : Vector Nat N` runtime | the rank is an index |
| FFT domain kind (fft/rfft/r2r(kind)/physical) | an inductive `SpectralKind` as a type index on `Domain` | **yes**: makes `ifft ∘ fft` domain-typed, and `irfft` needs the original length n in the index or as a field |
| `OrthogonalTransform` | `structure OrthoBasis where f : Nat → Float → Float; a b : Float` | no |
| TensorOperator per element | `Vector (Vector Float d) n` or flat `FloatArray` stride d·n | n and d are indices |

Guideline: indices are only `d`, `n`, grid rank, and spectral kind. Sizes stay runtime, since dependent sizes on `FloatArray` would force proof plumbing through every allocation. Proofs to weave in cheaply:
* `edges` output is sorted and unique;
* `interp ∘ (const field) = const`;
* `Σ_i ∇λ_i = 0` (a `theorem` over `Float` is not provable, so state it on ℚ/ℝ models or as a property test);
* `idst ∘ dst = id` (property test);
* `fftspace ∘ fftspace = id` on domains (provable by `rfl` if designed as an involutive sum type).

### 8.2 Performance: how Julia gets its speed, and Lean equivalents

* **`@generated` specialization on n and d** (`affineframe` at `element.jl:417`, `initpoints` at `:71-78`, Grassmann's Cramer inverse, `neighbors` at MT:373): in Lean, write kernels generic in `(n d : Nat)` with `@[specialize]`/`@[inline]`. For n ≤ 4, d ≤ 3, hand-write closed forms: triangle `revrot` formula, tet via cross products. Keep the Gram-inverse fallback (§4.1) for the rest.
* **Assembly loops** (`assembleincidence`, `interp`, degrees) are O(nt·n) scatter-adds: an `FloatArray` loop with `uset` and no allocation.
* **Quadratic hot spots to fix** (the port keeps the semantics and fixes complexity):
  * `facetsinterior`/`faces`/`∂` use linear `findfirst` over the facet list, O(F²). Use `Std.HashMap (sorted facet key) → index` while preserving first-appearance order.
  * `edgemeshdata` is also O(ne·E); use a HashMap.
  * `sinterp`/`findfirst` point location is O(nt) per query, and streamplots call it per step. Add a uniform-grid bucket index, or a walk from the last hit element (neighbors-based).
  * `edges` via a sparse adjacency plus `findall(triu)` gives column-major order. Replicate it by sorting pairs by `(j, i)`.
* **FFT:** Julia calls FFTW with plans. Lean needs a native complex FFT on an interleaved `FloatArray` (re, im): iterative radix-2 plus mixed-radix 3/5/7, with Bluestein for other N. Add `rfft` via a half-length complex FFT and r2r kinds REDFT10, REDFT01, RODFT10, RODFT01 via FFT of symmetric extensions. Cache twiddles in a `Plan N` structure; N can be a runtime field of the plan. The oracle compares at relative 1e-12. Alternatively, FFI to FFTW; the user's C-FFI resources are available, but a native port keeps the project self-contained.
* **Chebyshev D matrix** is O(N²) dense. Build it once and cache it in a `Chebyshev N` structure.
* **Caches:** the global bundle-id caches have no Lean equivalent. Canonical storage is already dense, so drop them.

### 8.3 Tricky semantics and upstream bugs (faithful mode vs fixed mode)

Recommend a `Faithful` flag, or separate `_jl` functions, only where goldens are needed. The default should be the correct math.

| id | Location | Behavior | Recommendation |
|---|---|---|---|
| B1 | MT/element.jl:312 | `assembleincidence` uses undefined `fibertype`, so `assembleload` crashes | implement the intended scatter-add |
| B2 | quotient.jl:21-24, Cartan.jl:908-909 | `OpenParameter(Int,Int[,…])` fails; `planes`, `spaces`, `orientedplane` and the docs' voxels examples are broken | implement `OpenParameter(n…)` = LinRange(0,1,n) product |
| B3 | element.jl:458-471 | the 1D and triangle `gradienthat` use unsigned measure, so CW elements get negated gradients | fixed mode: signed det or Gram inverse. Faithful: replicate for goldens. **Mesh ingest should reorient to CCW.** |
| B4 | MakieExt.jl:249 | `planesbundle` uses undefined `M` (should be `b,f`) | fix |
| B5 | element.jl:536 | `incidence(::FrameBundle)` references undefined `cols` | fix: `incidence(subimmersion(t))` |
| B6 | MT/element.jl:339 | `interior(e)` has its arguments swapped | fix: `sort(setdiff(1:totalnodes, vertices(e)))` |
| B7 | element.jl:506 | the "Laplacian" is `diag(#incident elements) − edge multiplicity` | expose both `graphLaplacian` (correct) and `cartanLaplacian` (faithful) |
| B8 | element.jl:687,695 | `LagrangeEdges` uses undefined `pt`; node-3 formula suspect | fix to `c_i + (x−2)c_ij` |
| B9 | spectral.jl:1089-1097 | Clenshaw-Curtis end weights are `1/(N²+1)` and 0 | fixed: standard CC; faithful for goldens |
| B10 | spectral.jl:776, 781, 783 | odd-N FFT wavenumbers are shifted | fixed: `[0..(N−1)/2, −(N−1)/2..−1]` |
| B11 | spectral.jl:42 | `rfftspace(ProductSpace)` uses `x.v[2]` twice | fix to `x.v[1]` |
| B12 | spectral.jl:73 | even-N `fftshift` axis is off by one from the data | fixed: `ω·(−N/2 : N/2−1)` |
| B13 | spectral.jl:353, 937 | `ChebyshevMatrix(::Chebyshev)` uses descending nodes, so `gradient_chebyshev` gives −d/dx | fixed: D on ascending nodes |
| B14 | spectral.jl:462-518 | the second-derivative Chebyshev-FFT formula has wrong powers and zero endpoints | fixed: Trefethen second derivative, or D² |
| B15 | spectral.jl:214, 223, 232, 225-227, 282, 300 | ChebyshevSecond(n,1)=1; OT maps assume x₀=0; a₀ not halved in restore; 4D/5D restore drops indices; no Chebyshev weight | fixed mode rewrites these; the faithful 1D Fourier-cosine path is the only one worth goldens |
| B16 | spectral.jl:381 | 3D `chebyshevfft` i=3 reverses along `dims=2` | fix |
| B17 | spectral.jl:602, 656 | 5D sinc typo `l.m`; matrix lagrangepolynomial uses `out[i]` and a dead NaN fallback | fix |
| B18 | spectral.jl:872 | `gradient_rfft(::AbstractArray{3,T})` has its type parameters swapped (method unreachable) | fix |
| B19 | spectral.jl:907, 913, 909-912 | the curve `integral_fft` default uses the *diff* vector; zero mean gives NaN | fix both |
| B20 | spectral.jl:49, 52, 61, 69 | the frequency step uses `(N−1)h` instead of `Nh`; derivative wavenumbers are unitless | document; offer `physicalFreqs` with 2π/(Nh) |
| B21 | Cartan.jl:651 | 5D `boundarycomponents` declares `FixedVector{8}` with 10 entries | fix |
| B22 | MakieExt.jl:838-843 | `Makie.Mesh` (the plot type) is used instead of `GeometryBasics.Mesh` | LeanPlot: implement the intended real-colored quad mesh |
| B23 | MakieExt.jl:110-121 | `streamplot`/`arrows2d` on a bare complex 2D field: no method at runtime | implement via vectorize |
| B24 | MakieExt.jl:600, 101-104 | `convert_single_argument` uses undefined `P`; the `Limit`/`LocalTensor` methods for `mesh(t, f)`/`lines(t, f)` drop `f` | fix |
| — | element.jl:15-20 | 4 exported names are undefined in Cartan | move to the Adapode port |

Other non-obvious semantics to keep:
* All indices are 1-based in Julia goldens. Convert at the JSON boundary.
* `edges` ordering is column-major over the upper triangle (§4.3).
* "Edge i is opposite vertex i" in `edgesindices`, Lagrange edge nodes, and `interpCR`.
* `volumes` are unsigned.
* `assembleload` evaluates f at nodes and divides by n.
* `interp` averages by incident-element count, not by area.
* Frequency domains are involutive and remember the physical domain.

### 8.4 What to skip or redesign

* **Skip:**
  * `Requires`-based loading (`Cartan.jl:984-1009`);
  * the MATLAB, TetGen, Triangle, QHull, MiniQhull, Delaunay and Meshes wrappers. Replace them with **file ingest** of the P/E/T matrices (§3.3), plus a small native structured-mesh generator for tests: rectangle to triangles with a choice of diagonal, cube to 6 tets, disk;
  * the global caches; `display`, `sleep` and animation loops (`variation(v, t, …)`).
* **Redesign:**
  * The special-function extensions become one generic `TensorField.map`.
  * Plotting becomes a **plot IR** shared with LeanPlot (below) rather than an imperative Makie binding.

### 8.5 LeanPlot co-development: plot IR spec derived from MakieExt

```lean
inductive Prim where
  | lines (pts : Array (Vector Float k)) (color : Option FloatArray) (linewidth : Float := 1.5) (dash : Bool := false) (cmap : Colormap := .viridis)
  | linesegments (pairs : Array (Vector Float k × Vector Float k)) (color : Option FloatArray)
  | scatter (pts : Array (Vector Float k)) (color : Option FloatArray)
  | text (pts : Array (Vector Float k)) (labels : Array String)
  | arrows (origins dirs : Array (Vector Float k)) (lengthscale : Float) (color : Color := .black)   -- arrows2d / arrows3d by k
  | mesh (verts : Array (Vector Float k)) (faces : Array (Vector Nat 3 ⊕ Vector Nat 4)) (color : Option FloatArray) (shading : Bool) (backlight : Float)
  | wireframe (verts …) (faces …)
  | surface (xs ys : FloatArray) (z : Grid2) (color : Grid2) (cmap : Colormap)
  | heatmap (xs ys : FloatArray) (z : Grid2) (cmap : Colormap)     -- xs,ys = centers; the renderer computes edges
  | contour (xs ys : FloatArray) (z : Grid2) (levels : Option FloatArray) (filled : Bool) (in3d : Bool)
  | volume (bbox : Box3) (data : Grid3) | volumeslices (xs ys zs) (data) | voxels (bbox) (data)
  | streamplot (f : Vec k → Vec k) (box : Box k) (gridsize : Vector Nat k) (transform : Option (Vec k → Vec m))
structure Figure where axis : AxisKind (Axis2 | Scene3) ; prims : Array Prim
```

Implement `Field.plot : TensorField … → Figure` following §5.2 row by row. Each golden compares the primitive kind, the array shapes, color extrema (or full arrays at small N), lengthscale and gridsize with the Julia dump (§9). The scale-factor rules in §4.10 are pure functions and should be ported exactly.

### 8.6 Suggested module decomposition (rough LOC)

| Module | Contents | LOC |
|---|---|---|
| `Cartan/FEM/Mesh.lean` | `PointCloud d`, `SimplexTopology n`, `SimplexMesh d n`, 1D `initMesh`, P/E/T ingest, `totalMesh`, 1D `refine!`, structured generators | 400 |
| `Cartan/FEM/Geometry.lean` | volumes (signed and unsigned), detsimplex, wedge, affineframe, means/centroids/curls, gradienthat (closed forms plus Gram), faithful variants | 350 |
| `Cartan/FEM/Topology.lean` | adjacency and antiadjacency (COO/CSR), edges (column-major order), edgesindices, facets/faces/∂ (hash-based), oriented ∂, neighbors, facetsigns, incidence, degrees, laplacians, interior | 450 |
| `Cartan/FEM/Assembly.lean` | assembleincidence, assembleload, interp, pretni, gradient (nodal and face), weights, interpCR | 250 |
| `Cartan/FEM/Locate.lean` | point location (bucket grid plus walk), barycentric solve, `sinterp` | 220 |
| `Cartan/FEM/Lagrange.lean` | Lagrange node placement (edges, triangles, tets) with the counting functions | 250 |
| `Cartan/Spectral/FFT.lean` | complex FFT (radix-2, mixed radix, Bluestein), rfft/irfft, bfft, r2r kinds, dct (orthonormal), dst/idst | 650 |
| `Cartan/Spectral/Domain.lean` | `FourierSpace`, fftspace/rfftspace/r2rspace (+ProductSpace), fftshift, wavenumbers, involution lemmas | 250 |
| `Cartan/Spectral/Transforms.lean` | TF wrappers, flt/bflt/rflt/brflt/iflt/irflt, fgt family, convolve | 250 |
| `Cartan/Spectral/Periodic.lean` | spectral_diff/sum (N-D along an axis), gradient_fft/rfft, integral_fft, impulses, toeplitz1/2, derivetoeplitz | 300 |
| `Cartan/Spectral/Chebyshev.lean` | points, D matrix, ChebyshevVector, chebfft/ifft, derivative (1D, 2D, 3D along an axis), fixed second derivative, CC weights (both modes) | 350 |
| `Cartan/Spectral/Interp.lean` | LagrangeWeights, barycentric evaluation, resample_lagrange N-D, resample_sinc N-D, rootspolynomial | 300 |
| `Cartan/Spectral/Series.lean` | OrthogonalTransform, series coefficients and restore, 1D-5D | 200 |
| `Cartan/Plot/IR.lean` | shared with LeanPlot | 250 |
| `Cartan/Plot/Dispatch.lean` | the §5.2 table | 750 |
| `Cartan/Plot/Helpers.lean` | spacing, argarrows scales, plane polygons, gridargs/streamargs, leaf traversal, boundarycomponents | 250 |
| `Cartan/Plot/Unicode.lean` | text-mode lineplot/scatter/heatmap (braille canvas), display hooks | 450 |
| `Tests/Golden/{FEM,Spectral,Plot}.lean` | JSON golden loaders and comparators | 450 |
| **Total** | | **≈ 6,020** |

---

## 9. Oracle test plan (Julia → JSON goldens)

General rules:
* Run in the Julia 1.13 env. For FFT and Toeplitz use the FFTW-augmented copy (`scratchpad/fftenv`, created offline from the same manifest; never modify the original env).
* Apply the MeshTopology monkey-patch from §7 for FEM.
* Dump Float64 with 17 significant digits (`repr`), complex as `[re, im]`, and indices 1-based with a `"base": 1` tag.
* Each record holds `{fn, args, out, faithful: true}`.
* Tolerances: exact for integer topology; rel 1e-13 for geometry; rel 1e-12 (plus abs 1e-12·max|x|) for FFT paths.

1. **Frequency and wavenumber tables:**
   * `fftspace/rfftspace/r2rspace(N)`, `r2rspace(N, kind, fs)` for N = 1..33 and all kinds 3..10;
   * the range versions on `range(a, b, length=N)` for (a,b) ∈ {(0,1), (−π,π), (0.3, 7.1)};
   * `fftwavenumber/rfftwavenumber/r2rwavenumber(N[,kind])`, `spectral_{diff,sum}_{fft,rfft}(N)`, `spectral_diff_chebfft(2)(N)`, `spectral_sum_impulse(N)`, `toeplitz1/2(N)`;
   * `fftshift/ifftshift` axes.
2. **FFT wrappers:**
   * random real vectors (seeded `MersenneTwister(k)`, uniform [−1,1]) for N ∈ {1,2,3,4,5,6,7,8,9,15,16,17,31,32,33,64,100,127,128}: `fft, ifft, bfft, rfft, irfft, brfft, dct, idct, r2r(kind 3..10), dst, idst`, with output axis and fiber;
   * 2D (N×M ∈ {(4,5),(8,8),(7,6)}) along dims 1 and 2 and full;
   * `convolve` of two random vectors.
3. **Spectral calculus:**
   * `gradient_fft/rfft`, `integral_fft/rfft`, `integrate_fft/rfft`, `gradient_impulse`, `integral_impulse` on sin(kθ), cos(kθ)+c and random periodic signals (N even and odd, to capture B10);
   * `derivetoeplitz(2)*v`;
   * the 2D `gradient_fft(matrix, i)`.
4. **Chebyshev:**
   * `Chebyshev(N)` and `Chebyshev(range)` points and angles, `unitpoints`, `ChebyshevMatrix(N)` and `ChebyshevMatrix(x)` for random sorted x, `ChebyshevVector(N)`, `clenshawcurtis(N)` for N = 2..24;
   * `chebyshevfft`;
   * `gradient_chebyshevfft` and `gradient2_chebyshevfft` on monomials x^0..x^8 and random coefficient polynomials, N ∈ {5,9,16,17}; 2D along each dim; `gradient_chebyshev`.
5. **Interpolation:**
   * `lagrangeweights` on equispaced, Chebyshev and random nodes (N = 2..12);
   * `lagrangepolynomial` at 50 random x in [a−0.2L, b+0.2L] **plus every node** (the NaN fallback path);
   * `resample_lagrange` and `resample_sinc` 1D (n ∈ {N, 2N−1, 3N}) and 2D;
   * `rootspolynomial`.
6. **Series:** `FourierCosine`/`FourierSine` coefficients and restore on `cos(kt)+c`, `t(π−t)` over 0:π/64:π, and the 2D product; ChebyshevFirst/Second **only on [0,L] domains** (otherwise DomainError).
7. **Laplace and Gabor:** `flt/bflt/rflt/brflt(σ::Number and Vector)`, `iflt/irflt`, `fgt` family with a Gaussian window; small N (8, 9).
8. **FEM geometry and topology:** meshes from native generators, emitted as P/E/T:
   * a rectangle [0,1]² split into 2·a·b triangles, a,b ∈ {1,2,3,5}, both diagonal patterns, with ±15% random jitter;
   * a copy with **randomly flipped orientation** (to capture B3);
   * 1D random sorted points;
   * the unit cube split into 6 tets, and 2×2×2 of them;
   * a triangulated sphere octant in 3D (surface).

   Dump: `volumes, detsimplex, ∧, affineframe, gradienthat, degrees, weights, adjacency, antiadjacency, edges, edgesindices, ∂, ∂(t,u) with u=ones, facets, faces(k), neighbors, facetsigns, incidence, Δ, means, barycenters, centroids, curls, assembleload(f ∈ {1, x, x·y+1}), interp(random FaceMap), pretni, gradient_2 and gradient of linear and quadratic u, interpCR(random edge values)`, `sinterp` at 100 random points (including outside, which gives 0), and `refinemesh!` 1D with random η.
9. **Lagrange nodes:** `LagrangeBundle` for triangles and tets, M = 2..5, on 1-2 element meshes: dump the node coordinates in local order (validates §4.7 before porting).
10. **Plot IR** (via CairoMakie, headless; extend `probe_makie.jl`):
    * for each row of §5.2, dump `{axis kind, [plotfunc, converted args (full arrays for N ≤ 64), color array or constant, colormap, linewidth, linestyle, lengthscale, gridsize, shading, backlight, text]}`;
    * inputs: the §6.1 doc examples (downsized) plus the probe fixtures (sin curve, unit circle and helix, 7×9 SurfaceGrid, 2D vector field, complex z², 10×13 polar surface, 5³ volume, two-triangle mesh).
    * Also dump `spacing`, the computed lengthscales for scaledarrows/arrowsbundle/tangentbundle, and `boundarycomponents` sizes.
    * UnicodePlots goldens are text: render with UnicodePlots in a separate env if it resolves (it did **not** resolve against the current manifest because of a ColorTypes/StatsBase compatibility conflict), otherwise derive from the §5.3 source rules.
