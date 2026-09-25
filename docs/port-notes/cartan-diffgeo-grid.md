# Cartan.jl `grid.jl` + `diffgeo.jl` — Lean 4 porting spec

Scope: `/Users/alokbeniwal/chakravala/Cartan.jl/src/grid.jl` (1465 lines) and `/Users/alokbeniwal/chakravala/Cartan.jl/src/diffgeo.jl` (1287 lines), Cartan v0.4.16 (git `02a105d`, "upgraded to Julia v1.13"; identical to the registered 0.4.16 in the oracle env).

Everything marked **[verified]** was executed against the Julia 1.13 oracle env
(`julia --startup-file=no --project=/private/tmp/claude-502/-Users-alokbeniwal-Grassmann/c6cc2308-bfca-4b9a-ad33-d89b110132a8/scratchpad/juliaenv`).

Artifacts produced while writing this spec (all in `/private/tmp/claude-502/-Users-alokbeniwal-Grassmann/c6cc2308-bfca-4b9a-ad33-d89b110132a8/scratchpad/diffgeo_probe/`):

* `oracle_diffgeo.jl` — ready-to-run golden dumper (117 goldens, 0 errors). Run: `julia --startup-file=no --project=<env> oracle_diffgeo.jl out.json`.
* `goldens_diffgeo.json` — its output (340 KB). Array data is **column-major flattened** (`vec(A)`, first index fastest); Chains are lists of components in Grassmann basis order; `TensorOperator` is a list of *columns*.
* `p1.jl … p14.jl` — the probes behind every [verified] claim.

Notation used below: `S(·)` = a stencil numerator applied to an array, `D(g) = S(g)/S(x)` = the derivative estimate, `h` = uniform step, `n`/`l` = number of points along the stencil axis, `f[k]` = value at 1-based index `k` along the stencil axis (Julia indexing, kept 1-based in this document; convert to 0-based in Lean).

---

## 1. Purpose & scope

`grid.jl` is the discrete-calculus engine for fields sampled on rectilinear (tensor-product) grids (`GridBundle`) with optional quotient (gluing) topologies:

* finite-difference derivatives: 4th-order "slow" 5-point stencil, 2nd-order "fast" 3-point stencil, 1st-order backward/forward stencils; each with open (one-sided 3rd-order), periodic and mirror boundary closures; the derivative is always computed as a **ratio of the same stencil applied to the field and to the grid coordinates** (`D(f) = S(f)/S(x)`), which makes it parameterization/spacing agnostic on uniform grids;
* per-axis and full gradients for N = 1..5 dimensional grids, metric-weighted variants, sparse `Tridiagonal` difference matrices;
* multilinear interpolation (evaluation of a `TensorField` at arbitrary coordinates, 1–5 D) including wrap/mirror for quotient topologies; leaf (slice) extraction;
* quadrature: trapezoid (`trapz`/`integrate`), cumulative trapezoid (`cumtrapz`/`integral`/`∫`), weighted Riemann ("Riesz") sums with trapezoid/Gauss–Legendre/Chebyshev/Clenshaw–Curtis weights, per-axis reductions, Haar averages, layer-cake;
* arc length, arc-length re-parameterization/resampling;
* discrete delta (`hat`/`spike`) and Heaviside step fields;
* fiber products of fields (outer-product grids).

`diffgeo.jl` is the differential-geometry layer built on those operators:

* curves (`IntervalMap`, `PlaneCurve`, `SpaceCurve`, `AbstractCurve`): speed, (unit) tangent/normal/binormal, curvature, radius, torsion, generalized curvatures, Frenet/Darboux/Bishop frames, Cartan (connection) matrices, evolute/involute, bending energy, tangent angle/total curvature/winding, reconstruction of a plane curve from curvature (`planecurve`), osculating planes, Wronskians;
* hypersurfaces (`VectorField` over an n-dim grid into R^(n+1)): tangent n-vector, normal (Hodge dual), unit normal, `normalnorm` (area element), Jacobian/Weingarten operators, first/second/third fundamental forms, shape operator, principal curvatures/axes, mean/Gauss curvature (intrinsic and "extrinsic sector" forms), surface area, "sector integral" volumes, intrinsic metric grids, Christoffel symbols of 1st/2nd kind, geodesic ODE right-hand side;
* exterior calculus front-end (`d`, `∂`, `δ`, `curl`, `div`, `∇`, `Δ`), Lie derivative/bracket of vector fields, connections;
* principal-bundle "action" machinery used for pullback integrals `integrate(ϕ, f)` and flux integrals;
* shape generators: unit circle/helix/sphere/disk/ball/pipe/cylinder/cone/conoid, revolutions, ruled/scroll/tangent surfaces, sectorization, link maps and Gauss linking number;
* small numeric utilities (ball volume, sphere area, bounds/clamping).

Out of scope here (other reports): `TensorField`/`GridBundle`/`PointArray`/`ProductSpace` core types (`Cartan.jl`, `fiber.jl`, `topology.jl`), `QuotientTopology` (MeshTopology.jl `quotient.jl`; only the neighbour-remap semantics needed by stencils are specified here), spectral methods (`spectral.jl`: `gradient_fft`, `integral_fft`, `ChebyshevVector`, `clenshawcurtis`, `convolve`, … are *exported* from `grid.jl:19-22` but *defined* in `spectral.jl`), simplex/FEM (`element.jl`), Grassmann algebra (Chain, ∧, ⋆, ⋅, `TensorOperator`, `eigpolys`, `eigvals`).

---

## 2. Public API inventory

The two files carry 237 distinct names in `export` statements (`centraldiff` is exported by both; `gradient_fft`…`convolve` exported here but defined in `spectral.jl`; `tangent_fast`, `gausseintrinsicnorm_slow` exported but undefined).

Status legend: **OK** (works as described, [verified] where probed), **BUG** (runs but wrong vs. evident intent — replicate for oracle parity, see §8.6), **BROKEN** (throws in 0.4.16), **n/p** (not probed; read from source).

Type aliases used in signatures (defined in `Cartan.jl:118-148`, `topology.jl:382-385`):
`IntervalMap = TensorField{B,F,1,<:Interval}` (1-D base with *Real* coordinates),
`RealFunction` (IntervalMap with real fiber), `PlaneCurve`/`SpaceCurve` (fiber `Chain` with 2/3 components), `AbstractCurve` (fiber any `Chain`),
`ScalarField` (real fiber, any dim), `VectorField = GradedField{1}` (fiber grade-1 `Chain`), `RealSpace{N}` (base = array of `Coordinate{Chain{V,1,<:Real}}`), `RectangleMap`/`HyperrectangleMap` (2-D/3-D `RealSpace`), `DiagonalField`/`EndomorphismField` (fiber `DiagonalOperator`/`Endomorphism`), `IntervalRange` (`GridBundle{1}` whose points are an `AbstractRange`), `AlignedSpace{N}` (N-D `GridBundle` over a `ProductSpace` of ranges).

### 2.1 `grid.jl` — products, evaluation, interpolation

| Symbol | Signature(s) | Semantics | Line | Status |
|---|---|---|---|---|
| `fiberproduct` | `(f::TensorField, g::TensorField, fun::Function)` | New field over `base(f)×base(g)` (product grid, product topology) with fiber `fun(f[i…], g[j…])`; ranks (1,1)…(1,4),(4,1),(2,2),(2,3),(3,2) via `_product` | 25-68 | OK [verified 1×1] |
| `fibersphere` | same | as above but base `cross_sphere(base f, base g)` (pole gluing) | 69-71 | OK |
| `fibersector` | same | as above but base `cross_sector` (centre point collapse) | 72-74 | OK |
| `linterp` (unexp.) | `(x,x1,x2,f1,f2)`; `(m, t)` | scalar: `f1 + (f2-f1)*(x-x1)/(x2-x1)`; field: 1-D evaluation (§4.7) | 76, 114-137 | OK |
| `bilinterp`,`trilinterp`,`quadlinterp`,`quintlinterp` (unexp.) | scalar kernels (`x,y,…,x1,x2,…,f11,f21,f12,f22…`) and field versions `(m, t::Chain)` | nested linear interpolation, first axis innermost (§4.7) | 77-96, 272-456 | 2-D/3-D OK; 4-D field version **BROKEN** (§8.6 B7); 5-D n/p |
| callable `TensorField` | `m(s::Coordinate)`, `m(s::LocalTensor)`, `m(t::Real/Chain)` (1-D), `m(x,y)`, `m(t::Chain)` (2-D), `m(x,y,z)` (3-D), `m(t::Complex)`, `m(t::PseudoCouple)` (2-D) | evaluate by multilinear interpolation | 108-113, 272-277, 308-311, 352-355, 409-412 | OK 1-3D [verified] |
| `leaf` | `(m::RectangleMap, i::Int, j=2)`, `(m::RectangleMap, t::AbstractFloat, j=2)`, `m(t::Real)` | slice at index `i` / interpolated slice at coordinate `t` along axis `j` (default last axis), result is a 1-D field over the *other* axis | 147-156 | OK [verified] |
| `leaf`,`leaf2` 3-D | `(m::HyperrectangleMap, i/t, j=3)`, `leaf2(m,i,j,k=3)`, `leaf2(m,t,s,k=3)` | 2-D slice / 1-D line (bilinear in the two fixed coords) | 158-183 | OK n/p |
| `leaf`,`leaf3` 4-D; `leaf`,`leaf4` 5-D | … | slices of 4-D/5-D grids | 185-256 | **BUG/BROKEN** (§8.6 B8) |
| `leaf` (FiberProductBundle) | `(m, i::Int)`, `m(t::Int)`, `m(t::Real)` | column `i` / interpolated column | 258-264 | n/p |
| curve push-forward | `(X::VectorField{…,N})(Y::VectorField{B,Chain{V,1,T,N},1})` | evaluate field `X` along curve `Y`: `TensorField(base(Y), X.(fiber(Y)))` | 268 | OK n/p |
| | `(m::GridBundle{N})(t::VectorField{…,1})` | curve re-based onto grid points `m.(fiber t)` | 269 | n/p |
| `parametric` (unexp.) | `(t, m, d=diff(fiber)./diff(points))` | piecewise-linear evaluation using precomputed slopes, no topology | 141-145 | OK |
| `searchpoints` (unexp.) | `(p::AbstractVector, t)` | `(i, below)` bracketing index (§4.7) | 102-106 | OK |
| `reposition*` (unexp.) | | wrap/mirror of out-of-range coordinate (§4.7) | 98-100 | OK |

### 2.2 `grid.jl` — hat / heaviside

| Symbol | Signature | Semantics | Line | Status |
|---|---|---|---|---|
| `hat` | `hat(x::Real) = iszero(x) ? 1 : 0`; `hat(x::Chain)=∏ hat.(x)`; `hat(x,t)=hat(x-t)`; `hat(x::Chain,t)=∏hat.(x,t)` | Kronecker delta | 459-463 | OK |
| | `hat(t::TensorField, x...) = hat(base(t), x...)`; `hat(b::GridBundle, x::Chain)` | | 464-465 | OK |
| | `hat(b::GridBundle{1}, x=0)` … `hat(b::GridBundle{5}, x=0,y=x,z=y,w=z,v=w)` | zero field with a single `1.0` at the grid node **nearest** to `(x,y,…)`; all-zero if the point is outside `[p1,pn)` on any axis (§4.8) | 466-524 | OK [verified 1-D, 2-D] |
| `spike` | `const spike = hat` | alias | 525 | OK |
| | `hat(b::SimplexBundle[, x…])` | simplex version: `1` at argmin distance vertex | 527-533 | (FEM, n/p) |
| `heaviside` | `heaviside(x::Real) = x<0 ? 0 : 1` (so H(0)=1); `(x::Chain) = ∏`; `(x::LocalTensor)`, `(x::TensorField)` elementwise; `heaviside(x,t)=heaviside(x-t)`; Chain/LocalTensor/TensorField with `t...` → `Values(t)` | step function | 535-546 | OK [verified] |

### 2.3 `grid.jl` — difference operators

| Symbol | Signature | Semantics | Line | Status |
|---|---|---|---|---|
| `AbstractOperator`, `AbstractDifference` | abstract types | marker types | 550-551 | OK |
| `CentralDifference{N,M}` | empty struct | tag type: `M`=derivative order, `N`=variant | 552 | OK |
| `ZeroDifference{N}`, `FirstDifference{N}`, `SecondDifference{N}` | `= CentralDifference{N,0/1/2}` | | 553-555 | OK |
| `LinearAlgebra.Diagonal(x, ::Type{<:ZeroDifference})` | `I(length(x))` (Bool identity) | | 559 | OK [verified] |
| `Tridiagonal(x, ::Type{<:ZeroDifference})` | tridiagonal identity | | 560 | OK |
| `Tridiagonal(x, FirstDifference{-1})` | backward difference matrix (row 1 forward) | | 561-565 | OK [verified] |
| `Tridiagonal(x, FirstDifference{0})` | forward difference matrix (row n backward) | | 566-569 | OK [verified] |
| `Tridiagonal(x, FirstDifference{1})` | central difference matrix (1st/last row one-sided) | | 570-576 | OK [verified] |
| `Tridiagonal(x, SecondDifference{1})` | non-uniform 3-point 2nd derivative; rows 1/n degenerate | | 578-585 | OK [verified] |
| `centraldiff_calc(::FirstDifference{3},…)` / `(::FirstDifference{2},…)` (unexp.) | dispatch to slow / fast kernels | | 781-786, 897-905 | OK |

### 2.4 `grid.jl` — `centraldiff*` / `gradient*`

Generated by the loop `for fun ∈ (:_slow,:_fast,:_forw,:_back)` at `grid.jl:634-771`, so every name below exists in four variants (`X ∈ {slow, fast, forw, back}`):

| Symbol | Signature | Semantics | Line |
|---|---|---|---|
| `centraldiff_X` | `(f::AbstractArray, args...)` | wrap raw array as open `GridBundle`, apply stencil; with no extra args returns **raw numerators** `S(f)`; with a `d::DenseVector` returns `S(f)./d` | 670 |
| | `(f::AbstractArray, q::QuotientTopology, args...)` | same with topology `q` | 671 |
| | `(f::RealRegion)` = `ProductSpace(centraldiff_X.(f.v))` | per-axis denominators of a product of ranges | 672 |
| | `(f::GridBundle{N,…InducedMetric…,<:ProductTopology/OpenTopology})` | `ProductSpace` of per-axis denominators | 673-674 |
| | `(f::GridBundle{N,…InducedMetric…})` (quotient) | `sum.(value.(centraldiff_X_calc(f)))` — full N-D stencil on point Chains, summed over axes (§4.5) | 675 |
| | `(f::GridBundle{…,<:OpenTopology})` non-induced metric | `applymetric.(centraldiff_X(points(f)), metricextensor(f))` | 677 |
| | `(f::GridBundle)` non-induced, quotient | `applymetric.(sum.(value.(calc(f))), metricextensor(f))` | 678 |
| | `(f::AbstractRange, q::OpenTopology, s=size(f))` = `(f, s)` | | 679 |
| | `(f::AbstractRange, q::QuotientTopology, s)` | analytic denominators with topology (`calc(i,q,step,n)`) | 680-686 |
| | `(f::AbstractRange, s)` | analytic open denominators (`calc(i,step,n)`) | 687-693 |
| | `(dt::Real, s::Tuple)` | analytic open denominators for step `dt` | 694-700 |
| `centraldiff` | `(f::AbstractVector, args...) = centraldiff_slow`; `(f::AbstractArray, args...) = centraldiff_fast` | default variant by rank | 589-590 |
| `centraldifffiber`, `centraldiffpoints` (unexp.) | same split by rank | `…_fiber(f, args…) = calc(GridBundle(PointArray(0,fiber(f)),immersion(f)), args…)`; `…_points(f, args…)` same on `points(f)` | 591-594, 638-639 |
| `centraldiff_X_points` | `(f::TensorField{…RealSpace{…InducedMetric}}, ::Val{N})` | per-axis denominators for axis `N` using `subtopology(immersion(f), Val(N))`; returns `0f` if that axis has 1 point | 640-644 |
| `gradient_X` | `(f::IntervalMap, d::AbstractVector = centraldiff_X_points(f))` | `TensorField(base f, centraldiff_X_fiber(f, d))` = `D(f)` | 645-647 |
| | `(f::TensorField{…,N,<:AbstractArray}, d = centraldiff_X(base(f)))` | full gradient: fiber `Chain{Submanifold(N),1}(D₁f,…,D_Nf)` | 648-650 |
| | `(f::IntervalMap, ::Val{1}, d)` | same as 1-D | 651-653 |
| | `(f::TensorField{…RealSpace{…InducedMetric}}, n::Val{N}, d = centraldiff_X(points(f).v[N]))` | per-axis partial derivative `D_N f` (scalar-valued if fiber scalar) | 654-656 |
| | `(f::TensorField{…RealSpace}, n::Val{N}, d)` non-induced metric | per-axis with metric factor `sqrt(g_{N+1,N+1})` — **BUG** (loop only touches one element, §8.6 B5) | 657-664 |
| | `(f::TensorField, n::Val{N}, d = centraldiff_X_points(f, n))` | generic per-axis; returns `0f` when axis length 1 | 665-668 |
| | `(f::TensorField, n::Int, args...) = gradient_X(f, Val(n), args...)` | | 669 |
| `gradient` | `(f::IntervalMap, args...) = gradient_slow`; `(f::TensorField{…,<:AbstractArray}, args...) = gradient_fast` | **1-D real-parameter curves use the 4th-order stencil; everything else (incl. 1-D `ProductSpace` bases!) the 2nd-order one** | 596-597 |
| `unitgradient` | `(f::TensorField, args...)` | `t = gradient(f,…); t/abs(t)` | 598-601 |
| `derivative` | `(f::TensorField, args...) = gradient(f, args...)` | alias (imported from AbstractAnalysis, exported by Cartan) | 606 |
| | `(f::TensorField{B,F,2}) where F<:AbstractComplex` | Wirtinger `∂/∂z = (∂ₓf + ∂ᵧf / i)/2` with `i = imagunit(F)` | 607-611 |
| `imagunit` (unexp.) | `Complex{T}` → `im`; `Couple{V,B}` → `B` | | 603-604 |
| `centraldiffdiff` (unexp.) | `(f, dt, l)`, `(f, dt)` | twice-applied centraldiff; **BROKEN** for real `dt` (§8.6 B3) | 587-588 |
| `applymetric` (exported from diffgeo) | `(f::Chain{V,G}, g::DiagonalOperator{…Multivector})`, `(…DiagonalOperator{…Chain})`, `(f, g::Outermorphism)`, `(f, g::Endomorphism{…Simplex})`, generated `(x::Chain{V,G,T,N}, g::Simplex)` | componentwise `x_k / sqrt(g_kk)` | 773-779 |

### 2.5 `grid.jl` — q-analogs, Richardson, parallel reductions

| Symbol | Semantics | Line | Status |
|---|---|---|---|
| `qnumber(n,q) = (q^n-1)/(q-1)` | q-integer | 1045 | OK |
| `qfactorial(n,q) = prod(cumsum([q^k for k∈0:n-1]))` | `∏_{m=1..n} [m]_q` | 1046 | OK |
| `qbinomial(n,k,q)` | Gaussian binomial | 1047 | OK [verified `qbinomial(3,1,4)=21`] |
| `richardson(k)` | Richardson extrapolation weights, vector of length k+1: `[(-1)^(j+k) 2^(j(1+j)) qbinomial(k,j,4) / ∏_{n=1..k}(4^n-1) for j ∈ k:-1:0]`; sums to 1 | 1049 | OK [verified] |
| `psum(A, j)` | intended threaded `sum` along dim j — **BROKEN** (`sum!(…; dims)` has no method) | 1055-1065 | BROKEN [verified] |
| `pcumsum(A, j)` | threaded cumsum of each slice `A[…,k,…]` (k along dim j) **along dimension j of the (N-1)-dim slice**, i.e. along original axis j+1 (j<N) | 1056-1072 | OK but surprising [verified] |

### 2.6 `grid.jl` — quadrature

| Symbol | Signature | Semantics | Line | Status |
|---|---|---|---|---|
| `RieszQuadrature{L,G,T}` | `struct(v::T<:AbstractVector{L}, g::Vector{G}) <: DenseVector{L}` | nodes `v` + weights `g`; indexes like `v` | 1084-1091 | OK |
| `rieszweights` | `(t::FiberBundle)`, `(t::ProductSpace)` (per axis), `(t::RieszQuadrature)=t.g`, `(t::AbstractVector)=trapzweights(t)` | default weights = trapezoid | 1092-1095 | OK |
| `GaussLegendre` | `(N::Int)`: Golub–Welsch nodes on [-1,1] (eigenvalues of Jacobi matrix with off-diagonal `β_k = 0.5/sqrt(1-(2k)^-2)`), weights `2*V[1,:]^2`; `(x::AbstractVector)`: N=length(x) nodes mapped to `[x1,xN]`, weights scaled by `(xN-x1)/2`; `(t::ProductSpace)`, `(t::RieszQuadrature)=t` | | 1102-1115 | OK [verified] |
| `gausslegendre` | `(t::AbstractVector) = rieszweights(GaussLegendre(t))`, `(t::RieszQuadrature)`, `(t::FiberBundle)`, `(t::ProductSpace)` | weights only | 1097-1100 | OK |
| `ChebyshevQuadrature` | `(t::AbstractVector) = RieszQuadrature(t, ChebyshevVector(t))` (weights from spectral.jl), ProductSpace, RieszQuadrature | | 1117-1120 | n/p |
| `ClenshawCurtis` | `(t::AbstractVector) = RieszQuadrature(t, clenshawcurtis(t))` (spectral.jl:1078-1105) | | 1123-1126 | OK [verified via `integrate_clenshawcurtis`] |
| `TrapezoidQuadrature` | `(t::AbstractVector) = RieszQuadrature(t, trapzweights(t))` | | 1129-1131 | OK |
| `trapzweights` (unexp.) | `(t::FiberBundle)`, `(t::ProductSpace)` per axis, `(t::AbstractRange) = trapzweights(length, step)`, `(n::Int, h::Real) = [h/2, h, …, h, h/2]`, `(f::AbstractVector)` non-uniform `w_i = (x_{i+1}-x_{i-1})/2`, ends `(x2-x1)/2`, `(xn-x_{n-1})/2` | | 1133-1147 | OK [verified] |
| `metricvolume` | `(f) = principalnorm(base(f))`; `(f, j)`=`sqrt.(abs.(g_jj))` | volume density `sqrt‖det g‖` | 1149-1151 | **BROKEN** for induced metric [verified] |
| `metricfiber` | `(f) = fiber(principalaction(f))`; `(f, ::Val{J}) = fiber(f) .* sqrt.(abs.(g_JJ))` | fiber pre-multiplied by the metric density (identity for induced metric) | 1152-1154 | OK |
| `integral_{trapz,chebyshev,clenshawcurtis,gausslegendre}` | `(t, w = Weights(t))`, `(t, j::Int, w)`, `(t, ::Val{J}, w)` | `integral_riesz(t, [j,] w)` | 1156-1165 | OK [verified trapz, gl, cc] |
| `integrate_{…}` | same | `integrate_riesz(t, [j,] w)` | 1156-1165 | OK |
| `integrate_riesz` | `(f::TensorField{…,1}, d::DenseVector = rieszweights(f)) = d ⋅ metricfiber(f)`; `(f, j::Int/Val, d)`; `@generated (m::TensorField{…,N}, d::Values = rieszweights(m))` (weights per axis, reduce axes N..1); `@generated (m, ::Val{J}, d)` reduce one axis → field over remaining axes | weighted sum `Σ w_i f_i` | 1167-1193 | OK |
| `integral_riesz` | 1-D: `TensorField(f, cumsum(d .* metricfiber(f)))`; N-D (N=2..5): successive weighted `cumsum` along axes 1..N; per-axis `Val{J}` | cumulative weighted sum (NOT a cumulative trapezoid: `cumsum(w.*f)`) | 1195-1224 | OK [verified] |
| `integrate` | `integrate(args...) = trapz(args...)` | | 1226 | OK |
| `trapz` (exported by diffgeo) | 1-D `(f, d = diff(points(f)))`: `Σ (d_i/2)(g_i + g_{i+1})`; `(f, j::Int/Val{1})`; `(f::TensorField{…,1,<:IntervalRange})`: `h((f₁+f_n)/2 + Σ f₂..f_{n-1})`; N-D aligned `(f::TensorField{…,N,<:AlignedSpace{N}})`; N-D general `(m, D::Values = diff.(points(m).v))`; per-axis `(m, ::Val{J})` aligned and general | trapezoid rule | 1229-1283 | OK [verified] (aligned N-D non-induced **BROKEN** §8.6 B4) |
| `trapz1`, `cumtrapz1` (unexp.) | array kernels with steps `h...` | | 1233, 1245-1248, 1323-1327, 1340-1344 | OK |
| `integral` | `integral(args...) = cumtrapz(args...)` | | 1285 | OK |
| `∫` | `const ∫ = integral` (ASCII alias: `integral`) | | 1286 | OK |
| `cumtrapz` (exported by diffgeo) | 1-D `(f, d = diff(points))` **BUG** on non-uniform grids (§8.6 B1); `(f::…IntervalRange)` = `cumtrapz1(fiber, step)` correct; `(f, j::Int/Val{1})`; aligned per-axis `(m, ::Val{J})`; aligned N-D `(f::…AlignedSpace{N})` (N=2..5); general N-D `(m, D::Values)`; general per-axis `(m, ::Val{J})` | cumulative trapezoid, starting at 0 on the first node of each integrated axis | 1317-1377 | OK / BUG |
| `linecumtrapz` | `(γ::IntervalMap, f::Function)` | `cumtrapz(TensorField(base γ, f.(fiber γ) .⋅ fiber(gradient γ)))` = ∫ f(γ)·γ' dt | 1378-1380 | n/p |
| `integrate_haar` | `(f, z, θ = range(-π,π,70))` | `(Σ_i f(θ_i, z))/N` | 1384-1391 | **BROKEN** for scalar `z` (`.+=` on Float) [verified]; works for array `z` |
| `integral_haar` (unexp.) | same | `TensorField(θ, cumsum(f(θ_i,z))/N)` | 1393-1401 | OK [verified] |
| `minmax` (unexp.) | `(f)` | `(min, max)` single pass | 1405-1412 | OK |
| `layercake` | `(f, n::Int = length(f))` | `y = range(minmax(fiber f)..., length(f))` (**n ignored**), `TensorField(y, cakelayer.(Ref(f), y))`, `cakelayer(f,y) = integrate(y<0 ? -(f .≤ y) : f .≥ y)` | 1414-1420 | **BROKEN** [verified: promotion error] |
| `ArrayFunction{T,N,F}` | `struct(f::F, v::Array{T,N}) <: DenseArray{T,N}`; `ArrayFunction(v::Array, f) = ArrayFunction(f, f.(v))`; `getindex`,`size`,`length` forward to `v` | cached map | 1422-1434 | OK |
| `indefstep`,`countindef`,`countindef2`,`indefintegrate`,`indefintegrate2` (unexp.) | lazy `AbstractAnalysis.Limit` sequences of trapezoid partial sums | Julia-specific, skip | 1436-1464 | n/p |
| `arclength` | `(f::DenseVector) = Σ value(‖Δf_i‖)` (polyline length); `(f::IntervalMap)` = cumulative polyline length field (starts at 0) | chord length, **not** ∫speed | 1228, 1312-1316 | OK [verified] |
| `arcsteps`(unexp.), `totalarclength` | `Real.(abs.(diff(fiber f), refdiff(metricextensor f)))`; `sum(arcsteps f)` | | 1310-1311 | OK [verified] |
| `arctime` | `(f) = TensorField(fiber(arclength f), points(f))` | inverse map s ↦ t | 1309 | OK [verified] |
| `arcparametrize` | `(f::IntervalMap) = TensorField(fiber(arclength f), fiber f)` | re-based on arclength | 1308 | OK [verified] |
| `arcresample` | `(f::IntervalMap, i = length f)` | `at = arctime f; ts = at.(LinRange(0, L, i)); TensorField(ts, f.(ts))` (equal-arclength samples, *original* parameter) | 1296-1300 | OK [verified] |
| `arcsample` | same | `TensorField(LinRange(0,L,i), f.(ts))` (arclength parameter) | 1301-1306 | OK [verified] |
| `refdiff` (unexp.) | `(x::Global) = ref(x)`; `(x) = x[2:end]` | metric for `diff` | 1288-1289 | OK |
| `isregular` (unexp.) | `(f::IntervalMap) = prod(.!iszero.(fiber(speed f)))` | | 1291 | OK |
| `Grassmann.metric(f::TensorField, g::TensorField)` | `maximum(fiber(abs(f-g)))` | sup distance | 1293 | OK |
| `LinearAlgebra.norm(f::IntervalMap, g::IntervalMap)` | `arclength(f-g)` (a *field*) | | 1294 | OK |

### 2.7 `diffgeo.jl` — analysis helpers, topology

| Symbol | Semantics | Line | Status |
|---|---|---|---|
| `boundabove(x, lim=10)` | `x ≤ lim ? x : lim` (Real, LocalTensor, TensorField elementwise) | 19-21 | OK [verified] |
| `boundbelow(x, lim=-10)` | `x ≥ lim ? x : lim` | 22-24 | OK [verified] |
| `bound(x, lim=10)` | Real: `‖x‖ ≤ lim ? x : sign(x)*lim`; non-real: `‖z‖ ≤ lim ? z : (lim/‖z‖) z`; LocalTensor real: **`T(sign(fiber*lim))`** (returns ±1, BUG B11); TensorField elementwise | 25-29 | OK/BUG |
| `boundlog(x, lim=10)` | Real: `‖x‖ ≤ lim ? x : sign(x)(lim + log(‖x‖+1-lim))`; LocalTensor real/non-real analogous; generic `boundlog(z,…)` **BROKEN** (undefined `s`,`T`) | 30-34 | OK [verified 12.0 → 11.0986…]/BROKEN |
| `isclosed(t::IntervalMap)` | `norm(fiber[end]-fiber[1]) ≈ 0` — `isapprox(x, 0)` with default tolerances ⇒ **true only if exactly 0** | 36 | OK (surprising) [verified] |
| `updatetopology(t::IntervalMap)` | `isclosed(t) ? TorusTopology(t) : t` | 37 | OK |

### 2.8 `diffgeo.jl` — exterior calculus & Lie derivatives

| Symbol | Semantics | Line | Status |
|---|---|---|---|
| `getnabla(t)` (unexp.) | builds `Chain{W}` of symbolic tangent derivations ∂₁…∂ₙ from `tangent(supermanifold(W),1,n)` | 40-45 | **BROKEN** for all standard grids (`supermanifold` returns an `Int`) [verified] |
| `cartan(ξ) = invd(ξ)⋅ξ` | Maurer–Cartan-style form of a frame field | 49 | n/p |
| `firststructure(θ,ω) = d(θ) + ω∧θ`, `secondstructure(ω) = d(ω) + ω∧ω` | Cartan structure equations | 50-51 | n/p |
| `Base.div(t::TensorField) = divergence(t)`; `divergence(t) = ∂(t)` | | 53-54 | BROKEN (via getnabla) |
| `Grassmann.curl(t) = ⋆d(t)`; `δ(t) = -∂(t)` | | 55-56 | BROKEN (via getnabla) |
| `Grassmann.d(t::TensorField) = TensorField(fromany(getnabla(t)∧Chain(t)))`; `∂(t) = TensorField(fromany(Chain(t)⋅getnabla(t)))` | exterior derivative / boundary via symbolic nabla | 57-58 | BROKEN [verified] |
| `d(t::ScalarField{…,<:FrameBundle,<:AbstractArray}) = gradient(t)` | | 59 | OK [verified] |
| `dvec(t)` (unexp., generated) | `TensorField(base, Chain{V,1}.(fiber(gradient(t[1])), …, fiber(gradient(t[N]))))`: outer index = **component**, inner = derivative direction (transpose of `gradient` layout) | 71-74 | n/p |
| `d(t::TensorField{B,<:Chain{V,G,<:Chain}})` | `Chain{V,1}(d(t[1]),…,d(t[N]))` recursion | 76-79 | n/p |
| `d(t::DiagonalField{…FrameBundle…})` | `DiagonalOperator(dvec(value(t)))` | 80 | n/p |
| `d(t::EndomorphismField{…})` | `TensorOperator(Chain{V,1}(Chain{V,1}(d(x_j[i]) for i) for j))` with `x_j = t[j]` — entrywise gradient of the matrix field | 81-88 | OK (used by `secondkind`) |
| `invd(t::EndomorphismField)` | as `d` with negated entries and swapped `(i,j)` roles; DiagonalOperator case `DiagonalOperator.(dvec(.-value.(t)))` | 89-97 | n/p |
| `*`,`/`,`∧`,`∨`,`⋅` with `::Nabla` and a TensorField | `op(getnabla(t), Chain(t))` / reversed | 99-106 | BROKEN (getnabla) |
| `∇∧s`, `s∧∇`, `∇*s`, `s*∇`, `∇⋅s`, `s⋅∇` for `s::ScalarField` | `gradient(s)` | 109-110, 113-114, 117-118 | `∇*s` resolves to the broken generic method in 0.4.16 [verified]; intended = gradient |
| `Δ∧s`, `Δ*s`, `Δ⋅s` (+ reversed), `(::Laplacian)(f::ScalarField)` | `_laplacian(s) = tr(jacobian(gradient(s)))` | 111-120, 383-384 | OK [verified `Δ*s`] |
| `n::Submanifold * t`, `t * n`, `n⋅t`, `t⋅n` | if `istangent(n)`: `gradient(t, Val(indices(n)[1]))` (partial derivative ∂ᵢ); else elementwise product/contraction with the basis blade | 131-158 | n/p |
| `𝓛, Lie, LieBracket, LieDerivative, bracket` | re-exported from Grassmann; `(X::LieDerivative)(f::ScalarField) = action(X.v, f)` | 162-165 | OK [verified `Lie[X,Y]`] |
| callable fields | `X(Y)` (both VectorField same dims) = `action(X,Y)`; `X(f::ScalarField)`, `(X::GradedVector)(f)`, `(X::ScalarField)(f)` = `action` | 166-169 | OK [verified] |
| `action` | `(X::VectorField, f::ScalarField) = Real(X⋅gradient(f))`; `(X::GradedVector, f) = X⋅gradient(f)`; `(X::ScalarField, f) = X⋅gradient(f)`; `(X::VectorField, Y::VectorField) = TensorField(base X, 𝓛dot.(fiber X, fiber(gradient Y)))` with `𝓛dot(x, y::Simplex{V}) = Chain{V}(Real.(x .⋅ value(y)))` ⇒ **`action(X,Y)_k = X · ∂_k Y`** (i.e. `J_Yᵀ X`, not the directional derivative `(X·∇)Y`) | 170-176 | OK [verified; §4.13] |
| `Connection{T}` | `struct(ω::T)`; `(∇::Connection)(X) = CovariantDerivative(∇.ω⋅X, X)`; `(∇::Connection)(X, Y) = X(Y) + ((∇.ω⋅X)⋅Y)` | 178-184 | n/p |
| `CovariantDerivative{T,X}` | `struct(ωv, v)`; `CovariantDerivative(∇::Connection, X) = ∇(X)`; `(∇x)(Y) = ∇x.v(Y) + (∇x.ωv⋅Y)` | 186-193 | n/p |

### 2.9 `diffgeo.jl` — principal bundles, pullback & flux integrals

| Symbol | Semantics | Line |
|---|---|---|
| `principal`, `principalnorm`, `principalbase`, `principalfiber`, `principalbasetype`, `principalfibertype` on `LocalPrincipal` | fiber / `Real(abs(det(fiber)))` / base / fiber / types | 234-239 |
| `inv(T::LocalPrincipal)` | inverts the fiber | 241 |
| `(P::LocalPrincipal)(f)`, `(P)()`, `(P::PrincipalFiber)(f)`, `(P)()` | `principalaction(P, f)` / `principalaction(P)` | 243-246 |
| `principalaction(P::LocalPrincipal, f)` | `select_action(P, f(base))` (TensorField/Function) or `select_action(P, f)` (numbers, TensorAlgebra) | 248-253 (`principalaciton` typo at 253) |
| `principalaction(P::PrincipalFiber{…,IntervalMap,AbstractCurve}, f)` | curve over interval with curve-valued fiber: `principalnorm(P) * pre_action(P, f)` for curve-valued fields; `principalnorm(P)*f` for numbers | 255-259 |
| `principalaction(P::PrincipalFiber{…,IntervalMap}, f)` | ScalarField of reals: `principalnorm * f`; other TensorField: `principal(P) ⋅ pre_action(P,f)`; Function: `principal(P) ⋅ f.(base P)`; numbers `principal(P) * f`; TensorAlgebra: `principal(P) ⋅ f` | 260-266 |
| `principalaction(P::PrincipalFiber, f)` (general) | `select_action(P, pre_action(P, f))` / `select_action(P, f.(base P))` / `select_action(P, f)` | 267-272 |
| `principalaction(P::FrameBundle[, g])` | `principal(P)` / `pre_action2(P, g)` weighted by `sqrt‖det(metric)‖` unless induced | 273-282 |
| `principalaction(t::TensorField)` | if extrinsic or non-induced: act by the frame bundle; else `t` | 283 |
| `principalaction(t, d, f)` family | builds `PrincipalFiber(t, _outermorphism(d))` (or `compound(d, Val(G))` for grade-G `f`) and acts | 285-294 |
| `select_action(P, f)` | `principal(P)⋅f`; for Real/Complex/grade-0/ScalarField: `principalnorm(P)*f` | 296-300 |
| `pre_action(P,f)`, `pre_action2(P,f)` | `f` if coordinates/points match else `f.(base(P))` | 301-302 |
| `principal(P::PrincipalFiber) = fiber(P)`; `principal(P::FrameBundle) = metrictensorfield(P)`; `principalnorm(P::PrincipalFiber) = TensorField(base(p), Real.(abs.(det.(fiber p))))`; `principalnorm(P::FrameBundle) = sqrt.(abs.(Real.(det.(metric))))`; `principalbundle`, `principalbase`, `principalfiber`, `principalbasetype`, `principalfibertype`, `localfiber`, `inv(P)` | | 304-325 |
| `_outermorphism(x)` (unexp.) | identity for Vector/ScalarField else `Outermorphism(x)` | 327-329 |
| `UnitTangentBundle(t, d=unitjacobian t)`, `TangentBundle(t, d=jacobian t)`, `PathTangentBundle`, `UnitPullback(t, d)=PrincipalFiber(t, Outermorphism(inv d))`, `Pullback`, `UnitNormalBundle(t, d=normalunitframe t)`, `NormalBundle(t, d=normalframe t)`, `PathNormalBundle` | constructors of `PrincipalFiber` | 331-340 |
| `unittangentaction`, `tangentaction`, `unitpullbackaction`, `pullbackaction`, `unitnormalaction`, `normalaction` (unexp.) | `principalaction(t, d, f)` with the matching `d` | 342-347 |
| `retract(f, x = -normal(f)) = inv(normalframe f)⋅(x - f)`; `retract(P::PrincipalFiber, f = -normal(base P)) = inv(P)(f - base P)` | | 350-351 |
| `transport(f, x) = normalunitframe(f)⋅x + f`; `transport(P, f) = P(f) + base(P)` | | 352-353 |
| `paralleltransport(P::PrincipalFiber, f::IntervalMap)` | 2-D field over `base(f)⊕principalbundle(P)` of transported copies | 354-361 |
| `trapz(ϕ::TensorField, f)`, `trapz(ϕ, f, Ω)`, `cumtrapz(ϕ, f)`, `cumtrapz(ϕ, f, Ω)` for `f::TensorField/Function/AbstractFloat` | pullback integral `trapz(tangentaction(f, ϕ))` (optionally `Ω *` density) — so `integrate(ϕ, f)` is ∫ over the image of ϕ | 363-370 |
| `fluxintegral(N, f[, Ω]) = cumtrapz(normalaction(f, N))`, `fluxintegrate(N, f[, Ω]) = trapz(normalaction(f,N))` | flux integrals | 371-378 |
| `⨍` | `const ⨍ = fluxintegral` (ASCII alias: `fluxintegral`) | 379 |

Verified semantics of pullback integrals (p12.jl): for a curve `circ = 2(cos t, sin t)`, `integrate(circ, 1.0) = 12.559999995880043` (= ∫|γ'| dt, circumference on `0:0.01:2π`), but `integrate(circ, x->1.0) = -1.01461e-5v₁ - 0.00637055v₂` (for an IntervalMap base and a *Function*, the action is `principal(P)⋅f.(base)` = `γ' f`, a vector integral). For the torus surface `integrate(tor, x->1.0) == integrate(tor, 1.0) = 39.138…` (area). `fluxintegrate(tor, x->x) = -29.3535v` (= −3·volume, inward normal).

### 2.10 `diffgeo.jl` — tangent/normal/Jacobian family

| Symbol | Definition | Line |
|---|---|---|
| `tangent(f::IntervalMap) = gradient(f)`; `tangent(f::ScalarField) = tangent(graph f)`; `tangent(f::VectorField) = ∧(gradient f)` (wedge of the partial-derivative vectors, an n-vector) | | 385-387 |
| `normal(f::ScalarField) = ⋆tangent(f)`; `normal(f::VectorField) = ⋆tangent(f)` | Hodge dual of tangent n-vector (for 2-D→3-D: `∂₁γ × ∂₂γ`) | 388-389 |
| `normalframe(f) = normal(f)` (generic) | | 390 |
| `unittangent(f::ScalarField/VectorField, n = tangent f) = unit(n)`; `unittangent(f::IntervalMap) = unitgradient(f)` | | 391-393 |
| `unitnormal(f) = ⋆unittangent(f)`; `normalunitframe(f) = unitnormal(f)` | | 394-395 |
| `normalnorm(f) = Real(abs(det(normalframe f)))` | area element `‖N‖`; **for a PlaneCurve `normalframe = normal = κN` so `normalnorm = κ`** (curvature, not speed!) [verified] | 396 |
| `tangentnorm(f) = Real(abs(det(jacobian f)))` (unexp.) | | 397 |
| `jacobian(f::IntervalMap) = gradient(f)`; `jacobian(f::ScalarField) = jacobian(graph f)`; `jacobian(f::VectorField) = TensorOperator(gradient f)` (columns = ∂ᵢγ) | | 398-400 |
| `unitjacobian(f::IntervalMap) = unitgradient(f)`; `(f::ScalarField)` via graph; `(f::VectorField) = TensorOperator.(map.(unit, fiber(gradient f)))` (unit columns) | | 401-403 |
| `weingarten(f::VectorField) = jacobian(unitnormal(f))` | columns ∂ᵢν | 404 |
| `Base.adjoint(f)` = `f'` | `jacobian(f)` for IntervalMap/ScalarField/VectorField; complex 2-D field → `derivative(f)` | 405-408 |
| `*_slow` variants: `tangent_slow`, `normal_slow`, `unittangent_slow`, `unitnormal_slow`, `normalnorm_slow = Real(abs(normal_slow f))`, `jacobian_slow`, `unitjacobian_slow`, `weingarten_slow` | same with `gradient_slow` | 410-426 |
| `tangent_fast` | exported (213) but **never defined** | — |

### 2.11 `diffgeo.jl` — sector / area / curvature of hypersurfaces

| Symbol | Definition | Line |
|---|---|---|
| `ribbon(f::AbstractCurve, g::Vector{<:AbstractCurve})` | `TensorField(points(f) ⊕ LinRange(0,1,length(g)+1), hcat(fiber f, fiber.(g)...))` | 428 |
| `ribbon(f, g::AbstractCurve, n=100) = tangentsurface(f, g-f, n)` | | 429 |
| `tangentsurface(f, g::AbstractCurve, n=100) = ribbon(f, Ref(f) .+ (LinRange(1/n,1,n) .* Ref(g)))`; `tangentsurface(f, v::Real=1, n=100) = tangentsurface(f, v*tangent(f), n)` | [verified size (26,4) for n=3] | 430-431 |
| `sector(f::Chain{V,G,<:Real}, J::Chain{V,G,<:Real}) = Chain{V}(f, J)`; `sector(f::Real, J::Chain{W,1,<:Real}) = Chain(f, value(J)...)`; `sector(f::Chain{V,G}, J::Chain{W,1,<:Chain{V,G}}) = Chain{V}(f, value(J)...)`; `sector(f::TensorField, J::TensorField)` elementwise; `sector(f::RealFunction) = f`; `sector(f::TensorField) = TensorOperator(sector(f, gradient f))` | matrix `[γ, ∂₁γ, …, ∂ₙγ]` | 433-438 |
| `sectordet(f::RealFunction) = f`; `sectordet(f::PlaneCurve) = f∧gradient(f)`; `sectordet(f::VectorField) = f∧(∧(gradient f))` | `γ∧∂₁γ∧…∧∂ₙγ` (top form) | 439-441 |
| `sectorintegral(f::RealFunction) = integral(f)`; `sectorintegral(f::TensorField) = integral(sectordet f)/mdims(fibertype f)` | cumulative "sector volume" | 442-443 |
| `sectorintegrate(f)` | `integrate(sectordet f)/mdims(fibertype f)` (volume enclosed, signed) | 444-445 |
| `indexintegral`, `indexintegrate` | `integral/integrate(sectordet f)/spherearea(mdims(fibertype f))` | 446-449 |
| `degreeintegrate(f, ω::TensorField) = integrate(f, ω)/integrate(ω)`; `degreeintegrate(f, ω::Real=1) = integrate(f, float(ω))/integrate(TensorField(f, ω))` | mapping degree [verified circle → 0.99999999967] | 450-451 |
| `sector_slow`, `sectordet_slow`, `sectorintegral_slow`, `sectorintegrate_slow`, `indexintegral_slow`, `indexintegrate_slow`, `degreeintegrate_slow` | `gradient_slow` variants; `indexintegr*_slow`/`degreeintegrate_slow` call undefined `integral_slow`/`integrate_slow` → **BROKEN** | 452-466 |
| `area(f::VectorField) = integral(normalnorm f)`; `surfacearea(f::VectorField) = integrate(normalnorm f)`; `surfacearea(f::ElementBundle) = sum(fiber(volumes f))`; `surfacearea(f::ScalarMap) = surfacearea(base(graphbundle f))`; `surfacearea(f::FaceMap) = surfacearea(interp f)` | | 468-472 |
| `principals(f::VectorField[, i]) = eigvals(shape f[, i])`; `principalaxes(f[, i]) = eigvecs(shape f[, i])` | | 473-476 |
| `curvatures(f::VectorField[, i]) = eigpolys(shape f[, i])` | normalized elementary symmetric functions of the principal curvatures: `e_k/C(n,k)` → for surfaces `(H, K)` | 477-478 |
| `meancurvature(f::VectorField) = eigpolys(shape f, Val(1))` | `tr(S)/n` | 479 |
| `gausssign(f) = sign(sectordet(unitnormal f))` | | 480 |
| `gaussextrinsicnorm(f) = norm(gaussextrinsic f)`; `gaussintrinsicnorm(f, N=normal f) = norm(gaussintrinsic(f, N))` | | 481-482 |
| `gaussextrinsic(f) = sectordet(unitnormal f)` | `K_e = ν∧∂₁ν∧…∧∂ₙν` (pseudoscalar of R^(n+1)) | 483 |
| `gaussintrinsic(f, N = normal f)` | `n = ‖N‖`; `Chain{Manifold(T), mdims(T)}.(Real(sectordet(N/n))/n)` with `T = pointtype(f)` — i.e. `K = K_e/‖N‖` as a top-grade Chain of the *parameter* space | 484-487 |
| `*_slow` Gauss variants | `gaussintrinsic_slow` uses `Chain{…}(…)` without broadcast dot (likely BROKEN on fields); `gausseintrinsicnorm_slow` exported but undefined | 489-498 |
| `area(f::PlaneCurve) = sectorintegral(f)`; `sectorarea(f::PlaneCurve) = sectorintegrate(f)`; `sectorvolume(f::VectorField) = sectorintegrate(f)` (unexp.) | | 500-503 |
| `sphereradius(n, a=1) = (a/spherearea(n))^(1/(n-1))`; `ballradius(n, v=1) = (v/ballvolume(n))^(1/n)` | | 505-506 |
| `spherearea(n, r) = spherearea(n) r^(n-1)`; `spherearea(n::Int) = n·ballvolume(n)` | area of S^(n-1) ⊂ R^n | 508-509 |
| `ballvolume(n, r) = ballvolume(n) r^n`; `ballvolume(n::Int)`: `k = n÷2`; even `π^k/k!`; odd `2·k!·(4π)^k/n!` | volume of unit n-ball | 510-518 |

### 2.12 `diffgeo.jl` — curve geometry

All take `(f::…, d = centraldiffpoints(f), t = centraldifffiber(f, d))` unless noted: `d` = raw slow-stencil of the parameter points, `t = D(γ) = γ'` (4th-order). Internally `D(x) := centraldiff(x, immersion(f), d)` (topology-aware slow stencil divided by `d`), `|·|` and `unit` use `refmetric(f)` (identity for induced metric).

| Symbol | Output (fiber per sample) | Line |
|---|---|---|
| `speed(f::IntervalMap)` | `s = ‖γ'‖` | 544-546 |
| `normal(f::IntervalMap)` | `D(γ'/s)/s = κN` | 547-550 |
| `unitnormal(f::IntervalMap)` | `unit(D(unit(γ')))` = N | 551-553 |
| `curvature(f::AbstractCurve)` | `κ = ‖D(γ'/s)‖/s` | 560-563 |
| `radius(f::AbstractCurve)` | `s/‖D(γ'/s)‖` = 1/κ | 564-567 |
| `_bending` (unexp.) | `‖D(γ'/s)‖²/s / 2` = κ² s /2 | 568-571 |
| `bending(f)` / `bendingenergy(f)` (latter unexp.) | `integral(_bending)` / `integrate(_bending)` = ½∫κ² ds | 572-573 |
| `localevolute` (unexp.) | `n = D(γ'/s)`; `(s/‖n‖²) n` = N/κ | 574-579 |
| `evolute(f) = f + localevolute(f)` | centre of curvature | 580 |
| `involute(f) = f - unittangent(f)*arclength(f)`; `involute(f, l) = f - unittangent(f)*(s - s(float l))` | extends `Grassmann.involute` | 581-585 |
| `osculatingplane(f)` | `TensorOperator(Chain(γ', κN))` (2 columns) | 586-588 |
| `unitosculatingplane(f)` | `T = unit(γ')`; `TensorOperator(Chain(T, unit(D(T))))` | 589-592 |
| `binormal(f::SpaceCurve)` | `⋆(γ' ∧ κN)` = sκB | 593-595 |
| `unitbinormal(f::SpaceCurve)` | `T = unit.(t)` (no metric); `⋆(T ∧ unit(D(T)))` = B | 596-599 |
| `torsion(f::SpaceCurve)` | `n = D(γ')` (=γ''), `b = γ'∧n`; `τ = Real((b ∧ D(n)) / ‖⋆b‖²)` = `det(γ',γ'',γ''')/‖γ'×γ''‖²` | 600-604 |
| `frame(f::AbstractCurve...) = TensorOperator.(Chain.(f...))` | assemble columns | 610 |
| `frame(f::PlaneCurve) = osculatingplane(f)` | | 611 |
| `frame(f::AbstractCurve)` (N≥3, generated) | `s=‖e1‖`, `e1 = γ'`; `e_i = D(unit(e_{i-1}))/s` for i=2..N-1; `e_N = ⋆(e1∧…∧e_{N-1})`; columns `[e1,…,e_N]` (3-D: `[γ', κN, sκ B]`) | 612-618 |
| `unitframe(f::AbstractCurve...) = frame(unit.(f)...)`; `unitframe(f::PlaneCurve) = unitosculatingplane(f)` | | 619-620 |
| `unitframe(f::AbstractCurve)` (N≥3) | `e1 = unit(γ')`; `e_i = unit(D(e_{i-1}))`; `e_N = ⋆(e1∧…∧e_{N-1})`; Frenet frame `[T,N,B,…]` | 621-628 |
| `darbouxframe(f::AbstractCurve...)`, `(f::RealFunction...)` | assemble | 629-630 |
| `darbouxframe(f::RealFunction, d=nothing, e1=nothing) = f` | | 631 |
| `darbouxframe(f::AbstractCurve)` (generated) | `e_i = D(e_{i-1})` for i=2..N-1 (raw derivatives, **not** normalized, **not** /s); columns `[γ, γ', γ'', …, γ^(N-1)]` (Wronskian matrix; includes the position!) | 632-638 |
| `darbouxunitframe(...)` | `e1 = unit(γ)` (unit **position**), `e_i = unit(column i of darbouxframe)` for i=2..N | 639-648 |
| `wronskian(f::RealFunction...)`, `(f::AbstractCurve...) = det.(TensorOperator.(Chain.(f...)))`; `wronskian(f::AbstractCurve) = det(darbouxframe f)` | | 649-651 |
| `unitwronskian(...)` | `wronskian(unit.(f)...)`; `det(darbouxunitframe f)` | 652-654 |
| `normalframe(f::PlaneCurve) = normal(f,d,e1)` (κN); `normalframe(f::AbstractCurve) = _normalframe(TensorField(base f, e1), d, e1)` | columns `[e2,…,e_N]` of `frame` (3-D: `[κN, sκB]`) | 655-656 |
| `normalunitframe(f::PlaneCurve) = unitnormal(f)`; `(f::AbstractCurve) = _normalunitframe(...)` | columns `[N, B, …]` | 664-665 |
| `_normal`, `_unitnormal`, `_normalframe`, `_normalunitframe` (unexp.) | helpers on a tangent field; `_normalframe(t::PlaneCurve)` references undefined `f` → **BROKEN** | 674-697 |
| `cartan(f::PlaneCurve)` | `Chain(Chain(0,κ), Chain(-κ,0))` (Chain of Chains, *not* a TensorOperator) | 699-702 |
| `cartan(f::SpaceCurve)` | `n = D(γ')`, `s=‖γ'‖`, `b = γ'∧n`, `κ = ‖D(γ'/s)‖/s`, `τ = (b∧D(n))/‖⋆b‖²`; `TensorOperator(Chain(Chain(0,κ,0), Chain(-κ,0,τ), Chain(0,-τ,0)))` — columns; matrix `[[0,-κ,0],[κ,0,-τ],[0,τ,0]]` (row-major display) | 703-709 |
| `cartan(f::AbstractCurve)` (N≥4, generated) | `s = ‖γ'‖` (no metric); `e_i` = columns of `unitframe`; `κ_i = ⟨e_{i+1}, D(e_i)⟩/s`, i=1..N-1; column i has `κ_i` at row i+1 and `-κ_{i-1}` at row i-1 | 710-719 |
| `frenet(f::PlaneCurve)` | `T=γ'/s`, `N=unit(D(T))`; `TensorOperator(D(Chain(T,N))/s)` = `d/ds[T,N]` | 720-725 |
| `frenet(f::SpaceCurve)` | `d/ds [T, N, ⋆(T∧N)]` | 726-731 |
| `frenet(f::AbstractCurve) = (F = unitframe(f); F⋅cartan(F))` | only reached for N≥4 | 732 |
| `curvatures(f::PlaneCurve/SpaceCurve/AbstractCurve, i::Int, args...)` | `= curvatures(f, Val(i), args...)` | 735-737 |
| `curvatures(f::PlaneCurve, d::AbstractVector=…, t=…)` | `curvatures(f, Val(1), d, t)` = `κ · v₁₂` (a `Single`) | 738 |
| `curvatures(f::SpaceCurve, ::Val{2}, …)` | `torsion(f) * Λ(V).b[7]` (= τ v₂₃) | 739-742 |
| `curvatures(f::SpaceCurve, d, t)` | `n = D(γ'/s)/s` (κN), `b = γ'∧n`; `Chain{V,2}(‖n‖, 0, (b∧D(n))/‖⋆b‖²)` = `κ v₁₂ + 0 v₁₃ + τ̃ v₂₃` (τ̃ uses `κN` in place of γ'' — different discretization than `torsion`) | 743-749 |
| `curvatures(f::AbstractCurve, d, t)` (N≥4, generated) | bivector `Chain{V,2}` with `κ_i` at basis `e_{i+1}∧e_{i+2}` (via `bladeindex`), 0 elsewhere | 750-759 |
| `curvatures(f::AbstractCurve, ::Val{j}, …)` (generated) | j=1: `curvature * Λ(V).b[N+2]` (e₁₂); j>1: recursive derivatives, `⟨unit(e_{j+1}), D(unit(e_j))⟩/‖e1‖` times `e_{j+1}∧e_{j+2}` | 760-769 |
| `darboux(f) = compound(unitframe f, Val(2))⋅curvatures(f)`; `darboux(f, j)` | Darboux bivector in ambient coordinates | 770-771 |
| `bishopframe(f::SpaceCurve, θ0=0.0, d, t)` | **BUG** `s,b = Real.(abs.(t))` destructures → `s` = first speed only; `T = t/s`, `N = D(T)/s` (κN), `B = ⋆(T∧N)`; `τs = torsion·s`; `θ = θ0 + (Δx/2)·cumsum(τs[2:]+τs[1:-1])` (BUG for non-uniform Δx), `θ₁ = θ0`; columns `[T, cosθ N − sinθ B, sinθ N + cosθ B]` | 773-783 |
| `bishopunitframe(...)` | same bug; `T = unit(t)`, `N = unit(D(t/s))`, `B = ⋆(T∧N)` | 784-794 |
| `bishoppolar(f::AbstractCurve, θ0=0.0, …)` | `Chain(κ, θ)` with correct per-sample `s`; `τs = ((b∧D(n))/‖⋆b‖²)·s`, `b = γ'∧γ''` | 795-803 |
| `bishop(f, θ0=0.0, …)` | `Chain(κ cos θ, κ sin θ)` | 804-812 |
| `normalangle(f, …)` | `θ` with θ0 = 0 | 815-822 |
| `tangentangle(f) = integral(curvature f)`; `totalcurvature(f) = integrate(curvature f)`; `winding(f) = totalcurvature(f)/(2π)` | **∫κ dt over the parameter, not ∫κ ds** | 824-826 |
| `planecurve(κ::RealFunction, φ::Real=0.0)` | `θ = integral(κ) (+φ)`; `integral(Chain.(cos θ, sin θ))` — curve with unit speed in the parameter of κ, starting at origin | 828-831 |
| `compare(f)` (unexp., "???") | `D(γ'/s) - D(γ')/s` over base `fiber(f)` | 922-928 |

### 2.13 `diffgeo.jl` — surface constructors & generators

| Symbol | Definition | Line |
|---|---|---|
| `scrollsurface(f, g, n::Int=61) = linedsurface(f, g-f, n)`; `scrollsurface(f, g, t) = ruledsurface(f, g-f, t)` | | 833-834 |
| `linedsurface(f, g = tangent(f), n::Int=61) = ruledsurface(f, g, OpenParameter(n))` | | 836 |
| `ruledsurface(f, g, n::Int=61) = ruledsurface(f, g, TensorField(LinRange(-1,1,n)))`; `ruledsurface(f, g, t)` = `TensorField(base f × base t, [f_i + t_j g_i])` | [verified] | 837-840 |
| `revolve22(f,g) = Chain(f₁g₁, f₁g₂, f₂)`; `revolve32(f,g) = Chain(f₁g₁, f₂g₂, f₃)`; `revolve23(f,g) = Chain(f₁g₁, f₁g₂, f₂+g₃)`; `revolve33(f,g) = Chain(f₁g₁, f₂g₂, f₃+g₃)` (unexp.) | | 842-845 |
| `revolve`, `revolvesphere`, `revolvesector` | `(f, n::Int=61) = …(f, unitcircle(n))`; `(f::TensorField, n::AbstractRange)`; 2-comp `f` with PlaneCurve `g` → revolve22, SpaceCurve `g` → revolve23; 3-comp f with PlaneCurve → revolve32, SpaceCurve → revolve33; `(f::RealFunction, g...) = …(graph(f), g...)`; `(f, g::RealFunction) = …(f, unithelix(g))`; combined via `fiberproduct`/`fibersphere`/`fibersector` respectively | 846-859 |
| `linkmap(f::Chain, g::Chain) = g - f`; `linkmap(f::SpaceCurve, g::SpaceCurve) = fiberproduct(f, g, linkmap)` | | 861-862 |
| `link(tf, tg, f, g)` | `((g-f) ∧ tf ∧ tg)/‖g-f‖³` (trivector) | 863-866 |
| `link(f::SpaceCurve, g::SpaceCurve)` | field over `base f × base g` of `link(tangent f_i, tangent g_j, f_i, g_j)` | 867-870 |
| `linkintegral(f,g) = integral(link(f,g))/4π`; `linknumber(f,g) = integrate(link(f,g))/4π` | Gauss linking number [verified 0.999573v₁₂₃] | 871-872 |
| `sectorize23(f,g) = Chain(f₁g₁, f₁g₂, f₂g₃)`; `sectorize33 = componentwise product` (unexp.) | | 874-875 |
| `sectorize(f::TensorField) = sectorize(10, f)`; `(f::Int, g) = sectorize(LinRange(0,1,f), g)`; `(f::AbstractRange, g) = sectorize(TensorField(f), g)`; `(f::RealFunction, g::IntervalMap/TensorField) = fibersector(f, g, *)`; `(f::PlaneCurve, g) = fibersector(f, g, sectorize23)`; `(f::SpaceCurve, g) = fibersector(f, g, sectorize33)` | radial fill | 876-882 |
| `cylinderize(f, n::Int=30) = cylinderize(f, LinRange(0,1,n))`; `(f, t::AbstractRange)`; `(f, t::RealFunction) = sectorize(Chain.(t, 0t+1), f)` | | 883-885 |
| `unitcircle(n::Int=61) = unitcircle(SphereParameter(n))` (periodic, θ ∈ [-π,π]); `(t::AbstractRange) = unitcircle(TensorField t)` (open); `(t::RealFunction) = Chain.(cos t, sin t)` | [verified] | 887-889 |
| `unithelix(n::Int=61) = unithelix(LinRange(0,2π,n))`; `(t::AbstractRange)`; `(f::RealFunction, g::PlaneCurve = unitcircle(TensorField(base f))) = TensorField(base f, _helix.(f,g))`, `_helix(f,g) = Chain(g₁, g₂, f₁)` | `(cos t, sin t, t)` [verified] | 891-894 |
| `unitsphere(n::Int=31, m=61) = unitsphere(LinRange(-π/2,π/2,n), m)`; `(n, m) = revolvesphere(unitcircle(n), unitcircle(m))` | `(cosφ cosθ, cosφ sinθ, sinφ)`, SphereTopology (poles) [verified 3×5] | 896-897 |
| `unitdisk(n=61, r=20) = sectorize(r, unitcircle(n))`; `unitball(n=31, m=61, r=10) = sectorize(r, unitsphere(n,m))` | | 898-899 |
| `riemannsphere(n::Int=31, m=61) = unitsphere(n,m)/2 + Chain(0,0,1/2)` | | 900 |
| `riemannline(x, n=11)` | `resample(TensorField(0:2, [Chain(x₁,x₂,0), Chain(x₁,x₂,‖x‖²)/(‖x‖²+1), Chain(0,0,1)]), n)` | 901 |
| `unitpipe(n::Int=20, m=61) = unitpipe(LinRange(-1,1,n), m)`; `(t::AbstractRange, m) = unitpipe(TensorField t, m)`; `(t::RealFunction, m) = revolve(Chain.(0t+1, t), m)` | | 903-905 |
| `unitcylinder(n=20, m=61, r=20) = cylinderize(unitpipe(n,m), r)` | | 906 |
| `unitconic(n::Int=20, m=61) = unitconic(LinRange(0,1,n), m)`; `(t::AbstractRange, m) = revolvesector(TensorField t, m)` | | 908-909 |
| `unitcone(n::Int=20, m=61, r=20) = unitcone(LinRange(0,1,n), m, r)`; `(t::AbstractRange, m, r) = cylinderize(revolve(TensorField t, m), r)` | | 910-911 |
| `conoid(f::SpaceCurve, n::Int=61) = revolve(TensorField(LinRange(-1,1,n), 0), f)`; `(f::RealFunction, n::Int) = conoid(unithelix f, n)`; `(f::RealFunction, g::PlaneCurve=unitcircle(…), n=61)` | | 914-916 |
| `rightconoid(...)` | as `conoid` with `OpenParameter(n)` ([0,1]) | 917-919 |
| `frame(f::VectorField{…,2,<:RealSpace{2}})` (surface Darboux frame) | `Ψu,Ψv = ∂₁γ, ∂₂γ`; `ξ3 = ⋆(Ψu∧Ψv)`; columns `[Ψu, ⋆(ξ3∧Ψu), ξ3]` | 930-935 |
| `unitframe(f::VectorField{…,2,<:RealSpace{2}})` | columns `[Ψu/‖Ψu‖, ξ2/‖ξ2‖, ξ3/‖ξ3‖]`, `ξ2 = ⋆(ξ3∧Ψu)` | 936-942 |

### 2.14 `diffgeo.jl` — fundamental forms, intrinsic metric, Christoffel, geodesics

| Symbol | Definition | Line |
|---|---|---|
| `EFG(V, ∂₁γ, …, ∂ₙγ)` (unexp., n=2..5) | `TensorOperator(Chain{V}(Chain{V}(g₁₁,g₁₂,…),…))`, `g_ij = Real(∂ᵢγ⋅∂ⱼγ)` (Gram matrix, symmetric; column j = `(g_1j,…,g_nj)`) | 949-988 |
| `EG(V, …)` (unexp.) | `DiagonalOperator(Chain{V}(g₁₁,…,g_nn))` | 953-990 |
| `LMN(V, n, second partials…)` (unexp.) | `h_ij = Real(∂ᵢⱼγ ⋅ n)`, symmetric `TensorOperator` | 956-995 |
| `firstform(dom::ScalarField, f::Function)`; `firstform(t::ScalarField, g = gradient t, V = Submanifold(ndims t))` | graph metric `δ_ij + ∂ᵢf ∂ⱼf` (n=2..5); n=1 returns `g` (the gradient) | 997-1018 |
| `firstformdiag(t::ScalarField, g, V)` | `DiagonalOperator(1 + (∂ᵢf)²)` | 1020-1041 |
| `firstform(dom, f::Function)`; `firstform(t, g = gradient t, V)` (VectorField) | n=1: speed `Real.(abs.(g))`; n=2..5: `EFG` | 1043-1056 |
| `firstformdiag(t, g = gradien(t), V)` | **default arg typo `gradien` → BROKEN unless `g` passed** [verified] | 1058-1071 |
| `secondform(dom, f)`; `secondform(t, g = gradient t, V)` | `n = ⋆unittangent(t, ∧(g))` = unit normal; second partials `∂₁∂ᵢγ` from `gradient(∂₁γ)` (full), `∂ⱼ∂ⱼγ`/`∂ⱼ∂ₖγ` (j≥2) from `gradient(∂ⱼγ, Val(k))`; `LMN`. **BROKEN** for ScalarField input [verified]; 5-D mixed term bug (B9) | 1073-1103 |
| `firstsecondform(t, g, V)` | tuple `(EFG, LMN)` with identical computations | 1105-1139 |
| `thirdform(dom, f)`; `thirdform(t, V) = firstform(t, gradient(unitnormal t), V)` | `III = dν·dν` | 1141-1142 |
| `shape(dom, f)`; `shape(t, g = gradient t, V) = inv(EFG)⋅LMN` | shape operator `S = I⁻¹ II` | 1144-1148 |
| `intrinsicmetric(t::DiagonalField)` / `(t::EndomorphismField)` / `(t, g = gradient t)` | `GridBundle(PointArray(points t, Outermorphism.(fiber(firstform(t,g,V)))), immersion t)` with `V = Submanifold(MetricTensor(ones(n,n)))` (all-ones placeholder signature allowing full metric) | 1150-1169 |
| `intrinsicmetricdiag(...)` | same with `DiagonalForm(ones)` and `firstformdiag` | 1171-1185 |
| `surfacemetric`, `surfacemetricdiag` | `const = intrinsicmetric, intrinsicmetricdiag` | 1186 |
| `intrinsicframe(t::DiagonalField) = intrinsicframediag(t)`; `(t::FrameBundle) = intrinsicframe(metrictensorfield t)`; `(t::EndomorphismField)` (3-D+ **BROKEN**: `getindex.(3,3)`); `(t, g = gradient t)` n=2 → `intrinsicframe(base, E, F, G)`; n≥3 calls undefined arities → **BROKEN** | | 1188-1215 |
| `intrinsicframe(b, E, F, G)` | `mag = sqrt(E²+F²)`, `sig = sign(F²-EG)`; `TensorOperator(Chain(Chain(E,F)/mag, Chain(F,-E)/(sig·mag)))` | 1216-1219 |
| `intrinsicframediag(...)` | references undefined `g` → **BROKEN** | 1222-1230 |
| `surfaceframe`, `surfaceframediag` | `const = intrinsicframe, intrinsicframediag` | 1231 |
| `_firstkind(dg, k, i, j) = dg[k,j][i] + dg[i,k][j] - dg[i,j][k]` (unexp.) | Christoffel-1st-kind numerator `[ij,k]` when `dg = d(g/2)` | 1233 |
| `firstkind` | `firstkind(g::FrameBundle)`, `firstkind(g::TensorField) = TensorField(base g, firstkind.(d(g/2)))`; `firstkind(dg::DiagonalOperator, i,j,k) = _firstkind(dg,k,i,j)`; generated `firstkind(dg,i,j,k) = Σ_l _firstkind(dg,l,i,j)` (**BUG: ignores k**, B10) → `firstkind(dg,i,j) = Chain_k`, `firstkind(dg,j) = Chain_i`, `firstkind(dg) = TensorOperator(Chain_j)` | 1234-1248 |
| `secondkind(g::FrameBundle)`, `secondkind(g::TensorField) = TensorField(base g, secondkind.(inv(g), d(g/2)))`; `secondkind(ig::DiagonalOperator, dg, i,j,k) = ig[k,k]·_firstkind(dg,k,i,j)`; generated `secondkind(ig,dg,i,j,k) = Σ_l ig[l,k]·_firstkind(dg,l,i,j)` = Γᵏᵢⱼ; `…(ig,dg,i,j) = Chain_k Γᵏᵢⱼ`; `…(ig,dg,j) = Chain_i`; `…(ig,dg) = TensorOperator(Chain_j)` | OK [verified on torus] | 1250-1264 |
| `geodesic(Γ) = x -> geodesic(x, Γ)`; `geodesic(g::FrameBundle) = geodesic(secondkind g)`; `geodesic(x, Γ::Function/TensorField) = Chain(x₂, -geodesic(x₂, Γ(x₁)))`; generated `geodesic(x::Chain{…,N}, Γ) = Σ_i Σ_j Γ[i,j]·(x_i x_j)` | first-order geodesic ODE RHS on phase state `x = Chain(position, velocity)`; `Γ(x₁)` interpolates the Christoffel field | 1266-1272 |
| `metricscale(x::Chain, g::Simplex)` (unexp.) | `Chain(x_k sqrt(g_kk))` | 1273-1275 |
| `beta(a, b, n=30000) = integrate(x^(a-1)(1-x)^(b-1))` on `OpenParameter(n)`; `betafunction(a, b, n=100) = integral(…)` (unexp.) | Euler Beta by trapezoid | 1279-1286 |

Unicode operators and ASCII aliases in scope: `∫` ≡ `integral` (grid.jl:1286); `⨍` ≡ `fluxintegral` (diffgeo.jl:379); `𝓛` ≡ `Lie`/`LieDerivative` (Grassmann; re-exported diffgeo.jl:163); `∇` (`Nabla`), `Δ` (`Laplacian`) from Leibniz; `spike` ≡ `hat`; `surfacemetric` ≡ `intrinsicmetric`; `surfacemetricdiag` ≡ `intrinsicmetricdiag`; `surfaceframe` ≡ `intrinsicframe`; `surfaceframediag` ≡ `intrinsicframediag`; `f'` (`adjoint`) ≡ `jacobian(f)`; `div` ≡ `divergence` ≡ `∂`.

---

## 3. Data representations

### 3.1 Types the algorithms operate on (defined elsewhere, summarized for the implementer)

* `TensorField{B,F,N,M,A}` (`Cartan.jl:100-106`): fields `dom::M` (a `FiberBundle{B,N}`, usually `GridBundle`), `cod::A <: AbstractArray{F,N}`. `base(t)=dom`, `fiber(t)=cod`, `points(t)=points(base t)`, `immersion(t)=immersion(base t)`, `metricextensor(t)`. Element access `t[i…]` is a `LocalTensor(base point => fiber value)`.
* `GridBundle{N,C,PA,TA}` (`fiber.jl:446-450`): `p::PA` (a `PointArray`: `points` array + `metricextensor` array), `t::TA` (an `ImmersedTopology`, default `OpenTopology(size(p))`). `points(g)` is the coordinate array; for N≥2 grids built from `ProductSpace`, `points(g).v` is the `Values` of per-axis 1-D coordinate vectors (usually ranges); for N=1 it is a plain vector/range of reals.
* Coordinates: 1-D grids built from a real vector/range (`TensorField(0:0.1:1)`) have **Real** points ⇒ `IntervalMap` ⇒ slow (4th-order) gradient. Grids built from `ProductSpace(...)` have `Chain` points, even in 1-D (`ProductSpace(-2:0.03:2)` has points `Chain{⟨_1_⟩,1}`) ⇒ not an `IntervalMap` ⇒ fast gradient. [verified types]
* `ProductSpace` default manifold is `⟨_1…1_⟩`: a Submanifold of an (N+2)-dim parent with bit mask selecting basis indices 2..N+1 (displayed `v₂, v₃`); verified for N=2: 2-D points print as `1.5708v₂ + 1.5708v₃` and `Manifold(X) = ⟨_11_⟩ :: Submanifold{4,2,0x06}`; 1-D prints `⟨_1_⟩`. For the port this is irrelevant: a point is just an `N`-tuple of reals. **Gradients** however use `Submanifold(N)` (`⟨11⟩`, basis `v₁,v₂`) as the outer Chain basis (`grid.jl:730,737`).
* Metric: `InducedMetric` (Euclidean, `isinduced` true) is the common case; `refmetric(x) = ref(metricextensor(x))` (`topology.jl:273-276`) — with an induced metric all `abs(·,g)`, `unit(·,g)`, `⋆(·,g)`, `⋅` reduce to Euclidean ops. Non-induced metrics arise from `intrinsicmetric` (metric extensor is an `Outermorphism` of the first fundamental form) — only `gradient`, `metricfiber`, `principalaction` react to it.
* `QuotientTopology{N,L,M,O,LA}` (MeshTopology `quotient.jl:27-36`): `p::Values{O,Int}` partner face ids, `q::Values{O,LA}` transverse index maps (one `ImmersedTopology` of rank N-1 per glued face), `r::Values{M=2N,Int}` face → slot in `p/q` (0 = open face), `s::Values{N,Int}` sizes, `c::Values{2N,Int}` (collapse/cover flags, used by plotting and `SphereTopology` etc.). **Face numbering: face `2a-1` = lower face of axis `a`, face `2a` = upper face.** `OpenTopology` = `O = 0` (all `r` zero). `_to_axis(f) = ceil(f/2)` (`quotient.jl:187`). Examples [verified]: `TorusTopology(9)`: `p=[2,1], r=[1,2]`; `MirrorTopology(9)`: `p=[1], r=[1,0]` (lower face glued to itself = mirror, upper open); `ClampedTopology(9)`: `p=[1,2], r=[1,2]` (both mirror); 2-D torus `p=[2,1,4,3], r=[1,2,3,4]`; `SphereTopology` 2-D: `p=[1,2,4,3], r=[1,2,3,4], c=[1,1,0,0]`, `q[1] = CrossRange` (longitude shift by half a turn across the poles); `MobiusTopology`: `p=[2,1], r=[1,2,0,0]`, `q = n2:-1:1` (flip).
* `Chain{V,G,T,N}` (Grassmann): static vector of `N = binomial(dim V, G)` components of grade `G`; grade-2 components in lexicographic blade order (`v₁₂, v₁₃, v₂₃` in 3-D). `Simplex{V,T,N}` = `Chain{V,1,T,N}` with Chain-valued components (used for "Chain of Chains" = matrix columns). `TensorOperator`/`Endomorphism` wraps a Chain of column Chains; `DiagonalOperator` wraps the diagonal.

### 3.2 Layout / ordering conventions (must match for goldens)

* Arrays are Julia column-major: linear index `k = i₁ + n₁(i₂-1) + n₁n₂(i₃-1) + …` (first index fastest). All goldens use `vec(A)`.
* `gradient(f)` on an N-D grid: fiber `Chain{Submanifold(N),1}(D₁f, …, D_Nf)` — **outer index = derivative direction**, inner = fiber component (e.g. torus `gradient[4,5] = (∂₁γ)v₁ + (∂₂γ)v₂` with each `∂ᵢγ` a 3-vector) [verified].
* `jacobian(f::VectorField) = TensorOperator(gradient f)`: matrix whose **columns** are `∂ᵢγ` (so row = ambient component, column = parameter direction).
* `dvec(t)` is the transpose convention (outer = component).
* `TensorOperator(Chain(c₁,…,c_n))` displays as a matrix with column j = `c_j`; `M[i,j] = c_j[i]`.
* Cumulative integrals (`integral`, `cumtrapz`) put 0 on the first node of each integrated axis, and have the same size as the input.
* Reductions (`integrate`, `trapz`) over all axes return a scalar fiber value (Float or Chain) — **not** a `Single`/blade in 0.4.16 (docs showing `1.98v₁`, `3.14…v₁₂` are from an older version; current returns `1.98`, `3.1414139999999997`) [verified]. Sector integrals return pseudoscalar `Single`s (`3.1415v₁₂`).

### 3.3 Compile-time vs runtime (Julia)

| Julia type parameter | Meaning | Lean recommendation |
|---|---|---|
| `N` in `TensorField{…,N}` / `GridBundle{N}` | grid rank (1..5; generated code only for 1..5) | type index `N : Nat` (erased) |
| `Val{M}` / `Val{N}` axis arguments | stencil axis | `a : Fin N` runtime value (cheap); optionally `@[specialize]` |
| `CentralDifference{N,M}` | operator tag | enum / type-level tag |
| `V` (Submanifold) of fiber Chains | fiber vector-space dim & metric | fiber dim `k : Nat` as index; metric as a separate runtime value only when non-induced |
| `OpenTopology` vs `QuotientTopology` (type-level `O=0`) | selects the OpenTopology fast path of `getindex(g, j, n, i…)` (`fiber.jl:507`) | runtime per-face enum, precomputed |
| sizes `s`, points, steps | runtime | runtime (`Array Float`/`FloatArray`) |
| `PlaneCurve`/`SpaceCurve` (fiber dim 2/3) | dispatch of frames/cartan/torsion | fiber dim index `k` with `k = 2`/`k = 3` specializations |

---

## 4. Algorithms

### 4.1 The derivative framework: `D(g) = S(g) / S(x)`

Every finite-difference derivative in Cartan is the ratio of a stencil `S` applied to the fiber and the *same* stencil applied to the coordinates:

```
gradient_X(f::IntervalMap)           # grid.jl:645-647
  d  = centraldiff_X_points(f)       # d[i] = S_X(points)[i]            (grid.jl:639, 715-721)
  gf = centraldiff_X_fiber(f, d)     # gf[i] = S_X(fiber)[i] / d[i]     (grid.jl:638, 708-714)
  return TensorField(base f, gf)
```

For N-D: `d = centraldiff_X(base f)` is an array of per-point Chains `(S₁x₁, …, S_Nx_N)` and the fiber derivative is `Chain(S₁(f)/d₁, …, S_N(f)/d_N)` (`grid.jl:729-734`). Consequences:

* On uniform grids `S(x)` equals the textbook normalization (`12h` interior, `6h` near open boundaries for slow; `2h` / `6h` for fast), so results equal textbook stencils [verified: slow gradient of x³ on 0:0.1:1 matches textbook to 4.4e-15].
* On **non-uniform** grids the result is *not* the non-uniform finite-difference formula; it is exact only for functions linear in x, and can be badly wrong near boundaries (x² on `[0,0.1,0.3,0.35,0.6,1.0,1.2]` gives `-8.35` at the last node vs exact 2.4) [verified]. Port verbatim.
* Exactness for linear functions requires `S(1) = 0` (the stencil annihilates constants). All branches satisfy it except the upper-mirror slow branch (bug B2).
* Raw `centraldiff(v)` on a plain array without a `d` returns the **numerators** `S(v)` (no division) [verified]; `centraldiff(v, d)` divides.

### 4.2 Neighbour access and boundary remapping

Inside the kernels, `f[j, Val(a), i…]` means "the point/fiber `j` steps from multi-index `i` along axis `a`":

* OpenTopology: `getpoint(g, j, Val(a), i…) = points(g)[i with i_a ↦ i_a + j]` — raw index, no remapping (`fiber.jl:507-510`). Open stencils never step outside `1..n`.
* QuotientTopology: `points(g)[ immersion(g)[Val(a), i with i_a ↦ i_a + j]… ]` (`fiber.jl:511-513`), where the topology's `getindex(m, Val(a), idx…)` (MeshTopology `quotient.jl:400-560`) is:

```
bounds(i, n, Val(A), Val(M)) = (A ∈ (0, M)) ? (1 < i < n) : (0 < i ≤ n)     # quotient.jl:418
# i.e. along the stencil axis a the boundary indices 1 and n THEMSELVES count as out of bounds;
# along the other axes only genuinely out-of-range indices do.
remap(m, a, idx):                       # idx = candidate multi-index (Int tuple)
  if exactly the stencil-axis coordinate idx_a is "out of bounds" (all others in bounds):
     face = idx_a < 2 ? 2a-1 : 2a
     r = m.r[face]
     if r == 0: return idx              # open face: unchanged (never happens in practice)
     pr = m.p[r]; b = ceil(pr/2)        # partner face and its axis
     if idx_a < 2:  k = isodd(pr) ? (2 - idx_a)                     # |i-1|+1  reflect about 1
                                  : (s[b] - 1 + idx_a)              # s[b]-|i-1| wrap to the top
     else:          k = iseven(pr) ? (s[b] + n_a - idx_a)          # reflect about n (same axis: 2n-i)
                                   : (idx_a + 1 - n_a)              # wrap to the bottom
     transverse = m.q[r][ idx without its a-th entry ]              # permuted other indices
     return insert k at position b into transverse                  # getlocate
  else return idx
```

Key consequences [all verified on 1-D Torus/Mirror/Clamped]:

* **Periodic** (partner face is the *other* face of the same axis): index `1` maps to `n`, `0 ↦ n-1`, `-1 ↦ n-2`; `n ↦ 1`, `n+1 ↦ 2`, `n+2 ↦ 3`. So the grid duplicates the seam point (node 1 and node n are the same geometric point, e.g. `LinRange(0,2π,n)`).
* **Mirror** (partner face is the face itself, `p[r] == face`): `0 ↦ 2`, `-1 ↦ 3`, `1 ↦ 1`; `n+1 ↦ n-1`, `n+2 ↦ n-2`, `n ↦ n`.
* Transverse permutations `q` (Möbius flip, Klein, sphere/ball/cone poles via `CrossRange` = shift by half the length) are applied to the other indices whenever the seam is crossed. `CrossRange(n)` (MeshTopology.jl:49-55): shift `m = ceil(n/2) - 1`, `q[1] = [5,6,7,8,1,2,3,4,5]` for n=9 [verified].

Cartan's boundary branches then decide which of three closures to use per face (see `centraldiff_slow_calc`, `grid.jl:801-841`):

```
r = immersion(f).r[2a-1]  (lower)  or  r[2a]  (upper)
r == 0                         → OPEN   (one-sided stencil, raw indices)
immersion(f).p[r] ≠ face       → PERIODIC ("glued to another face")
immersion(f).p[r] == face      → MIRROR  ("glued to itself")
```

### 4.3 Slow stencil `S_slow` (4th-order interior; `centraldiff_slow_calc`, grid.jl:788-841)

Notation: `f[k]` absolute index along the stencil axis *before* remapping; `F(k)` = value after topology remap (§4.2); `P = f[i]` (the point itself, raw). Julia source forms are kept verbatim (operation order matters for bit-parity; evaluate left-to-right).

Interior (`3 ≤ i ≤ n-2`), all topologies — **raw** indices via `getpoint` (grid.jl:798, 839), never remapped (this matters at `i = 3` / `i = n-2`, whose stencil touches the seam nodes 1 / n):
```
S = f[i-2] + 8*(f[i+1] - f[i-1]) - f[i+2]          # uniform: 12h·f'
```

OPEN (and any face with r==0):
```
i == 1   : 18*f[2] - 9*f[3] + 2*f[4] - 11*f[1]      # (-11,18,-9,2)      → 6h·f'
i == n   : 11*f[n] - 18*f[n-1] + 9*f[n-2] - 2*f[n-3]
i == 2   : 6*f[3] - f[4] - 3*f[2] - 2*f[1]          # (-2,-3,6,-1)       → 6h·f'
i == n-1 : 3*f[n-1] - 6*f[n-2] + f[n-3] + 2*f[n]
```
(branch order is `i==1`, `i==n`, `i==2`, `i==n-1`, else — matters when n ≤ 4.)

PERIODIC (lower face glued elsewhere; `F(1) := f[n]` etc.):
```
i == 1   : F(-1) + 7*(F(1) - P) + 8*(F(2) - F(0)) - F(3)
           = f[n-2] + 7(f[n]-f[1]) + 8(f[2]-f[n-1]) - f[3]
i == 2   : F(0) - F(1) + 8*F(3) - 7*f[1] - F(4)          # f[-1,..] is F(1)=f[n]; getpoint(-1) is raw f[1]
           = f[n-1] - f[n] + 8 f[3] - 7 f[1] - f[4]
```
upper face glued elsewhere:
```
i == n   : F(n-2) + 8*(F(n+1) - F(n-1)) + 7*(P - F(n)) - F(n+2)
           = f[n-2] + 8(f[2]-f[n-1]) + 7(f[n]-f[1]) - f[3]
i == n-1 : F(n-3) + 7*f[n] - 8*F(n-2) + F(n) - F(n+1)     # getpoint(+1) is raw f[n]
           = f[n-3] + 7 f[n] - 8 f[n-2] + f[1] - f[2]
```
Interpretation: the standard 5-point stencil where values across the seam are shifted by the jump `f[n]-f[1]` (so coordinates like θ ∈ [0,2π] that jump by the period still give `12h`). All four annihilate constants; S(x)=12h on uniform periodic grids [verified `pts cd` = 9.4248 = 12·π/4 everywhere].

MIRROR (face glued to itself):
```
i == 1   : (-F(-1)) + 7*(-F(1) - P) + 8*(F(2) + F(0)) - F(3)
           = -2 f[3] - 14 f[1] + 16 f[2]              # odd (point-)reflection about node 1
i == 2   : (-F(0)) + F(1) + 8*F(3) - 7*f[1] - F(4)
           = -6 f[1] - f[2] + 8 f[3] - f[4]
i == n   : F(n-2) + 8*(-F(n+1) - F(n-1)) + 7*(P - F(n)) + F(n+2)
           = 2 f[n-2] - 16 f[n-1]                      # BUG B2: odd reflection would be + 14 f[n]
i == n-1 : F(n-3) + 7*f[n] - 8*F(n-2) - F(n) + F(n+1)
           = f[n-3] - 8 f[n-2] + f[n-1] + 6 f[n]
```
[verified: `MirrorParameter(9)`, f=x²: `[0.5235987755982988, 1.4398966328953218, 3.14159…, …]` = `π/6, 11π/24, …`; `ClampedParameter(9)` sin: last value `-0.11858581969043375` (bug B2) instead of ≈0.988.]

Analytic denominators for ranges (`$cd(f::AbstractRange,…)`, used when the base is a `ProductSpace`/`RealRegion` with Open/Product topology):
```
centraldiff_slow_calc(i, dt, n)       = i ∈ (1,2,n-1,n) ? 6dt : 12dt              # grid.jl:882-888
centraldiff_slow_calc(i, q, dt, n)    = ((i∈(1,2) && q.r[1]==0) || (i∈(n-1,n) && q.r[2]==0)) ? 6dt : 12dt   # 889-895
centraldiff_slow_calc(i, dt, d1, d2, n)  # 843-855 (non-uniform ends; unused by main paths)
  i==1: 6(dt+d1);  i==n: 6(dt+d2);  i==2: 13dt-d1;  i==n-1: 13dt-d2;  else 12dt
centraldiff_slow_calc(::Val{1}, i, dt, d1, n) / (::Val{2}, i, dt, d2, n)          # 856-881 one-ended variants
```

### 4.4 Fast stencil `S_fast` (2nd-order interior; `centraldiff_fast_calc`, grid.jl:999-1043)

```
interior (2 ≤ i ≤ n-1): f[i+1] - f[i-1]   (raw getpoint, grid.jl:1005,1028)   # 2h·f'
OPEN   i==1: 18f[2] - 9f[3] + 2f[4] - 11f[1]   (same 3rd-order one-sided as slow; 6h)
       i==n: 11f[n] - 18f[n-1] + 9f[n-2] - 2f[n-3]
PERIODIC i==1: (F(2) - P) + (F(1) - F(0))  = (f[2]-f[1]) + (f[n]-f[n-1])
         i==n: (F(n+1) - F(n)) + (P - F(n-1)) = (f[2]-f[1]) + (f[n]-f[n-1])
MIRROR   i==1: (F(2) - P) - (F(1) - F(0))  = 2(f[2]-f[1])
         i==n: (F(n) - F(n+1)) + (P - F(n-1)) = 2(f[n]-f[n-1])
```
Note: for the fast stencil the second node (`i==2`) and `n-1` use the plain interior formula (neighbour 1 / n are in range). Analytic denominators: `centraldiff_fast_calc(i,dt,n) = i∈(1,n) ? 6dt : 2dt`; with topology `(i==1 && r1==0)||(i==n && r2==0) ? 6dt : 2dt`; non-uniform-end helpers `(i,dt,d1,d2,n) = i==1 ? dt+d1 : i==n ? dt+d2 : 2dt` (1032-1043; the `Val` helpers reference undefined `dt`, dead code).

[verified: periodic sin on 9 nodes fast = `0.9003163161571061, 0.6366197723675814, …` = sin(h)/h·cos; mirror x² fast = `[0.7853981633974483, 1.5707963267948966, …]`.]

### 4.5 Backward / forward stencils (grid.jl:907-997)

```
back interior:  P - f[i-1]              forw interior:  f[i+1] - P          (raw getpoint)
OPEN ends (both): same 3rd-order one-sided formulas at i==1 and i==n (denominator 6h)
back PERIODIC i==1: F(1) - F(0) = f[n]-f[n-1];  i==n: P - F(n-1)
back MIRROR   i==1: P - F(2) = f[1]-f[2]      ;  i==n: P - F(n-1)
forw PERIODIC i==1: F(2) - P             ;  i==n: F(n+1) - F(n) = f[2]-f[1]
forw MIRROR   i==1: F(2) - P             ;  i==n: F(n-1) - P = f[n-1]-f[n]
analytic denominators: i∈(1,n) ? 6dt : dt   (topology-aware: 6dt only at open ends)
```
(Sign-flipped mirror branches are harmless because the same stencil is applied to x.)

### 4.6 Assembly of gradients (dispatch summary)

```
gradient(f::IntervalMap)            = gradient_slow(f)                         # grid.jl:596
gradient(f::TensorField (any other)) = gradient_fast(f)                        # grid.jl:597
gradient(f, j::Int)                  = gradient_fast(f, Val(j))  (IntervalMap: slow)
```
N-D full gradient (`gradient_X(f, d = centraldiff_X(base f))`, grid.jl:648):
```
denominator field d (per node, a Chain of N reals):
  Open/Product topology, induced metric:  d[i…] = (S_X(axis₁)[i₁], …, S_X(axis_N)[i_N])   (per-axis 1-D, analytic for ranges)
  Quotient topology, induced metric:      d[i…] = Σ_a S_X^{(a)}(points)[i…]   (each S^{(a)} applied to point Chains with remap, then the N Chains are summed)
  non-induced metric:                     d[i…] = applymetric(above, g[i…]) = (d_k / sqrt(g_kk))_k
numerator: for each axis a: S_X^{(a)}(fiber)[i…] (remapped via immersion)
result:    Chain{Submanifold(N),1}( S^{(1)}(f)/d₁, …, S^{(N)}(f)/d_N )
```
For rectilinear grids, `Σ_a S^{(a)}(points)` has component b equal to `S^{(b)}(x_b)` whenever the stencil annihilates constants on the mapped and unmapped node groups separately — true for all branches except slow upper-mirror (B2). Verified on SphereTopology poles and Möbius seam (fast): denominators equal the per-axis 1-D values (`1.0472 = 2·π/6`, corners `3.0 = 6·0.5`). A Lean port may therefore compute denominators per axis with the 1-D sub-topology (`subtopology(m, Val(a))`, MeshTopology `quotient.jl:589-601`: lower/upper face kinds reduced to `p ∈ {1,2}`) except for slow+upper-mirror where bit-parity requires the summed N-D form.

Per-axis gradient `gradient_X(f, Val(a))` returns the scalar (or fiber-typed) partial derivative field `S^{(a)}(f)/d_a` where `d_a` comes from the generic `centraldiff_X_points(f, Val(a))` (topology-aware) [verified: `gradient(s,1)` on a 2-D torus equals the first component of `gradient(s)` = `-0.4501581580785528`]. If axis `a` has length 1 the result is `0f`.

Minimum sizes: open axes need `n ≥ 4` (i=1 reads f[4]); `n = 3` throws `BoundsError` [verified on 3×3 and 3×3×3 grids]. Periodic axes read at most 2 nodes beyond the seam, so `n ≥ 3` is plausible but was not probed. The 4-D quadlinterp/leaf bugs aside, gradients exist for N=1..5 (`list(2,5)` loops).

Second derivatives are never computed with a dedicated stencil: `_laplacian(f) = tr(jacobian(gradient f))` applies the fast first-derivative twice (`gradient(gradient f)` → `TensorOperator` → trace), and `secondform` differentiates `∂ᵢγ` again with `gradient`. In the interior this equals the wide stencil `(f[i+2] - 2f[i] + f[i-2])/(4h²)` [verified `Δ(x²y) = 2y` exactly on a 5×5 grid].

`unitgradient(f) = g/|g|`; `derivative(z::complex 2-D) = (∂ₓz + ∂ᵧz / i)/2` [verified `z²` → `2z` at (-0.5, 0.5): `-1.0 + 1.0im`].

### 4.7 Interpolation (`linterp`, `bilinterp`, …) and evaluation

```
searchpoints(p, t):                                   # grid.jl:102-106
  i = searchsortedfirst(p, t) - 1     # number of nodes strictly less than t
  if i == 0 and t == p[1]: return (1, false)
  return (i, i == 0)                  # (bracket start, below-range flag)
# t in (p[k], p[k+1]] → k ; t == p[1] → 1 ; t < p[1] → (0,true) ; t > p[n] → n (upper out-of-range)

linterp(m, t):  (1-D field evaluation, grid.jl:114-137)
  t1 = t[1]; if isnan(t1) return zero(F)/0            # NaN of the fiber type
  (i, _) = searchpoints(p, t1)
  if topology is not Open:
     q = immersion(m)
     if i == 0:  return q.r[1]==0 ? zero(F) : m(reposition_odd(q.p[1], p, t1))
     if i == n:  return q.r[2]==0 ? zero(F) : m(reposition_even(q.p[2], p, t1))
  elif i == 0 or i == n: return zero(F)               # OUT OF RANGE ⇒ ZERO (not extrapolation, not NaN)
  return f[i] + (f[i+1]-f[i])*(t1-p[i])/(p[i+1]-p[i])

reposition_odd(pf, x, t)  = iseven(pf) ? x[end]-x[1]+t : 2x[1]-t     # below range: periodic shift up / mirror
reposition_even(pf, x, t) = isodd(pf)  ? x[1]-x[end]+t : 2x[end]-t   # above range: periodic shift down / mirror
# recursion handles multiple periods; 1-D uses q.p[1], q.p[2] directly (assumes r = identity)
```
N-D (`bilinterp`, `trilinterp`, `quintlinterp`; grid.jl:272-456): per-axis `searchpoints`; if Open and any axis out of range (`i==0` or `i==n_a`) → `zero(F)`; if Quotient: an out-of-range axis whose face is open (`q.r[face]==0`) → `zero(F)`; otherwise recurse on repositioned coordinates `reposition(lowFlag, highFlag, q.p[2a-1], q.p[2a], axis, t_a)` (uses `q.p[2a-1], q.p[2a]` positionally — assumes `r` is the identity; transverse permutations `q` are ignored, so interpolation across Möbius/sphere seams is only approximate). In range:
```
bilinterp(x,y,x1,x2,y1,y2,f11,f21,f12,f22):
  f1 = linterp(x,x1,x2,f11,f21);  f2 = linterp(x,x1,x2,f12,f22);  linterp(y,y1,y2,f1,f2)
with f11=f[i,j], f21=f[i+1,j], f12=f[i,j+1], f22=f[i+1,j+1]
trilinterp: bilinterp on the k-plane and k+1-plane, then linterp in z (corner order f111,f211,f121,f221,f112,f212,f122,f222)
quadlinterp / quintlinterp: same recursion (last axis outermost)
```
[verified: `g(x,y)=x+10y` on 3×3: `g(0.25,0.75)=7.75`, `g(1.5,0.5)=0.0` (out of range), `g(1,1)=11`; periodic `sin` on 9 nodes: `s(7.0) = 0.6453599636073625` (wrap), `s(-0.5) = -0.45015815807855325`.]

Callable forms: `m(x,y)` / `m(Chain)` / `m(Complex)` (2-D: re,im) / `m(PseudoCouple)`. For RectangleMap a single real argument means **leaf**, not evaluation: `m(t::Real) = leaf(m, t)` (grid.jl:147) → interpolated slice along axis 2 [verified `leaf(f,0.25)` of `x+10y` on 0:0.5:1² = `[2.5,3.0,3.5]`].

### 4.8 `hat` / `heaviside`

```
select_hat(p, t, i) = |p[i]-t| < |p[i+1]-t| ? i : i+1          # ties → i+1
hat(b::GridBundle{1}, x=0):
  (i, below) = searchpoints(p, x); out = zeros(n)
  if !(below || i == n): out[select_hat(p, x, i)] = 1
# N-D: same per axis; any axis out of range → all zeros; defaults y=x, z=y, … (diagonal point)
```
(`x == p[n]` gives `i = n-1` and selects `n`.) `heaviside(x) = x<0 ? 0 : 1` (H(0)=1), products over Chain components.

### 4.9 Difference matrices (`Tridiagonal`, grid.jl:559-585)

With `dx_i = x_{i+1}-x_i`:
```
FD{-1} (backward):  row 1: (-1/dx₁, +1/dx₁) at cols (1,2);  row i≥2: (-1/dx_{i-1}, +1/dx_{i-1}) at cols (i-1,i)
FD{0}  (forward):   row i<n: (-1/dx_i, +1/dx_i) at (i,i+1);  row n: (-1/dx_{n-1}, +1/dx_{n-1}) at (n-1,n)
FD{1}  (central):   row 1: (-1/dx₁, 1/dx₁); row i: (-b_i, 0, b_i) with b_i = 1/(x_{i+1}-x_{i-1}); row n: (-1/dx_{n-1}, 1/dx_{n-1})
SD{1}  (2nd deriv): row i (2..n-1): C_i=2/((dx_{i-1}+dx_i)dx_{i-1}), -(C_i+B_i), B_i=2/((dx_{i-1}+dx_i)dx_i);
                    row 1: (+1/(dx₁dx₂), -1/(dx₁dx₂));  row n: (-1/(dx_{n-2}dx_{n-1}), +1/(dx_{n-2}dx_{n-1}))
```
Beware in-place `pushfirst!/push!` on shared arrays in the Julia source; the formulas above are the resulting matrices [verified on 0:0.25:1: FD{1} rows `[-4,4,…]`, `[-2,0,2,…]`, SD{1} `[16,-16]`, `[16,-32,16]`, `[-16,16]`].

### 4.10 Quadrature

```
trapz 1-D (general, grid.jl:1229-1232):  d = diff(points); g = metricfiber(f); Σ_i (d_i/2)(g_{i+1}+g_i)
trapz 1-D IntervalRange (1259-1261):     trapz1(fiber, h) = h*((f₁+f_n)/2 + Σ_{i=2}^{n-1} f_i)     # ignores metric
cumtrapz 1-D IntervalRange (1354-1356):  cumtrapz1(f,h) = [0; (h/2)*cumsum(f[2:end]+f[1:end-1])]
cumtrapz 1-D general (1317-1322):        [0; (d/2) .* cumsum(g[2:end]+g[1:end-1])]      # BUG B1: should be cumsum((d/2).*(…))
trapz N-D aligned (1262-1267, 1245-1248): reduce axes N, N-1, …, 1 with trapz1 along that axis:
     i = h_a*((A[…,1,…] + A[…,end,…])/2 + sum(A[…,2:end-1,…], dims=a)[…,1,…])
trapz N-D general (1268-1274, gentrapz2): for a = N..1: A[…,k,…] = (d_a[k]/2)*(A[…,k,…]+A[…,k+1,…]) for k<n_a; A[…,n_a,…]=0; A = sum(A, dims=a) (drop axis)
trapz per-axis (m, Val(J)) (1237-1243 aligned / 1275-1283 general): reduce only axis J → field over remaining axes
cumtrapz N-D aligned (1357-1361, cumtrapz1 + gencat): for a = 1..N: A = (h_a/2)*cumsum(A[2:end]+A[1:end-1] along a, dims=a)
     then re-pad a zero slab at the start of each axis (axis 1 innermost): result same size as input
cumtrapz N-D general (1362-1367): per axis a: A = A[2:end]+A[1:end-1]; A[…,k,…] .*= d_a[k]/2; cumsum(dims=a); then zero-pad
cumtrapz per-axis (m, Val(J)): only axis J, zero slab at index 1 of axis J
integrate_riesz 1-D: w ⋅ metricfiber(f);  N-D: multiply by w_a[k] along each axis and sum, axes N..1
integral_riesz 1-D: cumsum(w .* g);  N-D: for a = 1..N: A[…,k,…] .*= w_a[k]; A = cumsum(A, dims=a)
metricfiber(f) = f if induced metric & not extrinsic, else f .* sqrt|det g| (full) or f .* sqrt|g_JJ| (per axis)
```
Exact order of axis reductions: trapz goes N→1, cumtrapz goes 1→N. `integral_riesz` with trapezoid weights is `cumsum(w.*f)`, whose intermediate values differ from `cumtrapz` (only the last value agrees) [verified: x² on 0:0.25:1 → riesz `[0, .015625, .078125, .21875, .34375]` vs cumtrapz `[0, .0078125, .046875, .1484375, .34375]`].

Gauss–Legendre (`GaussLegendre(N)`, 1104-1109): Jacobi matrix `T` tridiagonal with zero diagonal and off-diagonals `β_k = 0.5/sqrt(1-(2k)^{-2})`, k=1..N-1; nodes = eigenvalues (ascending from `eigen` of the symmetric matrix), weights `2*V[1,:].^2`. On `[a,b]` (from a vector x of length N): nodes `(c+1)(b-a)/2 + a`, weights `w (b-a)/2`. [verified N=5: nodes `[-0.906179845938662, -0.5384693101056816, 6.661338147750939e-16, 0.5384693101056837, 0.906179845938664]`, weights `[0.23692688505618867, 0.4786286704993673, 0.5688888888888884, 0.47862867049936597, 0.2369268850561885]` — note the non-symmetric rounding from LAPACK; the Lean port will not bit-match unless it uses the same eigensolver; compare with tol 1e-13.] **Important**: `integrate_gausslegendre(f)` uses GL *weights* but the *fiber values at the original grid nodes* (not at GL nodes) — the RieszQuadrature for a vector `x` has nodes computed but `integrate_riesz(t, w)` only uses `w`. So it is a weighted sum of samples at the wrong abscissae unless the field was sampled on `GaussLegendre(x)` nodes [verified: x² on 0:0.25:1 → 0.3391460131702572].

### 4.11 Arc length

```
arcsteps(f)      = [ |f_{i+1} - f_i|_g  for i=1..n-1 ]           # chord lengths, metric via refdiff
totalarclength   = Σ arcsteps
arclength(f)     = TensorField(base f, [0; cumsum(arcsteps)])     # cumulative chord length
arctime(f)       = TensorField(points = arclength values, fiber = original parameter)
arcparametrize(f)= TensorField(points = arclength values, fiber = fiber f)
arcsample(f, i)  : ral = LinRange(0, L, i); ts = arctime(f).(ral) (linear interp); TensorField(ral, f.(ts))
arcresample(f, i): same ts;                                        TensorField(ts, f.(ts))
```
[verified helix on 0:0.25:2π: `arclength[1:4] = [0.0, 0.27892679430042294, 0.5578535886008458, 0.8367803829012688]`, `totalarclength = 6.973169857510573`; `arcresample(helix,5)` points `[0.0, 1.5625…, 3.125, 4.6875, 6.25]`.]

### 4.12 Curves (IntervalMap/AbstractCurve), exact discretization

Let `x` = parameter nodes, `γ` = fiber, `d = S_slow(x)` (raw numerators), `D(v) = S_slow^{topo}(v)./d` (componentwise for Chains), `|·|` Euclidean (or metric), `unit(v) = v/|v|`:

```
t   = D(γ)                                    # γ'  (tangent(f) = gradient(f) is exactly this)
s   = |t|                                     # speed
T   = t ./ s                                  # unittangent (note: unittangent(f::IntervalMap) = unitgradient = t/|t|)
κN  = D(T) ./ s                               # normal(f)
N   = unit(D(unit(t)))                        # unitnormal(f)
κ   = |D(T)| ./ s                             # curvature(f)   (radius = s ./ |D(T)|)
n2  = D(t)                                    # γ''
b   = t ∧ n2                                  # bivector γ'∧γ''
τ   = Real((b ∧ D(n2)) ./ |⋆b|²)              # torsion (3-D): pseudoscalar coefficient of γ'∧γ''∧γ''' over |γ'×γ''|²
binormal     = ⋆(t ∧ κN)                      # sκB
unitbinormal = ⋆(unit(t) ∧ unit(D(unit(t))))  # B
frame (3-D)  = [t, κN, ⋆(t∧κN)]               # columns;  plane: osculatingplane = [t, κN]
unitframe(3-D) = [T, N, ⋆(T∧N)];              # plane: unitosculatingplane = [T, unit(D(T))]
cartan(space) = columns [(0,κ,0), (-κ,0,τ), (0,-τ,0)] with κ as above, τ as torsion
cartan(plane) = Chain(Chain(0,κ), Chain(-κ,0))
frenet(space) = TensorOperator( D(Chain(T, N', ⋆(T∧N'))) ./ s )  with N' = unit(D(T))     # d/ds of the Frenet frame
curvatures(space) = κ v₁₂ + 0 v₁₃ + τ̃ v₂₃,  τ̃ = ((t ∧ κN) ∧ D(κN)) / |⋆(t∧κN)|²
bishop θ: τs = τ .* s;  θ₁ = θ0;  θ_{k+1} = θ0 + ((x_{k+1}-x_k)/2) * Σ_{m≤k} (τs_m + τs_{m+1})   # BUG B1 for non-uniform x
bishoppolar = Chain(κ, θ);  bishop = Chain(κ cos θ, κ sin θ);  normalangle = θ (θ0=0)
bishopframe  = [T, cosθ·(D(T)/s) - sinθ·⋆(T∧D(T)/s), sinθ·(D(T)/s) + cosθ·⋆(…)]   with s := first speed only (BUG B6)
evolute = γ + (s ./ |D(T)|²) .* D(T);  involute = γ - T .* arclength(γ)
tangentangle = cumtrapz(κ) (over parameter);  totalcurvature = trapz(κ);  winding = totalcurvature/2π
planecurve(κ, φ) = cumtrapz( Chain.(cos θ, sin θ) ),  θ = cumtrapz(κ) + φ
```
Every `D` above uses the **same** `d` computed once from the parameter nodes and the curve's own topology (periodic curves get periodic stencils). [verified values in §6.]

Generated N-dim (N ≥ 4) curve frames/curvatures: see table §2.12 (lines 612-628, 710-719, 750-769); they follow the Gram–Schmidt-by-differentiation recursion `e_{i} = unit(D(e_{i-1}))`, `e_N = ⋆(e₁∧…∧e_{N-1})`, `κ_i = ⟨e_{i+1}, D(e_i)⟩/|γ'|`.

### 4.13 Hypersurfaces `γ: grid^n → R^{n+1}` (VectorField), default fast gradient

```
g_i   = D_i γ  (fast, topology-aware)                  # gradient(f)[i]
tangent  = g_1 ∧ … ∧ g_n                              # n-vector
normal   = ⋆tangent                                    # (2-D→3-D: g_1 × g_2, right-handed ⋆(v₁₂)=v₃)
unitnormal ν = ⋆unit(tangent) ;  normalnorm = |normal|
jacobian = [g_1 … g_n] (columns) ; weingarten = [D_1 ν … D_n ν]
I_ij  = g_i · g_j                          (firstform, symmetric TensorOperator over Submanifold(n))
II_ij = (D_j g_i) · ν   computed as: row/col 1 from gradient(g_1) (all partials of g_1),
        entries (j,k) with 2≤j≤k from gradient(g_j, Val(k))     (so II_12 = D_2(g_1)·ν, not D_1(g_2)·ν)
S     = inv(I) ⋅ II                        (shape)
H     = eigpolys(S, Val(1)) = tr(S)/n       (meancurvature; Grassmann eigpolys: `scalar(X)` for Val(1))
curvatures = Chain(e_k(κ)/C(n,k), k=1..n) with e_n = det S; computed from the characteristic polynomial (n≠2) or (tr/2, det) (n=2)
principals = eigvals(S), principalaxes = eigvecs(S)       (Grassmann; 2×2 ascending in probe)
K_e   = ν ∧ D_1ν ∧ … ∧ D_nν                 (gaussextrinsic, top form of R^{n+1})
K_i   = Real(sectordet(N/|N|)) / |N|        (gaussintrinsic; wrapped as top-grade Chain of the parameter space)
gausssign = sign(K_e)
III   = firstform with g replaced by gradient(ν)   (thirdform)
sectordet = γ ∧ g_1 ∧ … ∧ g_n ;  sectorintegrate = trapz(sectordet)/(n+1)  (signed enclosed volume)
surfacearea = trapz(normalnorm) ;  area = cumtrapz(normalnorm)
graph(s) for a ScalarField: (x_1,…,x_n, s)  ⇒ tangent(s)/normal(s)/jacobian(s) act on the graph
firstform(s::ScalarField) = δ_ij + ∂_i s ∂_j s  (graph metric) ;  firstformdiag(s) = diag(1 + (∂_i s)²)
```
Orientation: with `TorusParameter` and `torus(u,v) = ((2+½cos u)cos v, (2+½cos u) sin v, ½ sin u)` the computed normal points **inward** (`unitnormal[4,5] = -1.0v₃` at the top of the tube), so `II`, `S`, `H` are positive there and `sectorintegrate(tor)` is **negative** (`-9.83235v₁₂₃` on 60×60) [verified].

Intrinsic metric & Christoffel symbols:
```
intrinsicmetric(γ) = GridBundle(points, Outermorphism(I) per node, same topology)
dg   = d(g/2) : entrywise fast gradient of the metric matrix field, dg[k,j][i] = ½ ∂_i g_kj
[ij,k] = _firstkind(dg,k,i,j) = dg[k,j][i] + dg[i,k][j] - dg[i,j][k]
Γ^k_ij = secondkind = Σ_l (g⁻¹)[l,k] · [ij,l]           # layout: secondkind(g)[i,j] = Chain_k Γ^k_ij
firstkind(g)[i,j] = Chain_k Σ_l [ij,l]                 # BUG B10: should be Chain_k [ij,k]
geodesic RHS: x = Chain(pos, vel) ↦ Chain(vel, -Σ_{i,j} Γ(pos)[i,j] vel_i vel_j)
```
[verified torus 13×17 at u=π/2: `Γ^1_22 ≈ 3.97785 (exact 4)`, `Γ^2_12 ≈ -0.238732 (exact -0.25)`.]

### 4.14 Lie derivative / action convention (verified)

```
action(X::VectorField, f::ScalarField)  = X ⋅ ∇f                    (directional derivative, Real)
action(X::VectorField, Y::VectorField)  = Chain_k ( X ⋅ D_k Y )      # = J_Yᵀ X, NOT (X·∇)Y = J_Y X
Lie[X,Y] = X(Y) - Y(X)  with the above action
```
Probe (`X = (xy, x²+3y)`, `Y = (-y, x)` at (1, 0.25)): `X(Y) = 1.75v₁ - 0.25v₂`, `Lie[X,Y] = -0.1875v₁ - 3.0v₂` (the textbook bracket would be `(-2.6875, -2.25)`). Port the Cartan convention and name it clearly (`actionT`), optionally also provide the textbook one.

### 4.15 Products, revolutions, generators, links

* `fiberproduct(f, g, fun)`: fiber `A[i…, j…] = fun(f[i…], g[j…])`, first factor's indices first (fastest) [verified `(a,b)->a+10b` on 0:0.5:1 → `[0 5 10; .5 5.5 10.5; 1 6 11]`]. Topology: `immersion(f) × immersion(g)` (`fiber.jl:463-466`, MeshTopology `quotient.jl:195-283`): open×open = open; otherwise the second factor's partner ids `p` are shifted by `2·ndims(f)`, its non-zero `r` entries by `length(f.p)`, and the transverse maps `q` are extended by `ProductTopology` of the other factor's sizes.
* `revolve(profile, circle)` with `revolve22(f,g) = (f₁g₁, f₁g₂, f₂)` etc.; `unitsphere(n,m)` = `fibersphere(unitcircle(LinRange(-π/2,π/2,n)), unitcircle(m), revolve22)` → rows from south pole (-z) to north pole, columns starting at θ=-π [verified 3×5].
* `link(f,g)[i,j] = ((g_j - f_i) ∧ f'_i ∧ g'_j)/|g_j - f_i|³`; `linknumber = trapz_2D(link)/4π` (trivector).
* `sectorize(r::RealFunction, g) = fibersector(r, g, *)` — radial scaling fill; `cylinderize`.

### 4.16 Miscellaneous numerics

* `ballvolume(n)`: n even `π^(n/2)/(n/2)!`, odd `2·k!·(4π)^k/n!` with `k = n÷2` [verified `[2.0, π, 4.18879…, 4.93480…, 5.26379…]`]; `spherearea(n) = n·ballvolume(n)`.
* `bound`, `boundlog`: see §2.7. `boundlog(12.0) = 10 + log(3) = 11.09861228866811` [verified].

---

## 5. Display / printing

Neither `grid.jl` nor `diffgeo.jl` defines `show` methods. Everything prints through `TensorField`/`LocalTensor` display (Cartan core) and Grassmann `Chain`/`Single`/`TensorOperator` display (Grassmann report). Observed strings [verified, p13.jl], useful as display goldens once those printers are ported:

```
julia> speed(Chain.(cos(t),sin(t),t/2))          # t = TensorField(0:0.5:2)
5-element TensorField{Coordinate{Float64, InducedMetric}, Float64, 1, IntervalRange{…}, Vector{Float64}}:
 0.0 ↦ 1.1336650946718996
 0.5 ↦ 1.1162703313062396
 1.0 ↦ 1.1162256217923638
 1.5 ↦ 1.1162703313062396
 2.0 ↦ 1.1336650946718991

julia> show(stdout, speed(h))                        # compact form
LocalTensor{Coordinate{Float64, InducedMetric}, Float64}[0.0 ↦ 1.1336650946718996, 0.5 ↦ 1.1162703313062396, …]

julia> unittangent(h)       # vector-valued: each line "<param> ↦ <Chain>" (Chain printed with 6 significant digits)
 0.0 ↦ 0.0221229v₁ + 0.897211v₂ + 0.441047v₃
  0.5 ↦ -0.436475v₁ + 0.780293v₂ + 0.44792v₃      # (note: Julia right-aligns the "↦" column; leading spaces vary)

julia> integrate(h)
0.890274v₁ + 1.38652v₂ + 1.0v₃

julia> gradient(TensorField(ProductSpace(0:0.5:1.5,0:0.5:1.5), x->x[1]*x[2]))   # 2-D: matrix of "point↦value" cells, no spaces around ↦
 0.0v₂+0.0v₃↦0.0v₁+0.0v₂  0.0v₂+0.5v₃↦0.5v₁+0.0v₂  …
```
Other observed scalar/blade outputs: `sectorintegrate(circ) = 3.1415v₁₂`, `linknumber(...) = 0.999573v₁₂₃`, `gaussintrinsic(tor)[i] = 0.50257v₂₃` (top-grade Chain of the parameter manifold `⟨_11_⟩`, whose basis prints as `v₂,v₃`), `curvatures(helix)[i] = 0.833838v₁₂ + 0.0v₁₃ + 0.371398v₂₃`, `cartan(planecurve)[i] = (0.0v₁+0.330898v₂)v₁ + (-0.330898v₁+0.0v₂)v₂`, `wronskian(helix)[i] = 0.249284v` (grade-0 Chain prints with a bare `v`), TensorOperators print as `3×3 Endomorphism{⟨111⟩, Simplex{…}}:` followed by a header row of basis labels and one row per ambient basis vector (columns = Chains), e.g. `cartan(helix)[3]`:
```
3×3 Endomorphism{⟨111⟩, Simplex{⟨111⟩, Chain{⟨111⟩, 1, Float64, 3}, 3}}:
 v₁₂₃  v₁         v₂         v₃
   v₁   0.0       -0.796397   0.0
   v₂   0.796397   0.0       -0.399011
   v₃   0.0        0.399011   0.0
```
Recommendation: goldens should compare numbers, not strings; port display as a separate `Repr` layer.

---

## 6. Examples with expected outputs (golden candidates)

### 6.1 From the docs (`docs/src/fiber.md`) — with **current (0.4.16) values** where they differ

| Doc snippet (verbatim input) | Doc output | 0.4.16 oracle output |
|---|---|---|
| `linspace = ProductSpace(-2:0.03:2); diameter = TensorField(linspace, x->abs(x)<1); integrate(diameter)` (fiber.md:566-569) | `1.98v_1` | `1.98` |
| `square = ProductSpace(-2:0.003:2,-2:0.003:2); disk = TensorField(square, x->abs(x)<1); integrate(disk)` (574-577) | `3.141414000000001v_{12}` | `3.1414139999999997` |
| `cube = ProductSpace(-2:0.07:2,-2:0.07:2,-2:0.07:2); ball = TensorField(cube, x->abs(x)<1); integrate(ball)` (582-585) | `4.180680595387064v_{123}` | `4.191460000000001` (!) |
| `t = TensorField(0:0.001:2pi); circ = Chain.(cos(t),sin(t)); surfacearea(circ)` (605-610) | `6.283000000652752` | `6.283000000652752` |
| `sph = spher.(SphereParameter(60,60)); surfacearea(sph)` (606-611) | `12.533742943601457` | `SphereParameter(60,60)` **BROKEN** (MethodError, B12); with `SphereParameter(LinRange(-π/2,π/2,60), LinRange(-π,π,60))`: `12.538186337430929` |
| `(sectorintegrate(circ),sectorintegrate(sph))` (635-636) | `(3.1415v_{12}, 4.17791v_{123})` | `3.1415v₁₂`, `6.30575e-17v₁₂₃` (the doc's `spher` uses x₁ as colatitude but SphereParameter's x₁ ∈ [-π/2,π/2] double-covers with opposite orientations ⇒ 0) |
| `t = TensorField(0:0.01:2pi); f(t)=Chain(cos(t[1]),sin(t[1]),0); g(t)=Chain(0,1+cos(t[1]),sin(t[1])); linknumber(f.(t),g.(t))` (650-653) | `(…, 1.0)` | `0.999573v₁₂₃` |
| `tor = torus.(TorusParameter(60,60))` (675-680) | (plots) | `TorusParameter(60,60)` **BROKEN** (B12); `TorusParameter(LinRange(0,2π,60),LinRange(0,2π,60))`: `surfacearea = 39.32940002200309` (exact 4π²Rr = 39.478), `sectorintegrate = -9.83235v₁₂₃` (exact volume 2π²Rr² = 9.8696), `meancurvature[10,10] = 1.125642430712953`, `gaussintrinsic[10,10] = 0.50257v₂₃`, `gaussextrinsic[10,10] = 0.572618v₁₂₃`, Gauss–Bonnet `integrate(Real(gaussintrinsic(tor))*normalnorm(tor)) = 1.040448907880541e-15` |
| `t = TensorField(0:0.01:4*pi); lin = Chain.(cos(t)*t,sin(t)*11+t); arclength(lin); speed(lin); curvature(lin)` (444-451) | plots | dump via oracle |
| `planecurve(cos(t)*t)`, `planecurve(cos(t*t)*t)`, `planecurve(cos(t)-t*sin(t))` (452-457) | plots | `planecurve_cos_t` in goldens JSON |
| `tormet = surfacemetric(tor); torcoef = secondkind(tormet)` (727-728) | – | works (13×17 checked, §4.13) |

### 6.2 Probe goldens (inputs exactly as written; outputs copied from the oracle)

1-D stencils, `x = TensorField(0:0.1:1)`, `f = x*x*x`:
```
gradient(f)        = [-3.469446951953614e-17, 0.030000000000000023, 0.12, 0.2700000000000001, 0.48, 0.7499999999999999, 1.0799999999999998, 1.4700000000000002, 1.9200000000000004, 2.430000000000001, 2.9999999999999947]
gradient_fast(f)   = [-3.469446951953614e-17, 0.04000000000000001, 0.13, 0.2800000000000001, 0.49, 0.76, 1.0899999999999999, 1.4800000000000002, 1.9300000000000002, 2.44, 2.9999999999999947]
gradient_back(f)   = [-3.469446951953614e-17, 0.010000000000000002, 0.07000000000000002, 0.19, 0.37000000000000005, 0.61, 0.9100000000000001, 1.2699999999999996, 1.6900000000000006, 2.1700000000000004, 2.9999999999999947]
gradient_forw(f)   = [-3.469446951953614e-17, 0.07000000000000002, 0.19, 0.37000000000000005, 0.61, 0.9100000000000001, 1.2699999999999996, 1.6900000000000006, 2.1700000000000004, 2.7099999999999995, 2.9999999999999947]
centraldiffpoints(x)      = [0.6, 0.6000000000000001, 1.1999999999999997, 1.2000000000000002, 1.2000000000000002, 1.1999999999999997, 1.1999999999999995, 1.2000000000000006, 1.2000000000000006, 0.5999999999999994, 0.600000000000001]
centraldiff_fast_points(x)= [0.6, 0.2, 0.19999999999999998, 0.2, 0.2, 0.19999999999999996, 0.19999999999999996, 0.20000000000000007, 0.20000000000000007, 0.19999999999999996, 0.600000000000001]
```
Topologies, `tp = TorusParameter(9)` (LinRange(0,2π,9), periodic), `sin(tp)`:
```
gradient      = [0.9882151640869478, 0.6987736437972574, 8.124475112015072e-17, -0.6987736437972574, -0.9882151640869475, -0.6987736437972576, -1.4949559613190352e-16, 0.6987736437972574, 0.9882151640869478]
gradient_fast = [0.9003163161571061, 0.6366197723675814, 7.067899292141149e-17, -0.6366197723675813, -0.9003163161571061, -0.6366197723675815, -1.4135798584282297e-16, 0.6366197723675813, 0.9003163161571061]
gradient_back = [0.9003163161571061, 0.9003163161571061, 0.3729232285780567, -0.37292322857805654, -0.9003163161571061, -0.9003163161571062, -0.3729232285780567, 0.37292322857805643, 0.9003163161571061]
gradient_forw = [0.9003163161571061, 0.3729232285780567, -0.37292322857805654, -0.9003163161571061, -0.9003163161571062, -0.3729232285780567, 0.37292322857805643, 0.9003163161571061, 0.9003163161571061]
centraldiffpoints = [9.424777960769378, 9.42477796076938 ×7, 9.424777960769378]      (= 12h everywhere)
```
`mp = MirrorParameter(9)`, `mp*mp`:
```
gradient      = [0.5235987755982988, 1.4398966328953218, 3.141592653589793, 4.712388980384689, 6.283185307179586, 7.853981633974485, 9.424777960769378, 10.99557428756427, 12.566370614359199]
gradient_fast = [0.7853981633974483, 1.5707963267948966, 3.141592653589793, 4.71238898038469, 6.283185307179586, 7.853981633974484, 9.42477796076938, 10.995574287564276, 12.566370614359199]
```
`sin(ClampedParameter(9))` slow: last entry `-0.11858581969043375` (bug B2; fast gives `0.9003163161571061`).

Raw numerators, `v = collect(0:0.25:2).^2`:
```
centraldiff(v)                          = [0.0, 0.75, 3.0, 4.5, 6.0, 7.5, 9.0, 5.25, 6.0]
centraldiff_fast(v)                     = [0.0, 0.25, 0.5, 0.75, 1.0, 1.25, 1.5, 1.75, 6.0]
centraldiff(v, MeshTopology.TorusTopology(9)) = [6.0, 0.5, 3.0, 4.5, 6.0, 7.5, 9.0, 11.5, 6.0]
centraldiff(0:0.25:2)                   = [1.5, 1.5, 3.0, 3.0, 3.0, 3.0, 3.0, 1.5, 1.5]      (analytic 6h/12h)
centraldiff(collect(0:0.25:2), TorusTopology(9)) = [3.0, …, 3.0]
```
Non-uniform, `xs = [0.0,0.1,0.3,0.35,0.6,1.0,1.2]`, `fu = TensorField(xs, xs.^2)`:
```
gradient(fu)  = [1.925000000000002, 0.33695652173913054, 0.3857142857142857, 0.7799999999999999, 1.3186046511627907, 1.787209302325581, -8.349999999999897]
integrate(fu) = 0.5921249999999999
integral(fu)  = [0.0, 0.0005000000000000001, 0.011000000000000001, 0.008062499999999998, 0.10062499999999999, 0.43299999999999994, 0.46049999999999985]   # BUG B1 (non-monotone)
trapzweights(xs) = [0.05, 0.15, 0.12499999999999999, 0.15, 0.325, 0.3, 0.09999999999999998]
```
Quadrature: `x2 = TensorField(0:0.25:1)^2`: `integrate = 0.34375`, `integral = [0.0, 0.0078125, 0.046875, 0.1484375, 0.34375]`, `integral_riesz = [0.0, 0.015625, 0.078125, 0.21875, 0.34375]`, `integrate_gausslegendre = 0.3391460131702572`, `integrate_clenshawcurtis = 0.296078431372549`. 2-D `f2 = TensorField(ProductSpace(0:0.5:2,0:0.25:1), x->x[1]^2*x[2])`: `integrate = 1.375`; `integrate(f2,1) = [0.0, 0.6875, 1.375, 2.0625, 2.75]`; `integral(f2)` (5×5, column-major rows shown as Julia prints) `[0 0 0 0 0; 0 0.001953125 0.0078125 0.017578125 0.03125; 0 0.01171875 0.046875 0.10546875 0.1875; 0 0.037109375 0.1484375 0.333984375 0.59375; 0 0.0859375 0.34375 0.7734375 1.375]`; `integral(f2,2) = [0 0 0 0 0; 0 0.0078125 0.03125 0.0703125 0.125; 0 0.03125 0.125 0.28125 0.5; 0 0.0703125 0.28125 0.6328125 1.125; 0 0.125 0.5 1.125 2.0]`; `gradient(f2,1) = [0 0 0 0 0; 0 .25 .5 .75 1; 0 .5 1 1.5 2; 0 .75 1.5 2.25 3; 0 1 2 3 4]`; `_laplacian(f2)` rows `[0.0 0.5 1.0 1.5 2.0]` (= 2y).

Curves, `t = TensorField(0:0.25:2pi)`, `helix = Chain.(cos(t),sin(t),t/2)` (exact κ=0.8, τ=0.4):
```
speed[1:4]     = [1.1190652183764918, 1.1179191344011254, 1.1179183917500737, 1.117918391750074]
curvature[1:4] = [0.8338383062681279, 0.8017885144108534, 0.796396649634111, 0.8002603572587539]   (interior 0.7999586363451008)
torsion[1:4]   = [0.37101620066911134, 0.39833424147022256, 0.39901121220254987, 0.39758983408539467] (interior 0.40003101939973…)
normalangle[1:4] = [0.0, 0.10756209950621443, 0.2189830298890197, 0.33029989995560033]
bishoppolar[1:3] = [(0.8338383062681279, 0.0), (0.8017885144108534, 0.10756209950621443), (0.796396649634111, 0.2189830298890197)]
curvatures[1]  = (0.833838306268128, 0.0, 0.37139750711682945)      # (v₁₂, v₁₃, v₂₃)
frame[1]       = columns [(0.003705514350595962, 1.0011459594601693, 0.5), (-0.8338314421347417, -0.001563446991986741, 0.0030004568153352514), (0.0037856187132009845, -0.41692683930315844, 0.8347811857887774)]
unitframe[1]   = columns [(0.0033112586199147693, 0.8946270003035244, 0.4468014837646245), (-0.9999917680282439, -0.0018750002011589054, 0.0035983676844541946), (0.004056949759469164, -0.4468097208334423, 0.8946134271487471)]
arclength[1:4] = [0.0, 0.27892679430042294, 0.5578535886008458, 0.8367803829012688];  totalarclength = 6.973169857510573
integrate(helix) = (-0.03300622785097859, 0.0005477111705371879, 9.765625)
```
`ellipse = Chain.(2cos(t), sin(t))`: `curvature[1:4] = [2.282659651606191, 1.4979561266193164, 0.9210654477671031, 0.5442317371326649]`, `normalnorm[1:3] = [2.2826596516061906, 1.4979561266193162, 0.921065447767103]` (= curvature!), `surfacearea = totalcurvature = 4.8224240081866645`, `sectorintegrate = 6.249511031592964v₁₂` (area πab = 2π), `sectordet[1:2] = [2.00229v₁₂, 1.99974v₁₂]`, `totalarclength = 9.630385052196075`.
`planecurve(TensorField(0:0.1:2, x->1.0))[1:4] = [(0,0), (0.0997502082639013, 0.004991670832341408), (0.19850374541986468, 0.01991680820443588), (0.295273898768207, 0.044626285077255905)]`, end `0.90854v₁ + 1.41497v₂` (exact (sin 2, 1-cos 2)).

Surfaces, `tor = torus.(TorusParameter(LinRange(0,2pi,13),LinRange(0,2pi,17)))` with `torus(x) = Chain((2+0.5cos(x[1]))*cos(x[2]),(2+0.5cos(x[1]))*sin(x[2]),0.5sin(x[1]))`:
```
meancurvature[1:13, 1] = [1.1999999999999997, 1.1779738764024754, 1.1111111111111116, 0.9999999999999997, 0.8571428571428571, 0.7236654678598202, 0.6666666666666663, 0.7236654678598189, 0.8571428571428573, 0.9999999999999993, 1.1111111111111116, 1.1779738764024759, 1.1999999999999997]
gaussintrinsic[1:13, 1] = [0.7999999999999997, 0.7118955056099027, 0.4444444444444444, 1.1102230246251568e-16, -0.5714285714285711, -1.1053381285607227, -1.3333333333333324, -1.105338128560722, -0.5714285714285717, -1.1102230246251554e-16, 0.44444444444444414, 0.7118955056099029, 0.7999999999999997]
surfacearea = 36.73760950704862;  sectorintegrate = -9.18440237676215 v₁₂₃
at [4,5]: normal = (-0.0, -1.03315e-16, -0.930575); normalnorm = 0.9305745198610419; firstform = [[0.227973, 5.69813e-17],[5.69813e-17, 3.79856]];
          secondform = diag(0.455945, 2.10863e-16); shape = diag(2.0, 5.55112e-17); meancurvature = 0.9999999999999997;
          principals = (5.55112e-17, 2.0); gausssign = 1.0; sectordet = -0.465287v₁₂₃
secondkind(surfacemetric(tor))[4,5] = [[Γ¹₁₁,Γ²₁₁]=(3.48787e-16,-3.10138e-18), [Γ¹₁₂,Γ²₁₂]=(5.96706e-17,-0.238732), [Γ¹₂₂,Γ²₂₂]=(3.97785, 8.91835e-17)]
```
(Grid values at node 1 are exact to ~1e-16 because symmetric periodic errors cancel in these ratios — a strong golden.)

Interpolation and misc:
```
g2 = TensorField(ProductSpace(0:0.5:1, 0:0.5:1), x->x[1]+10x[2]):  g2(0.25,0.75)=7.75, g2(1.5,0.5)=0.0, g2(0.0,0.0)=0.0, g2(1.0,1.0)=11.0
x2(0.3)=0.09999999999999999, x2(1.5)=0.0, x2(-0.1)=0.0 ;  sin(TorusParameter(9))(7.0)=0.6453599636073625, (-0.5)=-0.45015815807855325
hat(base(TensorField(0:0.25:1)), 0.3) = [0.0, 1.0, 0.0, 0.0, 0.0];  hat 2-D (3×3 on 0:0.5:1, point (0.3,0.8)) = one at [2,3]
ballvolume.(1:5) = [2.0, 3.141592653589793, 4.1887902047863905, 4.934802200544679, 5.263789013914324]
spherearea.(1:5) = [2.0, 6.283185307179586, 12.566370614359172, 19.739208802178716, 26.31894506957162]
sphereradius(3) = 0.28209479177387814 ;  ballradius(3) = 0.6203504908994001
richardson(1) = [1.3333333333333333, -0.3333333333333333];  richardson(2) = [1.4222222222222223, -0.4444444444444444, 0.022222222222222223]
bound(12.0)=10.0; boundlog(12.0)=11.09861228866811; boundabove(12.0)=10.0; boundbelow(-12.0)=-10.0
unitcircle(5) = [(-1,-1.22465e-16), (6.12323e-17,-1), (1,0), (6.12323e-17,1), (-1,1.22465e-16)], topology maps [5],[2],[3],[4],[1]
degreeintegrate(Chain.(cos(t),sin(t))) (t = 0:0.01:2π) = 0.9999999996719778
linknumber on 0:0.05:2π = 0.9955867139542872 v₁₂₃
```

---

## 7. Dependencies on other chakravala packages

| Package | Symbols used by these two files | Where |
|---|---|---|
| **Grassmann.jl** | `Chain`, `Values`(via StaticVectors), `Single`, `Simplex`, `Submanifold`, `Manifold`, `mdims`, `list`, `value`, `Λ` (basis table, `.b[k]`), `bladeindex`, `binomial`, `∧`, `∨`, `⋆`, `⋅`/`contraction`, `contraction_metric`, `abs`/`abs2`/`unit` with metric, `det`, `inv`, `tr`, `TensorOperator`, `Endomorphism`, `DiagonalOperator`, `Outermorphism`, `outermorphism`, `compound`, `eigvals`, `eigvecs`, `eigpolys`, `scalar`, `MetricTensor`, `DiagonalForm`, `InducedMetric`, `istangent`, `indices`, `involute`, `metric`, `curl`, `d`, `∂`, `δ`, `𝓛`, `Lie`, `LieBracket`, `LieDerivative`, `bracket`, `realvalue`, `imagvalue`, `Couple`, `PseudoCouple`, `AbstractComplex`, `TensorAlgebra`, `TensorGraded`, `TensorNested`, `GradedVector`, `supermanifold`, `gradient` (generic function extended) | throughout |
| **Leibniz.jl** | `Nabla` (`Derivation{Bool,1}`), `Laplacian`, `∇`, `Δ` | diffgeo 99-120, 383 |
| **DirectSum.jl** | `tangent(V, 1, n)` (tangent-space manifold, used by broken `getnabla`), `Submanifold` metrics | diffgeo 43 |
| **AbstractTensors.jl** | `unit(t,g)`, `abs(t,g)`, `abs2(t,g)` (via Grassmann), `contraction_metric` | via Grassmann |
| **MeshTopology.jl** | `QuotientTopology` fields `p,q,r,s,c`, `OpenTopology`, `TorusTopology` (updatetopology), `isopen`, `immersion`, `subtopology(m, Val(N))`, `getindex(m, Val(N), i…)` neighbour remap, `cross_sphere`, `cross_sector`, `ProductTopology`, `CrossRange`, `×` of topologies | grid 118-457, 634-771, 1000-1043; diffgeo 37 |
| **StaticVectors.jl** | `Values` | |
| **AbstractAnalysis.jl** | `derivative` (name), `Limit`, `CountableVector`, `counter`, `supnorm` (indefintegrate only) | grid 606, 1448-1464 |
| Cartan core (same package) | `TensorField`, `GridBundle`, `PointArray`, `ProductSpace`, `RealRegion`, `Coordinate`, `LocalTensor`, `LocalPrincipal`, `PrincipalFiber`, `FrameBundle`, `SimplexBundle`, `FiberProductBundle`, `Global`, `base`, `fiber`, `points`, `coordinates`, `metricextensor`, `metrictensor`, `metrictensorfield`, `refmetric`, `isinduced`, `isextrinsic`, `graph`, `remove`, `split`, `resample`, `pointtype`, `fibertype`, `OpenParameter`, `SphereParameter`, `TorusParameter`, `unitdomain`, `volumes`, `graphbundle`, `interp` | |
| Julia stdlib | `LinearAlgebra` (`Tridiagonal`, `Diagonal`, `eigen`, `I`), `SparseArrays` (`spdiagm`), `Base.Threads.@threads`, `Base.Cartesian` (`@nloops`, `@nref`, `@ncall`) | |

---

## 8. Lean 4 porting notes

### 8.1 Core representation (recommended)

```lean
/-- Rank-`N` rectilinear grid. Axis coordinates are stored per axis (ProductSpace), which is all the
    algorithms here need; general curvilinear grids only arise as *fibers*. -/
structure Axis where
  pts   : FloatArray            -- strictly increasing
  step? : Option Float          -- `some h` when constructed from a range (enables analytic denominators)

inductive Face | open_ | periodic (partner : Fin (2*N)) (perm : TransPerm) | mirror (perm : TransPerm)
-- (precomputed from QuotientTopology.{p,q,r}: r=0 → open_, p[r]=self → mirror, else periodic)

structure Grid (N : Nat) where
  axes  : Vector Axis N
  faces : Vector Face (2*N)     -- index 2a / 2a+1 = lower / upper face of axis a (0-based)
  -- invariants (Prop, erased):
  hsz   : ∀ a, 1 ≤ (axes.get a).pts.size

/-- Field with fiber `α` stored column-major (first axis fastest) – identical to Julia `vec`. -/
structure Field (N : Nat) (α : Type) where
  grid : Grid N
  data : Array α                 -- or SoA: `Vector FloatArray k` for α = R^k (see 8.3)
  hdat : data.size = grid.card
```
Fibers: a small typeclass `FiberSpace α` with `add, sub, smul : Float → α → α, zero, dot, norm` (instances: `Float`, `Vec k := Vector Float k` / Grassmann `Chain`), so all stencils are written once. Stencil coefficients are small integers applied as `Float` multiplies in the same order as Julia (§4.3–4.5) for bit parity.

### 8.2 What should be dependent-type indices (zero runtime cost)

* Grid rank `N : Nat` and fiber dimension `k : Nat` (Chain size). Julia bakes both into types and generates code for N ≤ 5; Lean can be fully generic in `N` with `Fin N` axis indices and `Vector … N` shapes, and still specialize hot kernels for small `N` via `@[specialize]` / explicit instances.
* The stencil axis: replace `Val{M}` with `a : Fin N` (runtime, erased bounds proof).
* Size preconditions as erased `Prop` arguments: gradient requires `4 ≤ n_a` on every open axis (prevents the Julia `BoundsError` on 3-point axes, §4.6); interpolation brackets `i : Fin (n-1)`.
* `PlaneCurve`/`SpaceCurve` specializations become `k = 2` / `k = 3` instances (`frame`, `cartan`, `torsion`, `binormal` only exist for `k = 3`; generic `k ≥ 4` versions per §2.12).
* Stencil variant (`slow/fast/back/forw`) as an inductive argument that is always a literal at call sites so `@[inline]` + `match` constant-folds.
* Do **not** index types by grid sizes or by point values: sizes vary at runtime (resampling, arclength reparameterization) and would force recompilation/`cast`s.

### 8.3 Performance plan (how Julia gets its speed, and the Lean equivalent)

* Julia: `@generated` unrolling over `N ≤ 5` and over Chain components; `Base.Cartesian` loops (`@nloops/@nref/@ncall`) + `@threads` over the leading axis; static `Chain`/`Values` (stack-allocated SVectors) so per-node work allocates nothing; `Val{N}` axis dispatch compiled away. It recomputes denominators on every call (no caching) except that users can pass `d` explicitly.
* Lean plan:
  1. Store `Float` fields as `FloatArray` (unboxed). For `R^k` fibers use SoA: `k` FloatArrays (stencils become k independent scalar stencils — ideal for vectorization and for reusing one scalar kernel), or one interleaved FloatArray with stride `k`. Avoid `Array (Vector Float k)` (boxed per element).
  2. Precompute per axis the linear stride `st_a = ∏_{b<a} n_b`; interior nodes (`3 ≤ i_a ≤ n_a-2`) use `data[k ± st_a]`, `data[k ± 2 st_a]` without branching. Handle the 2+2 boundary slabs per axis in a separate loop using the face kind (§4.2) — the remap with transverse permutation only happens there.
  3. Denominators `S(x_a)` are 1-D per axis (see §4.6 justification) — compute once per (grid, variant, axis) and cache in the `Grid` (or pass explicitly like Julia's `d`). Slow+upper-mirror needs the N-D summed form for bit-parity (only affects `MirrorTopology`/`ClampedTopology`/sphere upper pole with the slow stencil).
  4. Curve pipelines (`curvature`, `torsion`, frames) call `D` 3–4 times on k=3 SoA arrays of length n; fuse where parity allows (it doesn't change results if each `D` is computed identically).
  5. Parallelism: optional `Task.spawn` over slabs of the last axis; results are deterministic (each output written once).
  6. Interpolation: binary search (`searchsortedfirst`) per axis; for repeated queries on a range axis use `O(1)` index arithmetic when `step?` is `some h` (result must still equal the binary-search bracket, including the `t == p[k+1] ↦ k` convention).
  7. Quadrature reductions: axis-by-axis over FloatArray, trapz in order `N → 1`, cumtrapz `1 → N`, to match rounding.

### 8.4 Proof opportunities that aid development (cheap, high value)

State over an abstract ordered field / `ℚ` model of the kernels (the Float kernels are the same code instantiated at `Float`):
* Consistency: every stencil branch annihilates constants (`S(1) = 0`) — `decide`/`norm_num` per branch; this is exactly the property violated by bug B2, so the proof *finds* it.
* Exactness: on a uniform grid (`x_i = x₀ + i h`), `S(x) = c·h` with `c ∈ {12, 6}` (slow), `{2, 6}` (fast), `{1, 6}` (back/forw); hence `D(a + b x) = b` exactly (over ℚ) — `ring`.
* Polynomial order: interior slow stencil exact for degree ≤ 4, one-sided exact for degree ≤ 3, fast interior exact for degree ≤ 2 (`ring` on symbolic `h`).
* Periodic remap is a bijection on `{1..n-1}` and `remap(n) = 1`, mirror remap is an involution fixing the face node — `omega`/`decide` for concrete, `Nat` lemmas in general.
* Trapezoid weights sum to `x_n - x_1`; cumtrapz last element = trapz (holds for the uniform branch and for the *fixed* non-uniform version; fails for Julia's B1 — keep the proof for the fixed variant).
* `richardson k` weights sum to 1; `qbinomial` symmetric; `ballvolume n = (2π/n) ballvolume (n-2)`; `spherearea n = n * ballvolume n`.
* Tridiagonal difference matrices annihilate constants (row sums 0).
* Frame orthonormality is *not* provable for the discrete Float version; test it numerically (property tests).

### 8.5 Tricky semantics to preserve

1. `D(f) = S(f)/S(x)` (ratio of identical stencils), including for non-uniform grids and for coordinates that jump across periodic seams.
2. Default variant by base type: real-parameter 1-D → slow (4th order); everything else (including 1-D `ProductSpace` bases) → fast (2nd order). `TensorField(TorusParameter(9))` silently drops the topology (wraps the field as an array ⇒ OpenTopology) [verified]; use `TorusParameter(9)` itself (already a TensorField).
3. Boundary indices themselves are remapped on quotient axes (`1 ↦ n` periodic), so seam nodes are expected to be duplicated (`LinRange(0,2π,n)` endpoints).
4. Out-of-range interpolation returns **zero** (not NaN, not extrapolation) on open faces; `NaN` input returns `zero/0`.
5. `integral`/`cumtrapz` returns same-size arrays with a leading zero slab; `integral_riesz` is a weighted cumsum, not a trapezoid cumsum.
6. `arclength` is cumulative **chord** length (polyline), not ∫|γ'|.
7. `normalnorm(PlaneCurve)` is curvature `κ` (since `normalframe = normal = κN` and `det(vector) = vector`); `surfacearea(planecurve) = ∫κ dt`; `tangentangle/totalcurvature/winding` integrate κ over the *parameter*.
8. `action(X, Y)_k = X·∂_kY` (transpose of the directional derivative) and `Lie` built from it (§4.14).
9. Surface orientation = `⋆(∂₁γ∧∂₂γ)` (right-handed), so standard torus/sphere parameterizations give inward normals and negative `sectorintegrate`.
10. `secondform` mixed term uses `D₂(∂₁γ)`; second derivatives are iterated first derivatives (wide stencil).
11. `isclosed` is an exact-zero test.
12. `hat` picks the nearest node with ties to the upper node; `heaviside(0) = 1`.
13. `GaussLegendre` quadratures use GL weights with values at the original nodes.

### 8.6 Known bugs / broken paths in 0.4.16 (decide: replicate vs fix)

| Id | Location | Symptom | Recommendation |
|---|---|---|---|
| B1 | grid.jl:1317-1322 (`cumtrapz` 1-D general), diffgeo.jl:779,790,800,809,819 (Bishop θ) | `(d/2).*cumsum(g[2:]+g[1:-1])` multiplies the running sum by the *current* step; wrong on non-uniform grids (non-monotone integral for positive integrand) | Implement correct `cumsum((d/2).*(…))`; add a `juliaCompat` flag reproducing the bug; goldens for non-uniform `integral` must be marked BUGGY (key `cumtrapz_nonuniform_x2_BUGGY`). Uniform grids agree either way. |
| B2 | grid.jl:818 (slow, upper-face mirror) | `7(points - f[0])` should be `7(points + f[0])`-equivalent (odd reflection); stencil doesn't annihilate constants → wrong derivative at the last node of Mirror/Clamped axes (e.g. `-0.1186` vs `0.988`) | Fix (use `2f[n-2] - 16f[n-1] + 14f[n]`); keep compat flag; goldens key `grad_slow_clamped_sin_BUGGY_upper`. |
| B3 | grid.jl:704 | `centraldiff_X_calc(f::GridBundle{1}, dt::Real, s)` uses undefined `l` → `UndefVarError` (breaks `centraldiffdiff(f, dt)`) | Fix (`s[1]`). |
| B4 | grid.jl:1264, 1359 | aligned N-D `trapz`/`cumtrapz` with non-induced metric reference undefined `j` | Fix (use full `metricfiber(f)`). |
| B5 | grid.jl:657-664 | metric per-axis gradient: `for i ∈ l[1]; for j ∈ l[2]` iterates a single Int (only one node scaled), 2-D only | Fix to full loops; low priority (non-induced metrics rare). |
| B6 | diffgeo.jl:774,785 | `s,b = Real.(abs.(t))` destructures the speed vector → `s` = first speed only | Fix to `s = speeds`; equal on constant-speed curves (helix/circle goldens remain valid). |
| B7 | grid.jl:356 | `function (m)(t::Chain{V,G,T,4})` defines a *function named `m`* instead of `quadlinterp(m,t)`; 4-D field evaluation throws `MethodError` [verified] | Implement the intended 4-D `quadlinterp(m,t)` (analogue of 3-D). |
| B8 | grid.jl:185-256 | 4-D/5-D `leaf`: wrong axis selection (`v[j>1 ? 2 : 1]` etc.), `leaf3`/`leaf4` call `bilinterp` with 3/4 coords, `m(j)` calls `leaf(m,t,j)` with undefined `t` | Re-derive from the 3-D version (other axes in increasing order). |
| B9 | diffgeo.jl:1099,1134 | 5-D `ddfdwdv = gradient(dfdv, Val(5))` (should be `dfdw`) | Fix. |
| B10 | diffgeo.jl:1237-1239 | generic `firstkind(dg,i,j,k)` sums `_firstkind` over all `l`, ignoring `k` (both components equal, [verified]) | Fix to `_firstkind(dg,k,i,j)`; secondkind is correct. |
| B11 | diffgeo.jl:25 | `bound(::LocalTensor{…,Real})` returns `sign(fiber*lim)` (±1) instead of `sign(fiber)*lim` | Fix. |
| B12 | Cartan quotient.jl (Parameter constructors) | `TorusParameter(60,60)`, `SphereParameter(60,60)`, `OpenParameter(9,7)` → `MethodError` (Topology constructors don't accept `ProductSpace`); 1-D and `XParameter(range, range)` forms work | Out of scope of this file but affects every doc example; the Lean API should accept `(n, m)`. |
| B13 | diffgeo.jl:40-45 | `getnabla` fails (`tangent(::Int,…)`), breaking `d`/`∂`/`curl`/`div`/`δ` on vector fields and `∇*s` | Redesign: implement `d`, `∂`, `curl`, `div` directly from gradient components (d of a vector field = `Σ ∂ᵢ ∧ Xᵢ` → antisymmetrized Jacobian; ∂ = trace). |
| B14 | diffgeo.jl:1059 | `firstformdiag(t, g = gradien(t))` typo | Fix. |
| B15 | diffgeo.jl:1073-1103 | `secondform(::ScalarField)` throws (`Real(::Chain)`) | Define via `graph(s)`. |
| B16 | diffgeo.jl:1188-1230 | `intrinsicframe` n≥3 and `intrinsicframediag` reference wrong args / undefined `g` | Implement n=2 only initially. |
| B17 | diffgeo.jl:681 | `_normalframe(t::PlaneCurve)` uses undefined `f` | Fix (`t`). |
| B18 | diffgeo.jl:461-466 | `indexintegral_slow`, `indexintegrate_slow`, `degreeintegrate_slow` call undefined `integral_slow`/`integrate_slow` | Drop or alias to non-slow. |
| B19 | grid.jl:1055-1065 | `psum` calls `sum!(…; dims)` (no such method) | Replace by plain axis sum. |
| B20 | grid.jl:1149-1151 | `metricvolume` fails for induced metric (`size(::Global)`) | Return all-ones for induced. |
| B21 | grid.jl:1384-1391, 1414-1420 | `integrate_haar` with scalar `z` (`.+=` on Float) and `layercake` (LocalTensor promotion) throw | Fix; `layercake` ignores `n`. |
| B22 | diffgeo.jl:213, 219 | exports `tangent_fast`, `gausseintrinsicnorm_slow` never defined | Omit. |
| B23 | diffgeo.jl:33 | generic `boundlog(z, lim)` uses undefined `s`, `T` | Fix to the non-real LocalTensor formula. |
| B24 | grid.jl:941-942, 987-988, 1033-1034 | `Val{1}/Val{2}` denominator helpers reference undefined `dt` | Dead code; omit. |

### 8.7 Julia-specific pieces to skip or redesign

* `@threads`, `@nthreads` macro (`grid.jl:613-632`, including the VERSION<1.13 `_nloops` shim) → plain loops (+ optional Tasks).
* `@generated`/`@eval` code generation over `N ∈ 2:5`, `J ∈ 1:N` (`grid.jl:634-771, 1057-1074, 1179-1224, 1237-1377`; `diffgeo.jl:71-97, 612-769, 1237-1272`) → generic loops over `Fin N`; keep the *order* of operations/axis reductions.
* `select1`/`select2`/`gentrapz*`/`gencat` expression builders → array slicing helpers (`sliceAt axis k`).
* `Ref(metric)` broadcasting and `refmetric` → pass `Metric` explicitly; specialize the induced (Euclidean) case.
* `ArrayFunction`, `indefintegrate*` (lazy `Limit` sequences from AbstractAnalysis) → skip.
* `Nabla`/`Derivation` symbolic algebra (`getnabla`) → skip; see B13.
* `PrincipalFiber` "action" dispatch zoo → a small explicit API: `pullbackIntegrate (γ) (f : Point → α)` using `|det J|` for scalar integrands and `J·f` for vector integrands, `fluxIntegrate`.
* Makie-oriented helpers (`ribbon` for plots, `unit*` generators) → keep generators (LeanPlot will want them), they're pure data.

### 8.8 Suggested Lean module decomposition (rough LOC)

| Module | Contents | LOC |
|---|---|---|
| `Cartan/Grid/Axis.lean` | `Axis`, `searchpoints`, range fast path | 120 |
| `Cartan/Grid/Topology.lean` | `Face` kinds from `QuotientTopology` (p,q,r), 1-D subtopology, neighbour remap (§4.2) incl. transverse perms | 250 |
| `Cartan/Grid/Field.lean` | `Grid N`, `Field N α` (SoA/FloatArray), strides, column-major indexing, slicing, map/zip, `fiberproduct` | 300 |
| `Cartan/Grid/Stencil.lean` | slow/fast/back/forw kernels, all boundary branches (§4.3-4.5), analytic denominators, compat flags B2 | 450 |
| `Cartan/Grid/Gradient.lean` | `centraldiff*`, `gradient*` (full, per-axis, metric), `unitgradient`, `derivative` (Wirtinger), `laplacian` | 300 |
| `Cartan/Grid/DiffMatrix.lean` | `Tridiagonal` FD{-1,0,1}, SD{1}, identity | 100 |
| `Cartan/Grid/Interp.lean` | `linterp`…`quintlinterp` (generic N), reposition, `leaf`, `hat`, `heaviside` | 300 |
| `Cartan/Grid/Quadrature.lean` | `trapz`/`cumtrapz` (1-D uniform/general, N-D, per-axis), `trapzweights`, Riesz sums, Gauss–Legendre (needs a symmetric tridiagonal eigensolver), CC weights hook, metricfiber | 450 |
| `Cartan/Grid/Arc.lean` | arcsteps, arclength, arctime, arcsample/arcresample | 120 |
| `Cartan/DiffGeo/Curves.lean` | speed … bishop, curvatures, frames (k=2,3 + generic k), cartan, frenet, evolute/involute, planecurve, winding | 550 |
| `Cartan/DiffGeo/Surfaces.lean` | tangent/normal/unitnormal/normalnorm/jacobian/weingarten, sectordet/sector integrals, fundamental forms, shape, curvatures, Gauss K_e/K_i, surfacearea, surface frames | 500 |
| `Cartan/DiffGeo/Metric.lean` | intrinsicmetric(diag), Christoffel 1st/2nd kind, geodesic RHS, applymetric/metricscale | 250 |
| `Cartan/DiffGeo/Exterior.lean` | d/∂/curl/div from gradients, `action`, Lie bracket, Connection/CovariantDerivative | 200 |
| `Cartan/DiffGeo/Pullback.lean` | pullback & flux integrals, degree/index integrals, transport/retract | 200 |
| `Cartan/DiffGeo/Generators.lean` | unitcircle/helix/sphere/disk/ball/pipe/cylinder/cone/conoid, revolve*, sectorize/cylinderize, ruled/lined/scroll/tangent surfaces, ribbon, link/linknumber | 350 |
| `Cartan/DiffGeo/Misc.lean` | ballvolume/spherearea/radii, bound*, q-analogs, richardson, beta | 120 |
| `Cartan/Grid/Proofs.lean` | §8.4 theorems over ℚ | 300 |
| `Cartan/Tests/DiffGeoOracle.lean` | JSON golden loader + comparisons | 350 |
| **Total** | | **≈ 5,200** |

---

## 9. Oracle test plan

The ready-made dumper `…/scratchpad/diffgeo_probe/oracle_diffgeo.jl` already emits 117 goldens (keys listed in the file) as JSON: 1-D stencils for all four variants on Open/Torus/Mirror/Clamped topologies and a non-uniform grid, raw `centraldiff` numerators, 2-D open/torus and 3-D gradients, per-axis gradients, Laplacian, all quadratures (1-D/2-D, per-axis, Riesz, GL, trapezoid weights), the full curve suite on a helix and an ellipse, `planecurve`, the full surface suite on a 13×17 torus, Christoffel symbols, interpolation, `hat`, `heaviside`, `ballvolume`, `spherearea`, `richardson`, Tridiagonal matrices, `unitcircle`, `unitsphere`, `linknumber`. Encoding: `Dict("size"=>…, "data"=>column-major list)` for fields; Chains → component lists (recursively for Chains of Chains); `TensorOperator` → list of columns; `Single` → its scalar.

Extend it along these axes (input distributions):

1. **Stencil exactness sweep** (per variant × topology): uniform grids `n ∈ {4,5,6,7,9,16,33,61}`, `h = 10^u` with `u ~ U[-3, 0]`, offset `x₀ ~ U[-5,5]`; fields = random polynomials of degree 0..5 with coefficients `~ N(0,1)`; periodic axes with random trig polynomials `Σ_{k≤3} a_k cos(kθ) + b_k sin(kθ)` on `LinRange(0,2π,n)` (and on shifted periods `LinRange(-π,π,n)` to exercise the jump correction). Dump `S(f)`, `S(x)`, `D(f)`. Expected tolerance: bit-identical (compare with `≤ 2 ulp` to allow FMA differences), since the operation order is specified.
2. **Non-uniform grids**: sorted `x = cumsum(U[0.05,1])`, n ∈ {4..20}; only for parity (semantics are "wrong" by design).
3. **N-D gradients**: 2-D/3-D grids of sizes `(n₁,n₂[,n₃])` with each `nᵢ ∈ {4,5,7,9}`, topologies Open, Torus, Cylinder, Möbius, Klein, Sphere, Mirror, Clamped, Cone (construct via `XParameter(LinRange…, LinRange…)` because of B12); scalar and 3-vector fibers. Dump full gradient and per-axis gradients.
4. **Interpolation**: for each grid above, 200 query points `~ U` over `[x₁ - 0.5L, xₙ + 0.5L]` per axis (in-range, out-of-range, exactly-on-node incl. first/last node, NaN). Tolerance 1e-15 relative.
5. **Quadrature**: same fields; `integrate`, `integral`, per-axis variants, `integral_riesz`, `integrate_gausslegendre` (tolerance 1e-13 because of LAPACK eigen), trapz weights; N-D aligned vs general code paths (ranges vs `collect`ed vectors on the same nodes must agree up to rounding — a cross-check the Lean port can assert).
6. **Curves**: helices `(a cos t, a sin t, c t)` with `a ~ U[0.5,2]`, `c ~ U[-1,1]`; ellipses `(a cos t, b sin t)`; random Fourier space curves (5 modes); closed curves on `TorusParameter(n)` (periodic stencils) and open ones on `0:h:T`; sample sizes 16..512. Dump every function of §2.12 (skip `_slow`); `bishop*` only on constant-speed curves for semantic tests, all curves for parity.
7. **Surfaces**: torus (R ~ U[1.5,3], r ~ U[0.2,0.8]), sphere (via `unitsphere(n,m)` and `SphereParameter(ranges)`), graphs of random quadratics/cubics on open grids, the docs' "wiggle" torus; sizes 13×17 … 60×60. Dump §2.11/§2.14 functions incl. `secondkind(surfacemetric(·))`, `thirdform`, `surfacearea`, `sectorintegrate`, Gauss–Bonnet integral (≈ 0 for tori — also a Lean-side property test).
8. **Generators**: `unitcircle(n)`, `unithelix(n)`, `unitsphere(n,m)`, `unitdisk`, `unitball`, `unitpipe`, `unitcone`, `revolve` of random profiles, `ruledsurface`, `link`, `linknumber` of Hopf-linked circles (expect ≈ ±1) and unlinked (≈ 0).
9. **Misc**: `ballvolume(1:12)`, `spherearea(1:12)`, `richardson(1:6)`, `qbinomial(n,k,q)` for n ≤ 8, `bound*` on random reals incl. ±∞, NaN.
10. Every BUG from §8.6 gets a dedicated golden key suffixed `_BUGGY` so the Lean port can run in `juliaCompat := true` mode for parity and `false` mode for the fixed semantics (with separate analytic expectations).

Tolerance policy: pure stencil/quadrature outputs — ≤ 2 ulp; composite geometry (frames, curvature, shape) — relative 1e-12 (sqrt/division chains); eigen-based (`GaussLegendre`, `principals`, `principalaxes`) — 1e-12 absolute with sign normalization of eigenvectors.
