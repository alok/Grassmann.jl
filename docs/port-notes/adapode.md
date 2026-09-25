# Adapode.jl → Lean 4 porting spec

Source: `/Users/alokbeniwal/chakravala/Adapode.jl` master @ `91e8516` ("split element.jl with grid.jl"), `Project.toml` version **0.3.14** (`Project.toml:4`).
All `file:line` citations refer to that checkout unless prefixed with another package name.

What was run: every claim tagged **[verified]** was executed in Julia 1.13, using the registered Grassmann 0.8.46, Cartan 0.4.16, MeshTopology 0.1.0 and AbstractAnalysis 0.2.2 from the juliaenv, with Adapode **master** loaded by `include` on its source.
The registered Adapode 0.3.13 in that env is older. It has no `grid.jl` and no `Flow`/`FlowIntegral`/`LieGroup` API, so an oracle must not rely on it (see §9).

Where the oracle scripts and goldens are:
- Scripts: `/private/tmp/claude-502/-Users-alokbeniwal-Grassmann/c6cc2308-bfca-4b9a-ad33-d89b110132a8/scratchpad/notes/adapode_oracle/`. The files are `load.jl`, `loadfft.jl`, `patch.jl`, `patch2.jl`, `mesh2d.jl`, `oracle_core.jl`, `oracle_spectral.jl`, `oracle_chaos.jl`, `bench.jl`, `plots1.jl` and `plots2.jl`.
- Goldens (already generated) are in `.../adapode_oracle/goldens/*.json`.
- Reference plots (CairoMakie) are in `.../adapode_oracle/plots/*.png`.

---

## 1. Purpose and scope

Adapode ("adaptive P/ODE") is the numerics layer on top of Cartan.jl (fiber bundles, meshes, `TensorField`) and Grassmann.jl (`Chain`, `TensorOperator`, `Values`) (`README.md:18-30`). It has four parts:

1. **ODE time stepping** on arbitrary vector-space-like states. A state can be a Grassmann `Chain`, a `Chain` of `Chain`s (for geodesics), or a whole `TensorField` (for flowing curves and fields). The methods are:
   - Euler/Heun and explicit Runge–Kutta of orders 1–4;
   - five embedded adaptive RK pairs;
   - Adams–Bashforth–Moulton PECE of orders 1–5, fixed-step and adaptive;
   - leapfrog/Störmer–Verlet;
   - a geodesic-equation wrapper.

   Code: `src/Adapode.jl`, `src/constants.jl`.
2. **P1 simplicial FEM assembly and solvers**: mass, stiffness, convection, streamline diffusion, Robin, divergence and load. The solvers cover Poisson, transport, transport-diffusion, heat (backward Euler), wave (Crank–Nicolson), bistable reaction–diffusion (Picard and Newton), nonlinear Poisson (Newton), plane-strain elasticity, Stokes (Crouzeix–Raviart/P0), Navier–Stokes (Chorin projection, currently broken), 2D Maxwell with Nédélec edge elements, symmetric-interior-penalty DG Poisson, P2 isoparametric mass/stiffness, and 1D adaptive refinement. Code: `src/element.jl`.
3. **Spectral solvers** on product grids, in `src/grid.jl` and `ext/FFTWExt.jl`:
   - Fourier/DCT/DST multiplier solutions of the heat, wave, rest-wave, biharmonic, Riesz and Schrödinger equations;
   - Chebyshev collocation for Helmholtz, biharmonic, Orr–Sommerfeld and polar Laplacian problems;
   - Dirichlet reshaping helpers.
4. **Plot glue** (`ext/MakieExt.jl`): streamlines of flows from seed points, and curves advected by a flow.

Explicitly out of scope, because it belongs to Cartan, Grassmann, MeshTopology or AbstractAnalysis: mesh generation, `TensorField`/bundle types, `volumes`/`gradienthat`/`means`, Chebyshev differentiation matrices, FFT frequency grids, the `orbit`/`Limit` iteration machinery, and plotting of `TensorField`s. §7 lists exactly which symbols Adapode uses and the semantics it relies on.

---

## 2. Public API inventory

`names(Adapode)` returns 169 exported symbols plus the module name **[verified]**.
Ten of them are **exported but undefined**, and a port should drop them. They are `AbstractFiber`, `ElementFunction`, `MeshFunction`, `pdegrad`, `detsimplex`, `residual` (Cartan re-exports that no longer resolve), and `assemblefunction`, `assemblemassfunction`, `assembletotalnodes`, `asssemblemasstotalnodes` (sic, triple "s").

### 2.1 Re-exports from Cartan, Grassmann and AbstractAnalysis (`src/Adapode.jl:28-38`)

`Values, odesolve, odesolve2, initmesh, pdegrad, ElementFunction, IntervalMap, PlaneCurve, SpaceCurve, SurfaceGrid, ScalarGrid, TensorField, ScalarField, VectorField, BivectorField, TrivectorField, RealFunction, ComplexMap, SpinorField, CliffordField, MeshFunction, GradedField, QuaternionField, LocalTensor, FiberBundle, AbstractFiber, base, fiber, domain, codomain, ↦, →, ←, ↤, basetype, fibertype, ProductSpace, RealRegion, Interval, Rectangle, Hyperrectangle, ⧺, ⊕, Limit, orbit, orbithold, orbiterror, residual, supnorm`

Of these, only `odesolve` and `odesolve2` are Adapode's own. The Lean `Adapode` namespace should re-export the Cartan-port equivalents. There is no ASCII alias for `↦`: `t ↦ x` builds `LocalTensor(t, x)`, which is a (base point, fiber value) pair.

### 2.2 ODE integrator types (`src/Adapode.jl:44-137`)

| Symbol | Kind / signature | Semantics | Line |
|---|---|---|---|
| `AbstractIntegrator` | abstract type | root | 48 |
| `StepIntegrator <: AbstractIntegrator` | abstract | fixed step | 49 |
| `AdaptiveIntegrator <: AbstractIntegrator` | abstract | adaptive | 50 |
| `integrator` | `const integrator = AbstractIntegrator`, **also** a function `integrator(::Flow)` / `integrator(::FlowIntegral)` / `integrator(::InitialCondition)` / `integrator(::LeapCondition)` | alias plus accessor | 52, 158, 191, 219, 645 |
| `EulerHeunIntegrator` | struct `(tol::Float64, skip::Int, geo::Bool)` | Heun (improved Euler) | 54-58 |
| `ExplicitIntegrator{o}` | struct `(tol, skip, geo)`, `o ∈ 1:4` | explicit RK `CB[o]` | 60-64 |
| `ExplicitAdaptor{o}` | struct `(tol, skip, geo)`, `o ∈ 1:5` | embedded RK `CBA[o]` | 66-70 |
| `MultistepIntegrator{o}` | struct `(tol, skip, geo)`, `o ∈ 1:5` | ABM-o PECE | 72-76 |
| `MultistepAdaptor{o}` | struct `(tol, skip, geo)`, `o ∈ 1:5` | adaptive ABM-o | 78-82 |
| `LeapIntegrator{o}` | struct `(skip::Int)`, `o ∈ {1,2}`. Not a subtype of Step/Adaptive; exported at line 624 | leapfrog | 84-86, 104 |
| `AbstractIntegrator(tol=15, int=ExplicitIntegrator{4}) = int(tol)` | **broken**: the default is a *type* annotated `::AbstractIntegrator`, so the zero-argument call throws | – | 88 |
| `AbstractIntegrator(tol, m, o=4)` | maps m to an integrator: 0 → EulerHeun(tol), 1 → Explicit{o}, 2 → ExplicitAdaptor{o}, 3 → Multistep{o}, 4 → MultistepAdaptor{o} (other m give `nothing`) | factory | 89-102 |
| constructors | `X{o}(tol, skip=1) = X{o}(tol, skip, false)`; `X{o}(tol::Int, skip::Int=1, geo=false) = X{o}(2.0^-tol, skip, geo)`. EulerHeun has the same pattern (105-106). `LeapIntegrator{o}() = LeapIntegrator{o}(1)` | **An Int `tol` is an exponent: the step is h = 2^-tol. A Float `tol` is the step itself.** | 105-112 |

Field meanings:
- `tol` is the *initial step size h*, not an error tolerance. It also sets `hmax` and the error window (§4.3).
- `skip`: 0 means return only the final `LocalTensor` (no trajectory is allocated); 1 means return the full trajectory; k>1 means store every k-th step.
- `geo` is never read anywhere. Drop it.

### 2.3 Time-step controller (`src/Adapode.jl:114-137`) — not exported, but load-bearing

`mutable struct TimeStep{T}` has fields `h, skip, hmin, hmax, emin, emax, e, i::Int, s::Int`.

The constructor is `TimeStep(h, skip=1, hmin=1e-16, hmax = h>1e-4 ? h : 1e-4, emin=10^(log2(h)-3), emax=10^log2(h))`. It initialises `e=(emin+emax)/2, i=1, s=0` and then runs `checkstep!` (124-125). `TimeStep(I) = TimeStep(I.tol, I.skip)` (128), and `Base.step(t) = t.h` (130).

`checkstep!` (132-137) does three things:
- clamps `|h|` to `[hmin, hmax]` with `copysign`;
- sets `i<1 ⇒ i=1`.

Verified values **[verified]**:

| h | h | hmin | hmax | emin | emax | e |
|---|---|---|---|---|---|---|
| 2^-7 | 0.0078125 | 1e-16 | 0.0078125 | 1.0e-10 | 1.0000000000000001e-7 | 5.005e-8 |
| 2^-15 | 3.0517578125e-5 | 1e-16 | 1e-4 | 9.999999999999999e-19 | 1e-15 | 5.005e-16 |
| 1e-5 | 1e-5 | 1e-16 | 1e-4 | 2.4567418588589852e-20 | 2.4567418588589855e-17 | 1.2295993003589222e-17 |

### 2.4 Flows and initial conditions (`src/Adapode.jl:139-220, 609-646`)

**Types and accessors**

| Symbol | Signature | Semantics | Line |
|---|---|---|---|
| `LieGroup{F}` | abstract | – | 141 |
| `Flow{F,N} <: LieGroup{F}` | fields `f::F` (system), `t::Float64` (duration). N=1 means exact system `f(x)`; N=2 means `FlowApprox`, where the system is called `f(x,h)` | – | 143-148 |
| `FlowApprox{F} = Flow{F,2}` | `FlowApprox(f, t::Float64)` | – | 150-151 |
| `Flow(f::Flow)=f`, `Flow(f)=Flow(f,2π)`, `Flow(f,t::Real)=Flow(f,float(t))` | – | default duration 2π | 153-155 |
| `system(Φ)`, `duration(Φ)` | accessors (not exported) | – | 156-157 |
| `integrator(::Flow) = ExplicitIntegrator{4}(2^-11, 0)` | – | RK4, h=2^-11, final state only | 158 |
| `Base.exp(X::TensorField{B,<:Chain{V,1}}) = Flow(X, 1.0)` | – | exponential map of a vector field | 159 |
| `FlowIntegral{F,I,N}` | fields `Φ::Flow`, `i::I`; `FlowIntegral(Φ, i=integrator(Φ))` | – | 179-183 |
| `FlowIntegral(f, tmax, i=ExplicitIntegrator{4}(2^-11))` (skip=1, full trajectory); `FlowIntegral(f)` gives tmax=2π | – | – | 185-186 |
| `InitialCondition{L,X}` | fields `Φ::L`, `x0::X`. The inner constructor stores `_init(x0)`: a `LocalTensor` is multiplied by `one(1.0)`, anything else is kept as is | – | 205-209, 471-476 |
| `IC` | `const IC = InitialCondition` | – | 211 |
| `InitialCondition(f, x0, tmax) = IC(Flow(f,tmax), x0)`; `IC(f,x0)` gives tmax=2π | – | – | 212-213 |
| accessors | `LieGroup(ic)`, `system(ic)`, `duration(ic)`, `parameter(ic)=ic.x0`, `integrator(ic)` | – | 215-219 |
| `(I::AbstractIntegrator)(ic)` | `= odesolve(ic, I)` | – | 220 |

**Call forms of a `Flow` or `FlowIntegral`**
- `(Φ::Flow)(x0, i=MultistepIntegrator{4}(2^-11,0))` computes `odesolve(IC(Φ,x0), i)`. The default here is **not** `integrator(Φ)`, and it hits bug B3 (§8.6).
- `(Φ::Flow)(x0::LocalTensor, i=integrator(Φ))` computes `Flow(system(Φ), duration(Φ)+base(x0))(fiber(x0), i)`. It integrates from 0 to t0+T, not from t0 to t0+T (bug B5).
- `(Φ::Flow)(x0, n::Int, i)` iterates the flow n−1 times and returns `Vector` of `localfiber`s. The loop variable `i` shadows the integrator argument, so the default integrator is always used (bug B6).
- `(Φ::Flow)(x0::TensorField, i)` flows a whole field: it builds the system `t -> TensorField(base(fiber(t)), Φ.f.(fiber(fiber(t))))` and solves with state = `TensorField`.
- `(Φ::FlowIntegral)(x0)` is `Flow(Φ)(x0, integrator(Φ))`.
- `(Φ::FlowIntegral)(x0::Vector{<:Chain})` always throws: it has a `typoef` typo and an undefined `n`.

(Flow call lines: 161, 162, 164-171, 173-177. FlowIntegral call lines: 193, 195-203.)

**Geodesics and leapfrog**

| Symbol | Signature | Semantics | Line |
|---|---|---|---|
| `geodesic` | `geodesic(Γ, x0v0)`, `geodesic(Γ, x0v0, tmax)`, `geodesic(Γ, x0, v0)` (tmax=2π), `geodesic(Γ, x0, v0, tmax)`. Each builds `InitialCondition(geodesic(Γ), Chain(x0,v0), tmax)`. `geodesic(Γ)` itself is Cartan's system `x -> geodesic(x,Γ)` (§4.6) | extends `Cartan.geodesic` | 611-614 |
| `Geodesic`, `GeodesicCondition` | `const Geodesic, GeodesicCondition = geodesic, geodesic, geodesic`; both alias `geodesic` | – | 615 |
| `geosolve` | `geosolve(ic, i, bc)`; `geosolve(ic, i=integrator(ic))`; `geosolve(Γ, x0, v0, tmax, tol, m, o=4)`; `geosolve(Γ, x0, v0, tmax=2π, tol=15, M=Val(1), B=Val(4))`. Returns `getindex.(odesolve(...), 1)`, i.e. the positions only | – | 617-622 |
| `LeapCondition{L,X,Y}` | fields `Φ, x0` (previous state), `x1` (current state) | – | 626-631 |
| `LeapCondition` ctors | `(f, x0::LocalTensor, x1, tmax)` puts x1 at time `zero(point(x0))`. `(f, x0, x1::LocalTensor, tmax)` puts x0 at time 0. `(f, x0::LT, x1::LT, tmax)` keeps both times. `(f, x0, x1, dt, tmax)` puts x0 at −dt and x1 at 0. `(f, x0, x1, dt)` gives tmax=2π | – | 633-637 |
| `leap(ic)` | returns `ic.x1`. `step(ic) = point(x1) - point(x0)` | – | 643-644 |
| `(I::AbstractIntegrator)(ic::LeapCondition)` | `= odesolve(ic, I)` | – | 646 |

### 2.5 Solve entry points (`src/Adapode.jl:478-591, 655-675`)

| Signature | Meaning | Line |
|---|---|---|
| `odesolve(ic::InitialCondition)` | uses `integrator(ic)`, which comes from the Flow and is **ExplicitIntegrator{4}(2^-11, 0)** | 478 |
| `odesolve(f, x0, tmax, tol, m, o=4)` | Int m and o are wrapped in `Val` | 479 |
| `odesolve(f, x0, tmax=2π, tol=15, M=Val(1), B=Val(4))` | `odesolve(IC(f,x0,tmax), AbstractIntegrator(tol,M,B))`. **Default: RK4, h=2^-15, T=2π, full trajectory** | 480-482 |
| `odesolve(ic, ::EulerHeunIntegrator, bc=identity)` | | 483-490 |
| `odesolve(ic, ::ExplicitIntegrator{o}, bc=identity)` | skip 0, 1 or k | 491-520 |
| `odesolve(ic, ::ExplicitAdaptor{o})` | no `bc` | 521-528 |
| `odesolve(ic, ::MultistepIntegrator{o}, bc=identity)` | skip 0, 1 or k | 529-562 |
| `odesolve(ic, ::MultistepAdaptor{o})` | | 563-571 |
| `odesolve(ic::LeapCondition, ::LeapIntegrator, bc=identity)` | | 655-675 |
| `odesolve2(...)` | Variant ABM using AB_{o−1} as predictor. It is **buggy** (§8.6 B9). For the non-multistep integrators it falls through to `odesolve` | 576-591 |
| `integrate(f::TensorField, x, tmax, tol, M, B)` | Not exported, legacy. Supports m=0 (Heun) and m=3 (ABM) only | 593-607 |

Return shape:
- full trajectory: a `TensorField` over the time grid, or over `base(x0) × time` when x0 is itself a field;
- skip=0: a `LocalTensor(t_final ↦ x_final)`;
- adaptive: a `TensorField` over a non-uniform `Vector{Float64}` of times.

### 2.6 FEM API (`src/element.jl`)

Throughout this table, "t" is a `SimplexBundle` (points plus P1 simplex topology) and "e" is a boundary bundle.

**Geometry helpers and local matrices**

| Symbol | Signature | Semantics | Line |
|---|---|---|---|
| `trilength` | `trilength(t::ElementBundle)`; `trilength(rc)` | per-triangle edge lengths `Values{3}`, edge j opposite vertex j | 35-36 |
| `trinormals` | `trinormals(t) -> (ds, dn)` | `ds[k]` = edge lengths; `dn[k][j]` = outward unit normal of edge j (opposite vertex j) | 37-43 |
| `gradientCR` | `gradientCR(t, m)`, `(g::TensorField)`, `(g::TensorOperator)`, `(g::Chain)` | Crouzeix–Raviart basis gradients ∇ψ_j = −∇φ_j + Σ_{i≠j} ∇φ_i = −2∇φ_j | 45-53 |
| `mass(a, b, ::Val{N})` | not exported | P1 element mass matrix per unit volume (§4.8) | 81 |
| `stiffness(c, g, ::Val{N})` | not exported | c ∇φ_i·∇φ_j | 84-85 |
| `convection(b, g, ::Val{N})` | not exported | C_ij = (b/N)·∇φ_j | 102 |
| `SD(b, g, ::Val)` | not exported | (b·∇φ_i)(b·∇φ_j) | 106 |

**Global assembly**

| Symbol | Signature | Semantics | Line |
|---|---|---|---|
| `assembleglobal` | `assembleglobal(M, t::SimplexBundle, m=volumes(t), c=1, g=0)`; `(M, t::ImmersedTopology{N}, m, c, g)` | `A = Σ_k scatter(M(c[k], g[k], Val(N)) * m[k])` | 55-63 |
| `assemblemassincidence` | `(t::SimplexBundle, f, m=volumes, l=m)`; `(t::ImmersedTopology, f, m, l)` | returns `(M, b)`: M = Σ_k m[k]·mass, and `b[t_k] += f[t_k]*l[k]` | 65-75 |
| `assemblemassload` | `(t, f, m=volumes(t), l=m)`; `(tf::TensorField, m, l)` | `assemblemassincidence(t, f(nodes)/sdims(t), m, l)` gives a lumped load | 77-78 |
| `assemblemass` | `assemblemass(t, m=volumes(t))` | global mass. **BoundsError whenever #elements > #nodes** (bug B13) [verified] | 82 |
| `assemblestiffness` | `(t, c=1, m=volumes(t), g=gradienthat(t,m))`; a SimplexBundle overload | Σ c_k m_k ∇φ_i·∇φ_j. `c` may be a Real, a per-element vector, or a function (evaluated at element barycentres) | 86-87 |
| `assembleconvection` | `(t, b, m=volumes(t), g=gradienthat(t,m))` | Σ m_k (b_k·∇φ_j)/N at (i,j). `b` is a per-element vector (or `Global` constant) of Chains in the gradient manifold ↓V | 103 |
| `assembleSD` | `(t, b, m, g)` | Σ m_k (b_k·∇φ_i)(b_k·∇φ_j) | 107 |
| `assembledivergence` | `(t2e, m, g) -> (D1, D2)` | nt×ne sparse; `D1[k, edges_k] = m_k·g_k[·]_x` and `D2` likewise for y | 109-118 |
| `assemble` | `assemble(t, c=1, a=1, f=0, m=volumes, g=gradienthat)` | returns `(A, M, b)`: A = stiffness(c), M = mass weighted by a (a=1 plain, else a.*m), b = lumped load of f | 120-123 |
| `assemblerobin` | `(eκ::TensorField)`; `(e, κ=1e6)`; `(e, κ, gD, gN=0)` | returns `(R, r)` (§4.8) | 125-133 |

**Solvers**

| Symbol | Signature | Semantics | Line |
|---|---|---|---|
| `solvepoisson` | `(t, e, c, f, κ, gD=0, gN=0)` | `TensorField(t, (A+R)\(b+r))` | 135-141 |
| `poisson` | `(t, e, c, a, f)`, not exported | homogeneous-Dirichlet reaction–diffusion | 143-147 |
| `solvetransportdiffusion` | `(tf, eκ, c, δ, gD=0, gN=0)` | `(A+R−Cᵀ+Sd)\r` (§4.9) | 149-159 |
| `solvetransport` | `(t, e, c, f=1, ϵ=0.1)` | `solvedirichlet(ϵA+C, b, e)` | 161-168 |
| `adaptpoisson` | `(g, pt, pe, c=1, a=0, f=1, κ=1e6, gD=0, gN=0)` | 1D adaptive refinement loop. κ, gD and gN are **unused** | 170-183 |
| `solveheat` | `(ic, f, κ, T)` | backward Euler via `orbit` | 185-190 |
| `solvewave` | `(pt, bc)` | Crank–Nicolson wave equation | 192-208 |
| `assemblestokes` | `(pt, ν=0.1, t2e=edgesindices(pt))` | CR–P0 saddle matrix with mean-pressure multiplier | 210-220 |
| `solvestokes` | `(pt, bc, ν=0.1, t2e=edgesindices(pt, base(bc)))` | returns `(velocity at nodes, pressure per element)` | 222-231 |
| `solvenavierstokes` | `(pt, pe, inbc, outbc, ν=0.001, T=range(0,1,101), skip=1)` | **broken**: `k` is undefined and `UVold` is never updated (bug B15) | 233-291 |
| `assembleelastic` | `(f, μ, λ) -> (K, M, F)` | plane strain. **Three bugs** (B11) [verified] | 293-314 |
| `solveelastic` | `(f, e, E=1, ν=0.3)` | clamped boundary; returns a nodal displacement Chain field | 316-321 |
| `assemblemaxwell` | `(p, e, t, κ, μ, fhat, t2e=edgesindices(p(t)), signs=facetsigns(t))` | complex Nédélec system | 323-337 |
| `solvemaxwell` | `(κ, bc, μ=1, fhat=Chain(0,0))` | returns `(Re E, Im E)` interpolated to nodes | 339-348 |
| `assemblejacobianresidue` | `(f, pe, u, Afcn, m, g, tiny=1e-8)`, not exported | Newton J and r for −∇·(a(u)∇u)=f | 350-376 |
| `solvenonlinearpoisson` | `(f, pe, Afcn)` | 5 Newton iterations, printing `\|d\|=…, \|r\|=…` | 378-390 |
| `solvebistable` | `(ic, ϵ=0.01, T=StepRangeLen(0,0.1,101), f=u->u-u^3)` | semi-implicit Euler with 3 Picard iterations | 392-398 |
| `solvebistable_newton` | `(ic, ϵ, T, f, df=u->1-3u^2)` | 3 Newton iterations per step | 414-431 |
| `gradienthat(ip::Simplex)` | `ip` is an already-inverted affine simplex | extends Cartan's function | 456-458 |
| `assembleDIPG` | `(pt, nbrs=neighbors(immersion(pt))) -> (P, S)` | DG penalty and flux matrices; needs a *discontinuous* P1 bundle | 460-507 |
| `solvepoissonDIPG` | `(f, c, β, α=-1)` | `(A − S + αSᵀ + βP)\b`. α=−1 is SIPG, +1 NIPG, 0 IIPG | 509-516 |

**Elasticity and Nédélec helpers**

| Symbol | Signature | Semantics | Line |
|---|---|---|---|
| `Eν2Lame(E, ν)` | not exported | returns `(μ, λ) = (E/(2(1+ν)), Eν/((1+ν)(1−2ν)))` | 518 |
| `elastic(μ, λ, Val(3))` | – | plane-strain D (3×3) | 520 |
| `strain(g, Val(3))` | – | 3×6 B matrix | 521-529 |
| `elasticstrain(μ, λ, g, Val(3))` | – | BᵀDB | 530-533 |
| `stress(μ, λ, dudx)` | – | 2μ ε + λ (div u) I | 656-660 |
| `maxwell(mμ, l, λ, g, Val(3))` | – | local Nédélec matrix | 535-544 |
| `_nedelec`, `nedelec` | – | local Nédélec mass matrix (λ-scaled) | 546-559 |
| `basisnedelec(p)` | – | reference Whitney basis at p | 561-567 |
| `interpnedelec`, `nedelecmean` | – | edge DOFs → element centroid field → nodes | 569-578 |
| `centroidvectors` | not exported | vectors from element centroid to its vertices | 580-591 |

**Error indicators**

| Symbol | Signature | Semantics | Line |
|---|---|---|---|
| `jumps` | `(t, c, a, f, u, m=volumes(t), g=gradienthat(t,m))` | a posteriori indicator per element. The 1D branch works; **the 2D branch is broken** in the current stack | 593-619 |
| `elementresiduals`, `edgeresiduals` | – | edgeresiduals is **broken**: it calls an unimported `gradient_2` and a default argument references `pt` before it exists | 621-654 |

**P1/P2 shapes and isoparametric assembly**

| Symbol | Signature | Semantics | Line |
|---|---|---|---|
| `shapeP1`, `gradientP1` | 1, 2 and 3 barycentric arguments, or a `Values` | P1 shapes and reference gradients | 664-687 |
| `shapeP2`, `gradientP2` | `(r, s)` | 6-node P2 shapes (§4.8) | 689-708 |
| `GaussShape`, `GaussGradient` | const | shapes and gradients pre-evaluated at `Gauss[2]` (P1) and `Gauss[4]` (P2) points | 710-711 |
| `isoparametric(xy, dS)` | – | returns `(J⁻¹·dS, det J)` | 713-716 |
| `volumePN`, `volumesPN` | – | `det(dS·xyᵀ)` | 718-721 |
| `assemblemassPN(pt, N)`, `assemblemassP1/P2` | – | quadrature mass. P1 matches `assemblemass` [verified]; **P2 throws** in the current Grassmann (`_vecdot` MethodError) | 725-748 |
| `assemblestiffnessPN(pt, N)`, `assemblestiffnessP1/P2` | – | same situation as the mass versions | 750-772 |
| `LagrangeP2(t::SimplexTopology)` | – | P2 topology: vertices followed by edge nodes numbered `nodes(t) + edgeindex` | 774-779 |
| `shapemultilinear`, `gradientmultilinear` | not exported | Q1 shapes on [−1,1]^d. The `Values...` forwarder recurses forever, and **the gradients lack the 1/2^d factor** | 781-832 |

**Re-exported from Cartan and MeshTopology via element.jl exports** (`element.jl:15-25`): `assembleload, edges, edgesindices, neighbors, gradienthat, gradient, interp, submesh, iterable, callable, value, laplacian, interior, incidence, degrees`.

### 2.7 Grid, spectral and Chebyshev API (`src/grid.jl`, `ext/FFTWExt.jl`)

**Dirichlet helpers and Chebyshev collocation**

| Symbol | Signature | Semantics | Line |
|---|---|---|---|
| `dirichlet!(u)` | for arrays of rank 1–5 | zero every boundary hyperface in place; returns u | grid 19-48 |
| `solvedirichlet(A, b, fixed, boundary)` | – | ξ[fixed]=boundary; ξ[free] = A[free,free] \ (b[free] − A[free,fixed]·boundary) | grid 54-60 |
| `solvedirichlet(M, b, fixed)` | – | homogeneous version | grid 61-66 |
| `solvedirichlet(M, b, e::SimplexBundle / SimplexTopology [, u])` | – | fixed = vertices(e) | grid 50-53 |
| `solvedirichlet(L, f::AbstractArray{T,1..5})` | – | Chebyshev interior solve with zero boundary padding | grid 108-127 |
| `reshapedirichlet(f, u)` | rank 1–5 | zero-pad the interior vector u back to size(f), wrapped as a TensorField like f | grid 71-100 |
| `reshapepolardirichlet(f::AbstractMatrix, u)` | – | `[zeros(1,M); reshape(u,N−1,M−1)[:, vcat(M−1, 1:M−1)]]` | grid 102-106 |
| `solvepolardirichlet(L, f)` | – | the reshaped solution divided by its ∞-norm | grid 135-139 |
| `solveiteration(L, f, u, solver=\)` | – | Picard iteration `u ← solver(L, f.(u))` until ‖Δ‖∞ ≤ 5eps(); no iteration cap | grid 142-149 |
| `helmholtz(f::AbstractVector, k=0)` | – | `(D²)[2:N−1, 2:N−1] + k² I` | grid 151-154 |
| `helmholtz(f::AbstractMatrix, k=0)` | – | `kron(I, D2X) + kron(D2Y, I) + k² I` | grid 155-161 |
| `solvehelmholtz(f, k=0)` | – | `solvedirichlet(helmholtz(f,k), f)`, i.e. solves u″ + k²u = f with u=0 on the boundary | grid 163 |
| `solvenonlinearhelmholtz(f, k, N::Int)` and `(f, k, N, M)` | – | **broken**: calls the undefined `nonlinearhelmholtz` | grid 165-172 |
| `solvenonlinearhelmholtz(f, k, u::TensorField)` | – | `solveiteration(helmholtz(u,k), f, u, solvedirichlet)` | grid 173-175 |
| `polarlaplacian(N=13, M=21)` | – | polar Laplacian on the disk. **Sign bug** (B17) [verified] | grid 177-185 |
| `biharmonic(v::AbstractVector, D=ChebyshevMatrix(points(v)))` | – | Trefethen p38 operator. **Sign bug** (B17) | grid 187-192 |
| `biharmonic(v::AbstractMatrix)` | – | ∇⁴ = D4X ⊕ D4Y + 2·D2Y⊗D2X | grid 194-201 |
| `orrsommerfeld(v, R=5772)` | – | returns `(A, B)` for Orr–Sommerfeld A u = λ B u. **Sign bug** (B17) | grid 203-212 |

**Fourier multipliers.** All are non-exported except where marked (grid 214-222):
- `restwavemultiplier(k,t) = cos(t|k|)` (exported);
- `wavemultiplier(k,t) = sin(t|k|)/|k|` (exported);
- `heatmultiplier(k,t) = exp(−t|k|²)` (exported);
- `rieszmultiplier(k,t,s=2) = exp(−t(|k|²)^{s/2})` (exported);
- `biharmonicmultiplier(k,t) = exp(−t|k|⁴)` (exported);
- `schrodingermultiplier(k,t) = exp(−i t|k|²/2)`;
- `multiplierstep(mult,k,t) = (mult(k,t)−1)/t` (unused).

**Multiplier solvers**

| Symbol | Signature | Semantics | Line |
|---|---|---|---|
| `heatperiodic`, `rieszperiodic`, `biharmonicperiodic`, `restwaveperiodic` | `(u0, t [, s], k=rfftspace(points(u0)))` | `irfft(rfft(u0) .* mult.(k,t))` | grid 227-230 |
| `waveperiodic(u0, u1, t, k)` | – | `irfft(rfft(u0)·cos + rfft(u1)·wm)` with `wm[1]=0` (the mean of u1 is dropped) | grid 231-234 |
| `fullwaveperiodic(u0, u1, t, k)` | – | same, but `wm[1]=t` (mean drift is kept) | grid 235-238 |
| `schrodingerperiodic(u0, t, k=fftspace(points(u0)))` | also takes a time vector / TensorField | `ifft(fft(u0) .* exp(−i t\|k\|²/2))` | grid 239-250 |
| `heatneumann`, `rieszneumann`, `restwaveneumann` | FFTWExt | `idct(dct(u0) .* mult.(k,t))` with k=r2rspace | FFTWExt 24, 29, 44 |
| `waveneumann`, `fullwaveneumann` | FFTWExt | DCT analogue of waveperiodic. `fullwaveneumann` is **not imported** into Adapode, so it is unreachable from the Adapode namespace (bug B19) | FFTWExt 49-56 |
| `heatdirichlet`, `rieszdirichlet`, `restwavedirichlet` | FFTWExt | `r2r(r2r(u0, RODFT10)/Π(2 size) .* mult.(ω,t), RODFT01)` | FFTWExt 25-27, 30-32, 45-47 |
| `wavedirichlet(u0, u1, t, ω)` | FFTWExt | sum of the u0-cos and u1-sin/k DST solutions | FFTWExt 57-61 |
| Time-series overloads | `t::AbstractVector` or `t::TensorField` for heat/restwave/biharmonic × {neumann, periodic} (grid 256-282), wave/fullwave × {neumann, periodic} (grid 284-309), riesz{neumann, periodic} (grid 311-330), and `*dirichlet` for heat/restwave/biharmonic/riesz/wave (FFTWExt 33-42, 62-87) | output shape `(size(u0)..., length(t))`. Slice 1 is **u0 itself**; slice i is the solution at t[i] | – |
| `biharmonicneumann`, `biharmonicdirichlet` (scalar t) | – | **undefined**; only their series stubs exist (bug B19) | – |

### 2.8 Plot glue (`ext/MakieExt.jl:19-80`)

The same method set is generated for `lines/lines!` and `Cartan.graylines/graylines!`:
- `lines(X::Function|VectorField, xi::Vector{<:Chain}, t=1; args...)` calls `lines(FlowIntegral(X,t), xi)`. It draws the trajectory from `xi[1]`, calls `display`, then draws the other seeds with `lines!`. Trajectories use RK4 at h=2^-11 over [0,t].
- `lines(X::Function|VectorField, c::AbstractCurve, n=7)` calls `lines(Flow(X,0.2), c, n)`. It draws the curve c, then applies `ϕt = ϕ(ϕt)` n times (each application is RK4 at h=2^-11, skip=0, over 0.2 time units) and calls `lines!(fiber(ϕt))`. The effect is the curve advected to t = 0.2, 0.4, …, 1.4.
- `lines(X, c::Components, n=7)` loops over the components.

---

## 3. Data representations

### 3.1 ODE states and trajectories

- **State.** A state is any type with `+`, scalar `*` and `/`, and elementwise `abs.(value(·))` plus `maximum` (for error norms). In practice:
  - `Chain{V,1,Float64,n}`: a fixed-length vector whose length is a type parameter;
  - `Chain(x, v)`: a Chain of two Chains, used for geodesics (a 2-by-n block);
  - `TensorField`: a field state, such as a curve or grid function; arithmetic is pointwise.
- **Time-stamped state.** `LocalTensor{B,F}`, written `t ↦ x`, is the pair (base point `point(x)`, fiber `fiber(x)`). `localfiber(y)` returns `fiber(y)` for a LocalTensor and `y` otherwise; this is how RHS results are normalised.
- **RHS convention.** `f(x::LocalTensor)` returns a state or a LocalTensor. Time dependence is read through `point(x)`. Indexing `x[i]` on a LocalTensor forwards to the fiber [verified]. `FlowApprox` systems are called `f(x, h)`.
- **Trajectory, full (skip≥1).** A `TensorField` whose base is the time grid:
  - an `IntervalRange` built from a Julia `StepRangeLen` (`tmin:h*skip:tmax`), for Explicit, Multistep and Heun;
  - a `GridBundle` over a `Vector{Float64}` of times, for the adaptive methods;
  - `base(x0) × t` when x0 is a field (`Adapode.jl:337-339`). In that case the storage is an array of size `(size(x0)..., nt)` with **time as the last dimension**.
- **Trajectory, skip=0.** A single `LocalTensor(t_end ↦ x_end)`.
- **Leapfrog output.** A `TensorField(base(u) ⊕ (tmin:dt*skip:tmin+tmax), data)` with data of size `(size(u)..., nplots+1)`.
- **Compile-time versus runtime.** The method order `o` (`Val{o}` / type parameter) and the state dimension (in the Chain type) are compile-time. Everything else — h, tmax, skip, and the number of steps — is runtime. The Butcher and Adams tables are indexed with `Val(o)` through `@pure` functions (`butcher`, `blength`, `shift`: `Adapode.jl:231-233, 261-262`), so a table lookup is constant-folded.

### 3.2 Butcher and Adams tables (`src/constants.jl`)

- **`CB[N]`, N=1..4** (lines 5-20). A `Values` of N rows: rows 1..N−1 are the strictly-lower-triangular stage rows `a_k` (row k has k entries, over stages 1..k), and row N is the weight vector `b`. CB[1] = (`Values{0}()`, (1)), i.e. Euler.
- **`CBA[o]`, o=1..5** (lines 24-59). Built as `constants(a, b, c) = Values(a..., b, b − c)` (line 22). The rows are:
  - the a-rows;
  - `b`, the weights used **to advance**;
  - `b − c`, the error-estimate weights. This is a Float64 difference computed after rounding each entry.

  The number of stages is `length(CBA[o]) − 1 − 0`; the code's `n = length(b) − A` with A=1 gives it (line 266, 281).
- **`CAB[k]`** (lines 61-65) holds the k-step Adams–Bashforth coefficients ordered **oldest → newest**. **`CAM[k]`** (lines 67-71) holds the Adams–Moulton coefficients with k entries (the (k−1)-step, order-k AM), oldest → newest, and the last entry multiplies f_{n+1}.
- **`Gauss[n]`, n=1..4** (lines 73-99). Each entry is `(weights, points)`, triangle quadrature on the reference triangle {(r,s): r,s≥0, r+s≤1}. The weights sum to 1; the code divides by 2 for the area.
- **All entries are correctly-rounded Float64 values of rationals.** `a/b` is Int/Int, and literals such as `0.09375`, `-0.18`, `0.25`, `0.5` equal the correctly-rounded rationals. A Lean port that stores (num, den) pairs and computes `Float.ofInt n / Float.ofInt d` reproduces them bit-for-bit. `b − c` must be formed in Float, not in ℚ.

The exact tables are listed below. Rows are shown as rationals; `Values(x,y)./d` means entrywise division.

```
CB[1] Euler:     a = [];                        b = (1)
CB[2] midpoint:  a = [(1/2)];                   b = (0, 1)
CB[3] Kutta3:    a = [(1/2), (-1, 2)];          b = (1,4,1)./6
CB[4] RK4:       a = [(0.5), (0, 0.5), (0,0,1)]; b = (1,2,2,1)./6

CBA[1] Heun–Euler: a=[(1)]                      b=(1,0) [Euler, advances]      c=(1/2,1/2)
CBA[2] Bogacki–Shampine: a=[(1/2),(0,3/4),(2/9,1/3,4/9)]
                 b=(7/24,1/4,1/3,1/8) [2nd order, advances]   c=(2/9,1/3,4/9,0) [3rd]
CBA[3] Fehlberg: a=[(1/4),(0.09375,0.28125),(1932/2197,-7200/2197,7296/2197),
                    (439/216,-8,3680/513,-845/4104),(-8/27,2,+3544/2565,1859/4104,-11/40)]  ← TYPO
                 b=(16/135,0,6656/12825,28561/56430,-0.18,2/55) [5th, advances]
                 c=(25/216,0,1408/2565,2197/4104,-0.2,0) [4th]
CBA[4] Cash–Karp: a=[(1/5),(3/40,9/40),(3/40,-9/10,6/5) ← TYPO (a41 should be 3/10),
                    (-11/54,5/2,-70/27,35/27),(1631/55296,175/512,575/13824,44275/110592,253/4096)]
                 b=(2825/27648,0,18575/48384,13525/55296,277/14336,0.25) [4th, advances]
                 c=(37/378,0,250/621,125/594,0,512/1771) [5th]
CBA[5] Dormand–Prince: a=[(1/5),(3/40,9/40),(44/45,-56/15,32/9),
                    (19372/6561,-25360/2187,64448/6561,-212/729),
                    (9017/3168,-355/33,46732/5247,49/176,-5103/18656),
                    (35/384,0,500/1113,125/192,-2187/6784,11/84)]
                 b=(35/384,0,500/1113,125/192,-2187/6784,11/84,0) [5th, advances]
                 c=(5179/57600,0,7571/16695,393/640,-92097/339200,187/2100,1/40) [4th]

CAB = [(1), (-1,3)./2, (5,-16,23)./12, (-9,37,-59,55)./24, (251,-1274,2616,-2774,1901)./720]
CAM = [(1), (1,1)./2, (-1,8,5)./12, (1,-5,19,9)./24, (-19,106,-264,646,251)./720]

Gauss[1] w=(1)                 pts=((1/3,1/3))
Gauss[2] w=(1,1,1)/3           pts=((1,1)/6,(4,1)/6,(1,4)/6)
Gauss[3] w=(-27,25,25,25)/48   pts=((1,1)/3,(1,1)/5,(3,1)/5,(1,3)/5)
Gauss[4] w=(35494641/158896895 ×3, 40960013/372527180 ×3)   (Σw = 0.9999999999999991)
         pts=((a,a),(a,b),(b,a),(c,c),(c,d),(d,c)) with a=100320057/224958844, b=16300311/150784976,
             c=13196394/144102857, d=85438943/104595944
```

Empirical orders, measured with fixed-step convergence on `x' = x·cos t + t` **[verified]** (`adapode_oracle/verify/t25.jl`):

| Pair | advancing weights (b) | other weights (c) |
|---|---|---|
| Heun–Euler | 0.99 | 1.98 |
| Bogacki–Shampine | 2.03 | 2.98 |
| Fehlberg | **0.83** (typo) | 4.01 |
| Cash–Karp | **0.98** (typo) | **0.98** |
| Dormand–Prince | 5.01 | 4.06 |

So the Fehlberg typo only damages the advancing solution: k₆ has weight 0 in c. The Cash–Karp typo corrupts k₄ and therefore both solutions.

The choice of which solution advances is inconsistent across the pairs:
- Heun–Euler, Bogacki–Shampine and Cash–Karp advance with the **lower**-order solution;
- Fehlberg and Dormand–Prince advance with the **higher**-order solution (local extrapolation).

### 3.3 Mesh and FEM data (types from Cartan and MeshTopology; the conventions Adapode relies on)

- **Points** are stored in **homogeneous/affine coordinates** `Chain{varmanifold(d+1)}(1.0, x, y, …)`: component 1 is the constant 1, and physical coordinates are `p[2], p[3], …` [verified]. User functions therefore read `x[2]` for x and `x[3]` for y (for example `x->x[2]*sin(x[2])`).
- **Simplices** are `Values{d+1,Int}` of 1-based global node indices, e.g. `[[1,2],[2,3],…]` for `initmesh(0:1/5:1)`.
- **Boundary.** For a 1D mesh from `initmesh(range)`, the boundary bundle has 0-simplices `[[1],[n]]`. In 2D it has edges `Values{2}`.
- **Gradients.** `gradienthat(t, m)` returns, per element, a `TensorOperator` whose columns are ∇φ_a (a = 1..d+1), expressed in the manifold ↓V of the spatial coordinates. For example, triangle (0,0),(0.5,0),(0.5,0.5) gives ∇φ = (−2,0), (2,−2), (0,2) [verified]. In 1D, ∇φ = (−1/h, +1/h).
- **Local edge numbering** (MeshTopology `localedge`, `element.jl:357-360` in that package): for a triangle (v1,v2,v3), edge j is **opposite vertex j**, i.e. edges (v2v3, v1v3, v1v2). `trinormals`, `neighbors`, `edgesindices`, the CR basis, the Nédélec basis and `assembleDIPG` all use this convention.
- **Neighbours.** `neighbors(t)[k][j]` is the element across edge j, or 0 on the boundary.
- **Facet signs.** `facetsigns(t)[k][j] = neighbor < k ? +1 : −1` (MeshTopology `element.jl:395-397`). The boundary neighbour is 0, so boundary facets get +1.
- **Chain-of-Chains matrices are column-major.** `Chain(c1, c2)[i,j] == c_j[i]` [verified], so local matrices `Chain(col1, col2, …)` store columns. `assemblelocal!(M, mat, m, tk)` (MeshTopology `element.jl:285-298`) performs `M[tk[i], tk[j]] += mat[i,j]*m` with **i outer, j inner**, elements in order. This is the floating-point summation order of every global sparse entry.
- **Global matrices** are `SparseMatrixCSC{Float64}` (complex for Maxwell), assembled as n_nodes × n_nodes. Solves use Julia `\`, which dispatches to UMFPACK (LU) or CHOLMOD.
- **Discontinuous P1 (DIPG).** DOFs are numbered `3(k−1) + (1,2,3)`, i.e. `totalnodes = 3·nt`.
- **Elasticity DOFs.** `solveelastic` uses the interleaved numbering node k → (2k−1, 2k). `assembleelastic`'s K scatter uses `[x1,x2,x3,y1,y2,y3]` (bug B11).
- **P2 (LagrangeP2).** Local nodes are `[v1, v2, v3, e(v2v3), e(v1v3), e(v1v2)]`, and edge node ids are `nodes(t) + edgeindex`.

### 3.4 Spectral grids

- 1D fields are `TensorField(range)`. Multi-D fields are `TensorField(ProductSpace(r1, r2, …))`, stored **column-major, x fastest**.
- Frequency grids come from Cartan (§4.10). A frequency point in multi-D is a `Chain` (k1, k2, …), and `|k|` is its Euclidean norm.
- Chebyshev grids: `Chebyshev(N)` has points `x_j = −cos(πj/(N−1))`, j=0..N−1, **ascending from −1 to 1** [verified].

---

## 4. Algorithms (exact semantics and evaluation order)

Notation: `lin(h, c, K) := ((((h*c1)*K1 + (h*c2)*K2) + (h*c3)*K3) + …)`. This is a **left fold**: the coefficient is multiplied by h *first* and then by the vector, as `weights(h*c, fx)` does (`Adapode.jl:224-230, 234-241`). All vector operations are componentwise. Following this order reproduces Julia **bit-for-bit** [verified for RK2–4 with skip=0, ABM2–5 with skip=1, adaptive RK2–5 and adaptive ABM1–5 on Lorenz, by independent re-implementations in `adapode_oracle/verify/t17.jl`, `t18.jl` and `t19.jl`. The elastic-bug check is `verify/t20.jl`, the convection/SD/P1-quadrature/DIPG check is `verify/t23.jl`, and the Chebyshev sign fixes are `verify/t13.jl` and `verify/t15.jl`].

### 4.1 One explicit RK step (`butcher` + `explicit`: `Adapode.jl:279-293`)

```
rkstep(f, t, x, h, rows a[1..s-1], b[1..s]):
  k1 = f(t ↦ x)
  for j = 2..s:  aj = a[j-1]  (length j-1)
      kj = f( (t + h*sum(aj)) ↦ (x + lin(h, aj, k[1..j-1])) )
  return x + lin(h, b, k[1..s])
```

- `sum(aj)` is the left-fold Float sum of the row, e.g. RK4 stage times are t+h/2, t+h/2, t+h.
- Order 1 (`Val(1)`) is special-cased as `x + h*f(t↦x)` (`Adapode.jl:291-293`).
- The result is a bare fiber. The caller attaches the new time.
- FlowApprox variant: `f(x, h)` wherever `f(x)` appears.

### 4.2 Fixed-step drivers

**Initial state** (`init`, 471-476). A plain `x0` becomes `0.0 ↦ x0`, so **the start time is always 0** unless x0 is a LocalTensor.

**Grid** (`initsteps`, 332-340). The grid is `tmin : h*skip : tmax`, a Julia range: length `floor((tmax−tmin)/(h·skip)) + 1` computed in TwicePrecision, with elements `tmin + i·h·skip`. With dyadic h the values are exact. Examples [verified]: T=2π, h=2^-7 gives n=805 and last t = 804·2^-7 = 6.28125; T=2π, h=2^-15 gives n=205888. `bc(x0)` is applied to the initial value.

**EulerHeun** (483-490, `heun` 243-246). For i = 2..n:

```
x_i = bc( x + (hk + h*f((t_{i-1}+h) ↦ (x + hk)))/2 )   with hk = h*f(t_{i-1} ↦ x_{i-1})
```

The step size is always `h`, whatever `skip` is, while the grid spacing is `h·skip` (bug B7 when skip≠1).

**ExplicitIntegrator{o}** (491-520):
- **skip=0.** `n = Int(round((T − t0)/h))`, rounding half to even, so 2π/2^-7 = 804.25 gives 804. Then take `|n|` steps of `sign(n)·h`, with the time accumulated as `t += sign(n)*h` (repeated addition, not grid multiplication). Apply `bc` to the LocalTensor after each step and return the final `t ↦ x`. **Negative duration integrates backwards** [verified].
- **skip=1.** `x_i = bc(rkstep(f, t_{i-1}, x_{i-1}, h))`, where t_{i-1} is the **grid** time.
- **skip=k>1.** The grid has step `h·k`. Each stored value comes from the previous stored value by k inner steps of h, with inner times accumulated by addition; `bc` is applied after each inner step.

**MultistepIntegrator{o} with skip=1** (544-549, `initsteps!` 388-398, `predictcorrect` 306-320, `multistep!` 298-301). Uses a ring buffer `F[1..o+1]` of RHS values and a slot pointer `s` (`t.s`, initially 0):

```
ring(s, m=o+1, l) = [((q + s + (m - l)) mod m) + 1  for q = 0..l-1]      # shift(Val(m),Val(l),i) with i=s+(m-l)

if o == 1:  x_{i+1} = x_i + h*f((t_i+h) ↦ (x_i + h*f(t_i ↦ x_i)))          # Euler predictor + one backward-Euler correction
else:
  first call (s==0): bootstrap with RK4 (CB[4], ALWAYS RK4 regardless of o):
      for j = 1..o-1:  F[j] = f(t_j ↦ x_j);  x_{j+1} = rkstep_RK4(t_j, x_j, h)   (stored in the grid)
      s = o;  i = o
  each step from x_i (grid time t_i):
      F[s] = f(t_i ↦ x_i)
      p    = x_i + lin(h, CAB[o], F[ring(s, o+1, o)])          # AB_o predictor
      s    = (s mod (o+1)) + 1
      F[s] = f((t_i+h) ↦ p)
      c    = x_i + lin(h, CAM[o], F[ring(s, o+1, o)])          # AM corrector (order o)
      x_{i+1} = bc(c);  i += 1
```

- Note that `F[s]` from the corrector (f at the *predicted* point) is overwritten by `f(x_{i+1})` at the start of the next step (PECE).
- The output loop runs `i = o+1 .. n`, so x_2..x_o come from the bootstrap.

**MultistepIntegrator with skip=0 and skip=k>1.** The intended algorithm is the same PECE recursion with a final-only or strided output. **Both paths are buggy as written** (B3, B4).

### 4.3 Adaptive embedded RK (`ExplicitAdaptor{o}`: 521-528, `explicit!` 427-435, `timeloop!` 677-694)

This reproduces Julia **bit-for-bit once the time points are stored** (see B1: the current Julia never stores them).

```
T=[t0], X=[x0]; ts = TimeStep(h0)   (hmax = h0 if h0>1e-4 else 1e-4; emin=10^(log2 h0 - 3); emax=10^(log2 h0))
tab = CBA[o]; s = length(tab)-1; a = tab[1..s-1]; b = tab[s]; db = tab[s+1]     # db = b - c (Float)
loop:
  # ---- timeloop!(x, t, tmax, Val(1))
  if e < emin: h *= 2; i -= 0; s_ = 0
  if e > emax: h /= 2; i -= 1; s_ = 0          # reject: overwrite x[i+1]
  if s_ == 0: checkstep!   (clamp |h| to [hmin,hmax], i>=1)      # s_ is always 0 for RK ⇒ clamp every step
  d = tmax - T[i]
  if d <= h: h = d
  if d <= hmax: truncate to i-1 entries; STOP         # NB drops the last accepted point (B2)
  # ---- explicit!(x, f, t, Val(o))
  ensure capacity ≥ i+1 (grow by 10000)
  K = stages(f, T[i], X[i], h, a, s)
  i += 1;  T[i] = T[i-1] + h;  X[i] = X[i-1] + lin(h, b, K)
  e = max_j | h * (((db1*K1 + db2*K2) + ...))_j |    # absolute, NOT pre-multiplied: db_l*K_l, left fold, then *h
```

Consequences:
- `h` can never exceed its initial value when h0 > 1e-4.
- The error window is `[1e-10, 1e-7]` for tol=7, a base-2 step tied to base-10 error thresholds.
- The run ends before reaching tmax: the last kept t lies in [tmax−2·hmax, tmax−hmax). For example, Lorenz with T=2π and hmax=2^-7 ends at 6.275360107421875, just below tmax−hmax = 6.2753727…

### 4.4 Adaptive ABM (`MultistepAdaptor{o}`: 563-571, `predictcorrect!` 437-469)

This is bit-exact with the patched oracle (`patch2.jl`), which stores the bootstrapped time points.

```
same TimeStep; e measured RELATIVELY: e = max_j |(c_j - p_j)/c_j|
timeloop!(..., Val(o)):  e<emin: h*=2, i -= floor(o/2), s=0;  e>emax: h/=2, i -= ceil(o/2), s=0
                         s==0 ⇒ checkstep!; d/done/truncate as above
o == 1: p = x_i + h f(t_i↦x_i); c = x_i + h f((t_i+h)↦p); append (t_i+h, c)
o >= 2: ensure capacity ≥ i+o;
        if s==0: RK4 bootstrap o-1 steps from (T[i],X[i]) storing (T,X)[i+1..i+o-1], F[1..o-1], s=o, i+=o-1
        PECE exactly as §4.2 (ring buffer), append (t_i+h, c)
```

So whenever h changes, the method discards the last ⌊o/2⌋ or ⌈o/2⌉ points and restarts the history with an RK4 bootstrap at the new h.

### 4.5 Leapfrog (`Adapode.jl:648-675`)

```
vold = bc(x0) at time -dt, v = bc(x1) at time 0;  dt = step(ic) = t(x1) - t(x0)
gap = I.skip; tplot = dt*gap; nplots = round(tmax/tplot)  (ties-to-even); dt = tplot/gap
out[..., 1] = v;  for i = 2..nplots+1: repeat gap times: (vold, v) = (v, bc(leap(vold, v)));  out[...,i] = v
Leap{1}:  v_new = vold - 2dt * fprime(v)          # u' = -fprime(u)  (note MINUS)
Leap{2}:  v_new = 2v - vold + dt^2 * fprime(v)    # Störmer–Verlet for u'' = fprime(u)
```

- The output time axis is `tmin : dt*gap : tmin+tmax`, a range. Its length can differ from `nplots+1` when `tmax/tplot` rounds up (latent bug B8).
- The `LocalTensor` time label of the new state is `point(vold)+dt`, which is wrong but never used.

### 4.6 Geodesic RHS (Cartan `diffgeo.jl:1266-1272`)

```
state X = (x, v);  f(X) = ( v , -Σ_{j=1..n} Σ_{i=1..n} Γ(x)[i,j] * (v_i * v_j) )
```

- The summation order is j outer, i inner, as a left fold: `+(Γ[1,1]*(v1v1), Γ[2,1]*(v2v1), Γ[1,2]*(v1v2), Γ[2,2]*(v2v2))`.
- `Γ[i,j]` is a Chain over k (the Christoffel symbols of the second kind Γ^k_ij), and `TensorOperator(Chain(C1, C2))[i,j] = C_j[i]`.
- For the half-plane example, `Γ(x)` returns (writing y = x[2]):

| Γ[i,j] | value | meaning |
|---|---|---|
| [1,1] | (0, 1/y) | Γ^y_xx = 1/y |
| [1,2] = [2,1] | (−1/y, 0) | Γ^x_xy = −1/y |
| [2,2] | (0, −1/y) | Γ^y_yy = −1/y |

This is the metric (dx²+dy²)/y².

### 4.7 FEM local matrices

N is the number of simplex vertices (2 for an interval, 3 for a triangle, 4 for a tetrahedron). Global assembly multiplies each local matrix by the element volume `m_k`.

- **Mass**: `(ones(N,N) + I) / ((N+1)!/(N−1)!)` = `(1+δ_ij)/(N(N+1))`. That is [[2,1],[1,2]]/6 in 1D, (1+δ)/12 on triangles and (1+δ)/20 on tetrahedra [verified].
- **Stiffness**: `c · ∇φ_i·∇φ_j`, with the column j vector `c*(∇φ_j · G)`. A special case for scalar `g::Float64` gives [[cg², −cg²], [−cg², cg²]].
- **Convection**: `C_ij = (b/N)·∇φ_j`, so all rows are equal. Globally this is the standard ∫ φ_i b·∇φ_j for element-constant b [verified against independent code].
- **SD**: `(b·∇φ_i)(b·∇φ_j)`.
- **CR gradients**: `∇ψ_j = G·(−1,1,1), G·(1,−1,1), G·(1,1,−1)`, i.e. −2∇φ_j.
- **Elasticity** (intended): `D = [[2μ+λ, λ, 0], [λ, 2μ+λ, 0], [0, 0, μ]]` (plane strain). B is 3×6 with columns `[∂xφ_a, 0, ∂yφ_a]` and `[0, ∂yφ_a, ∂xφ_a]` for a=1..3, interleaved (u_ax, u_ay). `K_loc = BᵀDB·m`.
- **Nédélec** (`_nedelec`, with f = stiffness(λ, g), i.e. f_ab = λ∇φ_a·∇φ_b):

```
m11=(f33-f23+f22)/6, m22=(f11-f13+f33)/6, m33=(f22-f12+f11)/6,
m12=(f31-f33-2f21+f23)/12, m13=(f32-2f31-f22+f21)/12, m23=(f12-f11-2f32+f31)/12
```

  These equal (1/|K|)∫ λ N_a·N_b with Whitney forms N_1 = φ₂∇φ₃ − φ₃∇φ₂ (cyclic).
- **Maxwell local matrix**: `M_ab = (1/(|K|²μ) + n_ab(κ²)) · l_a l_b`, times |K|. Here l are signed edge lengths `l[ed] .* signs[k]`.
- **Maxwell load**: `b[ed] += Re(f̂·(∇φ_{a+2} − ∇φ_{a+1})) · l_a·|K|/3`. This is one-point centroid quadrature of f̂·(l_a N_a); `curl(value(g))` evaluates to (g3−g2, g1−g3, g2−g1).
- **P1 shapes**: `(1−r−s, r, s)`; reference gradients `(−1,−1), (1,0), (0,1)`.
- **P2 shapes** at (r,s):

```
[1−3r−3s+2r²+4rs+2s², 2r²−r, 2s²−s, 4rs, 4s−4rs−4s², 4r−4r²−4rs]
```

  with gradients (∂r, ∂s):

```
(−3+4r+4s, −3+4r+4s), (4r−1,0), (0,4s−1), (4s,4r), (−4s, 4−4r−8s), (4−8r−4s, −4r)
```

- **Isoparametric quadrature**: `J = dS·xyᵀ` (a 2×2 matrix from shape gradients times node coordinates). Mass is `Σ_q (w_q/2)·det J · S_q S_qᵀ`; stiffness is `Σ_q (w_q/2)·det J · (J⁻¹dS)ᵀ(J⁻¹dS)`. P1 uses Gauss[2] and P2 uses Gauss[4].

### 4.8 FEM global operators

- **Lumped load.** `assembleload(t, f, m) = b`, with `b_i = Σ_{k∋i} f(p_i)·m_k / sdims`, where sdims = N (Cartan `element.jl:546` → MeshTopology `assembleincidence`). Here f is a function of the homogeneous point, a constant, or a nodal vector. This is nodal ("vertex") quadrature, **not** the consistent ∫fφ_i.
- **Mass-load.** `assemblemassload(t, f, m, l) = (M, b)`, with M_ij = Σ m_k·mass_ij and b_i = Σ_{k∋i} f_i·l_k/sdims.
- **Robin.** `assemblerobin(e, κ, gD, gN)`, with a = edge midpoints (`means(e)`) and v = boundary element volumes (1 for 0-simplices):
  - `R = Σ_e κ(a_e)·v_e · mass_e`, which is κ·v on the diagonal for 1D point boundaries;
  - `r_i = Σ_{e∋i} (κ(a_e)·gD(a_e) + gN(a_e))·v_e / sdims(e)`.
  - Checks [verified]: the unit square with κ=1e6 gives Σ R = 4e6, and with gD = x gives Σ r = 2e6.
- **Poisson.** `(A + R) u = b + r` solves −∇·(c∇u) = f with c∂ₙu = κ(gD−u) + gN.
- **Transport** (`solvetransport`): `(ϵA + C) u = b` with homogeneous Dirichlet on the vertices of e.
- **Transport–diffusion.** `A(c) + R − Cᵀ + Sd`, where C uses element-mean velocities (`means(immersion(t), f)`), and `Sd = assembleSD(√δ·b)`, which is δ(b·∇φ_i)(b·∇φ_j). The right-hand side is `r` only: there is no volume source.
- **Heat** (`solveheat`). `A = stiffness(base(ic))` and `(M, b) = massload(f) + robin(κ)`, where the tuples are added elementwise, so **M already contains R**. Each step solves:

```
u_{n+1} = (M + hA) \ (M u_n + h b)
```

  - The Robin matrix is therefore *not* scaled by h. This is a quirk: the boundary rows effectively evolve as u_{n+1} ≈ u_n + h·gD. Reproduce it for compatibility.
  - The step `h = step(T)` is taken from the range `T` and iterated by `orbit` over `T`, so the output has `length(T)` time slices with slice 1 = IC [verified: `solveheat_readme` golden].
- **Wave** (`solvewave`), Crank–Nicolson on `[u; v]` with `(A, M, b) = assemble(pt, 1, 1, 0)`:

```
LHS = [M, −Δt/2·M; Δt/2·A, M]
RHS = [M, Δt/2·M; −Δt/2·A, M]
[u;v] ← LHS\(RHS[u;v] + [0; Δt b])
```

  After each solve, `u[fixed] = bc[:, l]` (applied after solving, "the ugly way"), and `out[:, l] = u` for l=1..nt. Note that out[:,1] is **after** the first step and the initial state is 0. `bc` is a TensorField over (boundary vertices × time grid); Adapode reads `base(bc).g.v[1]` (time grid) and `base(bc).s` (boundary). The port should take them explicitly.
- **Bistable** (Picard), per time step:

```
ξ^{(0)} = ξ_n
ξ^{(k+1)} = (M + dtϵA) \ (M ξ_n + dt·M·f(ξ^{(k)}))    for k = 0, 1, 2
ξ_{n+1} = ξ^{(3)}
```

  Here `(A, M) = assemble(base(ic))`, i.e. c=1, a=1, f=0.
- **Bistable** (Newton), 3 iterations. With `ξ̄ = element means of ξ_tmp`:

```
(Mdf, b) = assemblemassload(base, f.(ξ_tmp), df.(ξ̄)·m, m)
J = (M + dtϵA) − dt·Mdf
ρ = (M + dtϵA)ξ_tmp − Mξ_n − dt·b
ξ_tmp ← ξ_tmp − J\ρ
```

- **Nonlinear Poisson**, −∇·(a(u)∇u) = f with u=0 on the boundary. Per element k:
  - Inputs: ū = element mean of u, `a = A(ū)`, `a' = (A(ū+1e−8) − a)/1e−8`, and gu_a = ∇u_k·∇φ_a.
  - Jacobian: `J_loc[a,b] = a ∇φ_a·∇φ_b + (a'/3)·gu_a`. The row factor comes from `Chain(dagug, dagug, dagug)` being column-major.
  - Residual: `r[t_k] += (f_k/3 − a·gu)·m_k`, where **f is per element** (indexed by k).
  - Boundary rows: zero the row, set the diagonal to 1 and r=0.
  - Update: `u += J\r`, 5 iterations, printing `|d|=…, |r|=…` each time.
  - Verified on the 2×2 square with a=1+u² and f=1: ‖d‖ = 0.0625, 2.71e−5, 1.53e−11, 3.46e−18, 3.46e−18.
- **Stokes (CR–P0).**

```
[νA_CR  0      B1ᵀ  0 ]
[0      νA_CR  B2ᵀ  0 ]
[B1     B2     0    m ]
[0      0      mᵀ   0 ]
```

  - The size is 2ne + nt + 1 (145 for the 4×4 square) [verified].
  - `A_CR = assemblestiffness(t2e, 1, m, gradientCR)` is assembled on the element→edge topology.
  - `B1[k, e] = −|K| ∂xψ_e` (from `assembledivergence(t2e, m, −gCR)`).
  - Boundary DOFs are the boundary edge ids for u and v. `solvedirichlet` with RHS 0 gives u, v at the edges and p per element. Velocity is interpolated to nodes with `interp`.
- **Elasticity** (intended): `K u = F` with `F_{2a} = Σ_k (M_loc·f_y)` (consistent mass times nodal force). Boundary DOFs of `e` are clamped to 0, and u is returned interleaved.
- **Maxwell.**
  - `A` is complex sparse (ne×ne) and b real.
  - `solvedirichlet(A, complex(b), boundary_edge_ids, bc_values)`.
  - Post-processing (`nedelecmean`): B = revrot(edge vectors)/(e1∧e2), a covariant Piola matrix. The field at the centroid is `Σ_a u[e_a]·sign_a·(B·N_a(1/3,1/3))` with reference `N = ((−y,x), (−y,x−1), (1−y,x))`. It is then nodally averaged (`interp`, weights 1/degree).
- **DIPG** (`assembleDIPG`), over elements i and local edges j. Let n be the neighbour across j.
  - Skip the edge if n > i. If n = 0, set n := i (boundary).
  - Quadrature points on the edge are the endpoints and the midpoint (`cmat = [(2,0),(1,1),(0,2)]/2` applied to the edge's two vertices) with Simpson weights w = (1,4,1)/6.
  - The jump vector is the 6-vector `J_q = [λ⁺(x_q); −λ⁻(x_q)]` (barycentrics of the + and − elements, from the inverse affine matrices). The average normal derivative is `avg = [n·∇φ⁺; n·∇φ⁻]/2`.
  - `PE = Σ_q w_q J_q J_qᵀ` (no length factor, i.e. the "divided by h_e" penalty) and `SE = Σ_q w_q|e| J_q avgᵀ`.
  - On the boundary only the upper-left 3×3 blocks are scattered, and `2SE` is used. Interior edges scatter the 6×6 at dofs `[3(i−1)+1:3; 3(n−1)+1:3]`.
  - Verified on the 2×2 square: Σ P = 8, tr P = 16, Σ S = 0, tr S = 10.
- **Jumps and adaptpoisson** (1D, working):
  - The indicator is `η_k = m_k·sqrt((ρ_k² + ρ_{k+1}²)·m_k/2)`, with nodal residual ρ = f(x) − a·u. It assumes nodes k and k+1 are the element's.
  - Each loop solves `(A + M)ξ = b` with homogeneous Dirichlet, then computes η and ϵ = rms(η) = ‖η‖/√nt.
  - It prints `"<summary of topology>, ϵ=$ϵ, α=$(ϵ/max η)"`.
  - It refines every element with η > ϵ by inserting midpoints and re-sorting the nodes. **It refines once more after the ϵ that stops the loop**, so the final mesh is never solved on.
  - The loop condition is `ϵ > 5e−5 && nt < 10000`.
  - Verified sequence for the README problem: nt = 4, 6, 8, 10, 14, 20, 30, 38, 56, 72, 106, 140, 208 → final 270 elements. The first ϵ values are 0.06250023291538927 and 0.01881851550353944; the last is 3.725363657493423e−5.
- **Jumps, 2D branch** (intended). The per-edge flux is `−c ∇u_k·n_{k,j}`; jumps are summed over the two sides with boundary edges masked out. Then:

```
η_k = sqrt(((ℓ3 J12)² + (ℓ1 J23)² + (ℓ2 J31)²)/2) + h_k·sqrt(‖f_k − a u_k‖/(3m_k))
```

  (sic: the norm is not squared, and the /(3m_k) comes from juxtaposition precedence).

### 4.9 Chebyshev operators

- **Differentiation matrix.** `ChebyshevMatrix(x)` (Cartan `spectral.jl:353-360`) is Trefethen's formula: `c = [2,1,…,1,2].*(−1)^j`, `D_ij = c_i/c_j/(x_i−x_j)`, `D_ii = −Σ_{j≠i} D_ij`.
  - **`ChebyshevMatrix(::Chebyshev)` negates the points**, so it returns −D_x on Adapode's ascending nodes. `ChebyshevMatrix(Vector)` returns +D_x [verified: both 5×5 matrices are in the goldens].
  - Even powers are unaffected. **Odd powers flip sign**, which silently breaks `biharmonic` (−8xD³ term), `orrsommerfeld` (through biharmonic) and `polarlaplacian` (the (1/r)∂_r term with r<0 nodes) (B17).
  - Using D consistent with the node ordering gives Trefethen's published results: Orr–Sommerfeld rightmost eigenvalue −7.8197e−5 − 0.2615677i (N=100); polar Laplacian eigenvalues 5.7832, 14.682 (×2), 26.375 (×2), 30.471. As written, the code gives 36.8 + 0.011i and eigenvalues 0, 14.68, 19.2, … [verified].
- **Helmholtz.** 1D: `L = (D²)[2:N−1, 2:N−1] + k²I` acting on interior values. 2D: `L = I_{M−2} ⊗ D2X + D2Y ⊗ I_{N−2} + k²I` on `vec(u[2:N−1, 2:M−1])` (x fastest).
- **Biharmonic** (1D, clamped): `L = ((diag(1−x²)D⁴ − 8 diag(x) D³ − 12D²)·S)[2:N−1, 2:N−1]` with `S = diag(0, 1/(1−x_j²), 0)`. 2D: `I⊗D4X + D4Y⊗I + 2(D2Y⊗I)(I⊗D2X)`.
- **Orr–Sommerfeld**: `A = (D4 − 2D2 + I)/R − 2iI − i diag(1−x²)(D2 − I)` and `B = D2 − I`. This is streamwise wavenumber α=1 (Trefethen p40).
- **Polar Laplacian.**

```
r = Chebyshev(2N) nodes
D1 = D²[2:N, 2:N],  D2 = D²[2:N, 2N−1:−1:N+1]
E1 = D[2:N, 2:N],   E2 = D[2:N, 2N−1:−1:N+1]
R  = diag(1/r[2:N])
D2t = Toeplitz(toeplitz2(M−1))
toeplitz2(n, h=2π/n) = [−π²/(3h²) − 1/6; 0.5(−1)^(k+1)/sin²(kh/2) for k = 1..n−1]
L = I_{M−1} ⊗ (D1 + R E1) + [[0,I],[I,0]] ⊗ (D2 + R E2) + D2t ⊗ R²
```

- **Picard iteration** (`solveiteration`): `u ← solver(L, f.(u))` until `‖u_new − u‖∞ ≤ 5eps()`.
  - Verified: `solvehelmholtz(e^{4x})` with N=17 has max error 1.94e−11 against (e^{4x} − x sinh4 − cosh4)/16.
  - Verified: the nonlinear problem u″ = e^u, N=17, gives u(0) = −0.3680560244414872.

### 4.10 Fourier and DCT/DST multiplier solvers

The frequency grids are Cartan's (`spectral.jl:31-66`). For a 1D range with N points and L = x_end − x_1 [verified]:

| Kind | Frequencies |
|---|---|
| Neumann / DCT (`r2rspace(x)`) | k_j = jπ/L, j = 0..N−1 |
| Dirichlet / DST (`r2rspace(x, RODFT10)`) | k_j = (j+1)π/L, j = 0..N−1. This comes from `kind ∈ (9,6,10) ⇒ +out[2]`, where RODFT10 = 9 in FFTW numbering |
| Periodic / rfft (`rfftspace(x)`) | k_j = 2πj/L, j = 0..⌊N/2⌋ |
| `fftspace(x)` (used by the Schrödinger solver) | k_j = 2πj/L, **j = 0..N−1, all non-negative** (not signed fftfreq; bug B18) |

In multi-D:
- `r2rspace` and `fftspace` are products of the 1D grids.
- `rfftspace(ProductSpace)` uses `rfftspace(x.v[2])` for dimension 1 (**bug**: it should be `x.v[1]`) and `fftspace` for the remaining dimensions (all non-negative). As a result, periodic multi-D solves are wrong for negative frequencies (B18).

Transforms follow FFTW semantics:
- `dct` and `idct` are the **orthonormal** DCT-II and DCT-III along all dimensions.
- `RODFT10` is `Y_k = 2 Σ_{n=0}^{N−1} X_n sin(π(n+½)(k+1)/N)`.
- `RODFT01` is `Y_k = (−1)^k X_{N−1} + 2 Σ_{n=0}^{N−2} X_n sin(π(n+1)(k+½)/N)`.
- RODFT01∘RODFT10 = 2N·id per dimension, hence the division by `prod(2.0 .* size(u0))`.
- `irfft(Y, N)` is normalised by 1/N.

Two details for porting:
- Dimension mismatch: the DCT-II eigenfrequency for grid spacing L/(N−1) is πj(N−1)/(NL), but Adapode uses πj/L. Port as-is; the goldens encode it.
- `wavemultiplier` is 0/0 at k=0. The code overwrites `wm[1]` (0 in the wave* solvers, t in the fullwave* solvers). For DST, k>0 always.

---

## 5. Display and printing

Adapode defines **no `show` methods**. Printed output comes from four places:

- `adaptpoisson` (`element.jl:179`) prints `println(Base.array_summary(stdout, immersion(pt), axes), ", ϵ=$ϵ, α=$(ϵ/maximum(η))")`. `array_summary` writes to stdout and returns `nothing`, so the literal text includes "nothing". `maximum(η)` of a TensorField is a LocalTensor, so α prints as a LocalTensor. A verified line:
  `4×2⊆5 SimplexTopology{2, Vector{Int64}, Vector{Int64}, (true, true)}nothing, ϵ=0.06250023291538927, α=1.0v₁ + 0.375v₂ ↦ 0.7071080987512746`
  The port should just log `(nt, ϵ, ϵ/max η)`.
- `solvenonlinearpoisson` (`element.jl:386`) prints `"|d|=$(norm(d)), |r|=$(norm(r))"` for each Newton iteration.
- `show_progress` (`Adapode.jl:701`) would print `"$(t) out of $(b)"`, but it is unused.
- The results display through Cartan, Grassmann and AbstractAnalysis:
  - a LocalTensor as `1.0 ↦ -5.5568v₁ - 0.79512v₂ + 29.6733v₃`;
  - a `Limit` (from `orbit`) as `"$(last) (n → $n, Δ → $residual)"` (AbstractAnalysis `metric.jl:115-120`).

  These formats belong to the Grassmann/Cartan port.

---

## 6. Examples and expected outputs (golden candidates)

All numbers below are **[verified]**. Every item is also stored in the JSON goldens (§9).

### 6.1 `test/runtests.jl` (4 tests, all "does not throw")

1. `odesolve(Lorenz, x0, 2π, 7, Val(k), Val(4))` for k = 0..4 (`runtests.jl:4-11`). The Lorenz system is σ=10, ρ=28, β=8/3 with x0 = (10,10,10) and h = 2^-7. As-is final values:

| k | method | n | last state | last t |
|---|---|---|---|---|
| 0 | Heun | 805 | (−4.16727, 0.371473, 28.4616) | 6.28125 |
| 1 | RK4 | 805 | (−4.19136, 0.812192, 28.979) | 6.28125 |
| 3 | ABM4 | 805 | (−4.20968, 0.771291, 28.9666) | 6.28125 |

   k=2 and k=4 (the adaptive integrators) **return garbage times** in the unpatched code (B1). Patched ExplicitAdaptor{4} gives n = 204032, last t 6.275360107421875, last state (−4.52677, 0.702252, 29.4272). Patched MultistepAdaptor{4} gives n = 4046, last t 6.27490234375, last state (−4.51837, 0.782591, 29.4955).
2. `\(assemblemassload(pt, x->x[2]*sin(x[2]))...)` on `initmesh(0:1/5:1)`:
   `[-0.013863142513283086, 0.027726285026566166, 0.14136119936109193, 0.34143293906982763, 0.5256199485817251, 0.9993965029209823]`
3. `x->2x[2]*sin(2π*x[2])+3`:
   `[2.781999575909511, 3.43600084818098, 3.7565326704749373, 2.359237680923145, 0.5744627893266803, 4.212768605336659]`
4. Backward-Euler heat, 1D, 100 steps with h = 0.005: ξ[51] = 0.12723526290687, sum = 8.474801782948974, ξ[1] = 2.520524341237724e-7.
5. `adaptpoisson(refinemesh(0:0.25:1)..., 1, 0, x->exp(-100abs2(x[2]-0.5)))` produces the element-count sequence in §4.8 and 271 final nodes. The first nodes are `[0.0, 0.125, 0.1875, 0.25, 0.28125, 0.296875, 0.3046875, 0.3125, 0.3203125, 0.328125]`.

### 6.2 README (`README.md`)

| # | Snippet | Plot | Expected / verified |
|---|---|---|---|
| R1 | Lorenz(10,60,8/3) evaluated on `ProductSpace(-40:0.2:40, -40:0.2:40, 10:0.2:90)` (L57-61) | `streamplot(vf, gridsize=(10,10))`, 3D streamlines | renders [verified, `plots/lorenz_streamplot.png`] |
| R2 | `odesolve(IC(Lorenz(10,28,8/3), x0, 2π), MultistepIntegrator{4}(2^-15))` (L65-67) | `lines`: 3D curve, colour = speed (viridis) | n=205888, last (−4.0959, 0.817649, 28.824) [`plots/lorenz_abm4.png`] |
| R3 | Torus geodesic: `TorusParameter(60,60)`, `surfacemetric`, `secondkind`, `geodesic(torcoef, (1,1), (1,√2), 10π)`, `geosolve(ic, ExplicitIntegrator{4}(2^-7))`, `lines(torus.(sol))`, `totalarclength`, `@basis MetricTensor([1 1;1 1])`, `arclength` (L88-107) | 3D curve on the torus; arclength line plots | **fails in registered Cartan 0.4.16** (`TorusTopology(::ProductSpace)` MethodError). It is a Cartan-port test |
| R4 | Klein bottle geodesic, `KleinParameter(100,100)`, `wireframe(kle)` (L111-127) | 3D curve plus wireframe | Cartan-dependent |
| R5 | Upper half plane: 5 × `geosolve(halfplane, x0, v0, 10π, 7)` (L131-139) | `lines`/`lines!`: five semicircles | **Analytic**: the geodesic through (x0, y0) with direction (vx, vy) is a semicircle centred at c = x0 + y0·vy/vx with radius √((x0−c)² + y0²). The endpoints (x at y→0) and computed values (n=4022, t_end=31.4140625): (1,1),(1,2) → 5.2360680 (computed 5.236067993996536); (1,0.1),(1,2) → 1.4236068 (1.4236231); (1,0.5),(1,2) → 3.1180340 (3.1180341); (1,1),(1,1) → 3.4142136 (3.4142136); (1,1),(1,1.5) → 4.3027756 (4.3027756) [`plots/halfplane_geodesics.png`] |
| R6 | da Rios / binormal flow: `start.(TorusParameter(180))`, `darios(t, dt=tangent(fiber(t))) = hodge(wedge(dt, tangent(dt)))`, `odesolve(darios, x1, 1.0, 2^-11)` (L144-148) | `mesh(sol, normalnorm)`: surface swept by the curve | fails in the registered stack (Cartan convert error). The state is a TensorField (field ODE) |
| R7 | Leapfrog: `fprime(v) = dirichlet!(laplacian_chebyshevfft(v))`; `dt = 6/(N−1)²`; `LeapCondition(fprime, u0, u0, dt, tmax)`; `LeapIntegrator{2}(round(tplot/dt))` (L153-158) | – | – |
| R7a | 2D: `Chebyshev(41)²`, `ex = exp(−40((X−0.4)² + Y²))`, `leapfrog(ex, 41, 4, 1/30)` (L162-168) | `contour(lf, alpha=0.03)`: volume over (x,y,t); `surface(lf[:,:,10])` | size (41,41,119), gap = round(0.0333/0.00375) = 9, nplots = round(118.5) = 118; u_centre(t_end) = −0.07669699195422375, max\|u\| at t_end = 0.17276028814862793 [`plots/leapfrog_surface10.png`] |
| R7b | 3D: `Chebyshev(31)³` (L172-178) | `contour(lf[:,:,:,10], alpha=0.02, levels=5)` | not run (cost) |
| R8 | `x = TensorField(0:0.01:π)`; `wavedirichlet`/`waveneumann`/`waveperiodic(0*x, x*(1+cos x), 0.4)` and over `0:0.01:2π` (L185-191) | `lines` (u vs x) and `surface` (x × t) | N=315; wavedirichlet t=0.4: Σ = 115.04844254823666, u[158] = 0.6073610956148955; waveneumann: u[1] = −0.21917719965332974; waveperiodic: u[1] = −0.27979445138372055 [`plots/wave*.png`]. Series shape (315, 629) |
| R9 | 2D restwave on `ProductSpace(0:0.01:π, 0:0.01:π)`, `2fun` with `fun = exp(−100((x−1)² + (y−0.7)²))`, t = 2.1 and 3.1 (L194-201) | `surface` ×6 | t=2.1: dirichlet Σ = −259.9359171720508, u[100,80] = 0.06671123587457149; neumann Σ = 628.3185307179587; periodic Σ = 628.3185307179585 [`plots/restwavedirichlet_2.1.png`] |
| R10 | 3D restwave on `0:0.05:π`³ (L204-211) | `contour(…, alpha, levels)` | not run |
| R11 | `x = TensorField(−1:0.01:1)`; `heatdirichlet`/`heatneumann(box.(x), 0.001)`; series over 0:0.01:1; `heatperiodic(sin(πx)+2, 0.001)` (L214-220) | `lines`, `surface` | `box` is undefined in the packages; it is the user function box(x) = \|x\|<0.5 ? 1 : 0. heatdirichlet Σ = 99.00000000000003; heatperiodic Σ = 402.0000000000001, u[1] = 1.9858169530159797 [`plots/heat*.png`] |
| R12 | 2D heatdirichlet of box on (−1:0.01:1)², t = 0.01, 0.1 (L223-225) | `surface` | t=0.01: Σ = 9800.541276929966, centre 0.9990103761087851 |
| R13 | 3D heat contours (L228-230) | `contour` | not run |
| R14 | `L2Projector(t,f) = mesh(t, color=\(assemblemassload(t,f)...))` (L237-239). The README's `initmesh(…)[3]` must be `[1]` in the current Cartan | 1D mesh drawn as a polyline with markers, coloured by value | [`plots/l2proj.png`]; values as in §6.1 items 2–3 |
| R15 | Disk eigenmodes: MATLAB `circleg` mesh, `assemble(pt,1,1,0)`, KrylovKit `geneigsolve((A,M), 10, :SR)` (L244-251) | `mesh(mode[7]); wireframe!(pt)` | needs MATLAB. Reproduce with an own disk mesh; the smallest generalized eigenvalue is ≈ j₀₁² = 5.783 |
| R16 | `solveheat(triangle.(pt), (x->2x[2]).(pt), (x->1e6).(pe), range(0,0.6,101))` on `initmesh(0:0.01:1)` (L307-311) | `surface` over (x,t) (the current Cartan fails to plot it) | size (101,101); u[51,2] = 0.4285756604563396, u[51,end] = 0.12587667370150693, Σ u[:,end] = 8.38832030667821 |
| R17 | `adaptpoisson` (L329) | console | §6.1 item 5 |
| R18 | Airfoil: FlowGeometry `NACA"6511"`, MATLAB `decsg`, `solvepoisson`, `gtf = −gradient(tf)`, `solvetransportdiffusion(gtf, kf, 0.01, 1/50, …)` (L336-354) | `wireframe(pt)`, `streamplot(gtf, …)`, `mesh(tf2)` | needs MATLAB and FlowGeometry. Note that the README passes 5 arguments, where the last is a source/gD function, which differs from the signature `(tf, eκ, c, δ, gD, gN)` |
| R19 | TetGen `cubesphere` tetrahedral Poisson with a 3D streamplot (L359-367) | – | needs TetGen |

### 6.3 `examples/chaos.jl` (`odesolve(f, x0)` default: RK4, h = 2^-15, T = 2π, n = 205888)

Golden last states (full lists in `goldens/chaos.json`) [verified]:

| System | Parameters | Last state |
|---|---|---|
| Lorenz | (10, 28, 8/3) | (−4.0959, 0.817649, 28.824) |
| Lorenz | (10, 60, 8/3) | (7.77843, −9.8897, 65.8765) |
| DiskDynamo | (14.625, 1, 5) | (−0.00345545, −0.00326912, 0.199997) |
| Rössler | (1/5, 1/5, c = 2.4) | (−4.47463, −14.5173, 73.6109) |
| Rössler | c = 3.5 | (13.2537, −12.3986, 12.3927) |
| Rössler | c = 4.0 | (12.3425, −12.4569, 2.76011) |
| Rössler | c = 4.23 | (11.6721, −12.4373, 1.53444) |
| Rössler | c = 4.3 | (11.461, −12.4241, 1.30113) |
| Rössler | c = 5.0 | (9.38738, −12.1123, 0.344938) |
| Rössler | c = 5.7 | (7.55863, −11.5189, 0.145338) |
| Rössler | (0, 0, 12) | (7.94166, 10.321, 2.5e−32) |
| Rössler | (0, 0, 25) | (9.37508, 10.0373, 6.3e−68) |
| Rössler | (0.343, 1.82, 9.75) | (10.5455, −20.8037, 98.9162) |

Two examples in the file are broken and should be fixed in the port:
- `ChemicalKinetics` (chaos.jl:34-38) is called with 8 arguments but takes 7, and it uses an undefined `k5`.
- `Rossler4` (40-45) uses `x[4]` with a 3D x0.

### 6.4 Flow API outputs (Lorenz, T=1, h=2^-11) [verified]

| Call | Result |
|---|---|
| `Flow(L,1.0)(x0, ExplicitIntegrator{4}(2^-11,0))` | `1.0 ↦ (−5.5568, −0.79512, 29.6733)` |
| full RK4 or ABM4 with skip=1, last state | the same (n = 2049) |
| RK1, RK2, RK3 (skip 0) | (−5.32818, −0.881728, 29.1703), (−5.55659, −0.79501, 29.673), (−5.55681, −0.795119, 29.6733) |
| Heun | (−5.55656, −0.795067, 29.6729) |
| **Default** `Flow(L,1.0)(x0)` (Multistep, skip 0) | `(−5.62685, −0.810574, 29.7825)`, **wrong** (B3) |
| `Flow(L,−0.5)(x0, RK4 skip0)` | `−0.5 ↦ (1580.2, 28.1866, 1.71852)` (backward, unstable) |
| `Flow(L,1.0)(0.5 ↦ x0, RK4 skip0)` | `1.5 ↦ (−12.4816, −18.0618, 24.9994)`: integrated over [0, 1.5] (B5) |

---

## 7. Dependencies on other chakravala packages

**Grassmann**

- Imported explicitly (`Adapode.jl:22-24`, `element.jl:28`):
  - `value, vector, valuetype, tangent, list`
  - `Values, Variables, FixedVector` (StaticVectors re-exports)
  - `Scalar, GradedVector, Bivector, Trivector`
  - `norm, column, columns`
- Used without import:
  - `Chain`, `Chain{V,1}`, `Submanifold(N)`, `∇` (`Submanifold(N)(∇)` = the all-ones Chain), `Manifold`, `↓` (drop the first basis element)
  - `outer` (`outer(a,b)[i,j] = a_i b_j`, with ∇ acting as ones), `TensorOperator`, `DiagonalOperator`, `transpose`, `⋅`, `∧`, `curl` (`(1,1,1)×G`)
  - `invdet`, `det`, `vectors`, `affinehull` (via Cartan), `hodge`, `wedge` (README)
  - `@basis`, `MetricTensor` (README)

**Cartan**

- Imported explicitly (`Adapode.jl:26`, `element.jl:29-33`):
  - `resize, resize_lastdim!, extract, assign!, geodesic`
  - `points, pointset, edges, iterpts, iterable, callable, revrot`
  - `gradienthat, laplacian, gradient, assemblelocal!, weights, degrees, assembleincidence, incidence`
  - `assembleload, interp, pretni, interior, facesindices, edgesindices, neighbor, neighbors`
- Used without import, grouped by role:

| Role | Symbols |
|---|---|
| Fields and local values | `TensorField`, `LocalTensor`, `↦`, `base`, `fiber`, `point`, `localfiber`, `fibertype`, `Coordinate`, `Global{1}` |
| Mesh accessors | `fullpoints`, `fullcoordinates`, `immersion`, `fullimmersion`, `subelements`, `vertices`, `totalnodes`, `nodes`, `elements`, `sdims`, `mdims`, `topology`, `columns`, `adjacency` |
| Bundle types | `SimplexBundle`, `FaceBundle`, `SimplexTopology`, `discontinuous` |
| Geometry | `means`, `volumes`, `curls`, `gradient_2`, `affmanifold`/`affinemanifold`, `varmanifold`, `facetsigns` |
| Meshing | `initmesh`, `initmeshdata`, `refinemesh`, `refinemesh!`, `select`, `rms` |
| Product spaces | `⊕`, `×`, `ProductSpace`, `split` |
| Iteration | `orbit` (TensorField over a time vector) |
| Chebyshev | `Chebyshev`, `ChebyshevMatrix`, `derivetoeplitz2`, `toeplitz2`, `laplacian_chebyshevfft` |
| FFT | `rfftspace`, `fftspace`, `r2rspace`; the `rfft`, `irfft`, `fft`, `ifft`, `dct`, `idct` and `r2r` wrappers on TensorField |
| Differential geometry (README) | `TorusParameter`, `KleinParameter`, `surfacemetric`, `secondkind`, `totalarclength`, `arclength`, `normalnorm` |
| Plotting (MakieExt) | `graylines(!)`, `AbstractCurve`, `Components`, `VectorField` |

**MeshTopology** (reached via Cartan's `import MeshTopology: …`):
- `assemblelocal!` (§3.3 order)
- `assembleincidence` (lumped load)
- `interior(fixed, n) = sort!(setdiff(1:n, fixed))`
- `edgesindices`/`localedge`, `neighbors`, `facetsign(s)`, `incidence`, `degrees`, `interp(t, b, w=weights)` (nodal averaging)

Registered 0.1.0 has **unbound names** `fibertype`, `fiber` and `Grassmann` inside MeshTopology, so `assembleload`, `edgesindices` and `LagrangeP2` all throw until they are patched (`load.jl` injects them). Even after patching, `Cartan.edgesindices(::SimplexBundle)` and `Cartan.discontinuous` fail on the 4×4 square with a `size(::Global)` MethodError, while the 2×2 cases (Stokes and DIPG goldens) work. So `solvestokes` and `solvemaxwell` on larger meshes could not be oracle-tested; their spec in §4.7–4.8 is derived from the code.

**AbstractAnalysis**:
- `orbit(f, x, n::AbstractVector{Int})`: iterate f over n and return `Limit(x, x_n, len+1, d(x_n, x_{n−1}), f, d)`.
- `orbithold(f, x, n)`: iterate `xn = f(x, xn)` with x held fixed.
- `Limit`, `supnorm`, `extract`, `assign!` (last-dimension slice get and set), `resize_lastdim!` (ElasticArrays).

**External packages**:
- Needed: SparseArrays, LinearAlgebra.
- Weak extensions: FFTW and Makie.
- Through Cartan extensions: ToeplitzMatrices, needed by `polarlaplacian`.
- README only: KrylovKit, MATLAB, FlowGeometry, TetGen, MiniQhull.

---

## 8. Lean 4 porting notes

### 8.1 Types, indices and zero-cost dependent typing

| Julia | Lean | Index or runtime? |
|---|---|---|
| `Chain{V,1,Float64,n}` state | `Vec n := {a : FloatArray // a.size = n}` (proof erased), plus `class OdeState σ` with `add`, `smul`, and a fused `axpyFold (x : σ) (h : Float) (c : Array Float) (ks : Array σ) : σ` implementing `x + lin(h,c,ks)` in **one pass per component with the exact left-fold order**, plus `maxAbs`, `maxRelDiff` | n is an **index** (zero-cost) |
| `Chain(x,v)` geodesic state | `Vec (2n)`, or a pair instance `OdeState (σ × σ)` | index |
| TensorField state (field ODE) | an `OdeState` instance for grid functions (`FloatArray` with a shape) | runtime shape |
| `Val{o}` order | `ExplicitIntegrator (o : Fin 4)`, `MultistepIntegrator (o : Nat) (h : 1 ≤ o ∧ o ≤ 5)` | index / Prop field (erased) |
| Butcher tables | `structure Tableau (s : Nat) where a : Vector (Array Float) (s-1); b : Vector Float s; db : Vector Float s; ha : ∀ i, (a.get i).size = i+1` built from `(Int × Nat)` rationals | s is an index. Proofs of the row-shape, row-sum and order conditions are checked over exact rationals **at compile time** with `decide` / `native_decide`. This would have caught the Fehlberg and Cash–Karp typos |
| ABM ring buffer | `Vector σ (o+1)` with slot `Fin (o+1)`; `ring` via `Fin` arithmetic, discharged by `omega` | index |
| `LocalTensor` | `structure Stamped (σ) where t : Float; x : σ` | – |
| Trajectory | `structure Traj (σ) where ts : FloatArray; xs : Array σ` (adaptive grows with `push`) | runtime |
| Skip mode | `inductive Output \| final \| full \| every (k : Nat) (hk : 2 ≤ k)` | runtime |
| Mesh | `structure Mesh (d : Nat) where pts : FloatArray` (d coordinates per point, **drop the homogeneous 1**) and `elems : Array (Vector (Fin np) (d+1))` | d is an index; np is a structure field with `Fin np` node ids, which removes bounds checks |
| Local matrices | `Mat (d+1)` as a `FloatArray` of size (d+1)² in column-major order | index |
| Global sparse | COO triplets in element order → CSR, summing duplicates **in insertion order** (reproduces Julia's floating-point sums) | runtime |

Keep these as runtime values, not types: h, tmax, the error thresholds, step counts, mesh sizes (as fields plus proofs, not type indices, to avoid friction), and the frequency grids.

### 8.2 How Julia gets its speed and what Lean should do

- Julia specialises on `Val{o}` and `@pure` table lookups (`Adapode.jl:231-233, 261-262`), keeps stage vectors in stack-allocated `Values`/`Variables`, and uses `@inbounds`, UMFPACK/CHOLMOD for sparse `\`, FFTW, and `@threads` (MeshTopology `neighbors`, `jumps`).
- Measured baselines, Julia 1.13, Lorenz, T=2π, h=2^-15, 205888 steps [verified with `bench.jl`]:

| Method | Time | Allocated |
|---|---|---|
| RK4 (skip 1) | 372 ms | 253 MiB (`butcher` allocates) |
| ABM4 | 19.5 ms | 49 MiB |
| Heun | 5.1 ms | 4.7 MiB |
| Dormand–Prince adaptive (tol exponent 10) | 35 ms | 18 MiB |
| `assemblestiffness`, 8192 triangles | 24.5 ms | – |
| `solvepoisson`, 8192 triangles | 37.6 ms | – |

  **Lean targets:** at least 5× faster on RK (fused `axpyFold`, one `FloatArray` allocation per stage, `@[specialize]` on the RHS closure, `@[inline]` on `rkstep` for constant tables), and parity on ABM and assembly.
- Hot paths:
  1. the stage loop in `rkstep`;
  2. the ABM PECE step;
  3. `assemblelocal!` scatter;
  4. sparse solve;
  5. FFT/DCT/DST.

  Use `FloatArray.uset`/`uget` with `Fin` proofs, and ensure unique ownership for in-place `set!`.
- The sparse direct solver is the biggest missing piece if the Cartan port lacks one.
  - Minimum viable: CSR, plus Cholesky (skyline or AMD-free left-looking) for the SPD Poisson/heat/Robin systems, plus sparse LU with partial pivoting for convection, Stokes (indefinite) and the complex Maxwell system.
  - Goldens compare at a relative tolerance of 1e-10, not bitwise.
  - A fallback: dense LU for n ≤ 2000, which covers all goldens.
- FFT: DCT-II/III, DST-II/III, rfft and irfft for arbitrary N (the goldens include N = 315 and 201). Implement Bluestein or mixed-radix, or an O(N²) reference first, which is fine for the goldens.

### 8.3 Suggested module decomposition (≈4,300 LOC)

| Module | Contents | ~LOC |
|---|---|---|
| `Adapode/Rat.lean` | tiny exact rational type for tables and order-condition proofs (or `Std`/Batteries `Rat` if available) | 80 |
| `Adapode/Tableau.lean` | CB, CBA (corrected **and** `compat` variants), CAB, CAM, Gauss; order-condition theorems via `decide`; Float projections | 300 |
| `Adapode/State.lean` | `OdeState` class; instances for `Vec n`, pairs, grid fields; `axpyFold`, `maxAbs`, `maxRelDiff` | 200 |
| `Adapode/Integrator.lean` | integrator structures, `tol` exponent/step constructors, `TimeStep`, `checkstep`, `timeloop` | 200 |
| `Adapode/Flow.lean` | Flow, FlowApprox, FlowIntegral, InitialCondition, LeapCondition, `exp` of a vector field, call forms (fixed semantics) | 180 |
| `Adapode/ODE/Explicit.lean` | `rkstep`, Heun, the skip-0/1/k drivers | 200 |
| `Adapode/ODE/Multistep.lean` | RK4 bootstrap, ring-buffer PECE; skip-0/1/k (fixed) | 220 |
| `Adapode/ODE/Adaptive.lean` | adaptive RK and ABM with the §4.3/§4.4 controller (plus a `compat` flag for the truncate-before-end quirk) | 250 |
| `Adapode/ODE/Leapfrog.lean`, `Geodesic.lean` | §4.5, §4.6, `geosolve` | 160 |
| `Adapode/FEM/Local.lean` | mass/stiffness/convection/SD/CR/elastic/Nédélec/P1/P2/Gauss/isoparametric | 400 |
| `Adapode/FEM/Assemble.lean` | global assembly, lumped load, Robin, divergence, DIPG, Stokes matrix | 400 |
| `Adapode/FEM/Solve.lean` | Poisson, transport(+diffusion), heat, wave, bistable ×2, nonlinear Poisson, elastic (fixed), Stokes, NS (fixed), Maxwell, DIPG, adaptpoisson (returns a log) | 650 |
| `Adapode/Spectral/Transforms.lean` | DCT/DST/rfft (if not provided by the Cartan port) | 350 |
| `Adapode/Spectral/Multipliers.lean` | multipliers, periodic/neumann/dirichlet solvers, time series | 250 |
| `Adapode/Spectral/Chebyshev.lean` | helmholtz, biharmonic, orrsommerfeld, polarlaplacian (sign-fixed), solveiteration (with max iterations), reshape helpers | 300 |
| `Adapode/Plot.lean` | LeanPlot adapters: trajectory → 2D/3D polyline coloured by speed; grid field → surface/heatmap; x×t field → surface; 1D mesh function → polyline + markers; streamlines from seeds; advected curves | 200 |
| tests | JSON golden loaders and comparisons | 400 |

### 8.4 Plot mapping for LeanPlot co-development

Each README figure reduces to a small set of primitives:

| Primitive | Figures |
|---|---|
| Polyline with per-vertex scalar colour (speed = ‖x_{i+1} − x_i‖/Δt) | R2, R5, `lorenz_*.png`, `halfplane_geodesics.png` |
| 1D line u(x) | R8, R11, R14 |
| Surface z = u(x,y) or u(x,t) | R8 series, R9, R12, R16, R7a slice |
| Isosurface/volume contours | R7a/b, R10, R13 |
| Streamplot | R1, R18, R19 |
| Triangle mesh coloured by nodal value, plus wireframe | R14, R15, R18 |

Reference PNGs are in `.../adapode_oracle/plots/`: `lorenz_rk4`, `lorenz_abm4`, `lorenz_streamplot`, `halfplane_geodesics`, `wave{dirichlet,neumann,periodic}_t0.4`, `wavedirichlet_surface`, `heatdirichlet_box`, `heatperiodic_sin`, `heatneumann_surface`, `restwavedirichlet_2.1`, `l2proj`, `leapfrog_surface10`, `leapfrog_contour`.

### 8.5 Julia-specific parts to skip or redesign

- **Skip or replace:**
  - Requires.jl and `__init__` (`Adapode.jl:703-712`); the `@pure`/`Val` plumbing.
  - The `integrate`, `heun2`, `odesolve2`, `multistep2!`, `predictcorrect2` and `initsteps2` legacy paths.
  - The `geo` field.
  - `show_progress`; `time(x) = x[1]`.
  - `shapemultilinear`'s recursive forwarder.
- **Replace with concrete types:**
  - The overloaded `bc` hook, which is applied inconsistently: sometimes to a bare Chain, sometimes to a LocalTensor. Make it `bc : σ → σ` applied to the state after every step, plus to the initial state(s).
  - The Cartan `TensorField` generality: take plain arrays plus mesh or grid descriptors. `solvewave` should receive `(boundaryNodes, timeGrid, bcValues)` explicitly.
  - `orbit`/`Limit`/`SequenceArray` laziness: return concrete arrays, or a `Limit`-like struct holding the final iterate and residual.
  - The printing in `adaptpoisson` and `solvenonlinearpoisson`: return logs.

### 8.6 Bugs found (fix in Lean; keep `compat` switches only where goldens need them)

| # | Where | Bug | Evidence |
|---|---|---|---|
| B1 | `Adapode.jl:433, 446, 456, 467` + Cartan `setindex!` (Cartan.jl:241-245) | Adaptive integrators store only fibers, never the time points. The time base is an uninitialised `Vector{Float64}`, so the loop exits randomly (garbage times such as 3.96e−19 or 2.1e−314) | [verified] fixed by `patch.jl` |
| B1b | `Adapode.jl:394` | The adaptive ABM bootstrap `assign!(x, i+j, fiber(xi))` also drops the times | [verified] fixed by `patch2.jl` |
| B2 | `Adapode.jl:689-692, 699` | `timeloop!` stops once `tmax − t ≤ hmax` **without the final step**, then `truncate!(x, i−1)` drops the last accepted point. Intended: step exactly to tmax and keep all accepted points | [verified] |
| B3 | `Adapode.jl:533-543, 378-387` | MultistepIntegrator with skip=0: `initsteps!(::LocalTensor)` computes the history but discards the advanced state, so the ABM starts again from x0 while the time label is t0 + (o−1)h. The default `(Φ::Flow)(x0)` uses this path | [verified] −5.62685 vs −5.5568 |
| B4 | `Adapode.jl:550-560, 530` | MultistepIntegrator with skip=k>1: `TimeStep(I.tol)` ignores skip, so the grid has step h while each output advances k·h, and x[2..o] are uninitialised | [verified] output zeros |
| B5 | `Adapode.jl:162` | `Flow(x0::LocalTensor)` integrates [0, t0+T] instead of [t0, t0+T] | [verified] |
| B6 | `Adapode.jl:164-171` | The loop variable `i` shadows the integrator, so the default integrator is always used | [verified] |
| B7 | `Adapode.jl:483-490` | EulerHeun ignores `skip` when stepping but the grid uses h·skip | code |
| B8 | `Adapode.jl:663-666` | Leapfrog: `nplots = round(...)` can make the data length differ from the range length | code |
| B9 | `Adapode.jl:352-370` | `odesolve2`: the ring of size o is written twice per step, so AB_{o−1} mixes f(p) and f(x) values | analysis |
| B10 | `constants.jl:40, 46` | Tableau typos: Fehlberg a₆₃ = +3544/2565 should be −3544/2565; Cash–Karp a₄₁ = 3/40 should be 3/10 | [verified] orders §3.2 |
| B11 | `element.jl:293-314` | `assembleelastic`: (i) passes `(λ, μ)` into `elasticstrain(μ, λ, …)`, swapping the Lamé parameters; (ii) scatters the interleaved 6×6 local matrix at DOFs `[x1,x2,x3,y1,y2,y3]`; (iii) `F[t] .= …` overwrites instead of accumulating | [verified] ‖K·u_rigid‖ = 5.64 vs 4.7e−16 for the corrected K; K equals the "swapped + x-first" matrix exactly |
| B12 | `element.jl:302-311` | Load uses the nodal force of each element's own nodes (fine) but the `.=` bug above loses sums | [verified] |
| B13 | `element.jl:82` + `Cartan.iterable` | `assemblemass(t)` builds a constant coefficient of length #nodes indexed per element, so it throws BoundsError when nt > np (every 2D mesh finer than 2×2) | [verified] |
| B14 | `element.jl:593-619` | 2D `jumps` calls `gradient_2(u, m, g)` with a Vector (no such method), indexes `F[k]` (nodal) by element, and has an unsquared norm | [verified MethodError] |
| B15 | `element.jl:259-272` | `solvenavierstokes`: `k` is undefined and `UVold` is never updated. The intended loop is in the commented block at lines 273-289 | code |
| B16 | `element.jl:627-654, 806-832, 781` | `edgeresiduals` is broken; `gradientmultilinear` lacks 1/2^d; `shapemultilinear(::Values...)` recurses forever | code |
| B17 | `grid.jl:177-212` + Cartan `ChebyshevMatrix(::Chebyshev)` | Odd-derivative sign error in `biharmonic`, `orrsommerfeld` and `polarlaplacian` | [verified] vs Trefethen |
| B18 | Cartan `spectral.jl:42, 53-56` | `rfftspace(ProductSpace)` uses `v[2]` for dimension 1; `fftspace` has no negative frequencies, which affects multi-D periodic and Schrödinger | code |
| B19 | FFTWExt 53; grid.jl 256-282 | `fullwaveneumann` is not imported; scalar-t `biharmonicneumann`/`biharmonicdirichlet` do not exist; `solvenonlinearhelmholtz(f,k,N::Int)` calls the undefined `nonlinearhelmholtz` | code |
| B20 | `Adapode.jl:88, 197-199, 303, 409, 419` | `AbstractIntegrator()` default is a Type; `typoef`/`n` in FlowIntegral(Vector); `h` is undefined in the FlowApprox `multistep!` and `initsteps!` | code |
| B21 | `element.jl:185-190` | `solveheat` adds Robin R to M, so it is not scaled by h (quirk; keep for compat) | analysis |
| B22 | `examples/chaos.jl:34-45` | `ChemicalKinetics` arity and `k5`; `Rossler4` with a 3D x0 | code |

---

## 9. Oracle test plan

### 9.0 Committed oracle (2026-09-25)

The ODE goldens are committed under `oracle/golden/adapode/` (generator `oracle/adapode/gen.jl`
with `oracle/adapode/sections/*.jl`; loader and patches `oracle/adapode/load.jl`; defects
`oracle/adapode/defects.toml`). The loader `include`s Adapode.jl master from `ADAPODE_SRC`
(default `~/chakravala/Adapode.jl/src/Adapode.jl`), because the registered 0.3.13 lacks the Flow
API. The benchmark twin is `oracle/bench/adapode.jl` (suite `adapode`, run in its own process).
Defect findings from the port:

- B8 is confirmed by a golden: Julia's leapfrog time axis is one point short of its data.
- `odesolve` with a TensorField state and skip ≥ 1 fails in Cartan 0.4.16.
- `Values(Values(...))` copy quirk in `CBA[1]` and `Gauss[1]`.

The notes below (9.1 onward) describe the exploratory scratch oracle that preceded it.

### 9.1 How to run the oracle

- Directory: `/private/tmp/claude-502/-Users-alokbeniwal-Grassmann/c6cc2308-bfca-4b9a-ad33-d89b110132a8/scratchpad/notes/adapode_oracle/`
- `load.jl` does three things:
  - loads registered Grassmann and Cartan;
  - injects the missing `fibertype`, `fiber`, `base`, `points` and `fullpoints` bindings, plus a `Grassmann` binding, into MeshTopology;
  - `include`s **Adapode master** `src/Adapode.jl`.
- `patch.jl` and `patch2.jl` provide the adaptive time-point storage fixes (B1 and B1b). With them, the Julia run equals the §4.3/§4.4 spec bit-for-bit.
- `loadfft.jl` additionally loads FFTW from a stacked env, then evaluates `ext/FFTWExt.jl` against the included module. The stacked env is `.../scratchpad/adapode_probe/fftenv`, which holds FFTW and ToeplitzMatrices; it is separate from the shared juliaenv, which was not modified.
- Commands:
  - `julia --startup-file=no --project=<juliaenv> oracle_core.jl`
  - `JULIA_LOAD_PATH="@:<fftenv>:@stdlib" julia --startup-file=no --project=<juliaenv> oracle_spectral.jl`
  - `julia … oracle_chaos.jl`
  - All finish in about 60 s in total.

### 9.2 Goldens produced (`goldens/*.json`) and how to compare

| File | Contents | Compare |
|---|---|---|
| `tables.json` | CB, CBA (as-is), CAB, CAM, Gauss; TimeStep fields for h ∈ {2^-7, 2^-11, 2^-15, 1e-5} | bitwise (compat tables). Order-condition proofs cover the corrected tables |
| `ode_fixed.json` | Problems: `lorenz` (x0 = 10,10,10), `osc` (x'' + 0.1x' + x = 0, x0 = (1,0)), and `nonauto` (x' = x·cos t + t, exercising stage times). h = 2^-8, T = 1. Stored: RK1–4 skip 0/1/4, Heun, ABM1–5 skip 1 (every 16th state and the last), and `ABM4_skip0_ASIS` (B3, compat only) | **bitwise** (op order §4). Grid times for dyadic h are exact |
| `ode_adaptive.json` | `osc` and `nonauto`, tol exponent 7, T=1; RKA1–5 and ABMA1–5 (patched oracle): n, first 20 and last 5 (t, x) | bitwise against the Lean *compat* controller (B2 quirk on). The fixed controller is checked separately against an analytic solution with rel. error ≤ 1e-5 |
| `geodesic_halfplane.json` | 5 cases: n, first 10, every 256th, last, analytic endpoint | bitwise for the trajectory; endpoint within 3e-5 of the analytic value |
| `leapfrog.json` | Leap1 and Leap2 with fprime(v) = −Kv, K = tridiag(−1,2,−1), dt 0.01, gap 5, T 1 | bitwise |
| `chaos.json` | 13 systems from examples/chaos.jl, RK4, h = 2^-15: last state and every 4096th | bitwise |
| `fem1d.json` | 0:1/5:1 nodes, volumes, stiffness, mass, lumped load, massload b, L2 projections, Robin; runtests heat; README solveheat (slices 2, 51, end); full adaptpoisson iteration log (nt, ϵ, max η, refined set, ξ) and final nodes | matrices bitwise (assembly order); solves rel. 1e-10; adaptpoisson sets exact, ϵ rel. 1e-9 |
| `fem2d.json` | squaremesh(2) and squaremesh(4) (`mesh2d.jl`: x-fastest nodes, cells split a-b-c / a-c-d) with per-element b_k = (1+0.1k, 0.5−0.05k). Stored: points, triangles, boundary edges, areas, gradients, stiffness (c=1 and c=1+x), mass, loads, convection, SD, Robin (κ=1e6, gD=x), Poisson, transport, neighbours, trinormal lengths, CR gradients, P1 quadrature mass/stiffness, nonlinear Poisson Newton history + solution, bistable Picard/Newton (IC 0.5 cos πx cos πy, 6 steps of 0.1), elastic as-is K/F, and for n=2 also the Stokes matrix, DIPG P/S and the DIPG solution (β=10) | assembly bitwise; solves rel. 1e-10; Newton ‖d‖ history rel. 1e-6 on the first 3 iterates |
| `chebyshev.json` | Chebyshev(5) points; D both conventions; helmholtz(5; k = 0, 2); Poisson e^{4x} (N=17); nonlinear e^u (N=17); biharmonic(8) as-is | 1e-12 abs |
| `spectral.json` | Frequency grids (r2r, r2r-DST, rfft, fft); multiplier samples; wave dirichlet/neumann/periodic/fullwave at t=0.4; heat/riesz(1.5)/restwave × dirichlet/neumann/periodic of box and sin(πx)+2 at t ∈ {0.001, 0.1}; biharmonic periodic; Schrödinger t=0.1; 2D restwave (dirichlet, neumann, periodic-ASIS) and heatdirichlet on a 32×32 grid | 1e-12 abs (FFT round-off) |
| `chebyshev_fft.json` | polarlaplacian(7,11) as-is matrix; the 10 smallest eigenvalues as-is and fixed; toeplitz2(8); Orr–Sommerfeld rightmost eigenvalue fixed and as-is for N = 60, 100; README 2D leapfrog: size, centre series, slice 10, max\|u\| series | matrices 1e-12; eigenvalues 1e-8; leapfrog 1e-10 |

### 9.3 Additional input distributions to add as the port grows (seeded, deterministic)

**ODE single steps.** For each tableau:
- 200 random states x ∈ U[−10,10]^n with n ∈ {1, 2, 3, 6};
- t ∈ U[0,5], h ∈ {2^-4, …, 2^-12};
- RHS from the family `f(t,x) = A x + sin(B x) + c·t`, with seeded A, B and c.

Compare `rkstep` and one PECE step bitwise.

**Controller edge cases:**
- negative durations;
- tmax an exact multiple of h, and tmax = h/3;
- h below hmin (the clamp);
- h0 ≤ 1e-4 (hmax = 1e-4 allows doubling);
- skip ∈ {0, 1, 2, 7}.

**Meshes:**
- squaremesh(n) with n ∈ {2, 4, 8, 16};
- the same meshes with interior nodes jittered by U[−0.2h, 0.2h] (seeded), to break symmetry and exercise general ∇φ;
- 1D graded meshes (x = (i/n)² for n ∈ {5, 20});
- per-element coefficients c ∈ U[0.5, 2], a ∈ U[0, 1], b ∈ U[−1,1]²;
- Robin κ ∈ {1, 1e3, 1e6}, gD = sin(πx)cos(πy), gN = x.

**Spectral:**
- N ∈ {16, 17, 64, 315} (even/odd, and non-power-of-2 for Bluestein);
- t ∈ {0, 1e-3, 0.1, 0.4, 2.1};
- s ∈ {0.5, 1, 1.5, 2} for Riesz;
- 2D grids 17×23 (non-square, to expose B18 when fixed vs compat).

**Chebyshev:**
- N ∈ {5, 9, 17, 33};
- Helmholtz with k ∈ {0, 1, 5}, f ∈ {e^{4x}, sin(πx)};
- fixed-sign biharmonic compared with Trefethen p38 (u⁗ = e^x; exact solution known);
- Orr–Sommerfeld against the literature value −7.82e-5 − 0.26157i;
- polar Laplacian eigenvalues against Bessel zeros j²_{mn}.

**Bug policy:**
- Every as-is (buggy) behaviour that a golden encodes is tagged `_ASIS`.
- The Lean default implements the fixed semantics.
- A `compat := true` flag exists only in the test harness paths (tableaux, the B2 controller quirk, the heat Robin scaling B21, spectral frequency grids B18).
