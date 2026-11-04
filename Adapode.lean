import Adapode.Constants
import Adapode.ODE
import Adapode.Element
import Adapode.Grid

/-!
# Adapode: adaptive ODE (and, later, PDE) solvers

Lean port of Michael Reed's Adapode.jl (master `91e8516`, version 0.3.14; semantics, citations and
defects in `docs/port-notes/adapode.md`). Adapode is the numerics layer over Cartan (fields over
meshes and grids) and Grassmann (the fiber algebra): time stepping of ODEs on Grassmann states or
whole `TensorField`s, and finite-element and spectral PDE solvers.

This port covers the ODE machinery, bit for bit with the Julia oracle (`oracle/adapode/gen.jl`,
`Tests/Adapode`):

```lean
open Adapode Grassmann
-- Julia: ic = InitialCondition(Lorenz(10.0,28.0,8/3), Chain(10.0,10.0,10.0), 2π)
--        odesolve(ic, MultistepIntegrator{4}(2^-15))
def ic := InitialCondition.of (lorenz 10 28 (8 / 3)) chaosStart
#eval (odesolve ic (.multistep (MultistepIntegrator.new 4 15))).lastFlat
-- Julia: odesolve(Lorenz(10.0,28.0,8/3), Chain(10.0,10.0,10.0))   (RK4, h = 2^-15)
#eval (odesolveCode (lorenz 10 28 (8 / 3)) chaosStart).lastTime
-- in-place system (no allocation per step) with the adaptive Dormand–Prince pair
#eval (odesolve ⟨.into (fun _ x o => lorenzInto 10 28 (8 / 3) x o), chaosStart, 0⟩
        (.explicitAdaptor (ExplicitAdaptor.new 5 10))).lastTime
```

* `Adapode.Constants`: the Butcher and Adams tables (`CB`, `CBA`, `CAB`, `CAM`, `Gauss`) as exact
  rationals with kernel-checked order conditions, and Julia's `Float64` values.
* `Adapode.ODE`: states, integrators, flows, the fixed-step, multistep, adaptive, leapfrog and
  geodesic solvers, `odesolve`, and the `examples/chaos.jl` systems.

* `Adapode.Element`: P1 finite elements on Cartan `SimplexBundle`s (intervals, triangles from
  `Cartan.Mesher`, tetrahedra): mass, stiffness, convection, streamline-diffusion, mass-load and
  Robin assembly in Julia's summation order, `solveDirichlet`, `solvePoisson`, `poisson`,
  `solveTransport`, `solveTransportDiffusion`, `solveHeat`, the 1-D `adaptPoisson` loop,
  `solveWave`/`solveWaveDirichlet`, Allen–Cahn (`solveBistable`, `solveBistableNewton`),
  `solveNonlinearPoisson`, plane-strain elasticity, Crouzeix–Raviart Stokes (`solveStokes`) and
  discontinuous Galerkin Poisson (`solvePoissonDIPG`), and P2 elements with isoparametric
  quadrature (`lagrange`, `assemblePN`, `solvePoissonPN`), and Maxwell with Nédélec edge elements
  (`solveMaxwell`, real `κ²`) (checked against the Julia values of port
  notes §4.8, §6.1–6.2 and against second-order convergence, d'Alembert and the patch test).

* `Adapode.Grid`: the spectral solvers of `src/grid.jl` and `ext/FFTWExt.jl`: heat, Riesz,
  biharmonic, rest-wave, wave and full-wave flows under periodic (`rfft`), Neumann (DCT) and
  Dirichlet (DST) conditions in any dimension, Schrödinger flow, and their time series (checked
  against the README values R8, R9, R11, R12 and the semigroup, conservation and unitarity laws).

**Pending** (port notes §2.6-2.7, §4.7-4.10): Navier–Stokes, complex-κ Maxwell and the 2-D `jumps`
indicator of `src/element.jl`, and the Chebyshev collocation operators of `src/grid.jl`
(Helmholtz, biharmonic, Orr–Sommerfeld, polar Laplacian).
-/
