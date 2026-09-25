import Adapode.Constants
import Adapode.ODE

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

**Pending** (port notes §2.6-2.7, §4.7-4.10): the finite-element solvers of `src/element.jl`
(assembly of mass/stiffness/convection/SD/Robin matrices, Poisson, transport, heat, wave, Stokes,
Navier–Stokes, elasticity, Maxwell, DIPG, bistable and nonlinear Poisson, `adaptpoisson`) and the
spectral solvers of `src/grid.jl`/`ext/FFTWExt.jl` (Fourier/DCT/DST multipliers, Chebyshev
Helmholtz/biharmonic/Orr–Sommerfeld/polar Laplacian). They need Cartan's simplex geometry
(`volumes`, `gradienthat`, `means`, `refinemesh`), a sparse direct solver, Cartan's FFT/DCT/DST
wrappers and frequency grids (`r2rspace`, `rfftspace`, `fftspace`), and `ChebyshevMatrix`/`Chebyshev`
grids (Cartan/Diffgeo, Cartan/Grid, Cartan/Element, Cartan/Spectral).
-/
