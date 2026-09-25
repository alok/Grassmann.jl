import Adapode.ODE.State
import Adapode.ODE.Integrator
import Adapode.ODE.Flow
import Adapode.ODE.Explicit
import Adapode.ODE.Multistep
import Adapode.ODE.Adaptive
import Adapode.ODE.Leapfrog
import Adapode.ODE.Geodesic

/-!
# Adapode ODE solvers

The time-stepping half of Adapode.jl (`src/Adapode.jl`, `src/constants.jl`, `examples/chaos.jl`):

| module | content |
|---|---|
| `Adapode.ODE.State` | `OdeState` (flat views of `Chain`/`Half`/`Multivector`/`Values`/`TensorField`/`Phase` states), Julia's `weights` and the fused step kernels |
| `Adapode.ODE.Integrator` | `Tol`, the integrator types, `Integrator` (Julia `AbstractIntegrator`), `TimeStep` |
| `Adapode.ODE.Flow` | `Flow`, `FlowApprox`, `FlowIntegral`, `InitialCondition`, `LeapCondition` |
| `Adapode.ODE.Explicit` | fixed-step Runge–Kutta and Heun |
| `Adapode.ODE.Multistep` | fixed-step Adams–Bashforth–Moulton with the RK4 bootstrap |
| `Adapode.ODE.Adaptive` | embedded pairs and adaptive ABM with Adapode's controller |
| `Adapode.ODE.Leapfrog` | leapfrog and Störmer–Verlet |
| `Adapode.ODE.Geodesic` | geodesic equations from Christoffel symbols |
-/
