import Adapode.Constants
import Adapode.ODE

/-!
# Adapode: adaptive ODE (and, later, PDE) solvers

Lean port of Michael Reed's Adapode.jl (master `91e8516`, version 0.3.14; semantics, citations and
defects in `docs/port-notes/adapode.md`).

* `Adapode.Constants`: the Butcher and Adams tables (`CB`, `CBA`, `CAB`, `CAM`, `Gauss`) as exact
  rationals with kernel-checked order conditions, and Julia's `Float64` values.
* `Adapode.ODE`: states, integrators, flows, and the fixed-step, multistep, adaptive, leapfrog and
  geodesic machines.
-/
