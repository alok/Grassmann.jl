import Tests.Adapode.Problems

/-!
# Fixed-step integrators against Julia (`fixed.json`)

Explicit Runge–Kutta of orders 1–4 (`skip` 0, 1, 4), Heun (`skip` 1, and Julia's single step per
point for `skip = 4`, B7 `compat`), Adams–Bashforth–Moulton of orders 1–5, Julia's `skip = 0`
multistep path (B3 `compat`), backward integration, non-dyadic steps (grid times against
accumulated times) and a duration that is not a multiple of the step, on the four problems of
`Tests.Adapode.Problems`: every time and every state coefficient bit for bit.

The `spin` problem multiplies multivectors: its right-hand side is Grassmann's geometric product
(the generated `ℝ3` kernel here, Grassmann.jl's generated code in Julia), whose accumulation
order may differ from Julia's in the last bit; it is compared with `rtol = 1e-13`.
-/

open Lean Tests.Small JuliaBase Adapode

namespace Tests.AdapodeTests.Fixed

/-- Run one golden case. -/
def runCase (c : Json) : TestM Unit := do
  if (c.getObjVal? "E").isOk then return
  let problem ← gStr c "problem"
  let method ← gStr c "method"
  let o ← gNat c "order"
  let h ← gFloatAt c "h"
  let skip ← gNat c "skip"
  let tmax ← gFloatAt c "tmax"
  let compat ← gBool c "compat"
  let label := s!"{problem} {method}{o} h={fmt h} skip={skip} tmax={fmt tmax}{if compat then " compat" else ""}"
  match mkIntegrator method o h skip compat with
  | none => check label false fun _ => "no integrator"
  | some I =>
    match runProblem problem I tmax with
    | none => check label false fun _ => "unknown problem"
    | some (ts, xs) =>
      checkEq s!"{label} n" (ts.size) (← gNat c "n")
      checkBits s!"{label} t" ts (← gFloatsAt c "t")
      if problem == "spin" then checkClose s!"{label} x" xs (← gFloatsAt c "x") 1e-13 1e-300
      else checkBits s!"{label} x" xs (← gFloatsAt c "x")

/-- Run the fixed-step goldens. -/
def run : TestM Unit := do
  let j ← load "fixed"
  for c in ← gArr j "cases" do runCase c

end Tests.AdapodeTests.Fixed
