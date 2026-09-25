import Tests.Adapode.Problems

/-!
# Adaptive integrators against Julia (`adaptive.json`)

`ExplicitAdaptor{1:5}` and `MultistepAdaptor{1:5}` with Julia's controller (`compat := true`: the B2
end of integration and its preallocation bookkeeping), on the four problems with `tol = 7`, on
`osc`/`nonauto` with `tol = 10`, and with `h₀ = 1e-4` (where the step may double) for the fifth
orders: the number of points, the whole step sequence and every state bit for bit (`digest`), and
the first and last points explicitly. The `spin` problem (geometric products) is compared on its
step sequence and with `rtol = 1e-12` on the states.
-/

open Lean Tests.Small JuliaBase Adapode

namespace Tests.AdapodeTests.Adaptive

/-- Run one golden case. -/
def runCase (c : Json) : TestM Unit := do
  if (c.getObjVal? "E").isOk then return
  let problem ← gStr c "problem"
  let method ← gStr c "method"
  let o ← gNat c "order"
  let h0 ← gFloatAt c "h0"
  let tmax ← gFloatAt c "tmax"
  let label := s!"{problem} {method}{o} tol={← gStr c "tol"}"
  match mkIntegrator method o h0 1 true with
  | none => check label false fun _ => "no integrator"
  | some I =>
    match runProblem problem I tmax with
    | none => check label false fun _ => "unknown problem"
    | some (ts, xs) =>
      let n ← gNat c "n"
      checkEq s!"{label} n" ts.size n
      if ts.size != n then return
      let d := xs.size / n
      let th ← gFloatsAt c "t_head"
      let tt ← gFloatsAt c "t_tail"
      checkBits s!"{label} t head" (sub ts 0 th.size) th
      checkBits s!"{label} t tail" (sub ts (n - tt.size) tt.size) tt
      let xh ← gFloatsAt c "x_head"
      let xt ← gFloatsAt c "x_tail"
      if problem == "spin" then
        checkClose s!"{label} x head" (sub xs 0 xh.size) xh 1e-12 1e-300
        checkClose s!"{label} x tail" (sub xs (n * d - xt.size) xt.size) xt 1e-12 1e-300
      else
        checkBits s!"{label} x head" (sub xs 0 xh.size) xh
        checkBits s!"{label} x tail" (sub xs (n * d - xt.size) xt.size) xt
        let dg ← gStr c "digest"
        let got := digest ts xs
        check s!"{label} digest" (got == dg) fun _ => s!"got {got}, expected {dg}"

/-- Run the adaptive goldens. -/
def run : TestM Unit := do
  let j ← load "adaptive"
  for c in ← gArr j "cases" do runCase c

end Tests.AdapodeTests.Adaptive
