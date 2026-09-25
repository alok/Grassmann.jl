import Tests.Adapode.Problems

/-!
# `examples/chaos.jl` against Julia (`chaos.json`)

The default `odesolve(f, x0)` (RK4, `h = 2^-15`, `t ∈ [0, 2π]`, 205 888 points) of every system of
the example file (with the two broken ones fixed, B22): the point count, the last time and state,
every 4096-th state, and the whole trajectory bit for bit (`digest`). The Lorenz, disk dynamo and
Rössler systems are also run in their in-place forms (`Flow.into`), which must give the same bits.
-/

open Lean Tests.Small JuliaBase Adapode Grassmann DirectSum Cartan

namespace Tests.AdapodeTests.Chaos

/-- `(times, states)` of a result. -/
def flatOf {σ : Type} [OdeState σ] (r : Result σ) : FloatArray × FloatArray :=
  match r with
  | .final t x => (FloatArray.empty.push t, toFlat x)
  | .path s => (timesOf s, s.data)

/-- The default solve (Julia `odesolve(f, x0)`) of a system of the example file. -/
def solve (name : String) (p : FloatArray) (inPlace : Bool) : Option (FloatArray × FloatArray) :=
  let q (i : Nat) := p.get! i
  let I := Integrator.default
  let run3 (f : Chain ℝ3 1 Float → Chain ℝ3 1 Float) (g : Chain ℝ3 1 Float → Chain ℝ3 1 Float → Chain ℝ3 1 Float) :=
    if inPlace then flatOf (odesolve ⟨.into (fun _ x o => g x o), chaosStart, 0⟩ I)
    else flatOf (odesolve ⟨.of f, chaosStart, 0⟩ I)
  match name with
  | "Lorenz" => some (run3 (lorenz (q 0) (q 1) (q 2)) (lorenzInto (q 0) (q 1) (q 2)))
  | "DiskDynamo" => some (run3 (diskDynamo (q 0) (q 1) (q 2)) (diskDynamoInto (q 0) (q 1) (q 2)))
  | "Rossler" => some (run3 (rossler (q 0) (q 1) (q 2)) (rosslerInto (q 0) (q 1) (q 2)))
  | "ChemicalKinetics" =>
    some (flatOf (odesolve ⟨.of (chemicalKinetics (q 0) (q 1) (q 2) (q 3) (q 4) (q 5) (q 6) (q 7)),
      chaosStart, 0⟩ I))
  | "Rossler4" =>
    some (flatOf (odesolve ⟨.of (rossler4 (q 0) (q 1) (q 2) (q 3)), vec4 10 10 10 10, 0⟩ I))
  | _ => none

/-- Run one golden case. -/
def runCase (c : Json) (inPlace : Bool) : TestM Unit := do
  let name ← gStr c "system"
  let p ← gFloatsAt c "params"
  let label := s!"{name}{p.toList.map fmt}{if inPlace then " in place" else ""}"
  match solve name p inPlace with
  | none => if !inPlace then check label false fun _ => "unknown system"
  | some (ts, xs) =>
    let n ← gNat c "n"
    checkEq s!"{label} n" ts.size n
    let d := xs.size / n
    checkFloat s!"{label} tlast" (ts.get! (n - 1)) (← jField c "tlast")
    checkBits s!"{label} last" (sub xs ((n - 1) * d) d) (← gFloatsAt c "last")
    checkBits s!"{label} every 4096" (every xs d 4096) (← gFloatsAt c "every4096")
    let dg ← gStr c "digest"
    let got := digest ts xs
    check s!"{label} digest" (got == dg) fun _ => s!"got {got}, expected {dg}"

/-- Run the chaos goldens. -/
def run : TestM Unit := do
  let j ← load "chaos"
  for c in ← gArr j "cases" do
    runCase c false
    let name ← gStr c "system"
    if name == "Lorenz" || name == "DiskDynamo" || name == "Rossler" then runCase c true

end Tests.AdapodeTests.Chaos
