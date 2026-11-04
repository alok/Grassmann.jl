import Tests.Adapode.Common
import Adapode.Grid

/-!
# Spectral PDE solvers (`Adapode.Grid`)

* **Julia values**: the README examples R8, R9, R11 and R12 (port-notes/adapode.md §7, run with
  Julia 1.13, Adapode `91e8516`, FFTW 1.9): the wave solvers on `0:0.01:π` at `t = 0.4`, the 2-D
  rest-wave on `(0:0.01:π)²` at `t = 2.1`, and the heat solvers on `-1:0.01:1` and its square.
  FFTW and the port's FFTs round differently, so values are compared to `1e-12`.
* **Mathematics**: the semigroup laws `H(s)H(t) = H(s+t)` for heat and biharmonic flow under all
  three boundary conditions, mass conservation under Neumann and periodic heat flow, `riesz` with
  `s = 2` is `heat`, a wave released from rest is `restwave`, Schrödinger flow is unitary and a
  group, and a 2-D periodic heat flow of a function of `y` alone is the 1-D flow of every column
  (Julia's B18: its non-negative `fftspace` frequencies on axis 2 damp `e^{-iy}` like `e^{i(N−1)y}`).
-/

open Lean Tests.Small Cartan Cartan.Spectral Adapode.Grid JuliaBase

namespace Tests.AdapodeTests.Grid

/-- `|a − b| ≤ tol·max(1, |b|)`. -/
def near (a b : Float) (tol : Float := 1e-12) : Bool := (a - b).abs ≤ tol * max 1 b.abs

/-- `Σ x`. -/
def vsum (x : FloatArray) : Float := x.data.foldl (· + ·) 0

/-- `max |a − b|`. -/
def maxDiff (a b : FloatArray) : Float :=
  (List.range a.size).foldl (fun m i => max m (a.get! i - b.get! i).abs) (if a.size == b.size then 0 else 1e300)

/-- `max |a|`. -/
def maxAbs (a : FloatArray) : Float := a.data.foldl (fun m x => max m x.abs) 0

/-- Values of `f` on a 2-D grid (column-major). -/
def grid2 (a b : Axis) (f : Float → Float → Float) : FloatArray := Id.run do
  let mut out := FloatArray.emptyWithCapacity (a.length * b.length)
  for j in [0:b.length] do
    for i in [0:a.length] do
      out := out.push (f (a.get i) (b.get j))
  return out

/-- The README `box(x) = |x| < 0.5` (a square box in 2-D). -/
@[inline] def box (x : Float) : Float := if x.abs < 0.5 then 1 else 0

/-- The README goldens. -/
def julia : TestM Unit := do
  -- R8: x = TensorField(0:0.01:π); wave*(0*x, x*(1+cos(x)), 0.4)
  let a := Axis.colon 0 0.01 piF
  checkEq "grid: 0:0.01:π has 315 points" a.length 315
  let x := a.toFloatArray
  let u0 : FloatArray := ⟨x.data.map fun _ => 0⟩
  let u1 : FloatArray := ⟨x.data.map fun x => x * (1 + F64.cos x)⟩
  let wd := waveDirichlet #[a] u0 u1 0.4
  check "grid: wavedirichlet Σu (README R8)" (near (vsum wd) 115.04844254823666) fun _ => s!"{vsum wd}"
  check "grid: wavedirichlet u[158] (README R8)" (near (wd.get! 157) 0.6073610956148955)
    fun _ => s!"{wd.get! 157}"
  let wn := waveNeumann #[a] u0 u1 0.4
  check "grid: waveneumann u[1] (README R8)" (near (wn.get! 0) (-0.21917719965332974))
    fun _ => s!"{wn.get! 0}"
  let wp := wavePeriodic #[a] u0 u1 0.4
  check "grid: waveperiodic u[1] (README R8)" (near (wp.get! 0) (-0.27979445138372055))
    fun _ => s!"{wp.get! 0}"
  let ts := (Axis.colon 0 0.01 twoPiF).toFloatArray.data
  let sd := series u0 (waveDirichlet #[a] u0 u1) ts
  checkEq "grid: wavedirichlet series shape (README R8)" (ts.size, sd.size / 315) (629, 629)
  check "grid: series slice 1 is u0, slice 41 is t = 0.4" (maxAbs (slice sd 315 0) == 0 &&
    maxDiff (slice sd 315 40) wd < 1e-12) fun _ => s!"{maxDiff (slice sd 315 40) wd}"
  -- R9: 2fun.(XY), fun(x) = exp(-100((x[1]-1)^2+(x[2]-0.7)^2)), t = 2.1
  let g := grid2 a a fun x y => 2 * F64.exp (-100 * ((x - 1) ^ 2 + (y - 0.7) ^ 2))
  let rd := restwaveDirichlet #[a, a] g 2.1
  check "grid: 2-D restwavedirichlet Σu (README R9)" (near (vsum rd) (-259.9359171720508) 1e-11)
    fun _ => s!"{vsum rd}"
  check "grid: 2-D restwavedirichlet u[100,80] (README R9)"
    (near (rd.get! (99 + 315 * 79)) 0.06671123587457149 1e-11) fun _ => s!"{rd.get! (99 + 315 * 79)}"
  let rn := restwaveNeumann #[a, a] g 2.1
  check "grid: 2-D restwaveneumann Σu (README R9)" (near (vsum rn) 628.3185307179587) fun _ => s!"{vsum rn}"
  let rp := restwavePeriodic #[a, a] g 2.1
  check "grid: 2-D restwaveperiodic Σu (README R9)" (near (vsum rp) 628.3185307179585) fun _ => s!"{vsum rp}"
  -- R11: x = TensorField(-1:0.01:1)
  let b := Axis.colon (-1) 0.01 1
  let xb := b.toFloatArray
  let bx : FloatArray := ⟨xb.data.map box⟩
  let hd := heatDirichlet #[b] bx 0.001
  check "grid: heatdirichlet Σu (README R11)" (near (vsum hd) 99.00000000000003) fun _ => s!"{vsum hd}"
  let hp := heatPeriodic #[b] ⟨xb.data.map fun x => F64.sin (piF * x) + 2⟩ 0.001
  check "grid: heatperiodic Σu (README R11)" (near (vsum hp) 402.0000000000001) fun _ => s!"{vsum hp}"
  check "grid: heatperiodic u[1] (README R11)" (near (hp.get! 0) 1.9858169530159797)
    fun _ => s!"{hp.get! 0}"
  -- R12: heatdirichlet(box.(XY), 0.01) on (-1:0.01:1)²
  let h2 := heatDirichlet #[b, b] (grid2 b b fun x y => box x * box y) 0.01
  check "grid: 2-D heatdirichlet Σu (README R12)" (near (vsum h2) 9800.541276929966 1e-11)
    fun _ => s!"{vsum h2}"
  check "grid: 2-D heatdirichlet centre (README R12)" (near (h2.get! (100 + 201 * 100)) 0.9990103761087851)
    fun _ => s!"{h2.get! (100 + 201 * 100)}"

/-- Mathematical properties. -/
def math : TestM Unit := do
  let a := Axis.colon 0 0.05 2
  let b := Axis.colon (-1) 0.1 1
  let u := grid2 a b fun x y => F64.exp (-(x - 0.8) ^ 2 * 9) * (1 + y) + F64.sin (3 * y) * x
  let axes := #[a, b]
  for (name, flow) in [("heat periodic", heatPeriodic axes), ("heat Neumann", heatNeumann axes),
      ("heat Dirichlet", heatDirichlet axes), ("biharmonic periodic", biharmonicPeriodic axes),
      ("biharmonic Neumann", biharmonicNeumann axes), ("biharmonic Dirichlet", biharmonicDirichlet axes)] do
    let e := maxDiff (flow (flow u 0.002) 0.003) (flow u 0.005)
    check s!"grid: {name} semigroup H(s)H(t) = H(s+t)" (e < 1e-13 * maxAbs u) fun _ => s!"{e}"
  for (name, flow) in [("Neumann", heatNeumann axes), ("periodic", heatPeriodic axes)] do
    let e := (vsum (flow u 0.01) - vsum u).abs
    check s!"grid: {name} heat conserves mass" (e < 1e-12 * vsum u) fun _ => s!"{e}"
  let e := maxDiff (rieszDirichlet axes u 0.01 2) (heatDirichlet axes u 0.01)
  check "grid: riesz s=2 is heat" (e < 1e-14) fun _ => s!"{e}"
  let zero : FloatArray := ⟨u.data.map fun _ => 0⟩
  for (name, w, r) in [("periodic", wavePeriodic axes u zero 0.7, restwavePeriodic axes u 0.7),
      ("Neumann", waveNeumann axes u zero 0.7, restwaveNeumann axes u 0.7),
      ("Dirichlet", waveDirichlet axes u zero 0.7, restwaveDirichlet axes u 0.7)] do
    check s!"grid: {name} wave from rest is restwave" (maxDiff w r < 1e-13) fun _ => s!"{maxDiff w r}"
  -- the mean of u1 drifts only in fullwave
  let one : FloatArray := ⟨u.data.map fun _ => 1⟩
  let fw := fullwavePeriodic axes zero one 0.3
  let fn := fullwaveNeumann axes zero one 0.3
  check "grid: fullwave moves a constant velocity by t" (maxDiff fw ⟨one.data.map (· * 0.3)⟩ < 1e-14
    && maxDiff fn ⟨one.data.map (· * 0.3)⟩ < 1e-14 && maxAbs (wavePeriodic axes zero one 0.3) < 1e-14)
    fun _ => s!"{maxDiff fw ⟨one.data.map (· * 0.3)⟩}"
  -- Schrödinger: unitary and a group
  let ψ := schrodingerPeriodic axes u 0.01
  let n0 := vsum ⟨u.data.map (· ^ 2)⟩
  let n1 := (List.range ψ.len).foldl (fun s k => s + ψ.re k ^ 2 + ψ.im k ^ 2) 0
  check "grid: Schrödinger flow is unitary" ((n1 - n0).abs < 1e-12 * n0) fun _ => s!"{n0} {n1}"
  let ψ2 := schrodingerPeriodicC axes (schrodingerPeriodicC axes (CVec.ofReal u) 0.004) 0.006
  check "grid: Schrödinger flow is a group" (maxDiff ψ2 ψ < 1e-13) fun _ => s!"{maxDiff ψ2 ψ}"
  -- B18: a function of y alone flows column by column like the 1-D problem
  let f := fun (y : Float) => F64.cos (piF * y) + 0.5 * F64.sin (2 * piF * y)
  let uy := grid2 a b fun _ y => f y
  let col := heatPeriodic #[b] ⟨b.toFloatArray.data.map f⟩ 0.02
  let h2 := heatPeriodic axes uy 0.02
  let e := (List.range a.length).foldl (fun m i =>
    (List.range b.length).foldl (fun m j => max m (h2.get! (i + a.length * j) - col.get! j).abs) m) (0 : Float)
  check "grid: 2-D periodic heat of f(y) is the 1-D flow (B18)" (e < 1e-13) fun _ => s!"{e}"

/-- Run the grid checks. -/
def run : TestM Unit := do
  julia
  math

end Tests.AdapodeTests.Grid
