import Tests.Adapode.Common
import Adapode.Element
import Cartan.Mesher

/-!
# Finite elements (`Adapode.Element`)

* **Julia values** (port-notes/adapode.md §6.1–6.2, verified there against Julia 1.13 /
  Adapode `91e8516`): the two `assemblemassload` L² projections of `test/runtests.jl` on
  `initmesh(0:1/5:1)`, the backward-Euler heat test, the README's `solveheat` (R16), and the
  whole `adaptpoisson` run (element counts, first and last `ϵ`, final nodes). Solves are compared
  to `1e-10` relative: Julia factors with UMFPACK/CHOLMOD, the port with an envelope Cholesky.
* **Mathematics** on meshes from `Cartan.Mesher`: the mass matrix sums to the area, stiffness rows
  sum to zero, the Robin sums of §4.8 (`Σ R = κ·perimeter`, `Σ r = κ ∮ gD`), exact nodal values
  for `−u″ = 1` in 1-D, second-order convergence of `−Δu = 2π² sin πx sin πy` on the unit square,
  and the first Dirichlet eigenvalue of the unit disk (`j₀₁² = 5.7832`, approached from above as
  the conforming P1 bound requires).
-/

open Lean Tests.Small Cartan Cartan.Solve Adapode.FEM Grassmann JuliaBase

namespace Tests.AdapodeTests.Fem

/-- The `c`-th spatial coordinate of a homogeneous point (Julia `x[c+1]`). -/
@[inline] def px {V : TensorBundle} (p : HPoint V) (c : Nat) : Float := getD p.v c

/-- `|a − b| ≤ tol·max(1, |b|)`. -/
def near (a b : Float) (tol : Float := 1e-10) : Bool := (a - b).abs ≤ tol * max 1 b.abs

/-- Elementwise `near`. -/
def nearAll (a : FloatArray) (b : Array Float) (tol : Float := 1e-10) : Bool :=
  a.size == b.size && (List.range b.size).all fun i => near (a.get! i) b[i]! tol

/-- The sum of all stored entries. -/
def sumAll (A : Sparse) : Float := A.vals.data.foldl (· + ·) 0

/-- `Σ x`. -/
def vsum (x : FloatArray) : Float := x.data.foldl (· + ·) 0

/-- The Julia golden checks. -/
def julia : TestM Unit := do
  -- runtests.jl: \(assemblemassload(pt, f)...) on initmesh(0:1/5:1)
  let (pt, pe) := SimplexBundle.initmesh ((Array.range 6).map fun i => i.toFloat / 5)
  let proj := fun (f : HPoint ℝ2 → Float) =>
    let (M, b) := assembleMassLoad pt (nodalOf pt f)
    M.solve b
  let u1 := proj fun x => px x 1 * Float.sin (px x 1)
  check "fem: L² projection of x sin x (runtests.jl)" (nearAll u1 #[-0.013863142513283086,
    0.027726285026566166, 0.14136119936109193, 0.34143293906982763, 0.5256199485817251,
    0.9993965029209823]) fun _ => s!"{u1.data}"
  let u2 := proj fun x => 2 * px x 1 * Float.sin (2 * 3.141592653589793 * px x 1) + 3
  check "fem: L² projection of 2x sin 2πx + 3 (runtests.jl)" (nearAll u2 #[2.781999575909511,
    3.43600084818098, 3.7565326704749373, 2.359237680923145, 0.5744627893266803,
    4.212768605336659]) fun _ => s!"{u2.data}"
  -- runtests.jl BackwardEulerHeat1D: x = 0:0.01:1, h = 0.005, 100 steps
  let xs := (Array.range 101).map fun i => i.toFloat / 100
  let (pt, pe') := SimplexBundle.initmesh xs
  let ic : FloatArray := ⟨xs.map fun x => 0.5 - (0.5 - x).abs⟩
  let f2 : FloatArray := ⟨xs.map (2 * ·)⟩
  let slices := solveHeat pt pe' ic f2 (fun _ => 1e6) 0.005 100
  let ξ := slices.back!
  check "fem: backward-Euler heat ξ[51] (runtests.jl)" (near (ξ.get! 50) 0.12723526290687 1e-9)
    fun _ => s!"{ξ.get! 50}"
  check "fem: backward-Euler heat Σξ (runtests.jl)" (near (vsum ξ) 8.474801782948974 1e-9)
    fun _ => s!"{vsum ξ}"
  check "fem: backward-Euler heat ξ[1] (runtests.jl)" (near (ξ.get! 0) 2.520524341237724e-7 1e-6)
    fun _ => s!"{ξ.get! 0}"
  -- README R16: solveheat(triangle.(pt), (x->2x[2]).(pt), (x->1e6).(pe), range(0,0.6,101))
  let s16 := solveHeat pt pe' ic f2 (fun _ => 1e6) 0.006 100
  checkEq "fem: solveheat slices (README R16)" s16.size 101
  check "fem: solveheat u[51,2] (README R16)" (near (s16[1]!.get! 50) 0.4285756604563396 1e-9)
    fun _ => s!"{s16[1]!.get! 50}"
  check "fem: solveheat u[51,end] (README R16)" (near (s16.back!.get! 50) 0.12587667370150693 1e-9)
    fun _ => s!"{s16.back!.get! 50}"
  check "fem: solveheat Σu[:,end] (README R16)" (near (vsum s16.back!) 8.38832030667821 1e-9)
    fun _ => s!"{vsum s16.back!}"
  -- adaptpoisson(refinemesh(0:0.25:1)..., 1, 0, x->exp(-100abs2(x[2]-0.5)))
  let (m0, _) := SimplexBundle.initmesh #[0, 0.25, 0.5, 0.75, 1]
  let (mf, log) := adaptPoisson m0 1 0 fun x => Float.exp (-100 * (px x 1 - 0.5) ^ 2)
  checkEq "fem: adaptpoisson element counts" (log.map (·.elements))
    #[4, 6, 8, 10, 14, 20, 30, 38, 56, 72, 106, 140, 208]
  checkEq "fem: adaptpoisson final elements" mf.elements 270
  check "fem: adaptpoisson first ϵ" (near log[0]!.ϵ 0.06250023291538927 1e-9) fun _ => s!"{log[0]!.ϵ}"
  check "fem: adaptpoisson second ϵ" (near log[1]!.ϵ 0.01881851550353944 1e-9) fun _ => s!"{log[1]!.ϵ}"
  check "fem: adaptpoisson last ϵ" (near log.back!.ϵ 3.725363657493423e-5 1e-8) fun _ => s!"{log.back!.ϵ}"
  let firstNodes := (Array.range 10).map fun v => mf.coord (v + 1) 1
  checkEq "fem: adaptpoisson first nodes" firstNodes
    #[0.0, 0.125, 0.1875, 0.25, 0.28125, 0.296875, 0.3046875, 0.3125, 0.3203125, 0.328125]
  let _ := pe

/-- Mathematical checks on 1-D and mesher meshes. -/
def math : TestM Unit := do
  -- −u″ = 1, u(0) = u(1) = 0: P1 is nodally exact, u = x(1 − x)/2
  let xs := (Array.range 11).map fun i => (i.toFloat / 10) ^ 2
  let (pt, pe) := SimplexBundle.initmesh xs
  let u := poisson pt pe (f := fun _ => 1)
  check "fem: −u″ = 1 is nodally exact on a graded mesh"
    ((List.range xs.size).all fun i => near (u.get! i) (xs[i]! * (1 - xs[i]!) / 2) 1e-13)
    fun _ => s!"{u.data}"
  -- unit square from the mesher
  let sq := Cartan.Mesher.polygon #[(0, 0), (1, 0), (1, 1), (0, 1)]
  let m := Cartan.Mesher.triangulateBundle sq { maxArea := 0.01 }
  let e := m.boundary
  check "fem: Σ mass = area" (near (sumAll (assembleMass m)) 1 1e-12) fun _ => s!"{sumAll (assembleMass m)}"
  let A := assembleStiffness m
  let rows := A.mulVec ⟨Array.replicate m.totalNodes 1⟩
  check "fem: stiffness annihilates constants" (rows.data.all (·.abs ≤ 1e-11))
  check "fem: stiffness is symmetric" A.isSymmetric
  let (R, r) := assembleRobin e (fun _ => 1e6) (fun x => px x 1)
  check "fem: Σ R = κ·perimeter (port notes §4.8)" (near (sumAll R) 4e6 1e-12) fun _ => s!"{sumAll R}"
  check "fem: Σ r = κ ∮ gD for gD = x (port notes §4.8)" (near (vsum r) 2e6 1e-12) fun _ => s!"{vsum r}"
  -- manufactured solution: second-order convergence
  let π := 3.141592653589793
  let exact := fun (x : HPoint ℝ3) => Float.sin (π * px x 1) * Float.sin (π * px x 2)
  let errAt := fun (a : Float) =>
    let m := Cartan.Mesher.triangulateBundle sq { maxArea := a, minAngle := 25 }
    let u := poisson m m.boundary (f := fun x => 2 * π * π * exact x)
    let ex := nodalOf m exact
    (List.range m.totalNodes).foldl (fun s i => max s (u.get! i - ex.get! i).abs) 0
  let e1 := errAt 0.004
  let e2 := errAt 0.001
  check "fem: Poisson error is small" (e2 < 5e-3) fun _ => s!"max error {e2}"
  check "fem: Poisson converges at second order (area ÷ 4 → error ÷ ≥ 3)" (e1 / e2 ≥ 3)
    fun _ => s!"errors {e1}, {e2}"
  -- Robin with large κ approaches the Dirichlet solution
  let mr := Cartan.Mesher.triangulateBundle sq { maxArea := 0.004, minAngle := 25 }
  let ur := solvePoisson mr mr.boundary (f := fun x => 2 * π * π * exact x)
  let ud := poisson mr mr.boundary (f := fun x => 2 * π * π * exact x)
  let dr := (List.range mr.totalNodes).foldl (fun s i => max s (ur.get! i - ud.get! i).abs) 0
  check "fem: Robin κ = 10⁶ ≈ Dirichlet" (dr < 1e-4) fun _ => s!"difference {dr}"
  -- the first Dirichlet eigenvalue of the unit disk by inverse iteration
  let dm := Cartan.Mesher.triangulateBundle (Cartan.Mesher.disk 96) { maxArea := 0.003, minAngle := 25 }
  let fixed := nodesOf dm.boundary
  let isB := fixed.foldl (fun (s : Array Bool) i => s.set! i true) (Array.replicate dm.totalNodes false)
  let free := (Array.range dm.totalNodes).filter fun i => isB[i]! == false
  let Af := submatrix (assembleStiffness dm) free free
  let Mf := submatrix (assembleMass dm) free free
  match Af.cholesky with
  | none => check "fem: disk stiffness is SPD" false
  | some F =>
    let x := (List.range 40).foldl (fun (x : FloatArray) _ =>
      let y := F.solve (Mf.mulVec x)
      let s := Float.sqrt (vsum ⟨y.data.map (· ^ 2)⟩)
      ⟨y.data.map (· / s)⟩) ⟨Array.replicate free.size 1⟩
    let ip := fun (a b : FloatArray) => (List.range a.size).foldl (fun s i => s + a.get! i * b.get! i) 0
    let lam := ip x (Af.mulVec x) / ip x (Mf.mulVec x)
    let j01sq := 5.783185962946784
    check "fem: first disk eigenvalue ≈ j₀₁² (README R15)" ((lam - j01sq).abs ≤ 0.01 * j01sq)
      fun _ => s!"λ = {lam}"
    check "fem: the P1 eigenvalue bounds j₀₁² from above" (lam > j01sq) fun _ => s!"λ = {lam}"
  -- transport–diffusion runs and is finite
  let uv := (Array.range mr.totalNodes).map fun _ => #[1.0, 0.5]
  let td := solveTransportDiffusion mr uv mr.boundary (fun _ => 1e6) 0.01 (1 / 50) (fun x => px x 1)
  check "fem: transport–diffusion is finite" (td.data.all fun x => !x.isNaN && !x.isInf)
  let ut := solveTransport mr mr.boundary (fun _ => #[1, 0])
  check "fem: transport is finite and positive inside" (ut.data.all fun x => x ≥ -1e-12 && !x.isNaN)

/-- Run the FEM checks. -/
def run : TestM Unit := do
  julia
  math

end Tests.AdapodeTests.Fem
