import Cartan.Element
import Cartan.Solve
import Adapode.Constants

/-!
# Finite elements: P1 assembly and solvers (Adapode `src/element.jl`)

Port notes: `docs/port-notes/adapode.md` §2.6, §4.7–4.8. Meshes are Cartan `SimplexBundle`s
with homogeneous points (`x[1] = 1`; coordinate `c ≥ 1` is the `c`-th spatial coordinate, Julia's
`x[c+1]`), so the same code assembles on intervals (`initmesh`), triangles (`Cartan.Mesher`) and
tetrahedra. Local matrices follow §4.7 and are scattered into a `Cartan.Solve.Sparse` element by
element, with `i` outer and `j` inner (Julia's `assemblelocal!`), so every global entry is summed
in Julia's order.

* `assembleMass`, `assembleStiffness`, `assembleConvection`, `assembleSD`, `assembleMassLoad`,
  `assembleRobin`, `assemble`: the global operators of §4.8 (`c`, `a`, `b`, `κ` per element).
* `solveDirichlet`: `A x = b` with prescribed values on the fixed nodes (Cartan `solvedirichlet`).
* `solvePoisson` (Robin), `poisson` (homogeneous Dirichlet reaction–diffusion), `solveTransport`,
  `solveTransportDiffusion`, `solveHeat` (backward Euler, Julia's unscaled Robin term B21), and
  the 1-D `jumps` indicator and `adaptPoisson` loop (which returns its log instead of printing).

Coefficients that Julia takes as "a number or a function of the element mean" are given here as
per-element functions `Nat → Float`; `atMeans m f` turns a function of the point into one.
-/

namespace Adapode.FEM

open Cartan Cartan.Solve Grassmann StaticVectors MeshTopology

variable {n k : Nat} {V : TensorBundle} {G : Type}

/-! ## Local data -/

/-- The P1 mass matrix per unit volume (§4.7): `(1 + δᵢⱼ)/(N(N+1))`. -/
@[inline] def massEntry (N i j : Nat) : Float :=
  (if i == j then 2 else 1) / Float.ofNat (N * (N + 1))

/-- The spatial dimension of the homogeneous points. -/
@[inline] def sdim (_ : SimplexBundle n (HPoint V) G) : Nat := V.n - 1

/-- Element volumes (`1` for 0-simplices, Julia's convention for point boundaries). -/
def vols (m : SimplexBundle n (HPoint V) G) : FloatArray :=
  if n ≤ 1 then ⟨Array.replicate m.elements 1⟩ else m.volumes.data

/-- The element mean points. -/
def meanPoints (m : SimplexBundle n (HPoint V) G) : Array (HPoint V) :=
  (Array.range m.elements).map fun e => m.means.get e

/-- A function of the point evaluated at the element means (Julia `iterable(means(t), c)`). -/
def atMeans (m : SimplexBundle n (HPoint V) G) (f : HPoint V → Float) : Nat → Float :=
  let ps := meanPoints m
  fun k => f ps[k]!

/-- The P1 gradients of every element, as rows: `grads[k][j][c] = ∂_c φⱼ` on element `k`. -/
def grads (m : SimplexBundle n (HPoint V) G) : Array (Array (Array Float)) :=
  let d := V.n - 1
  (Array.range m.elements).map fun e =>
    let T := m.gradienthatAt e
    (Array.range n).map fun j => (Array.range d).map fun c => T.entry c j

/-- `x · y` summed left to right. -/
@[inline] def dot (x y : Array Float) : Float :=
  (List.range x.size).foldl (fun s c => s + x[c]! * y[c]!) 0

/-- The 0-based vertices of element `k`. -/
@[inline] def verts (m : SimplexBundle n (HPoint V) G) (k : Nat) : Array Nat :=
  (Array.range n).map fun j => m.vertexOf k j - 1

/-- The sorted 0-based nodes of a (boundary) mesh. -/
def nodesOf (e : SimplexBundle n (HPoint V) G) : Array Nat :=
  let s : Std.HashSet Nat := (Array.range e.elements).foldl (fun s k =>
    (verts e k).foldl (·.insert ·) s) {}
  s.toArray.qsort (· < ·)

/-! ## Global assembly -/

/-- Julia `assembleglobal`: `Σₖ scatter(loc k)`, element by element, `i` outer, `j` inner. -/
def assembleGlobal (m : SimplexBundle n (HPoint V) G) (loc : Nat → Nat → Nat → Float) : Sparse :=
  Id.run do
    let ne := m.elements
    let np := m.totalNodes
    let mut I : Array Nat := Array.mkEmpty (ne * n * n)
    let mut J : Array Nat := Array.mkEmpty (ne * n * n)
    let mut X : FloatArray := FloatArray.emptyWithCapacity (ne * n * n)
    for k in [0:ne] do
      let vs := verts m k
      for i in [0:n] do
        for j in [0:n] do
          I := I.push vs[i]!
          J := J.push vs[j]!
          X := X.push (loc k i j)
    return Sparse.ofTriplets np np I J X

/-- Julia `assemblemass(t, m)`: `Σₖ mₖ (1 + δᵢⱼ)/(N(N+1))` (bug B13, a `BoundsError` when there
are more elements than nodes, does not arise here). -/
def assembleMass (m : SimplexBundle n (HPoint V) G) (w : FloatArray := vols m) : Sparse :=
  assembleGlobal m fun k i j => massEntry n i j * w.get! k

/-- Julia `assemblestiffness(t, c, m, g)`: `Σₖ (cₖ ∇φᵢ·∇φⱼ) mₖ`. -/
def assembleStiffness (m : SimplexBundle n (HPoint V) G) (c : Nat → Float := fun _ => 1)
    (w : FloatArray := vols m) (g : Array (Array (Array Float)) := grads m) : Sparse :=
  assembleGlobal m fun k i j => c k * dot g[k]![j]! g[k]![i]! * w.get! k

/-- Julia `assembleconvection(t, b, m, g)`: `Σₖ ((bₖ/N)·∇φⱼ) mₖ` at `(i, j)` (`∫ φᵢ b·∇φⱼ` for an
element-constant `b`). -/
def assembleConvection (m : SimplexBundle n (HPoint V) G) (b : Nat → Array Float)
    (w : FloatArray := vols m) (g : Array (Array (Array Float)) := grads m) : Sparse :=
  let N := Float.ofNat n
  assembleGlobal m fun k _ j => dot ((b k).map (· / N)) g[k]![j]! * w.get! k

/-- Julia `assembleSD(t, b, m, g)`: the streamline diffusion `Σₖ (bₖ·∇φᵢ)(bₖ·∇φⱼ) mₖ`. -/
def assembleSD (m : SimplexBundle n (HPoint V) G) (b : Nat → Array Float)
    (w : FloatArray := vols m) (g : Array (Array (Array Float)) := grads m) : Sparse :=
  assembleGlobal m fun k i j => dot (b k) g[k]![i]! * dot (b k) g[k]![j]! * w.get! k

/-- Julia `assemblemassincidence(t, f, m, l)`: the mass matrix weighted by `w` and the load
`b[tₖ] += f[tₖ] lₖ` (`f` nodal). -/
def assembleMassIncidence (m : SimplexBundle n (HPoint V) G) (f : FloatArray)
    (w : FloatArray := vols m) (l : FloatArray := w) : Sparse × FloatArray :=
  let M := assembleMass m w
  let b := (Array.range m.elements).foldl (fun b k =>
    (verts m k).foldl (fun b v => b.set! v (b.get! v + f.get! v * l.get! k)) b)
    (⟨Array.replicate m.totalNodes 0⟩ : FloatArray)
  (M, b)

/-- Julia `assemblemassload(t, f, m, l)` for nodal `f`: `assemblemassincidence(t, f/N, m, l)`, the
mass matrix and the lumped load. -/
def assembleMassLoad (m : SimplexBundle n (HPoint V) G) (f : FloatArray)
    (w : FloatArray := vols m) (l : FloatArray := w) : Sparse × FloatArray :=
  let N := Float.ofNat n
  assembleMassIncidence m ⟨f.data.map (· / N)⟩ w l

/-- `f` at every node of the full mesh (Julia `iterpts(t, f)`). -/
def nodalOf (m : SimplexBundle n (HPoint V) G) (f : HPoint V → Float) : FloatArray := m.nodal f

/-- Julia `assemble(t, c, a, f, m, g)`: the stiffness `A(c)`, the mass weighted by `a`, and the
lumped load of `f`. -/
def assemble (m : SimplexBundle n (HPoint V) G) (c : Nat → Float := fun _ => 1)
    (a : Nat → Float := fun _ => 1) (f : HPoint V → Float := fun _ => 0) (w : FloatArray := vols m)
    (g : Array (Array (Array Float)) := grads m) : Sparse × Sparse × FloatArray :=
  let aw : FloatArray := ⟨(Array.range m.elements).map fun k => a k * w.get! k⟩
  let (M, b) := assembleMassLoad m (nodalOf m f) aw w
  (assembleStiffness m c w g, M, b)

/-- Julia `assemblerobin(e, κ, gD, gN)` on a boundary mesh `e`: `R = Σ κ(aₑ) vₑ massₑ` and
`rᵢ = Σ_{e ∋ i} (κ(aₑ) gD(aₑ) + gN(aₑ)) vₑ / N`, with `aₑ` the facet means and `vₑ` their measures
(`1` for points). -/
def assembleRobin (e : SimplexBundle n (HPoint V) G) (κ : HPoint V → Float := fun _ => 1e6)
    (gD : HPoint V → Float := fun _ => 0) (gN : HPoint V → Float := fun _ => 0) :
    Sparse × FloatArray :=
  let a := meanPoints e
  let v := vols e
  let mv : FloatArray := ⟨(Array.range e.elements).map fun k => κ a[k]! * v.get! k⟩
  let lv : FloatArray := ⟨(Array.range e.elements).map fun k =>
    (κ a[k]! * gD a[k]! + gN a[k]!) * v.get! k⟩
  assembleMassLoad e ⟨Array.replicate e.totalNodes 1⟩ mv lv

/-! ## Solvers -/

/-- `x + y`. -/
@[inline] def vadd (x y : FloatArray) : FloatArray := ⟨(Array.range x.size).map fun i => x.get! i + y.get! i⟩

/-- The submatrix `A[rows, cols]` (0-based index lists). -/
def submatrix (A : Sparse) (rows cols : Array Nat) : Sparse := Id.run do
  let mut rmap : Array Nat := Array.replicate A.rows A.rows
  for i in [0:rows.size] do rmap := rmap.set! rows[i]! i
  let mut I : Array Nat := #[]
  let mut J : Array Nat := #[]
  let mut X : FloatArray := .empty
  for jj in [0:cols.size] do
    let j := cols[jj]!
    for p in [A.colPtr[j]!:A.colPtr[j + 1]!] do
      let r := rmap[A.rowIdx[p]!]!
      if r < rows.size then
        I := I.push r; J := J.push jj; X := X.push (A.vals.get! p)
  return Sparse.ofTriplets rows.size cols.size I J X

/-- Cartan `solvedirichlet(A, b, fixed, g)`: `x[fixed] = g`,
`x[free] = A[free, free] \ (b[free] − A[free, fixed] g)`. -/
def solveDirichlet (A : Sparse) (b : FloatArray) (fixed : Array Nat)
    (g : FloatArray := ⟨Array.replicate fixed.size 0⟩) : FloatArray := Id.run do
  let N := A.rows
  let isFixed := fixed.foldl (fun (s : Array Bool) i => s.set! i true) (Array.replicate N false)
  let free := (Array.range N).filter fun i => isFixed[i]! == false
  let Aff := submatrix A free free
  let Afx := submatrix A free fixed
  let r := Afx.mulVec g
  let rhs : FloatArray := ⟨(Array.range free.size).map fun i => b.get! free[i]! - r.get! i⟩
  let xf := Aff.solve rhs
  let mut x : FloatArray := ⟨Array.replicate N 0⟩
  for i in [0:fixed.size] do x := x.set! fixed[i]! (g.get! i)
  for i in [0:free.size] do x := x.set! free[i]! (xf.get! i)
  return x

/-- Julia `solvepoisson(t, e, c, f, κ, gD, gN)`: `(A + R) u = b + r` for `−∇·(c∇u) = f` with
`c ∂ₙu = κ(gD − u) + gN` on `e`. -/
def solvePoisson (m : SimplexBundle n (HPoint V) G) (e : SimplexBundle k (HPoint V) G)
    (c : Nat → Float := fun _ => 1) (f : HPoint V → Float := fun _ => 1)
    (κ : HPoint V → Float := fun _ => 1e6) (gD : HPoint V → Float := fun _ => 0)
    (gN : HPoint V → Float := fun _ => 0) : FloatArray :=
  let b := m.assembleload f
  let A := assembleStiffness m c
  let (R, r) := assembleRobin e κ gD gN
  (A + R).solve (vadd b r)

/-- Julia `poisson(t, e, c, a, f)`: `−∇·(c∇u) + a u = f`, `u = 0` on `e`. -/
def poisson (m : SimplexBundle n (HPoint V) G) (e : SimplexBundle k (HPoint V) G)
    (c : Nat → Float := fun _ => 1) (a : Nat → Float := fun _ => 0)
    (f : HPoint V → Float := fun _ => 1) : FloatArray :=
  let (A, M, b) := assemble m c a f
  solveDirichlet (A + M) b (nodesOf e)

/-- Julia `solvetransport(t, e, c, f, ϵ)`: `−ϵΔu + c·∇u = f`, `u = 0` on `e`. -/
def solveTransport (m : SimplexBundle n (HPoint V) G) (e : SimplexBundle k (HPoint V) G)
    (c : Nat → Array Float) (f : HPoint V → Float := fun _ => 1) (ϵ : Float := 0.1) : FloatArray :=
  let w := vols m
  let g := grads m
  let A := assembleStiffness m (fun _ => ϵ) w g
  let b := m.assembleload f
  let C := assembleConvection m c w g
  solveDirichlet (A + C) b (nodesOf e)

/-- Julia `solvetransportdiffusion(tf, eκ, c, δ, gD, gN)`: `(A(c) + R − Cᵀ + S_δ) u = r`, with the
velocity `b` given at the nodes (element means are used) and the streamline diffusion `δ`. -/
def solveTransportDiffusion (m : SimplexBundle n (HPoint V) G) (velocity : Array (Array Float))
    (e : SimplexBundle k (HPoint V) G) (κ : HPoint V → Float) (c δ : Float)
    (gD : HPoint V → Float := fun _ => 0) (gN : HPoint V → Float := fun _ => 0) : FloatArray :=
  let w := vols m
  let g := grads m
  let d := V.n - 1
  let N := Float.ofNat n
  let bm : Array (Array Float) := (Array.range m.elements).map fun k =>
    let vs := verts m k
    (Array.range d).map fun c => (vs.foldl (fun s v => s + velocity[v]![c]!) 0) / N
  let A := assembleStiffness m (fun _ => c) w g
  let C := assembleConvection m (fun k => bm[k]!) w g
  let sδ := Float.sqrt δ
  let Sd := assembleSD m (fun k => bm[k]!.map (sδ * ·)) w g
  let (R, r) := assembleRobin e κ gD gN
  (A + R - C.transpose + Sd).solve r

/-- Julia `solveheat(ic, f, κ, T)` (backward Euler): the slices `u₀ = ic`,
`uₗ₊₁ = (M + hA) \ (M uₗ + h b)` with `(M, b) = massload(f) + robin(κ)` (Julia adds the Robin
matrix to `M`, so it is not scaled by `h`: quirk B21, kept). `f` is nodal, `steps + 1` slices. -/
def solveHeat (m : SimplexBundle n (HPoint V) G) (e : SimplexBundle k (HPoint V) G)
    (ic f : FloatArray) (κ : HPoint V → Float) (h : Float) (steps : Nat) : Array FloatArray :=
  let A := assembleStiffness m
  let (M0, b0) := assembleMassLoad m f
  let (R, r) := assembleRobin e κ
  let M := M0 + R
  let b := vadd b0 r
  let LHS := M + h * A
  let hb : FloatArray := ⟨b.data.map (h * ·)⟩
  let F := if LHS.isSymmetric then LHS.cholesky else LHS.luNoPivot
  let step := fun (u : FloatArray) =>
    let rhs := vadd (M.mulVec u) hb
    match F with
    | some F => F.solve rhs
    | none => LHS.solve rhs
  (List.range steps).foldl (fun out _ => out.push (step out.back!)) #[ic]

/-! ## 1-D adaptivity -/

/-- Julia `jumps(t, c, a, f, u, m)` on an interval mesh with sorted nodes:
`ηₖ = mₖ √((ρₖ² + ρₖ₊₁²) mₖ/2)` with the nodal residual `ρ = f − a u` (`a` constant). -/
def jumps1 (m : SimplexBundle 2 (HPoint V) G) (a : Float) (f : HPoint V → Float) (u : FloatArray) :
    FloatArray :=
  let fn := nodalOf m f
  let w := vols m
  let fau : FloatArray := ⟨(Array.range fn.size).map fun i => fn.get! i - a * u.get! i⟩
  ⟨(Array.range m.elements).map fun i =>
    let mi := w.get! i
    mi * Float.sqrt ((fau.get! i ^ 2 + fau.get! (i + 1) ^ 2) * mi / 2)⟩

/-- One line of `adaptPoisson`'s log: elements, `ϵ = rms(η)` and `max η`. -/
structure AdaptStep where
  /-- Elements of the mesh solved on. -/
  elements : Nat
  /-- `rms(η)`. -/
  ϵ : Float
  /-- `max η`. -/
  maxη : Float
  deriving Repr, Inhabited

/-- Julia `adaptpoisson(g, pt, pe, c, a, f)` on an interval mesh: solve
`−(c u′)′ + a u = f`, `u = 0` at the ends, mark the elements with `η > rms η`, bisect them,
while `ϵ > 5·10⁻⁵` and there are fewer than 10000 elements. Like Julia it refines once more after
the last solve (so the returned mesh was not solved on); the log replaces the printing. -/
def adaptPoisson (m0 : SimplexBundle 2 (HPoint ℝ2)) (c a : Float) (f : HPoint ℝ2 → Float) :
    SimplexBundle 2 (HPoint ℝ2) × Array AdaptStep :=
  go m0 #[] 1 64
where
  /-- The loop. -/
  go (m : SimplexBundle 2 (HPoint ℝ2)) (log : Array AdaptStep) (ϵ : Float) :
      Nat → SimplexBundle 2 (HPoint ℝ2) × Array AdaptStep
    | 0 => (m, log)
    | fuel + 1 =>
      if !(ϵ > 5e-5 && m.elements < 10000) then (m, log)
      else
        let np := m.totalNodes
        let (A, M, b) := assemble m (fun _ => c) (fun _ => a) f
        let ξ := solveDirichlet (A + M) b #[0, np - 1]
        let η := jumps1 m a f ξ
        let ne := m.elements
        let ϵ' := Float.sqrt (η.data.foldl (fun s x => s + x * x) 0) / Float.sqrt (Float.ofNat ne)
        let mx := η.data.foldl max 0
        let marked := (Array.range ne).filterMap fun i => if η.get! i > ϵ' then some (i + 1) else none
        go (SimplexBundle.refine1 m marked).1 (log.push ⟨ne, ϵ', mx⟩) ϵ' fuel

/-! ## Time-dependent and nonlinear problems -/

/-- `x − y`. -/
@[inline] def vsub (x y : FloatArray) : FloatArray := ⟨(Array.range x.size).map fun i => x.get! i - y.get! i⟩

/-- `s x`. -/
@[inline] def vscale (s : Float) (x : FloatArray) : FloatArray := ⟨x.data.map (s * ·)⟩

/-- `‖x‖₂`. -/
@[inline] def vnorm (x : FloatArray) : Float := Float.sqrt (x.data.foldl (fun s v => s + v * v) 0)

/-- The `2×2` block matrix `[s₁₁A₁₁ s₁₂A₁₂; s₂₁A₂₁ s₂₂A₂₂]` of `np × np` blocks. -/
def block2 (np : Nat) (bs : Array (Sparse × Nat × Nat × Float)) : Sparse := Id.run do
  let mut I : Array Nat := #[]
  let mut J : Array Nat := #[]
  let mut X : FloatArray := .empty
  for (A, bi, bj, sc) in bs do
    for (i, j, x) in A.triplets do
      I := I.push (bi * np + i); J := J.push (bj * np + j); X := X.push (sc * x)
  return Sparse.ofTriplets (2 * np) (2 * np) I J X

/-- Julia `solvewave(pt, bc)` (Crank–Nicolson on `[u; v]`, `(A, M, b) = assemble(pt, 1, 1, 0)`):
from `u = v = 0`, each step solves `LHS [u; v] = RHS [u; v] + [0; Δt b]`, then overwrites
`u[fixed]` with that step's boundary values (Julia's "ugly way"). Returns `u` after every step,
one slice per entry of `bc` (the values at `fixed`, in its order).

The overwrite leaves `v` on the boundary to the free dynamics, so a wave driven through the
boundary enters with the wrong amplitude (`2/3` of the boundary value for a 1-D pulse, defect
`solvewave-boundary-overwrite`); `solveWaveDirichlet` imposes the boundary values in the solve. -/
def solveWave (m : SimplexBundle n (HPoint V) G) (fixed : Array Nat) (Δt : Float)
    (bc : Array FloatArray) : Array FloatArray :=
  let np := m.totalNodes
  let (A, M, b) := assemble m
  let LHS := block2 np #[(M, 0, 0, 1), (M, 0, 1, -Δt / 2), (A, 1, 0, Δt / 2), (M, 1, 1, 1)]
  let RHS := block2 np #[(M, 0, 0, 1), (M, 0, 1, Δt / 2), (A, 1, 0, -Δt / 2), (M, 1, 1, 1)]
  let zkb : FloatArray := ⟨Array.replicate np 0 ++ b.data.map (Δt * ·)⟩
  let F := LHS.luNoPivot
  let solve := fun (r : FloatArray) => match F with
    | some F => F.solve r
    | none => LHS.solve r
  let (_, out) := bc.foldl (fun (sol, out) g =>
    let sol := solve (vadd (RHS.mulVec sol) zkb)
    let sol := (Array.range fixed.size).foldl (fun s i => s.set! fixed[i]! (g.get! i)) sol
    (sol, out.push ⟨sol.data.extract 0 np⟩)) ((⟨Array.replicate (2 * np) 0⟩ : FloatArray), #[])
  out

/-- Crank–Nicolson for `u_tt = Δu + f` with Dirichlet values imposed in the solve: `u[fixed]`
takes the step's boundary values and `v[fixed]` the Crank–Nicolson-consistent
`2(gₙ₊₁ − gₙ)/Δt − vₙ`, the free unknowns are solved for (one factorization for all steps).
Starts from `u = v = 0` with `g₀ = 0`; returns `u` after every step. -/
def solveWaveDirichlet (m : SimplexBundle n (HPoint V) G) (fixed : Array Nat) (Δt : Float)
    (bc : Array FloatArray) : Array FloatArray := Id.run do
  let np := m.totalNodes
  let (A, M, b) := assemble m
  let LHS := block2 np #[(M, 0, 0, 1), (M, 0, 1, -Δt / 2), (A, 1, 0, Δt / 2), (M, 1, 1, 1)]
  let RHS := block2 np #[(M, 0, 0, 1), (M, 0, 1, Δt / 2), (A, 1, 0, -Δt / 2), (M, 1, 1, 1)]
  let zkb : FloatArray := ⟨Array.replicate np 0 ++ b.data.map (Δt * ·)⟩
  let fx := fixed ++ fixed.map (np + ·)
  let isFixed := fx.foldl (fun (s : Array Bool) i => s.set! i true) (Array.replicate (2 * np) false)
  let free := (Array.range (2 * np)).filter fun i => isFixed[i]! == false
  let Aff := submatrix LHS free free
  let Afx := submatrix LHS free fx
  let F := Aff.luNoPivot
  let mut sol : FloatArray := ⟨Array.replicate (2 * np) 0⟩
  let mut g0 : FloatArray := ⟨Array.replicate fixed.size 0⟩
  let mut out : Array FloatArray := #[]
  for g in bc do
    let vb : FloatArray := ⟨(Array.range fixed.size).map fun i =>
      2 * (g.get! i - g0.get! i) / Δt - sol.get! (np + fixed[i]!)⟩
    let gv : FloatArray := ⟨g.data ++ vb.data⟩
    let r := vadd (RHS.mulVec sol) zkb
    let ax := Afx.mulVec gv
    let rhs : FloatArray := ⟨(Array.range free.size).map fun i => r.get! free[i]! - ax.get! i⟩
    let xf := match F with
      | some F => F.solve rhs
      | none => Aff.solve rhs
    for i in [0:fx.size] do sol := sol.set! fx[i]! (gv.get! i)
    for i in [0:free.size] do sol := sol.set! free[i]! (xf.get! i)
    g0 := g
    out := out.push ⟨sol.data.extract 0 np⟩
  return out

/-- Julia `solvebistable(ic, ϵ, T, f)`: semi-implicit Euler for `u_t = ϵΔu + f(u)` (natural
boundary), with three Picard iterations
`ξ⁽ᵏ⁺¹⁾ = (M + dt ϵ A) \ (M ξₙ + dt M f(ξ⁽ᵏ⁾))` per step. `steps + 1` slices. -/
def solveBistable (m : SimplexBundle n (HPoint V) G) (ic : FloatArray) (ϵ : Float := 0.01)
    (dt : Float := 0.1) (steps : Nat := 100) (f : Float → Float := fun u => u - u ^ 3) :
    Array FloatArray :=
  let (A, M, _) := assemble m
  let MA := M + (dt * ϵ) * A
  let F := MA.cholesky
  let solve := fun (r : FloatArray) => match F with
    | some F => F.solve r
    | none => MA.solve r
  let step := fun (ξ : FloatArray) =>
    (List.range 3).foldl (fun ξt _ =>
      solve (vadd (M.mulVec ξ) (vscale dt (M.mulVec ⟨ξt.data.map f⟩)))) ξ
  (List.range steps).foldl (fun out _ => out.push (step out.back!)) #[ic]

/-- Julia `solvebistable_newton(ic, ϵ, T, f, df)`: the same scheme with three Newton iterations
per step (`J = M + dt ϵ A − dt M_{f′}`, `M_{f′}` the mass weighted by `f′` of the element means,
and the lumped load of `f`). -/
def solveBistableNewton (m : SimplexBundle n (HPoint V) G) (ic : FloatArray) (ϵ : Float := 0.01)
    (dt : Float := 0.1) (steps : Nat := 100) (f : Float → Float := fun u => u - u ^ 3)
    (df : Float → Float := fun u => 1 - 3 * u ^ 2) : Array FloatArray :=
  let w := vols m
  let (A, M, _) := assemble m
  let MA := M + (dt * ϵ) * A
  let N := Float.ofNat n
  let step := fun (ξ : FloatArray) =>
    (List.range 3).foldl (fun ξt _ =>
      let mid := (Array.range m.elements).map fun k =>
        ((verts m k).foldl (fun s v => s + ξt.get! v) 0) / N
      let (Mdf, b) := assembleMassLoad m ⟨ξt.data.map f⟩
        ⟨(Array.range m.elements).map fun k => df mid[k]! * w.get! k⟩ w
      let J := MA - dt * Mdf
      let ρ := vsub (vsub (MA.mulVec ξt) (M.mulVec ξ)) (vscale dt b)
      vsub ξt (J.solve ρ)) ξ
  (List.range steps).foldl (fun out _ => out.push (step out.back!)) #[ic]

/-- One Newton iteration of `solveNonlinearPoisson`: `‖d‖` and `‖r‖`. -/
structure NewtonStep where
  /-- The norm of the correction. -/
  d : Float
  /-- The norm of the residual. -/
  r : Float
  deriving Repr, Inhabited

/-- Julia `assemblejacobianresidue(f, pe, u, A, m, g)` for `−∇·(a(u)∇u) = f` (`f` per element):
with `ū` the element mean, `a = A(ū)`, `a′ = (A(ū + 10⁻⁸) − a)/10⁻⁸`, `γᵢ = ∇u·∇φᵢ`,
`J_loc[i, j] = a ∇φⱼ·∇φᵢ + (a′/N) γᵢ`, `r[tₖ] += (fₖ/N − a γ) mₖ`, and the boundary rows replaced by
the identity with `r = 0`. -/
def jacobianResidue (m : SimplexBundle n (HPoint V) G) (fixed : Array Nat) (f : Nat → Float)
    (u : FloatArray) (Afcn : Float → Float) (w : FloatArray := vols m)
    (g : Array (Array (Array Float)) := grads m) (tiny : Float := 1e-8) : Sparse × FloatArray :=
  Id.run do
    let np := m.totalNodes
    let N := Float.ofNat n
    let d := V.n - 1
    let isFixed := fixed.foldl (fun (s : Array Bool) i => s.set! i true) (Array.replicate np false)
    let mut I : Array Nat := #[]
    let mut J : Array Nat := #[]
    let mut X : FloatArray := .empty
    let mut r : FloatArray := ⟨Array.replicate np 0⟩
    for k in [0:m.elements] do
      let vs := verts m k
      let gk := g[k]!
      let uc := (vs.foldl (fun s v => s + u.get! v) 0) / N
      let a := Afcn uc
      let da := (Afcn (uc + tiny) - a) / tiny
      let gu := (Array.range d).map fun c => (Array.range n).foldl (fun s j => s + u.get! vs[j]! * gk[j]![c]!) 0
      let gug := (Array.range n).map fun i => dot gu gk[i]!
      let mk := w.get! k
      for i in [0:n] do
        for j in [0:n] do
          I := I.push vs[i]!; J := J.push vs[j]!
          X := X.push ((a * dot gk[j]! gk[i]! + da / N * gug[i]!) * mk)
        r := r.set! vs[i]! (r.get! vs[i]! + (f k / N - a * gug[i]!) * mk)
    -- the boundary rows: identity, zero residual
    let mut I' : Array Nat := #[]
    let mut J' : Array Nat := #[]
    let mut X' : FloatArray := .empty
    for q in [0:I.size] do
      if isFixed[I[q]!]! == false then
        I' := I'.push I[q]!; J' := J'.push J[q]!; X' := X'.push (X.get! q)
    for v in fixed do
      I' := I'.push v; J' := J'.push v; X' := X'.push 1
      r := r.set! v 0
    return (Sparse.ofTriplets np np I' J' X', r)

/-- Julia `solvenonlinearpoisson(f, pe, A)`: five Newton iterations from `u = 0` for
`−∇·(a(u)∇u) = f`, `u = 0` on `e` (`f` per element); the solution and the log of `(‖d‖, ‖r‖)`
that Julia prints. -/
def solveNonlinearPoisson (m : SimplexBundle n (HPoint V) G) (e : SimplexBundle k (HPoint V) G)
    (f : Nat → Float) (Afcn : Float → Float) (iterations : Nat := 5) :
    FloatArray × Array NewtonStep :=
  let w := vols m
  let g := grads m
  let fixed := nodesOf e
  (List.range iterations).foldl (fun (u, log) _ =>
    let (J, r) := jacobianResidue m fixed f u Afcn w g
    let d := J.solve r
    (vadd u d, log.push ⟨vnorm d, vnorm r⟩)) ((⟨Array.replicate m.totalNodes 0⟩ : FloatArray), #[])

/-! ## Plane-strain elasticity -/

/-- Julia `Eν2Lame(E, ν)`: `(μ, λ)`. -/
def lame (E ν : Float) : Float × Float := (E / (2 * (1 + ν)), E * ν / ((1 + ν) * (1 - 2 * ν)))

/-- Julia `assembleelastic(f, μ, λ)` with bug B11 fixed: the plane-strain stiffness
`Σₖ Bₖᵀ D Bₖ mₖ` (`D = diag(2μ, 2μ, μ) + λ [1 1 0; 1 1 0; 0 0 0]`, `B` with columns
`(∂ₓφₐ, 0, ∂ᵧφₐ)`, `(0, ∂ᵧφₐ, ∂ₓφₐ)`), the mass on each component, and the consistent load
`Σₖ massₖ fₖ` (accumulated). DOFs are interleaved: node `v` has `2v` (x) and `2v + 1` (y). `force`
is nodal. Triangles only. -/
def assembleElastic (m : SimplexBundle 3 (HPoint V) G) (force : Array (Float × Float)) (μ lam : Float) :
    Sparse × Sparse × FloatArray := Id.run do
  let np := m.totalNodes
  let w := vols m
  let g := grads m
  let D := #[#[2 * μ + lam, lam, 0], #[lam, 2 * μ + lam, 0], #[0, 0, μ]]
  let mut IK : Array Nat := #[]
  let mut JK : Array Nat := #[]
  let mut XK : FloatArray := .empty
  let mut IM : Array Nat := #[]
  let mut JM : Array Nat := #[]
  let mut XM : FloatArray := .empty
  let mut F : FloatArray := ⟨Array.replicate (2 * np) 0⟩
  for k in [0:m.elements] do
    let vs := verts m k
    let gk := g[k]!
    let mk := w.get! k
    -- B: 3 × 6, column 2a = (∂x, 0, ∂y), column 2a+1 = (0, ∂y, ∂x)
    let B : Array (Array Float) := (Array.range 6).map fun c =>
      let a := c / 2
      let gx := gk[a]![0]!
      let gy := gk[a]![1]!
      if c % 2 == 0 then #[gx, 0, gy] else #[0, gy, gx]
    let dofs := (Array.range 6).map fun c => 2 * vs[c / 2]! + c % 2
    let DB := (Array.range 6).map fun i => (Array.range 3).map fun r => dot D[r]! B[i]!
    for i in [0:6] do
      for j in [0:6] do
        -- `Bⱼ·D Bᵢ` from the smaller index, so the matrix is exactly symmetric
        let x := if i ≤ j then dot B[j]! DB[i]! else dot B[i]! DB[j]!
        IK := IK.push dofs[i]!; JK := JK.push dofs[j]!; XK := XK.push (x * mk)
    for a in [0:3] do
      for b in [0:3] do
        let x := massEntry 3 a b * mk
        IM := IM.push (2 * vs[a]!); JM := JM.push (2 * vs[b]!); XM := XM.push x
        IM := IM.push (2 * vs[a]! + 1); JM := JM.push (2 * vs[b]! + 1); XM := XM.push x
        F := F.set! (2 * vs[a]!) (F.get! (2 * vs[a]!) + x * force[vs[b]!]!.1)
        F := F.set! (2 * vs[a]! + 1) (F.get! (2 * vs[a]! + 1) + x * force[vs[b]!]!.2)
  return (Sparse.ofTriplets (2 * np) (2 * np) IK JK XK,
    Sparse.ofTriplets (2 * np) (2 * np) IM JM XM, F)

/-- Julia `solveelastic(f, e, E, ν)` (fixed): `K u = F` with prescribed displacements on the
nodes of `e` (Julia clamps them to zero; `bc` gives the values, default zero). Returns the nodal
displacements. -/
def solveElastic (m : SimplexBundle 3 (HPoint V) G) (e : SimplexBundle k (HPoint V) G)
    (force : Array (Float × Float)) (E : Float := 1) (ν : Float := 0.3)
    (bc : HPoint V → Float × Float := fun _ => (0, 0)) : Array (Float × Float) :=
  let (μ, lam) := lame E ν
  let (K, _, F) := assembleElastic m force μ lam
  let bn := nodesOf e
  let fixed := bn.flatMap fun v => #[2 * v, 2 * v + 1]
  let pts := (Array.range m.totalNodes).map fun v =>
    (Chain.ofFn fun c => m.coord (v + 1) c.1 : HPoint V)
  let vals : FloatArray := ⟨bn.flatMap fun v => let (x, y) := bc pts[v]!; #[x, y]⟩
  let d := solveDirichlet K F fixed vals
  (Array.range m.totalNodes).map fun v => (d.get! (2 * v), d.get! (2 * v + 1))

/-! ## Triangle edges, Crouzeix–Raviart Stokes and DIPG -/

/-- The edges of a triangle mesh in Julia's local convention (edge `j` of an element is opposite
vertex `j`): per element the three 0-based edge ids, the edges as 0-based node pairs (first
appearance order), and per element and edge the 1-based neighbour across it (`0` on the
boundary). -/
structure TriEdges where
  /-- `edgeOf[k][j]`: the edge opposite vertex `j` of element `k`. -/
  edgeOf : Array (Array Nat)
  /-- The edges `(a, b)`, `a < b`. -/
  edges : Array (Nat × Nat)
  /-- `nbr[k][j]`: the element (1-based) across edge `j` of `k`, `0` on the boundary. -/
  nbr : Array (Array Nat)
  deriving Inhabited

/-- Build `TriEdges`. -/
def triEdges (m : SimplexBundle 3 (HPoint V) G) : TriEdges := Id.run do
  let mut ids : Std.HashMap (Nat × Nat) Nat := {}
  let mut edges : Array (Nat × Nat) := #[]
  let mut owners : Array (Array Nat) := #[]
  let mut edgeOf : Array (Array Nat) := #[]
  for k in [0:m.elements] do
    let vs := verts m k
    let mut row : Array Nat := #[]
    for j in [0:3] do
      let a := vs[(j + 1) % 3]!
      let b := vs[(j + 2) % 3]!
      let key := (min a b, max a b)
      match ids.get? key with
      | some e =>
        row := row.push e
        owners := owners.modify e (·.push k)
      | none =>
        let e := edges.size
        ids := ids.insert key e
        edges := edges.push key
        owners := owners.push #[k]
        row := row.push e
    edgeOf := edgeOf.push row
  let nbr := (Array.range m.elements).map fun k => (edgeOf[k]!).map fun e =>
    match owners[e]!.find? (· != k) with
    | some o => o + 1
    | none => 0
  return ⟨edgeOf, edges, nbr⟩

/-- The boundary edges (used by one element), sorted. -/
def TriEdges.boundary (t : TriEdges) : Array Nat :=
  (Array.range t.edges.size).filter fun e =>
    (Array.range t.nbr.size).any fun k => (Array.range 3).any fun j => t.edgeOf[k]![j]! == e && t.nbr[k]![j]! == 0

/-- The midpoint of edge `e` as a homogeneous point. -/
def edgeMid (m : SimplexBundle n (HPoint V) G) (t : TriEdges) (e : Nat) : HPoint V :=
  let (a, b) := t.edges[e]!
  Chain.ofFn fun c => (m.coord (a + 1) c.1 + m.coord (b + 1) c.1) / 2

/-- Julia `assemblestokes(pt, ν, t2e)`: the Crouzeix–Raviart/P0 saddle-point matrix
`[νA 0 B₁ᵀ 0; 0 νA B₂ᵀ 0; B₁ B₂ 0 m; 0 0 mᵀ 0]` on the unknowns (u at the edges, v at the edges,
p per element, the mean-pressure multiplier): `A` the CR stiffness (`∇ψⱼ = −2∇φⱼ`, Julia's
`gradientCR`) and `B_c[k, e] = −mₖ ∂_c ψ` (`assembledivergence(t2e, m, −gCR)`). -/
def assembleStokes (m : SimplexBundle 3 (HPoint V) G) (t : TriEdges) (ν : Float := 0.1) : Sparse :=
  Id.run do
    let ne := t.edges.size
    let nt := m.elements
    let N := 2 * ne + nt + 1
    let w := vols m
    let g := grads m
    let mut I : Array Nat := #[]
    let mut J : Array Nat := #[]
    let mut X : FloatArray := .empty
    for k in [0:nt] do
      let mk := w.get! k
      let gcr := (Array.range 3).map fun j => g[k]![j]!.map (-2 * ·)
      let es := t.edgeOf[k]!
      for i in [0:3] do
        for j in [0:3] do
          let a := ν * (dot gcr[j]! gcr[i]! * mk)
          I := I.push es[i]!; J := J.push es[j]!; X := X.push a
          I := I.push (ne + es[i]!); J := J.push (ne + es[j]!); X := X.push a
      for i in [0:3] do
        for c in [0:2] do
          let bkc := mk * (-(gcr[i]![c]!))
          -- B_c[k, e] and its transpose
          I := I.push (2 * ne + k); J := J.push (c * ne + es[i]!); X := X.push bkc
          I := I.push (c * ne + es[i]!); J := J.push (2 * ne + k); X := X.push bkc
      I := I.push (2 * ne + k); J := J.push (N - 1); X := X.push mk
      I := I.push (N - 1); J := J.push (2 * ne + k); X := X.push mk
    return Sparse.ofTriplets N N I J X

/-- Julia `solvestokes(pt, bc, ν)` (no body force): the velocity at the edges (CR degrees of
freedom) and the pressure per element (mean zero), with the velocity `bc` imposed at the
midpoints of the boundary edges. -/
def solveStokes (m : SimplexBundle 3 (HPoint V) G) (bc : HPoint V → Float × Float) (ν : Float := 0.1) :
    Array (Float × Float) × FloatArray :=
  let t := triEdges m
  let ne := t.edges.size
  let nt := m.elements
  let L := assembleStokes m t ν
  let be := t.boundary
  let fixed := be ++ be.map (ne + ·)
  let gv := be.map fun e => bc (edgeMid m t e)
  let vals : FloatArray := ⟨gv.map (·.1) ++ gv.map (·.2)⟩
  let ξ := solveDirichlet L ⟨Array.replicate (2 * ne + nt + 1) 0⟩ fixed vals
  ((Array.range ne).map fun e => (ξ.get! e, ξ.get! (ne + e)),
    ⟨(Array.range nt).map fun k => ξ.get! (2 * ne + k)⟩)

/-- The discontinuous P1 copy of a triangle mesh (Julia's DIPG bundle): element `k`'s vertex `j`
is the node `3k + j`. -/
def discontinuous (m : SimplexBundle 3 (HPoint V) G) : SimplexBundle 3 (HPoint V) :=
  let pts := (Array.range m.elements).flatMap fun k => (verts m k).map fun v =>
    (Chain.ofFn fun c => m.coord (v + 1) c.1 : HPoint V)
  SimplexBundle.ofPoints pts ((Array.range m.elements).map fun k => #v[3 * k + 1, 3 * k + 2, 3 * k + 3])

/-- Julia `assembleDIPG(pt, nbrs)` (`P`, `S`) on the discontinuous copy `discontinuous m`, with the
neighbours of the continuous mesh `m`: for every edge once (and every boundary edge), Simpson's
rule at the endpoints and midpoint, jumps `[λ⁺; −λ⁻]`, `PE = Σ w_q J_q J_qᵀ` (the penalty over the
edge length) and `SE = Σ w_q |e| J_q {∂ₙφ}ᵀ` (twice, without the average, on the boundary). -/
def assembleDIPG (m : SimplexBundle 3 (HPoint V) G) : Sparse × Sparse := Id.run do
  let t := triEdges m
  let nt := m.elements
  let np := 3 * nt
  let g := grads m
  let wq : Array Float := #[1 / 6, 4 / 6, 1 / 6]
  let pt := fun (v c : Nat) => m.coord (v + 1) c
  -- barycentrics of the point x on element k: λᵢ(x) = δᵢ₀ + ∇φᵢ·(x − p₀)
  let bary := fun (k : Nat) (x : Array Float) => Id.run do
    let p0 := (verts m k)[0]!
    return (Array.range 3).map fun i =>
      (if i == 0 then (1 : Float) else 0) + dot g[k]![i]! #[x[0]! - pt p0 1, x[1]! - pt p0 2]
  let mut IP : Array Nat := #[]
  let mut JP : Array Nat := #[]
  let mut XP : FloatArray := .empty
  let mut IS : Array Nat := #[]
  let mut JS : Array Nat := #[]
  let mut XS : FloatArray := .empty
  for i in [0:nt] do
    let vs := verts m i
    for j in [0:3] do
      let n0 := t.nbr[i]![j]!
      if n0 > i + 1 then continue
      let n := if n0 == 0 then i else n0 - 1
      let a := vs[(j + 1) % 3]!
      let b := vs[(j + 2) % 3]!
      let xa := #[pt a 1, pt a 2]
      let xb := #[pt b 1, pt b 2]
      let dx : Float := xb[0]! - xa[0]!
      let dy : Float := xb[1]! - xa[1]!
      let len := Float.sqrt (dx * dx + dy * dy)
      -- outward unit normal of edge j (away from vertex j)
      let nrm0 := #[(xb[1]! - xa[1]!) / len, -(xb[0]! - xa[0]!) / len]
      let toJ := #[pt vs[j]! 1 - xa[0]!, pt vs[j]! 2 - xa[1]!]
      let nrm := if dot nrm0 toJ > 0 then nrm0.map (- ·) else nrm0
      let avg := ((Array.range 3).map fun q => dot nrm g[i]![q]! / 2) ++
        ((Array.range 3).map fun q => dot nrm g[n]![q]! / 2)
      let qs := #[xa, #[(xa[0]! + xb[0]!) / 2, (xa[1]! + xb[1]!) / 2], xb]
      let jumps : Array (Array Float) := qs.map fun x => bary i x ++ (bary n x).map (- ·)
      let dofs := (Array.range 3).map (3 * i + ·) ++ (Array.range 3).map (3 * n + ·)
      let size := if n == i then 3 else 6
      for r in [0:size] do
        for c in [0:size] do
          let pe := (List.range 3).foldl (fun s q => s + jumps[q]![r]! * wq[q]! * jumps[q]![c]!) 0
          let se := (List.range 3).foldl (fun s q => s + jumps[q]![r]! * (wq[q]! * len) * avg[c]!) 0
          IP := IP.push dofs[r]!; JP := JP.push dofs[c]!; XP := XP.push pe
          IS := IS.push dofs[r]!; JS := JS.push dofs[c]!; XS := XS.push (if n == i then 2 * se else se)
  return (Sparse.ofTriplets np np IP JP XP, Sparse.ofTriplets np np IS JS XS)

/-- Julia `solvepoissonDIPG(f, c, β, α)`: `(A − S + αSᵀ + βP) u = b` on the discontinuous copy
(`α = −1` SIPG, `+1` NIPG, `0` IIPG; Dirichlet `u = 0` weakly through the penalty). Returns the
discontinuous mesh and the nodal values (three per element). -/
def solvePoissonDIPG (m : SimplexBundle 3 (HPoint V) G) (f : HPoint V → Float) (c β : Float)
    (α : Float := -1) : SimplexBundle 3 (HPoint V) × FloatArray :=
  let dm := discontinuous m
  let b := dm.assembleload f
  let A := assembleStiffness dm (fun _ => c)
  let (P, S) := assembleDIPG m
  (dm, (A - S + α * S.transpose + β * P).solve b)

/-! ## P2 (quadratic) Lagrange elements and isoparametric quadrature -/

/-- Julia `shapeP1(r, s)`: `(1 − r − s, r, s)`. -/
def shapeP1 (r s : Float) : Array Float := #[1 - r - s, r, s]

/-- Julia `gradientP1(r, s)`: `(∂ᵣ, ∂ₛ)` of the P1 shapes. -/
def gradientP1 (_ _ : Float) : Array (Float × Float) := #[(-1, -1), (1, 0), (0, 1)]

/-- Julia `shapeP2(r, s)` (§4.7): vertices, then the nodes on the edges opposite vertices 1, 2, 3. -/
def shapeP2 (r s : Float) : Array Float :=
  #[1 - 3 * r - 3 * s + 2 * r * r + 4 * r * s + 2 * s * s, 2 * r * r - r, 2 * s * s - s, 4 * r * s,
    4 * s - 4 * r * s - 4 * s * s, 4 * r - 4 * r * r - 4 * r * s]

/-- Julia `gradientP2(r, s)` (§4.7). -/
def gradientP2 (r s : Float) : Array (Float × Float) :=
  #[(-3 + 4 * r + 4 * s, -3 + 4 * r + 4 * s), (4 * r - 1, 0), (0, 4 * s - 1), (4 * s, 4 * r),
    (-4 * s, 4 - 4 * r - 8 * s), (4 - 8 * r - 4 * s, -4 * r)]

/-- A planar Lagrange mesh of degree 1 or 2: node coordinates, element node lists (Julia
`LagrangeP2` order for degree 2: `[v₁, v₂, v₃, e(v₂v₃), e(v₁v₃), e(v₁v₂)]`, edge nodes numbered
after the vertices), and the boundary nodes. -/
structure LagrangeMesh where
  /-- Degree (1 or 2). -/
  degree : Nat
  /-- Node coordinates. -/
  xy : Array (Float × Float)
  /-- Element node lists (0-based). -/
  elems : Array (Array Nat)
  /-- Boundary nodes (0-based, sorted). -/
  boundary : Array Nat
  deriving Inhabited

/-- Julia `LagrangeP2(t)` (degree 2) or the P1 mesh itself (degree 1) of a triangle mesh. -/
def lagrange (m : SimplexBundle 3 (HPoint V) G) (degree : Nat := 2) : LagrangeMesh :=
  let t := triEdges m
  let np := m.totalNodes
  let vxy := (Array.range np).map fun v => (m.coord (v + 1) 1, m.coord (v + 1) 2)
  let be := t.boundary
  let bv := nodesOf m.boundary
  if degree ≤ 1 then ⟨1, vxy, (Array.range m.elements).map (verts m), bv⟩
  else
    let exy := t.edges.map fun (a, b) => ((vxy[a]!.1 + vxy[b]!.1) / 2, (vxy[a]!.2 + vxy[b]!.2) / 2)
    ⟨2, vxy ++ exy, (Array.range m.elements).map fun k => verts m k ++ t.edgeOf[k]!.map (np + ·),
      (bv ++ be.map (np + ·)).qsort (· < ·)⟩

/-- The shapes and reference gradients at the quadrature points of Julia's rules (`Gauss[2]` for
P1, `Gauss[4]` for P2; `GaussShape`, `GaussGradient`). -/
def quadrature (degree : Nat) : Array (Float × Array Float × Array (Float × Float)) :=
  let R := Adapode.Gauss (2 * degree)
  (Array.range R.w.size).map fun q =>
    let r := R.r.get! q
    let s := R.s.get! q
    (R.w.get! q / 2, if degree ≤ 1 then shapeP1 r s else shapeP2 r s,
      if degree ≤ 1 then gradientP1 r s else gradientP2 r s)

/-- Julia `isoparametric(xy, dS)`: `J = dS xyᵀ`, the physical gradients `J⁻¹ dS`, and `det J`. -/
def isoparametric (xy : Array (Float × Float)) (dS : Array (Float × Float)) :
    Array (Float × Float) × Float :=
  let j11 := (List.range dS.size).foldl (fun a i => a + dS[i]!.1 * xy[i]!.1) 0
  let j12 := (List.range dS.size).foldl (fun a i => a + dS[i]!.1 * xy[i]!.2) 0
  let j21 := (List.range dS.size).foldl (fun a i => a + dS[i]!.2 * xy[i]!.1) 0
  let j22 := (List.range dS.size).foldl (fun a i => a + dS[i]!.2 * xy[i]!.2) 0
  let det := j11 * j22 - j12 * j21
  (dS.map fun (a, b) => ((j22 * a - j12 * b) / det, (-j21 * a + j11 * b) / det), det)

/-- Julia `assemblemassPN` / `assemblestiffnessPN` together with the consistent load
`bᵢ = Σ_q w_q det J f(x_q) Sᵢ(x_q)` (Julia's `PN` assembly has no load). -/
def assemblePN (L : LagrangeMesh) (f : Float × Float → Float := fun _ => 0) :
    Sparse × Sparse × FloatArray := Id.run do
  let np := L.xy.size
  let Q := quadrature L.degree
  let mut IA : Array Nat := #[]
  let mut JA : Array Nat := #[]
  let mut XA : FloatArray := .empty
  let mut XM : FloatArray := .empty
  let mut b : FloatArray := ⟨Array.replicate np 0⟩
  for ti in L.elems do
    let xy := ti.map (L.xy[·]!)
    let d := ti.size
    let mut AK : Array Float := Array.replicate (d * d) 0
    let mut MK : Array Float := Array.replicate (d * d) 0
    for (w, S, dS) in Q do
      let (g, det) := isoparametric xy dS
      let wx := w * det
      let xq := (List.range d).foldl (fun (a : Float × Float) i => (a.1 + S[i]! * xy[i]!.1, a.2 + S[i]! * xy[i]!.2)) (0, 0)
      let fq := f xq
      for i in [0:d] do
        b := b.set! ti[i]! (b.get! ti[i]! + wx * fq * S[i]!)
        for j in [0:d] do
          AK := AK.modify (i * d + j) (· + wx * (g[j]!.1 * g[i]!.1 + g[j]!.2 * g[i]!.2))
          MK := MK.modify (i * d + j) (· + S[i]! * (S[j]! * wx))
    for i in [0:d] do
      for j in [0:d] do
        IA := IA.push ti[i]!; JA := JA.push ti[j]!
        XA := XA.push AK[i * d + j]!; XM := XM.push MK[i * d + j]!
  return (Sparse.ofTriplets np np IA JA XA, Sparse.ofTriplets np np IA JA XM, b)

/-- `−Δu = f`, `u = 0` on the boundary, with Lagrange elements of the mesh's degree. -/
def solvePoissonPN (L : LagrangeMesh) (f : Float × Float → Float) : FloatArray :=
  let (A, _, b) := assemblePN L f
  solveDirichlet A b L.boundary

end Adapode.FEM
