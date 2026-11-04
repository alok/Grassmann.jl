import Cartan.Element
import Cartan.Solve

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

end Adapode.FEM
