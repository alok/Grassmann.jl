import Cartan.Product
import AbstractAnalysis.Limit

/-!
# Small Cartan utilities

`besseljzero`, `spacing`, `interval_scale`, `affinepoint`, `⧺` (chain concatenation),
`graphbundle` and `discontinuous` of simplex fields (Cartan.jl `src/Cartan.jl:324-329, 474-479,
598-606`, `src/topology.jl:26-28, 113-115`).
-/

namespace Cartan

open Grassmann DirectSum StaticVectors AbstractTensors JuliaBase MeshTopology

/-- Julia `besseljzero(n, m, x = (m + n/2 - 1/4)π) = x - (4n² - 1)/(8x)` (`Cartan.jl:599`): the
first McMahon term of the `m`-th zero of `J_n`. -/
def besseljzero (n m : Nat) : Float :=
  let nf := n.toUInt64.toFloat
  let x := (m.toUInt64.toFloat + nf / 2 - (1 : Float) / 4) * piF
  x - (4 * (nf * nf) - 1) / (8 * x)

/-- Julia `affinepoint(p)` (`topology.jl:26-28`): the homogeneous lift `(1, p…)`. -/
def affinePoint {V : TensorBundle} (p : Chain V 1 Float) : Chain (TensorBundle.euclidean (Leibniz.binomial V.n 1 + 1)) 1 Float :=
  Chain.ofFn fun i => if i.1 = 0 then 1 else p.v.get! (i.1 - 1)

/-- Julia `affinepoint(p)` of a product-space point (`topology.jl:26-28`): `(1, x, y, …)` in the
algebra one dimension up (`1.0v₁ + 0.5v₂ + 0.25v₃`). -/
def AffinePoint.homogeneous {N : Nat} (p : AffinePoint N) : Chain (TensorBundle.euclidean (N + 1)) 1 Float :=
  Chain.ofFn fun i => if i.1 = 0 then 1 else p.get! (i.1 - 1)

/-- Julia `a ⧺ b` of two vectors (`topology.jl:115`): the coordinates of `a` followed by those of
`b`, a vector of the Euclidean algebra on all of them. -/
def concat {V W : TensorBundle} (a : Chain V 1 Float) (b : Chain W 1 Float) :
    Chain (TensorBundle.euclidean (Leibniz.binomial V.n 1 + Leibniz.binomial W.n 1)) 1 Float :=
  let na := Leibniz.binomial V.n 1
  Chain.ofFn fun i => if i.1 < na then a.v.get! i.1 else b.v.get! (i.1 - na)

/-- Julia `⧺` (`\doubleplus`). -/
scoped infixl:65 " ⧺ " => concat

namespace TensorField

variable {F : Type} [FlatFiber F] [LinearFiber F] [FiberNorm F]

/-- `‖t[j] - t[i]‖` of two fibers, on the flat encoding. -/
def diffNorm {M : Type} [FrameBundle M] {m : M} (t : TensorField m F) (i j : Nat) : Float :=
  let w := FlatFiber.width F
  let buf := buildFlat (F := Float) w fun c => t.data.get! (j * w + c) - t.data.get! (i * w + c)
  fnorm (FlatFiber.read buf 0 : F)

/-- Julia `spacing(x)` of a 1-D field (`Cartan.jl:324`): `sum(norm.(diff(fiber(x))))/(length(x)-1)`
(Julia's pairwise sum). -/
def spacing1 {M : Type} [FrameBundle M] {m : M} (t : TensorField m F) : Float :=
  let n := card m
  F64.sum (buildFlat (F := Float) (n - 1) fun i => t.diffNorm i (i + 1)) / (n - 1).toUInt64.toFloat

/-- Julia `spacing(x, a+1)` of a grid field (`Cartan.jl:326-329`): the mean norm of the
differences along axis `a` (`norm.(diff(fiber(x), dims=a+1))`, summed in column-major order). -/
def spacingAxis {N : Nat} {P G : Type} {b : GridBundle N P G} (t : TensorField b F) (a : Fin N) : Float :=
  let s := b.size
  let d : Vector Nat N := s.set a (s[a] - 1)
  let len := MeshTopology.gridLength d
  let st := MeshTopology.axisStride s a
  let norms := buildFlat (F := Float) len fun k =>
    let idx := (MeshTopology.cartesianIndex d (k + 1)).map (· - 1)
    let lin := b.linear idx
    t.diffNorm lin (lin + st)
  F64.sum norms / len.toUInt64.toFloat

/-- Julia `spacing(x)` of an N-D grid field (`Cartan.jl:325`): the least mean spacing over the
axes. -/
def spacing {N : Nat} {P G : Type} {b : GridBundle N P G} (t : TensorField b F) : Float :=
  (List.finRange N).foldl (fun acc a => F64.min acc (t.spacingAxis a)) ((1 : Float) / 0)

end TensorField

/-- Julia `interval_scale(t)` of a 1-D grid (`Cartan.jl:476-479`): `points[end] - points[1]`. -/
def GridBundle.intervalScale1 {P G : Type} (b : GridBundle 1 P G) : Float := b.space.axes[0].width

/-- Julia `interval_scale(t)` of a product grid (`Cartan.jl:475`): the widths of the axes. -/
def GridBundle.intervalScale {N : Nat} {P G : Type} (b : GridBundle N P G) : Vector Float N :=
  b.space.widths

/-! ## Simplex fields -/

namespace TensorField

variable {n : Nat} {P G F : Type} [FlatFiber P] [FlatFiber F] [Inhabited G]

/-- Julia `graphbundle(t::SimplexMap)` (`Cartan.jl:606`): the mesh lifted one dimension up by the
field's values (the points `graph.(t)`), with the same elements (numbered within the bundle) and
the same fibers. -/
def graphBundle {b : SimplexBundle n P G} (t : TensorField b F) :
    Σ b' : SimplexBundle n (Chain (TensorBundle.euclidean (FlatFiber.width P + FlatFiber.width F)) 1 Float),
      TensorField b' F :=
  let b' : SimplexBundle n _ := ⟨⟨buildFlat (card b) t.graphAt, .induced, 0⟩, b.top.subImmersion⟩
  ⟨b', (t.rebase? b').getD default⟩

/-- Julia `t(i::ImmersedTopology)` for a simplex field (`Cartan.jl:311`): the field restricted to
the sub-mesh `top` of the same point cloud, `TensorField(coordinates(t)(i), fiber(t)[vertices(i)])`
(vertices of `top` outside the field's bundle read the zero fiber). -/
def restrict {b : SimplexBundle n P G} (t : TensorField b F) (top : SimplexTopology n) :
    TensorField (b.withTop top) F :=
  ofFn _ fun i =>
    let full := top.getImage (i + 1)
    let j := b.top.vinv.get (full - 1)
    if j == 0 then FlatFiber.read (buildFlat (F := Float) (FlatFiber.width F) fun _ => 0) 0
    else t.get (j - 1)

/-- Julia `discontinuous(t::SimplexMap)` (`Cartan.jl:604-605`): the field over the discontinuous
bundle of its base, node `i` carrying the fiber of its vertex (`view(fiber(t), vertices(m))`). -/
def discontinuous {b : SimplexBundle n P G} (t : TensorField b F) : TensorField b.discontinuous F :=
  let vinv := b.top.vinv
  ofFn _ fun i => t.get (vinv.get (b.discontinuous.image i - 1) - 1)

/-- Julia `discontinuous(t::SimplexMap)` (`Cartan.jl:604-605`) as a disconnected mesh: every element
gets its own copies of its vertices (`view(fiber(t), vertices(m))`, the per-element vertex
values), and the element `e` uses the nodes `N e, …, N e + N - 1`. -/
def disconnect {b : SimplexBundle n P G} (t : TensorField b F) : Σ b' : SimplexBundle n P, TensorField b' F :=
  let els := (b.top.topology)
  let ids := els.flatMap (·.toArray)
  let pts := ids.foldl (fun acc v => FlatFiber.push acc (b.cloud.get (v - 1))) FloatArray.empty
  let conn : Array (Vector Nat n) := (Array.range els.size).map fun e => Vector.ofFn fun k => n * e + k.1 + 1
  let b' : SimplexBundle n P := ⟨⟨pts, .induced, 0⟩, SimplexTopology.ofElements conn (p := some ids.size)⟩
  let vinv := b.top.vinv
  ⟨b', ofFn b' fun i => t.get (vinv.get (ids[i]?.getD 1 - 1) - 1)⟩

end TensorField

/-! ## Orbits of field maps (AbstractAnalysis `orbit`, `Cartan.jl:37`)

Julia iterates maps of fields with AbstractAnalysis's `orbit`, `orbiterror` and `orbithold`,
measuring steps with `supnorm(a, b) = supnorm(a - b)` (the `@metric` of `supnorm`,
`metric.jl:24-33`; a field's `supnorm` is the largest fiber norm, `Cartan.jl:513`). -/

namespace TensorField

variable {M : Type} [FrameBundle M] {m : M} {F : Type} [FlatFiber F] [FiberNorm F]
  [Sub (TensorField m F)]

/-- Julia `supnorm(a, b)` of two fields: `supnorm(a - b)`. -/
def supdist (a b : TensorField m F) : Float := (a - b).supnorm

/-- Julia `orbit(f, x, ϵ)` for a map of fields: iterate until `supnorm(xₙ₊₁ - xₙ) ≤ ϵ`. -/
def orbitLimit (f : TensorField m F → TensorField m F) (x : TensorField m F)
    (ϵ : Float := 5 * 2.220446049250313e-16) : AbstractAnalysis.Limit (TensorField m F) (TensorField m F) :=
  AbstractAnalysis.orbit f x ϵ supdist

/-- Julia `orbiterror(f, x, ϵ)`: `orbitLimit` with the residual of every step. -/
def orbitError (f : TensorField m F → TensorField m F) (x : TensorField m F)
    (ϵ : Float := 5 * 2.220446049250313e-16) :
    AbstractAnalysis.Limit (TensorField m F) (TensorField m F) × FloatArray :=
  AbstractAnalysis.orbitError f x ϵ supdist

/-- Julia `orbit(f, x, k::Int)`: exactly `k` steps. -/
def orbitSteps (f : TensorField m F → TensorField m F) (x : TensorField m F) (k : Nat) :
    AbstractAnalysis.Limit (TensorField m F) (TensorField m F) :=
  AbstractAnalysis.orbitN f x k supdist

/-- Julia `orbithold(f, x, 1:k)`: iterate `xₙ ↦ f(x, xₙ)` with `x` held. -/
def orbitHold (f : TensorField m F → TensorField m F → TensorField m F) (x : TensorField m F)
    (k : Nat) : AbstractAnalysis.Limit (TensorField m F) (TensorField m F) :=
  AbstractAnalysis.orbitHold f x k supdist

end TensorField

end Cartan
