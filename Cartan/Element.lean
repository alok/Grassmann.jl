import Cartan.Operator
import Cartan.Solve

/-!
# Finite elements on simplex bundles (Cartan.jl `src/element.jl`)

The finite-element layer on `SimplexBundle`/`FaceBundle` (port notes
`cartan-element-spectral-plot.md` §2.1, §4.1-4.8): simplex geometry, P1 hat-function gradients,
element↔node transfers, the lumped load vector, evaluation of piecewise-linear fields, 1-D meshes
and their refinement, graph operators, and the mesh-level forwarders of MeshTopology. Adapode's
assembly (stiffness, mass, convection, solvers) consumes `volumes`, `gradienthat` and `means`.

**Points.** A mesh point is homogeneous, `Chain V 1 Float` with coordinates `(1, x₁, …, x_d)`
(Julia `Chain{varmanifold(d+1),1}`), so `V.n = d + 1`; an element with `n` vertices is the
`Simplex (euclidean n) V Float` whose columns are its points (`simplexAt`, Julia
`affinehull(t)[k]`), and every per-element formula is Grassmann's (`Grassmann.Forms.Simplex`),
bit-identical to Julia's.

**Julia defects fixed** (port notes §8.3; the tests record Julia's values and the fix):
* **B3** — `gradienthat` of a 1-D element with `x₂ < x₁` or of a clockwise triangle divides by the
  *unsigned* measure, so every gradient is negated; here the measure is signed (for positively
  oriented elements the arithmetic, and so the result, is Julia's bit for bit).
* **B1** — `assembleload`/`assembleincidence`/`interp`/`gradient` throw `UndefVarError` upstream
  (MeshTopology never imports `fibertype`, `means`, …); implemented with the intended semantics.
* `refinemesh!` resizes `vertices(t)`, a `OneTo` for every mesh `initmesh` builds (MethodError);
  `refine1` returns the intended refined mesh.
* **B6** `interior` (swapped arguments) and **B5** `incidence(::FrameBundle)` (undefined `cols`)
  are MeshTopology's fixed `interiorNodes`/`incidence`.
* **B7** — Julia's `Δ(t) = Diagonal(degrees) - adjacency` mixes element counts with edge
  multiplicities (rows do not sum to zero); `laplacian` keeps Julia's matrix, `graphLaplacian`
  is the graph Laplacian `D - A` of the edge graph.
-/

namespace Cartan

open Grassmann DirectSum StaticVectors AbstractTensors JuliaBase MeshTopology Grassmann.Forms
open Cartan.Solve

/-- Homogeneous mesh points (Julia `Chain{varmanifold(d+1),1,Float64}`). -/
abbrev HPoint (V : TensorBundle) := Chain V 1 Float

/-- One element as a simplex operator: `n` columns, the homogeneous points. -/
abbrev ElementSimplex (n : Nat) (V : TensorBundle) := Simplex (TensorBundle.euclidean n) V Float

namespace SimplexBundle

variable {n : Nat} {V : TensorBundle} {G : Type}

/-- Coordinate `c` (0-based, homogeneous: `c = 0` is the `1`) of full vertex `v` (1-based). -/
@[inline] def coord (m : SimplexBundle n (HPoint V) G) (v c : Nat) : Float :=
  m.cloud.points.get! ((v - 1) * V.n + c)

/-- The number of elements (Julia `elements(t)`). -/
@[inline] def elements (m : SimplexBundle n (HPoint V) G) : Nat := m.top.elements

/-- The number of nodes of the full mesh (Julia `totalnodes(t)`). -/
@[inline] def totalNodes (m : SimplexBundle n (HPoint V) G) : Nat := m.top.totalNodes

/-- Element `e` (0-based) as a simplex operator (Julia `affinehull(t)[e+1]`). -/
def simplexAt (m : SimplexBundle n (HPoint V) G) (e : Nat) : ElementSimplex n V :=
  let vs := m.top.get (e + 1)
  TensorOperator.ofFn fun i j => m.coord vs[j.1]! i.1

/-- The face bundle of the mesh (Julia `FaceBundle(t)`). -/
abbrev faces' (m : SimplexBundle n (HPoint V) G) : FaceBundle n (HPoint V) G := .ofSimplex m

/-! ## Geometry (§4.1) -/

/-- The edge vectors `pᵢ - p₁` of element `e` without the homogeneous coordinate (Julia
`affineframe(t)[e+1]`). -/
def affineframeAt (m : SimplexBundle n (HPoint V) G) (e : Nat) :
    Simplex (TensorBundle.euclidean (n - 1)) (Forms.drop1 V) Float :=
  (m.simplexAt e).affineframe

/-- Whether the elements are embedded (fewer vertices than homogeneous dimensions, e.g.
triangles in 3-D). -/
@[inline] def embedded (_ : SimplexBundle n (HPoint V) G) : Bool := n < V.n

/-- `∧` of an element (Julia `∧(FaceBundle(t))[e+1]`): the wedge of its homogeneous points (a
pseudoscalar of `V`, one coefficient) or, embedded, of its edge vectors (`C(d, n-1)`
coefficients of a blade of `↓V`). -/
def wedgeAt (m : SimplexBundle n (HPoint V) G) (e : Nat) : Array Float :=
  if m.embedded then
    let F := m.affineframeAt e
    (wedgeList F.cols1).toArray
  else #[(m.simplexAt e).det]

/-- `(n-1)!` as a float. -/
def factF (k : Nat) : Float := Float.ofNat (TensorOperator.factorial k)

/-- Julia `detsimplex(t)[e+1] = ∧/(n-1)!` (a Grassmann element divided by a real: times the
reciprocal). -/
def detsimplexAt (m : SimplexBundle n (HPoint V) G) (e : Nat) : Array Float :=
  let r := 1 / factF (n - 1)
  (m.wedgeAt e).map (· * r)

/-- Julia `volumes(t)[e+1]` (`element.jl:45-54`): the length of a segment, else
`|detsimplex|` (the norm of the blade when embedded). -/
def volumeAt (m : SimplexBundle n (HPoint V) G) (e : Nat) : Float :=
  if n == 2 then (m.simplexAt e).edgelength
  else
    let d := m.detsimplexAt e
    if d.size == 1 then d[0]!.abs
    else Float.sqrt (d.foldl (fun s x => s + x * x) 0)

/-- Julia `volumes(t)`: the unsigned measures, a field over the elements. -/
def volumes (m : SimplexBundle n (HPoint V) G) : TensorField m.faces' Float :=
  TensorField.ofFn _ m.volumeAt

/-- The signed measure of a non-embedded element (`detsimplex`; `volumes` of an embedded one). -/
def signedVolumeAt (m : SimplexBundle n (HPoint V) G) (e : Nat) : Float :=
  if n == 2 && V.n == 2 then
    let T := m.simplexAt e
    let l := T.edgelength
    if T.entry 1 1 < T.entry 1 0 then -l else l
  else if m.embedded then m.volumeAt e
  else (m.detsimplexAt e)[0]!

/-- Julia `∧(t)` as a field of flat coefficients (per element: one float, or the blade). -/
def wedgeField (m : SimplexBundle n (HPoint V) G) : Array (Array Float) :=
  (Array.range m.elements).map m.wedgeAt

/-- The pairs `(i, j)`, `i < j < n`, in lexicographic order. -/
def pairsLex (n : Nat) : Array (Nat × Nat) :=
  (Array.range n).flatMap fun i => ((Array.range n).filter (i < ·)).map fun j => (i, j)

/-- The sign of the permutation `(i, j, K…)` of `0 … n-1` with `K` the rest ascending (the right
complement `⋆eᵢⱼ = σ e_K`). -/
def pairSign (n i j : Nat) : Bool :=
  -- inversions of (i, j, rest…): i and j each precede every smaller element of the rest
  let rest := (List.range n).filter fun k => k != i && k != j
  let inv := (rest.filter (· < i)).length + (rest.filter (· < j)).length + (if j < i then 1 else 0)
  inv % 2 == 1

/-- Julia `curls(t)[e+1]` (Grassmann `composite.jl:942-945`, `curl(m) = V(∇) × m = ⋆(∇ ∧ m)` of the
element's vertex chain): component `K` (the `(n-2)`-subsets in lexicographic order) is
`σ (p_j − p_i)` for the complementary pair `i < j`, the sign applied by negating the difference
(so zeros come out as `-0.0`, as in Julia). For a triangle: `(p₃ − p₂, −(p₃ − p₁), p₂ − p₁)`. -/
def curlsAt (m : SimplexBundle n (HPoint V) G) (e : Nat) : Values (HPoint V) (Leibniz.binomial n 2) :=
  let vs := m.top.get (e + 1)
  let ps := pairsLex n
  let P := ps.size
  Values.ofFn fun t =>
    let (i, j) := ps[P - 1 - t.1]!
    let neg := pairSign n i j
    Chain.ofFn fun c =>
      let d := m.coord vs[j]! c.1 - m.coord vs[i]! c.1
      if neg then -d else d

/-- Julia `means(t)`: element centroids `Σpᵢ/n` (times `1/n`). -/
def means (m : SimplexBundle n (HPoint V) G) : TensorField m.faces' (HPoint V) :=
  TensorField.ofFn _ fun e => (m.simplexAt e).mean

/-- Julia `barycenters(t)`: `Σ pᵢ`. -/
def barycenters (m : SimplexBundle n (HPoint V) G) : TensorField m.faces' (HPoint V) :=
  TensorField.ofFn _ fun e => (m.simplexAt e).barycenter

/-- Julia `centroids(t)`: `s / s[1]` with `s = Σ pᵢ`. -/
def centroids (m : SimplexBundle n (HPoint V) G) : TensorField m.faces' (HPoint V) :=
  TensorField.ofFn _ fun e => (m.simplexAt e).centroid

/-- Julia `curls(t)` (see `curlsAt`). -/
def curls (m : SimplexBundle n (HPoint V) G) :
    TensorField m.faces' (Values (HPoint V) (Leibniz.binomial n 2)) :=
  TensorField.ofFn _ m.curlsAt

/-- The P1 barycentric gradients of element `e` (Julia `gradienthat(t)[e+1]`, `element.jl:456-471`):
column `i` is `∇λᵢ ∈ ↓V`. Segments: `(∓1/h)` with the *signed* length `h`; planar triangles:
`revrot(curlᵢ)/(2A)` with the *signed* area (Julia divides by `|A|`, bug B3; for positively
oriented triangles the arithmetic is Julia's: `curl·(1/(2|A|))`, then `(-y, x)`); tetrahedra and
embedded elements: Grassmann's Cramer `gradient` (orientation-correct). -/
def gradienthatAt (m : SimplexBundle n (HPoint V) G) (e : Nat) :
    Simplex (TensorBundle.euclidean n) (Forms.drop1 V) Float :=
  if V.n == 2 then
    let h := m.signedVolumeAt e
    let c := 1 / h
    TensorOperator.ofFn fun _ j => if j.1 = 0 then -c else c
  else if V.n == 3 && n == 3 then
    let vol := m.volumeAt e
    let r0 := 1 / (2 * vol)
    let r := if m.signedVolumeAt e < 0 then -r0 else r0
    let cs := m.curlsAt e
    TensorOperator.ofFn fun i j =>
      let c := cs.get! j.1
      if i.1 = 0 then -(getD c.v 2 * r) else getD c.v 1 * r
  else (m.simplexAt e).gradient

/-- Julia `gradienthat(t)`: the P1 gradients of every element. -/
def gradienthat (m : SimplexBundle n (HPoint V) G) :
    TensorField m.faces' (Simplex (TensorBundle.euclidean n) (Forms.drop1 V) Float) :=
  TensorField.ofFn _ m.gradienthatAt

/-! ## Topology on the bundle (MeshTopology, §4.3) -/

/-- Julia `degrees(t)` (number of elements at each node of the full mesh). -/
def degrees (m : SimplexBundle n (HPoint V) G) : Array Nat := m.top.degrees

/-- Julia `weights(t) = inv(degrees(t))`. -/
def weights (m : SimplexBundle n (HPoint V) G) : FloatArray := m.top.weights

/-- Julia `adjacency(t)` as a `Cartan.Solve.Sparse` matrix (edge multiplicities). -/
def adjacency (m : SimplexBundle n (HPoint V) G) : Sparse := sparseOfInt m.top.adjacency
where
  /-- A MeshTopology integer matrix as a float CSC matrix. -/
  sparseOfInt (A : SparseInt) : Sparse :=
    ⟨A.m, A.n, A.colPtr, A.rowVal.map (· - 1), ⟨A.nzVal.map Float.ofInt⟩⟩

/-- Julia `antiadjacency(t)`. -/
def antiadjacency (m : SimplexBundle n (HPoint V) G) : Sparse := adjacency.sparseOfInt m.top.antiadjacency

/-- Julia `incidence(t)` (node × element; B5 fixed). -/
def incidence (m : SimplexBundle n (HPoint V) G) : Sparse := adjacency.sparseOfInt m.top.incidence

/-- Julia `Δ(t) = Diagonal(degrees(t)) - adjacency(t)` (`element.jl:505-506`, Cartan's convention,
B7: element counts minus edge multiplicities). -/
def laplacian (m : SimplexBundle n (HPoint V) G) : Sparse :=
  Sparse.lincomb 1 (Sparse.diagm ⟨m.degrees.map (·.toFloat)⟩) (-1) m.adjacency

/-- The graph Laplacian `D - A` of the edge graph (`A` 0/1, `D` its row sums; B7 fixed). -/
def graphLaplacian (m : SimplexBundle n (HPoint V) G) : Sparse := Id.run do
  let A := m.adjacency
  let mut I := #[]
  let mut J := #[]
  let mut Vv : FloatArray := .empty
  let mut deg : Array Nat := Array.replicate A.rows 0
  for j in [0:A.cols] do
    for k in [A.colPtr[j]!:A.colPtr[j + 1]!] do
      let i := A.rowIdx[k]!
      if i != j then
        I := I.push i; J := J.push j; Vv := Vv.push (-1)
        deg := deg.modify i (· + 1)
  for i in [0:A.rows] do
    I := I.push i; J := J.push i; Vv := Vv.push deg[i]!.toFloat
  return Sparse.ofTriplets A.rows A.cols I J Vv

/-- Julia `edges(t)`: the edge mesh on the same points. -/
def edges (m : SimplexBundle n (HPoint V) G) : SimplexBundle 2 (HPoint V) G := m.withTop m.top.edges

/-- Julia `facets(t)`. -/
def facets (m : SimplexBundle n (HPoint V) G) : SimplexBundle (n - 1) (HPoint V) G := m.withTop m.top.facets

/-- Julia `neighbors(t)` (0 = no neighbour across that facet). -/
def neighbors (m : SimplexBundle n (HPoint V) G) : Array (Vector Nat n) := m.top.neighbors

/-- Julia `facetsigns(t)`. -/
def facetsigns (m : SimplexBundle n (HPoint V) G) : Array (Vector Int n) := m.top.facetSigns

/-- Julia `edgesindices(t)`: per element, the global edge ids (edge `i` opposite vertex `i` for
triangles). -/
def edgesindices (m : SimplexBundle n (HPoint V) G) : SimplexTopology (n * (n - 1) / 2) :=
  m.top.edgesIndices

/-- The boundary facets of a topology (Julia `∂(t::SimplexTopology{N})`, `element.jl:301-308`):
for triangles the edges of odd multiplicity (in `edges` order), otherwise the facets met once (in
first-appearance order). -/
def boundaryTop (t : SimplexTopology n) : SimplexTopology (n - 1) :=
  if h : n = 3 then
    let A := t.adjacency
    let odd := t.edgeList.filter fun e => A.get e[0] e[1] % 2 != 0
    h ▸ SimplexTopology.ofElements odd 0 (some t.totalNodes)
  else
    let (top, again) := t.facetsInterior
    let keep := (Array.range top.elements).filter fun k => !again.contains (k + 1)
    SimplexTopology.ofElements (keep.map fun k => top.get (k + 1)) 0 (some t.totalNodes)

/-- Julia `∂(t)`: the boundary mesh on the same points. -/
def boundary (m : SimplexBundle n (HPoint V) G) : SimplexBundle (n - 1) (HPoint V) G :=
  m.withTop (boundaryTop m.top)

/-- Julia `interior(e)` (B6 fixed): the nodes not on the boundary mesh `e`, sorted. -/
def interior (e : SimplexBundle n (HPoint V) G) : Array Nat := e.top.interiorNodes

/-! ## Assembly and transfer (§4.2) -/

/-- Julia `assembleincidence(t, f, m, Val(true))` (MeshTopology `element.jl:311-319`, B1 fixed):
`b[tₖ] .+= f[tₖ] .* m[k]` element by element (`f` nodal, `m` per element). -/
def assembleincidence (m : SimplexBundle n (HPoint V) G) (f : FloatArray) (w : FloatArray) :
    FloatArray := Id.run do
  let mut b : FloatArray := ⟨Array.replicate m.totalNodes 0⟩
  for k in [0:m.elements] do
    let vs := m.top.get (k + 1)
    let wk := w.get! k
    for j in [0:n] do
      let v := vs[j]! - 1
      b := b.set! v (b.get! v + f.get! v * wk)
  return b

/-- The nodal values `f(x)` of a function of the homogeneous point at every full node (Julia
`iterpts(t, f)`). -/
def nodal (m : SimplexBundle n (HPoint V) G) (f : HPoint V → Float) : FloatArray :=
  ⟨(Array.range m.totalNodes).map fun v => f (Chain.ofFn fun c => m.coord (v + 1) c.1)⟩

/-- Julia `assembleload(t, f, m = volumes(t))` (`element.jl:546`): the lumped P1 load
`bᵢ = Σ_{k ∋ i} (fᵢ / n) |Tₖ|`, with `f` given at the nodes. -/
def assembleloadNodal (m : SimplexBundle n (HPoint V) G) (f : FloatArray)
    (vol : FloatArray := m.volumes.data) : FloatArray :=
  let nf := Float.ofNat n
  m.assembleincidence ⟨f.data.map (· / nf)⟩ vol

/-- Julia `assembleload(t, f)` for a function of the (homogeneous) point. -/
def assembleload (m : SimplexBundle n (HPoint V) G) (f : HPoint V → Float := fun _ => 1) : FloatArray :=
  m.assembleloadNodal (m.nodal f)

/-- Julia `interp(t::FaceMap)` (`element.jl:550`): node values as the averages of the incident
element values (`wᵢ Σ_{k∋i} bₖ`, element by element). -/
def interp (m : SimplexBundle n (HPoint V) G) (b : TensorField m.faces' Float) : TensorField m Float :=
  let vals := m.top.interpValues b.data
  if h : vals.size = FlatFiber.width Float * card m then ⟨vals, h, none⟩
  else TensorField.ofFn m fun i => vals.get! (m.image i - 1)

/-- Julia `pretni(t::SimplexMap) = means(t)` (`element.jl:556`): element averages of node values
(`Σ uᵢ / n`). -/
def pretni (m : SimplexBundle n (HPoint V) G) (u : FloatArray) : TensorField m.faces' Float :=
  let nf := Float.ofNat n
  TensorField.ofFn _ fun e =>
    let vs := m.top.get (e + 1)
    let s := (List.range n).foldl (fun acc j => if j == 0 then u.get! (vs[0]! - 1) else acc + u.get! (vs[j]! - 1)) 0
    s / nf

/-- Julia `gradient_2(t, u)` (`element.jl:491-501`): the constant gradient of the P1 field with
node values `u` on each element, `Σᵢ uᵢ ∇λᵢ` (left to right). -/
def gradient2 (m : SimplexBundle n (HPoint V) G) (u : FloatArray) :
    TensorField m.faces' (Chain (Forms.drop1 V) 1 Float) :=
  let g := m.gradienthat
  TensorField.ofFn _ fun e =>
    let vs := m.top.get (e + 1)
    let T := g.get e
    Chain.ofFn fun c =>
      (List.range n).foldl (fun acc j =>
        let x := u.get! (vs[j]! - 1) * T.entry c.1 j
        if j == 0 then x else acc + x) 0

/-- Julia `gradient(t::SimplexMap)` (`element.jl:479-483`): the element gradients averaged onto
the nodes (`interp` of `gradient_2`, component by component). -/
def gradient (m : SimplexBundle n (HPoint V) G) (u : FloatArray) :
    Array (Chain (Forms.drop1 V) 1 Float) := Id.run do
  let g2 := m.gradient2 u
  let w := m.weights
  let d := (Forms.drop1 V).n
  let mut acc : Array FloatArray := Array.replicate d ⟨Array.replicate m.totalNodes 0⟩
  for k in [0:m.elements] do
    let vs := m.top.get (k + 1)
    let gk := g2.get k
    for j in [0:n] do
      let v := vs[j]! - 1
      for c in [0:d] do
        acc := acc.modify c fun a => a.set! v (a.get! v + w.get! v * getD gk.v c)
  return (Array.range m.totalNodes).map fun v => Chain.ofFn fun c => acc[c.1]!.get! v

/-! ## Evaluation (§4.4) -/

/-- Julia `findfirst(P, t)` (`element.jl:400-406`): the first element (1-based) containing the
homogeneous point `P` (Grassmann's sign test on the Cramer numerators), `0` if none. -/
def findfirst (m : SimplexBundle n (HPoint V) G) (P : HPoint V) : Nat := Id.run do
  for k in [0:m.elements] do
    if (m.simplexAt k).contains P then return k + 1
  return 0

/-- Julia `t(P)` for a piecewise-linear field (`sinterp`, `element.jl:33-42`): `Σ uᵢ λᵢ(P)` on the
first element containing `P` (barycentric coordinates by Cramer's rule), `0` outside the mesh. -/
def sinterp (m : SimplexBundle n (HPoint V) G) (u : FloatArray) (P : HPoint V) : Float :=
  let j := m.findfirst P
  if j == 0 then 0 else
    let vs := m.top.get j
    let T := m.simplexAt (j - 1)
    T.interpolate (Values.ofFn fun i => u.get! (vs[i.1]! - 1)) P

end SimplexBundle

/-! ## 1-D meshes (§4.5) -/

namespace SimplexBundle

/-- A homogeneous 1-D point `(1, x)`. -/
def hp1 (x : Float) : HPoint ℝ2 := Chain.ofFn fun i => if i.1 = 0 then 1 else x

/-- Julia `initmesh(r)` (`element.jl:61-67`): the segments `[i, i+1]` on the points `(1, rᵢ)`, and
the boundary mesh of the two end nodes. -/
def initmesh (xs : Array Float) : SimplexBundle 2 (HPoint ℝ2) × SimplexBundle 1 (HPoint ℝ2) :=
  let np := xs.size
  let t := SimplexBundle.ofPoints (xs.map hp1) ((Array.range (np - 1)).map fun i => #v[i + 1, i + 2])
  let bnd := SimplexTopology.ofElements #[#v[1], #v[np]] 0 (some np) (some (IdxVec.arr #[1, np]))
  (t, t.withTop bnd)

/-- Julia `refinemesh!(r, pt, pe, η)` (`element.jl:131-157`, fixed): bisect the elements `η`
(1-based, element `i` = `[xᵢ, xᵢ₊₁]` of the sorted points), re-sort the points, and rebuild the
consecutive elements and the end-node boundary. -/
def refine1 (m : SimplexBundle 2 (HPoint ℝ2)) (η : Array Nat) :
    SimplexBundle 2 (HPoint ℝ2) × SimplexBundle 1 (HPoint ℝ2) :=
  let np := m.totalNodes
  let xs := (Array.range np).map fun v => m.coord (v + 1) 1
  let mids := η.map fun i => (xs[i]! + xs[i - 1]!) / 2
  initmesh ((xs ++ mids).qsort (· < ·))

end SimplexBundle

/-! ## Face fields: norms and markers (§4.8) -/

namespace TensorField

variable {M : Type} [FrameBundle M] {m : M}

/-- Julia `rms(η) = norm(η)/√length(η)` (`element.jl:125`). -/
def rms (t : TensorField m Float) : Float :=
  let s := t.data.data.foldl (fun acc x => acc + x * x) 0
  Float.sqrt s / Float.sqrt (Float.ofNat (card m))

/-- Julia `select(η, ϵ = rms(η))` (`element.jl:126`): the sorted 1-based indices with `η > ϵ`
(the refinement marker). -/
def select (t : TensorField m Float) (ε : Float := t.rms) : Array Nat :=
  (Array.range (card m)).filterMap fun i => if t.get i > ε then some (i + 1) else none

end TensorField

end Cartan
