/-
Sampled curves and vector fields of versors (Grassmann.jl `src/Grassmann.jl:68, 312-314`
and `ext/GeometryBasicsExt.jl:28-33`): the README's `points`, `chainfield`,
`vectorfield`/`pointfield`.

* `points(f, r = -2π:0.0001:2π) = vector.(f.(r))` (`src/Grassmann.jl:68`): a curve sampled
  on a range. `points` returns the vectors (`Array (Chain V 1 Float)`, Julia's
  `Vector{Chain}`); `pointsCoords` returns the coordinates of chosen generators as one
  `FloatArray` each (Julia's `V(2,3,4).(points(f))`, what a plot consumes), without
  keeping the vectors.
* `chainfield(t, V = Manifold(t), W = V) = p -> V(vector(↓(↑((V∪Manifold(t))(p)) ⊘ t)))`
  (`src/Grassmann.jl:314`): the vector field of a versor `t` acting on points, a point `p`
  of the subspace `W` embedded in `t`'s space, lifted (`↑`), sandwiched (`x ⊘ t`),
  projected down (`↓`), and read in the subspace `V`.
* `vectorfield`/`pointfield` (GeometryBasics extension; `vectorfield = pointfield`): the
  same map on coordinate vectors (Julia's `Point`s), here `Values Float`.

* `scalarfield(t, ϕ)`, `chainfield(t, ϕ)` (`src/Grassmann.jl:315-339`): barycentric
  interpolation on a simplicial mesh (points in homogeneous coordinates, elements as 1-based
  vertex index lists): at `P`, the first element `Pᵢ` containing it gives `(Pᵢ \ P) ⋅ ϕ[tᵢ]`
  (`0`, resp. the homogeneous origin, outside the mesh); `rectangle`, `rectanglefield`
  (`src/Grassmann.jl:341-348`) sample it on the bounding box of the points.
-/
import Grassmann.Composite.Project
import Grassmann.Forms.Simplex
import JuliaBase.Range

namespace Grassmann

open DirectSum StaticVectors AbstractTensors JuliaBase

namespace Fields

variable {V : TensorBundle}

/-- The grade-1 part of a sandwich result (Julia `vector(x)`), as a vector. -/
class VectorPart (Z : Type) (V : outParam TensorBundle) where
  /-- Julia `vector(z)`. -/
  vec : Z → Chain V 1 Float

instance : VectorPart (Chain V 1 Float) V := ⟨id⟩
instance : VectorPart (Multivector V Float) V := ⟨fun m => gradePart m 1⟩

/-- `2π` as Julia evaluates it. -/
def twoPi : Float := f64! 6.283185307179586

/-- Julia's default sample range of `points`, `-2π:0.0001:2π` (125 664 values). -/
def pointsRange : FloatArray := (colon (-twoPi) (f64! 0.0001) twoPi).toFloatArray

/-- The loop of `points`. -/
@[specialize] def pointsLoop (f : Float → Chain V 1 Float) (r : FloatArray) (i : Nat)
    (out : Array (Chain V 1 Float)) : Array (Chain V 1 Float) :=
  if h : i < r.size then pointsLoop f r (i + 1) (out.push (f r[i])) else out
termination_by r.size - i

/-- Julia `points(f, r)` (`src/Grassmann.jl:68`, `vector.(f.(r))`): the curve `f` sampled at
every value of `r` (default `pointsRange`). -/
@[inline] def points (f : Float → Chain V 1 Float) (r : FloatArray := pointsRange) : Array (Chain V 1 Float) :=
  pointsLoop f r 0 (Array.mkEmpty r.size)

/-- Push the coordinates `idx` (0-based chain indices) of `w` onto the columns. -/
@[inline] def pushCoords {n : Nat} (w : Values Float n) (idx : Array Nat) (cols : Array FloatArray) :
    Array FloatArray :=
  (idx.zip cols).map fun (k, c) => c.push (getD w k)

/-- The loop of `pointsCoords`. -/
@[specialize] def coordsLoop (f : Float → Chain V 1 Float) (idx : Array Nat) (r : FloatArray) (i : Nat)
    (cols : Array FloatArray) : Array FloatArray :=
  if h : i < r.size then coordsLoop f idx r (i + 1) (pushCoords (f r[i]).v idx cols) else cols
termination_by r.size - i

/-- The coordinates `idx` (0-based generator indices of `V`) of `points(f, r)`, one column
each: Julia `V(i₁+1, …).(points(f, r))` as plot data. -/
@[inline] def pointsCoords (f : Float → Chain V 1 Float) (idx : Array Nat) (r : FloatArray := pointsRange) :
    Array FloatArray :=
  coordsLoop f idx r 0 (idx.map fun _ => FloatArray.emptyWithCapacity r.size)

variable [Kernels V]

/-- The point map of a versor, `p ↦ vector(↓(↑p ⊘ t))` on vectors of `t`'s space. -/
@[inline] def versorMap {X Z : Type} [Sandwich (Chain V 1 Float) X Z] [VectorPart Z V] (t : X)
    (p : Chain V 1 Float) : Chain V 1 Float :=
  Chain.down (VectorPart.vec (Sandwich.sandwich (Chain.up p) t : Z))

/-- Julia `chainfield(t, V, W)` (`src/Grassmann.jl:314`): the field of the versor `t` on the
points of the subspace `W` (embedded in `t`'s space), read in the subspace `S`. -/
@[inline] def chainfield {X Z : Type} [Sandwich (Chain V 1 Float) X Z] [VectorPart Z V] (t : X)
    (S W : SubSpace V) (p : Chain (Forms.restrict V W.mask) 1 Float) :
    Chain (Forms.restrict V S.mask) 1 Float :=
  (versorMap t (Chain.embedSub W p)).project S

/-- Julia `chainfield(t)` on the whole space (`V = W = Manifold(t)`). -/
@[inline] def chainfieldFull {X Z : Type} [Sandwich (Chain V 1 Float) X Z] [VectorPart Z V] (t : X)
    (p : Chain V 1 Float) : Chain V 1 Float :=
  versorMap t p

/-- Julia `vectorfield(t, V, W)` (`ext/GeometryBasicsExt.jl:30`, `pointfield` is the same
function): `chainfield` on coordinate vectors (a `Point` of `W`'s coordinates in, of `S`'s
out). -/
@[inline] def vectorfield {X Z : Type} [Sandwich (Chain V 1 Float) X Z] [VectorPart Z V] (t : X)
    (S W : SubSpace V) (p : Values Float ((Layout.chain 1).size (Forms.restrict V W.mask).n)) :
    Values Float ((Layout.chain 1).size (Forms.restrict V S.mask).n) :=
  (chainfield t S W ⟨p⟩).v

/-- Julia `pointfield` (`vectorfield = pointfield`). -/
@[inline] def pointfield {X Z : Type} [Sandwich (Chain V 1 Float) X Z] [VectorPart Z V] (t : X)
    (S W : SubSpace V) (p : Values Float ((Layout.chain 1).size (Forms.restrict V W.mask).n)) :
    Values Float ((Layout.chain 1).size (Forms.restrict V S.mask).n) :=
  vectorfield t S W p

/-! ## Mesh interpolation -/

section Mesh

variable {W U : TensorBundle}

/-- The simplex of element `idx` (1-based vertex indices into `pts`, Cartan's `affinehull`). -/
@[inline] def element (pts : Array (Chain W 1 Float)) (idx : Array Nat) :
    Option (Simplex (TensorBundle.euclidean W.n) W Float) :=
  affinehull pts idx.toList

/-- The barycentric coordinates `Pᵢ \ P` in the first element containing `P`, with the element's
vertex indices (Julia's loop over `t`, `src/Grassmann.jl:318-322`). -/
def locate (pts : Array (Chain W 1 Float)) (elems : Array (Array Nat)) (P : Chain W 1 Float) :
    Option (Array Nat × Values Float ((Layout.chain 1).size (TensorBundle.euclidean W.n).n)) :=
  elems.findSome? fun idx =>
    match element pts idx with
    | some T => if T.contains P then some (idx, (T.solve P).v) else none
    | none => none

/-- Julia `scalarfield(t, ϕ)` (`src/Grassmann.jl:315-326`) at `P`: `(Pᵢ \ P) ⋅ ϕ[tᵢ]` in the
first element `Pᵢ` containing `P` (the barycentric interpolation of the vertex values `ϕ`),
`0.0` outside the mesh. -/
def scalarfield (pts : Array (Chain W 1 Float)) (elems : Array (Array Nat)) (ϕ : Array Float)
    (P : Chain W 1 Float) : Float :=
  match locate pts elems P with
  | some (idx, lam) =>
    let f : Values Float ((Layout.chain 1).size (TensorBundle.euclidean W.n).n) :=
      Values.ofFn fun k => ϕ[(idx[k.1]?.getD 1) - 1]?.getD 0
    Forms.Mat.dotPlain lam f
  | none => 0

/-- Julia `chainfield(t, ϕ)` (`src/Grassmann.jl:327-339`) at `P`: `(Pᵢ \ P) ⋅ ϕ[tᵢ]` with vector
values `ϕ` (the barycentric combination of the vertex vectors, left to right), the
homogeneous origin `(1, 0, …)` outside the mesh. -/
def chainfieldMesh (pts : Array (Chain W 1 Float)) (elems : Array (Array Nat)) (ϕ : Array (Chain U 1 Float))
    (P : Chain W 1 Float) : Chain U 1 Float :=
  match locate pts elems P with
  | some (idx, lam) =>
    let term := fun (k : Nat) => (ϕ[(idx[k]?.getD 1) - 1]?.getD Chain.zero) * getD lam k
    match (Layout.chain 1).size (TensorBundle.euclidean W.n).n with
    | 0 => Chain.zero
    | m + 1 => (List.range m).foldl (fun acc k => acc + term (k + 1)) (term 0)
  | none => ⟨Values.ofFn fun i => if i.1 = 0 then 1 else 0⟩

/-- Julia `rectangle(p, nx, ny)` (`src/Grassmann.jl:341-347`): the homogeneous points
`(1, x, y)` of an `ny × nx` grid over the bounding box of the points' second and third
coordinates (`range(min, max, length = n)`), row `j` at `y_j`. -/
def rectangle (pts : Array (Chain W 1 Float)) (nx : Nat := 100) (ny : Nat := nx) :
    Array (Array (Chain W 1 Float)) :=
  let px := pts.map fun p => getD p.v 1
  let py := pts.map fun p => getD p.v 2
  let lo := fun (a : Array Float) => a.foldl (fun m x => if x < m then x else m) (a[0]?.getD 0)
  let hi := fun (a : Array Float) => a.foldl (fun m x => if x > m then x else m) (a[0]?.getD 0)
  let xs := (range (lo px) (hi px) nx).toFloatArray
  let ys := (range (lo py) (hi py) ny).toFloatArray
  (Array.range ny).map fun j => (Array.range nx).map fun i =>
    ⟨Values.ofFn fun k => if k.1 = 0 then 1 else if k.1 = 1 then xs[i]! else if k.1 = 2 then ys[j]! else 0⟩

/-- Julia `rectanglefield(t, ϕ, nx, ny) = chainfield(t, ϕ).(rectangle(points(t), nx, ny))`
(`src/Grassmann.jl:348`). -/
def rectanglefield (pts : Array (Chain W 1 Float)) (elems : Array (Array Nat)) (ϕ : Array (Chain U 1 Float))
    (nx : Nat := 100) (ny : Nat := nx) : Array (Array (Chain U 1 Float)) :=
  (rectangle pts nx ny).map (·.map (chainfieldMesh pts elems ϕ))

end Mesh

end Fields

end Grassmann
