import Cartan.Local

/-!
# Frame bundles: the bases of tensor fields

Julia's `FrameBundle{C,N} <: FiberBundle{C,N}` (Cartan.jl `src/fiber.jl:405-810`) is an array of
`Coordinate`s together with an immersed topology. Every field lives over one; its fiber array has
the base's shape.

| Julia | Lean |
|---|---|
| `GridBundle{N}` over a `ProductSpace` (`fiber.jl:446-528`) | `GridBundle N P G` |
| `IntervalRange` / 1-D range base (`TensorField(0:0.1:1)`) | `GridBundle 1 Float G` |
| `AlignedRegion{N}` (`TensorField(ProductSpace(…))`) | `GridBundle N (AffinePoint N) G` |
| `PointCloud` (`fiber.jl:216-273`) | `PointCloud P G` (no global cache) |
| `SimplexBundle{N}` (`fiber.jl:572-667`) | `SimplexBundle n P G` (`n` vertices per element) |
| `FaceBundle{N}` (`fiber.jl:686-742`) | `FaceBundle n P G` |

Two classes connect them to fields: `FrameBundle M` gives the number of points (`card`, the length
of every fiber array over it), `Coordinates M P G` the point and metric at a linear index.

**Point types.** A 1-D base built from a range has real points (`Float`), one built from a
`ProductSpace` has `AffinePoint N` points; Julia dispatches on the difference (`IntervalMap`), so
it is in the type (`GridPoint N P`). Simplex points are homogeneous `Chain`s (`(1, x, y, …)`,
port notes §3.2 invariant 5) stored flat.

**Metrics.** `G = Induced` (Julia `Global{N}(InducedMetric())`) stores nothing per point;
`MetricStore.pointwise` is Julia's per-point metric array.

**Ids.** Julia's `PointCloud` registers every point vector in a global cache and numbers bundles
with global counters (`point_cache`, `point_id`, `top_id`); here `id` is a plain field, `0` by
default, and nothing is global (port notes §8.5).
-/

namespace Cartan

open Grassmann DirectSum StaticVectors AbstractTensors JuliaBase MeshTopology

/-! ## Metric storage -/

/-- The metric of a base: one global value (Julia `Global{N}(g)`, `topology.jl:246-270`) or one
value per point (a Julia `AbstractArray{G}`). -/
inductive MetricStore (G : Type) where
  /-- Julia `Global{N}(g)`. -/
  | global (g : G)
  /-- A per-point metric array (column-major). -/
  | pointwise (a : Array G)
  deriving Inhabited

namespace MetricStore

variable {G : Type}

/-- The metric at point `i` (0-based; `default` beyond a per-point array). -/
@[inline] def get [Inhabited G] (m : MetricStore G) (i : Nat) : G :=
  match m with
  | global g => g
  | pointwise a => a[i]!

/-- Julia `isinduced` of a metric array (`fiber.jl:162-165`): a global induced metric. -/
def isGlobal : MetricStore G → Bool
  | global _ => true
  | pointwise _ => false

/-- Gather the metric at the given points (Julia `metricextensor(m)[inds]`; a global metric
stays global). -/
def gather [Inhabited G] (m : MetricStore G) (inds : Array Nat) : MetricStore G :=
  match m with
  | global g => global g
  | pointwise a => pointwise (inds.map (a[·]!))

instance [BEq G] : BEq (MetricStore G) where
  beq
    | global a, global b => a == b
    | pointwise a, pointwise b => a == b
    | _, _ => false

end MetricStore

/-- The induced metric (Julia `Global{N}(InducedMetric())`). -/
def MetricStore.induced : MetricStore Induced := .global {}

/-! ## Classes -/

/-- A discretized base manifold: an array of `card m` points (Julia `length(m)` of a
`FrameBundle`). A field over `m` stores `card m` fiber values. -/
class FrameBundle (M : Type) where
  /-- The number of points (Julia `length(m)`). -/
  card : M → Nat

/-- The coordinates of a frame bundle: the point and metric at each 0-based linear (column-major)
index (Julia `m[i+1]::Coordinate`). Indices at or past `card m` give unspecified values. -/
class Coordinates (M : Type) [FrameBundle M] (P G : outParam Type) where
  /-- Julia `points(m)[i+1]`. -/
  point : M → Nat → P
  /-- Julia `metricextensor(m)[i+1]`. -/
  metricAt : M → Nat → G

export FrameBundle (card)

namespace FrameBundle

variable {M P G : Type} [FrameBundle M] [Coordinates M P G]

/-- Julia `m[i+1]`: the coordinate at a linear index. -/
@[inline] def coordinate (m : M) (i : Nat) : Coordinate P G :=
  ⟨Coordinates.point m i, Coordinates.metricAt m i⟩

/-- Julia `collect(points(m))`, boxed (for tests and display). -/
def pointArray (m : M) : Array P := (Array.range (card m)).map (Coordinates.point m)

/-- Julia `points(m)`, flat (`width P` floats per point). -/
def pointsFlat [FlatFiber P] (m : M) : FloatArray := buildFlat (card m) (Coordinates.point m)

end FrameBundle

/-! ## Grid bundles -/

/-- The point type of a structured grid: how the point with a given linear index is read off a
`ProductSpace` (Julia: a range base has real points, a `ProductSpace` base `Chain` points). -/
class GridPoint (N : Nat) (P : Type) where
  /-- The point with 0-based linear index `k`. -/
  pointOf : ProductSpace N → Nat → P

/-- 1-D real points: the coordinate vector itself (Julia `PointArray(0, range)`). -/
instance : GridPoint 1 Float := ⟨fun ps k => (ps.axes[0]).get k⟩

/-- Affine points of a `ProductSpace` (Julia `Chain{affinemanifold(N),1}`). -/
instance {N : Nat} : GridPoint N (AffinePoint N) := ⟨ProductSpace.point⟩

/-- Julia `GridBundle{N}` over a `PointArray` of a `ProductSpace` (`fiber.jl:446-528`): a tensor
product grid of points with a `QuotientTopology` (boundary gluing) and a metric. -/
structure GridBundle (N : Nat) (P : Type) (G : Type := Induced) where
  /-- The coordinate axes (Julia `points(m)`, a `ProductSpace`, or a range for `N = 1`). -/
  space : ProductSpace N
  /-- Julia `immersion(m)`: the gluing of the faces. -/
  top : QuotientTopology N
  /-- Julia `metricextensor(m)`. -/
  metric : MetricStore G
  /-- Julia `bundle(coordinates(m))` (`PointArray` id), `0` = uncached. -/
  id : Nat := 0
  /-- The topology has the grid's shape. -/
  size_top : top.size = space.size

namespace GridBundle

variable {N : Nat} {P G : Type}

instance : FrameBundle (GridBundle N P G) := ⟨fun m => m.space.length⟩

instance [Inhabited G] : Inhabited (GridBundle N P G) :=
  ⟨⟨default, QuotientTopology.openTop (default : ProductSpace N).size, .global default, 0, rfl⟩⟩

instance [GridPoint N P] [Inhabited G] : Coordinates (GridBundle N P G) P G where
  point m k := GridPoint.pointOf m.space k
  metricAt m k := m.metric.get k

/-- Julia `size(m)`. -/
@[inline] def size (m : GridBundle N P G) : Vector Nat N := m.space.size

/-- Julia `GridBundle(PointArray(0, ps))` (`fiber.jl:456-457`): the open grid of a product space
with the induced metric. -/
def ofSpace (ps : ProductSpace N) : GridBundle N (AffinePoint N) :=
  ⟨ps, QuotientTopology.openTop ps.size, .induced, 0, rfl⟩

/-- Julia `GridBundle(PointArray(0, r))` of a 1-D vector: the open interval with real points
(`TensorField(0:0.1:1)`, `IntervalRange`). -/
def ofAxis (a : Axis) : GridBundle 1 Float :=
  ⟨⟨#v[a]⟩, QuotientTopology.openTop (ProductSpace.size ⟨#v[a]⟩), .induced, 0, rfl⟩

/-- A grid with the given topology, or the open grid when the topology's size does not match
(the construction used by slicing and resampling, whose sizes always agree). -/
def mkChecked (space : ProductSpace N) (top : QuotientTopology N) (metric : MetricStore G)
    (id : Nat := 0) : GridBundle N P G :=
  if h : top.size = space.size then ⟨space, top, metric, id, h⟩
  else ⟨space, QuotientTopology.openTop space.size, metric, id, rfl⟩

/-- Julia `m(t::ImmersedTopology)` = `GridBundle(coordinates(m), t)` (`fiber.jl:495`): the same
points re-glued. -/
def withTop (m : GridBundle N P G) (t : QuotientTopology N) (h : t.size = m.space.size) :
    GridBundle N P G := { m with top := t, size_top := h }

/-- `withTop` with a runtime size check (`none` on a mismatch). -/
def withTop? (m : GridBundle N P G) (t : QuotientTopology N) : Option (GridBundle N P G) :=
  if h : t.size = m.space.size then some (m.withTop t h) else none

/-- A per-point metric (Julia `PointArray(0, points, metric)`); `none` if the array does not have
one value per point. -/
def withMetric? {G' : Type} (m : GridBundle N P G) (g : Array G') : Option (GridBundle N P G') :=
  if g.size = card m then some ⟨m.space, m.top, .pointwise g, m.id, m.size_top⟩ else none

/-! ### Named gluings (Julia `XTopology(m::GridBundle) = m(XTopology(size(m)))`, `Cartan.jl:313-322`) -/

/-- Julia `OpenTopology(m)`. -/
def openTop (m : GridBundle N P G) : GridBundle N P G := m.withTop (.openTop m.size) rfl
/-- Julia `MirrorTopology(m)`. -/
def mirror (m : GridBundle N P G) : GridBundle N P G := m.withTop (.mirror m.size) rfl
/-- Julia `ClampedTopology(m)`. -/
def clamped (m : GridBundle N P G) : GridBundle N P G := m.withTop (.clamped m.size) rfl
/-- Julia `TorusTopology(m)`. -/
def torus (m : GridBundle N P G) : GridBundle N P G := m.withTop (.torus m.size) rfl
/-- Julia `BallTopology(m)` (`PolarTopology`). -/
def ball (m : GridBundle N P G) : GridBundle N P G :=
  m.withTop (.ball m.size) (by unfold QuotientTopology.ball; split <;> rfl)
/-- Julia `SphereTopology(m)`. -/
def sphere (m : GridBundle N P G) : GridBundle N P G :=
  m.withTop (.sphere m.size) (by unfold QuotientTopology.sphere; split <;> rfl)
/-- Julia `CylinderTopology(m)`. -/
def cylinder (m : GridBundle 2 P G) : GridBundle 2 P G := m.withTop (.cylinder m.size) rfl
/-- Julia `MobiusTopology(m)`. -/
def mobius (m : GridBundle 2 P G) : GridBundle 2 P G := m.withTop (.mobius m.size) rfl
/-- Julia `WingTopology(m)`. -/
def wing (m : GridBundle 2 P G) : GridBundle 2 P G := m.withTop (.wing m.size) rfl
/-- Julia `KleinTopology(m)`. -/
def klein (m : GridBundle 2 P G) : GridBundle 2 P G := m.withTop (.klein m.size) rfl
/-- Julia `ConeTopology(m)`. -/
def cone (m : GridBundle 2 P G) : GridBundle 2 P G := m.withTop (.cone m.size) rfl
/-- Julia `TubeTopology(m)` (2-D; `RevolvedTopology`). -/
def tube (m : GridBundle 2 P G) : GridBundle 2 P G := m.withTop (.tube2 m.size) rfl
/-- Julia `TubeTopology(m)` (3-D). -/
def tube3 (m : GridBundle 3 P G) : GridBundle 3 P G := m.withTop (.tube3 m.size) rfl
/-- Julia `HopfTopology(m)` (2-D). -/
def hopf (m : GridBundle 2 P G) : GridBundle 2 P G := m.withTop (.hopf2 m.size) rfl
/-- Julia `HopfTopology(m)` (3-D). -/
def hopf3 (m : GridBundle 3 P G) : GridBundle 3 P G := m.withTop (.hopf3 m.size) rfl
/-- Julia `GeographicTopology(m)`. -/
def geographic (m : GridBundle 2 P G) : GridBundle 2 P G := m.withTop (.geographic m.size) rfl

/-! ### Indexing -/

/-- The 0-based linear index of a 0-based multi-index (column-major). -/
@[inline] def linear (m : GridBundle N P G) (idx : Vector Nat N) : Nat :=
  (List.finRange N).foldr (fun a acc => idx[a] + m.size[a] * acc) 0

/-- The 0-based multi-index of a 0-based linear index. -/
@[inline] def cartesian (m : GridBundle N P G) (k : Nat) : Vector Nat N :=
  (MeshTopology.cartesianIndex m.size (k + 1)).map (· - 1)

/-- Julia `g[j, Val(a+1), i…]` (`fiber.jl:507-513`): the 0-based linear index of the point `j`
steps from the 0-based multi-index `idx` along axis `a`, through the topology's gluing (the raw
index on an open face). `none` when the result lies outside the grid (a step past an open face,
where Julia throws a `BoundsError`). -/
def neighbor (m : GridBundle N P G) (j : Int) (a : Fin N) (idx : Vector Nat N) : Option Nat :=
  let raw : Vector Int N := Vector.ofFn fun b =>
    Int.ofNat idx[b] + 1 + (if b = a then j else 0)
  let r := m.top.ghost (a.1 + 1) raw
  if (List.finRange N).all fun b => 1 ≤ r[b] && r[b] ≤ (m.size[b] : Int) then
    some (m.linear (r.map fun x => (x - 1).toNat))
  else none

/-! ### Slicing (Julia `m(i…, :, j…)`, `fiber.jl:496-499`) -/

/-- The parent's 0-based linear indices of the points of the slice keeping the axes `ks`
(ascending) with every other axis fixed at `fixed` (0-based, indexed by parent axis; the entries
of kept axes are ignored), in the slice's column-major order. -/
def sliceIndices {K : Nat} (m : GridBundle N P G) (ks : Vector (Fin N) K) (fixed : Vector Nat N) :
    Array Nat :=
  let sub : Vector Nat K := ks.map (m.size[·])
  let len := MeshTopology.gridLength sub
  (Array.range len).map fun k =>
    let ck := (MeshTopology.cartesianIndex sub (k + 1)).map (· - 1)
    let full : Vector Nat N := Vector.ofFn fun a =>
      match (List.finRange K).find? (fun i => ks[i] == a) with
      | some i => ck[i]
      | none => fixed[a]
    m.linear full

/-- The 1-based values of the fixed axes (ascending), as `QuotientTopology.slice` takes them. -/
def fixedValues {K : Nat} (ks : Vector (Fin N) K) (fixed : Vector Nat N) : Array Int :=
  ((List.finRange N).filter fun a => !ks.toList.contains a).toArray.map fun a => Int.ofNat fixed[a] + 1

/-- Julia `m(i…, :, …, :, j…)` with colons at the axes `ks` (ascending): the sub-grid of the kept
axes with the topology `subtopology` (MeshTopology `quotient.jl:579-752`) and the metric
restricted to the slice. Its points are a `ProductSpace` of the kept axes (for one kept axis Julia
returns the range itself: use `sliceLine`). -/
def slice {K : Nat} (m : GridBundle N P G) (ks : Vector (Fin N) K) (fixed : Vector Nat N) [Inhabited G] :
    GridBundle K (AffinePoint K) G :=
  mkChecked (m.space.select ks) (m.top.slice ks (fixedValues ks fixed))
    (m.metric.gather (m.sliceIndices ks fixed))

/-- Julia `m(i…, :, j…)` with one colon at axis `a`: the 1-D grid of that axis, with real points
(Julia returns the range itself, `topology.jl:125-129`), and its sliced topology. -/
def sliceLine (m : GridBundle N P G) (a : Fin N) (fixed : Vector Nat N) [Inhabited G] :
    GridBundle 1 Float G :=
  mkChecked ⟨#v[m.space.axis a]⟩ (m.top.slice #v[a] (fixedValues #v[a] fixed))
    (m.metric.gather (m.sliceIndices #v[a] fixed))

/-- The axes of `Fin (N+1)` other than `a`, ascending. -/
def otherAxes (a : Fin (N + 1)) : Vector (Fin (N + 1)) N :=
  Vector.ofFn fun i => if i.1 < a.1 then ⟨i.1, by omega⟩ else ⟨i.1 + 1, by omega⟩

/-- Julia `m(…, i, …)` fixing axis `a` at the 0-based index `i` and keeping the others (a
`ProductSpace` of the remaining axes; for a single remaining axis use `sliceLine`). -/
def sliceAt (m : GridBundle (N + 1) P G) (a : Fin (N + 1)) (i : Nat) [Inhabited G] :
    GridBundle N (AffinePoint N) G :=
  m.slice (otherAxes a) (Vector.replicate (N + 1) i)

/-! ### Resampling and products -/

/-- Julia `resample(m, n)` (`fiber.jl:480-488`): resampled axes and topology (MeshTopology
`resample`, whose non-open case throws in Julia, B2; here the intended transversal resampling of
`QuotientTopology.resample?`). An induced metric stays induced; a per-point metric cannot be
interpolated here (that needs the grid interpolation of the grid stage) and is dropped to the
metric at the first point. -/
def resample [Inhabited G] (m : GridBundle N P G) (n : Vector Nat N) : GridBundle N P G :=
  let t := (m.top.resample? n).getD (QuotientTopology.openTop n)
  mkChecked (m.space.resample n) t (.global (m.metric.get 0))

/-- Julia `a ⊕ b` of grid bundles (`fiber.jl:463`): the product grid with the product topology
(`QuotientTopology.cross`, which rebuilds the transversal maps as identities, Q13) and the induced
metric. -/
def append {M : Nat} {P' G' : Type} (a : GridBundle M P G) (b : GridBundle N P' G') :
    GridBundle (M + N) (AffinePoint (M + N)) :=
  mkChecked (a.space.append b.space) (a.top.cross b.top) .induced

/-- Julia `a ⊕ v` with a 1-D vector (`fiber.jl:464`): an open axis appended
(`QuotientTopology.crossInt`, which keeps the maps). -/
def pushAxis (a : GridBundle N P G) (v : Axis) : GridBundle (N + 1) (AffinePoint (N + 1)) :=
  mkChecked (a.space.push v) (a.top.crossInt v.length) .induced

/-- Julia `==` of grid bundles (as used by `checkdomain`, `Cartan.jl:494`): equal points and
topology. -/
instance [BEq G] : BEq (GridBundle N P G) :=
  ⟨fun a b => a.space == b.space && a.top == b.top && a.metric == b.metric⟩

end GridBundle

/-! ## Point clouds and simplex bundles -/

/-- Julia `PointCloud` = `PointVector` (`fiber.jl:216-273`): explicit points (flat, `width P`
floats each) with their metric. -/
structure PointCloud (P : Type) (G : Type := Induced) where
  /-- The points, flat (Julia `points(m)`). -/
  points : FloatArray
  /-- Julia `metricextensor(m)`. -/
  metric : MetricStore G
  /-- Julia `bundle(m)`; `0` = uncached. -/
  id : Nat := 0

namespace PointCloud

variable {P G : Type}

/-- Julia `PointCloud(points)` with the induced metric (and no cache registration). -/
def ofArray [FlatFiber P] (pts : Array P) : PointCloud P :=
  ⟨pts.foldl FlatFiber.push (FloatArray.emptyWithCapacity (pts.size * FlatFiber.width P)), .induced, 0⟩

/-- The number of points. -/
def size [FlatFiber P] (m : PointCloud P G) : Nat := m.points.size / FlatFiber.width P

/-- Point `i` (0-based). -/
@[inline] def get [FlatFiber P] (m : PointCloud P G) (i : Nat) : P :=
  FlatFiber.read m.points (i * FlatFiber.width P)

instance [FlatFiber P] : FrameBundle (PointCloud P G) := ⟨size⟩
instance [FlatFiber P] [Inhabited G] : Coordinates (PointCloud P G) P G := ⟨get, fun m i => m.metric.get i⟩

end PointCloud

/-- Julia `SimplexBundle{N}` (`fiber.jl:572-667`): a point cloud with a `SimplexTopology` of
`n`-vertex elements; its points (and the fields over it) are the topology's vertices (Julia
`size(m) = size(vertices(m))`, the whole cloud when the topology covers it). Julia's type
parameter `N = mdims(P) - 1` is the manifold dimension of the homogeneous points. -/
structure SimplexBundle (n : Nat) (P : Type) (G : Type := Induced) where
  /-- Julia `fullcoordinates(m)`: every point of the mesh. -/
  cloud : PointCloud P G
  /-- Julia `immersion(m)`. -/
  top : SimplexTopology n

namespace SimplexBundle

variable {n : Nat} {P G : Type}

/-- Julia `PointCloud(points)(t)` (`fiber.jl:586`). -/
def ofPoints [FlatFiber P] (pts : Array P) (els : Array (Vector Nat n)) : SimplexBundle n P :=
  ⟨.ofArray pts, SimplexTopology.ofElements els (p := some pts.size)⟩

/-- The full-mesh vertex id (1-based) of vertex `i` (0-based) of the bundle (Julia
`getimage(immersion(m), i+1)`). -/
@[inline] def image (m : SimplexBundle n P G) (i : Nat) : Nat := m.top.getImage (i + 1)

instance : FrameBundle (SimplexBundle n P G) := ⟨fun m => m.top.nodes⟩

/-- Julia `m[i]` (`fiber.jl:633-636`): the coordinate of full vertex `getimage(t, i)`. -/
instance [FlatFiber P] [Inhabited G] : Coordinates (SimplexBundle n P G) P G where
  point m i := m.cloud.get (m.image i - 1)
  metricAt m i := m.cloud.metric.get (m.image i - 1)

/-- Julia `m(t::ImmersedTopology)` (`fiber.jl:621`): the same points with another topology. -/
def withTop {k : Nat} (m : SimplexBundle n P G) (t : SimplexTopology k) : SimplexBundle k P G :=
  ⟨m.cloud, t⟩

/-- Julia `m(fixed)` (`fiber.jl:665-667`): the sub-bundle on the elements whose vertices all lie
in `fixed` (1-based full ids). -/
def byVertices (m : SimplexBundle n P G) (fixed : Array Nat) : SimplexBundle n P G :=
  ⟨m.cloud, m.top.byVertices fixed⟩

/-- Julia `m(immersion(m)[ks])`: the sub-bundle of the elements `ks` (1-based). -/
def getSub (m : SimplexBundle n P G) (ks : Array Nat) : SimplexBundle n P G :=
  ⟨m.cloud, m.top.getSub ks⟩

/-- Julia `refine(m)`. -/
def refine (m : SimplexBundle n P G) : SimplexBundle n P G := ⟨m.cloud, m.top.refine⟩

/-- Julia `points(m)[t[e]]`: the points of element `e` (0-based) of the bundle. -/
def elementPoints [FlatFiber P] (m : SimplexBundle n P G) (e : Nat) : Vector P n :=
  (m.top.get (e + 1)).map fun v => m.cloud.get (v - 1)

end SimplexBundle

/-- Julia `FaceBundle{N}` (`fiber.jl:686-742`): the same data as a `SimplexBundle`, but its
points are the elements, located at their centroids. -/
structure FaceBundle (n : Nat) (P : Type) (G : Type := Induced) where
  /-- Julia `fullcoordinates(m)`. -/
  cloud : PointCloud P G
  /-- Julia `immersion(m)`. -/
  top : SimplexTopology n

namespace FaceBundle

variable {n : Nat} {P G : Type}

/-- Julia `FaceBundle(m::SimplexBundle)` (`fiber.jl:697`). -/
def ofSimplex (m : SimplexBundle n P G) : FaceBundle n P G := ⟨m.cloud, m.top⟩

/-- Julia `SimplexBundle(m::FaceBundle)` (`fiber.jl:696`). -/
def toSimplex (m : FaceBundle n P G) : SimplexBundle n P G := ⟨m.cloud, m.top⟩

/-- Julia `mean(points[t[e]])` (Grassmann `src/composite.jl:936`: `sum(m)/N`, the sum left to
right, then Grassmann's division by a real, `x * (1/N)`, or `x / N` for real points): the
centroid of element `e` (0-based), computed on the flat encoding. -/
def centroid [FlatFiber P] [LinearFiber P] (m : FaceBundle n P G) (e : Nat) : P :=
  let w := FlatFiber.width P
  let vs := (m.top.get (e + 1)).toList.map fun v => (v - 1) * w
  let nf := Float.ofNat n
  let r := (1 : Float) / nf
  let comp (k : Nat) : Float :=
    let s := match vs with
      | [] => 0
      | o :: os => os.foldl (fun acc o' => acc + m.cloud.points[o' + k]!) m.cloud.points[o + k]!
    if LinearFiber.recipDiv P then s * r else s / nf
  FlatFiber.read (buildFlat w comp) 0

instance : FrameBundle (FaceBundle n P G) := ⟨fun m => m.top.elements⟩

/-- Julia `m[i]` (`fiber.jl:736-740`): the centroid, with the global metric (an induced metric),
or the mean of the vertex metrics. -/
instance [FlatFiber P] [LinearFiber P] [Inhabited G] :
    Coordinates (FaceBundle n P G) P G where
  point m e := m.centroid e
  metricAt m e := m.cloud.metric.get e

end FaceBundle

end Cartan
