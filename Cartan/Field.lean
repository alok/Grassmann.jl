import Cartan.Bundle

/-!
# `TensorField`: sections of a trivial bundle over a discretized base

Julia's `TensorField{B,F,N,M,A}` (Cartan.jl `src/Cartan.jl:100-106`) pairs a base `dom::M` (a
`FrameBundle`) with a fiber array `cod::A` of the same shape; its elements are the local tensors
`t[i] = base[i] ↦ fiber[i]`.

**The base is in the type.** `TensorField m F` is indexed by the base *value* `m`; the structure
stores only the fibers. Binary operations take two fields over the same `m`, so Julia's runtime
`checkdomain` (an O(n) structural comparison, `Cartan.jl:494`) is replaced by type checking at no
runtime cost, and the fibers always have the base's length (`size_data`). Dynamic code can pack a
field with its base (`AnyField`) and re-base it after a runtime check (`cast?`).

**Fibers are flat.** The values are one `FloatArray`, `width F` floats per point in column-major
point order (`FlatFiber`), so a field of `Chain V 1 Float` over `n` points is `n·dim` unboxed
floats, as Julia's `Vector{Chain}` is.

**Lazy ranges.** Julia keeps the identity field of a range lazy, and range arithmetic keeps it so
(`fiber(t + t) == 0.0:0.5:4.0`); its elements are then computed in `TwicePrecision`, and can differ
in the last bit from eager arithmetic (`3 .* (0:0.1:1)` vs `3 .* collect(0:0.1:1)`). A `Float`
field records the range its fibers equal in `range?` (always materialized in `data` as well);
the `Float` operations that Julia keeps lazy propagate it (`Cartan.Algebra`).

| Julia constructor (`Cartan.jl:109-160`) | Lean |
|---|---|
| C1 `TensorField(dom::FrameBundle, cod::Array)` | `ofArray?`, `ofFlat?` |
| C2/C10 `TensorField(range_or_space, fun)` (`fun` sees raw points) | `ofAxisFn`, `ofSpaceFn` |
| C11 `TensorField(dom::FrameBundle, fun)` (`fun` sees `Coordinate`s) | `tabulate` |
| C12 `TensorField(dom, x::Number)` | `const` |
| C13 `TensorField(dom)` (identity field) | `identity`, `ofAxis`, `ofSpace` |
| C5 `TensorField(dom::FrameBundle, cod::FrameBundle)` | `ofPoints?` |
| C6 `TensorField(a::TensorField, b::TensorField)` (base from `a`'s values) | `reparametrize` |
| C7 Bool arrays become `0.0/1.0` | `mapPred` |
| C8 `TensorField(dom, fun::TensorField)` | `rebase?` |
| C16 / `Chain.(t₁, …)` | `chainOf`; inverse `component`, `split` |
| `broadcast(f, t)` (raw fibers) / `f.(t)` (local tensors) (`Cartan.jl:167`, §4.2) | `map` / `mapLocal` |
-/

namespace Cartan

open Grassmann DirectSum StaticVectors AbstractTensors JuliaBase MeshTopology

/-- Julia `TensorField{B,F,N}` over the base `m` (a `FrameBundle`) with fibers of type `F`
(`Cartan.jl:100-106`): `card m` fiber values stored flat. -/
structure TensorField {M : Type} [FrameBundle M] (m : M) (F : Type) [FlatFiber F] where
  /-- The fibers (Julia `fiber(t)`), `width F` floats per point, column-major point order. -/
  data : FloatArray
  /-- One fiber per base point. -/
  size_data : data.size = FlatFiber.width F * card m
  /-- For a `Float` field: the Julia range its fibers equal, when Julia keeps them lazy (the
  identity field of a range and its range arithmetic). Always `none` for other fibers. -/
  range? : Option Axis := none

/-- A field packed with its base, for code that decides bases at runtime. -/
structure AnyField (M : Type) [FrameBundle M] (F : Type) [FlatFiber F] where
  /-- The base. -/
  base : M
  /-- The field. -/
  field : TensorField base F

namespace TensorField

variable {M : Type} [FrameBundle M] {m : M} {F F' F'' : Type}
  [FlatFiber F] [FlatFiber F'] [FlatFiber F'']

/-! ## Construction -/

/-- Write `f i, f (i+1), …, f (i+k-1)` at the offsets `off, off + w, …` (tail recursive). -/
@[specialize] def fillLoop (f : Nat → F) : (k i off : Nat) → FloatArray → FloatArray
  | 0, _, _, a => a
  | k + 1, i, off, a => fillLoop f k (i + 1) (off + FlatFiber.width F) (FlatFiber.write a off (f i))

@[simp] theorem size_fillLoop (f : Nat → F) : ∀ (k i off : Nat) (a : FloatArray),
    (fillLoop f k i off a).size = a.size
  | 0, _, _, _ => rfl
  | k + 1, i, off, a => by rw [fillLoop, size_fillLoop f k (i + 1), FlatFiber.size_write]

/-- The field `i ↦ f i` over `m` (`i` the 0-based linear index). All constructors reduce to it.
The fibers are written into a preallocated buffer (`Cartan.Flat.zeros`, `FlatFiber.write`):
no `FloatArray.push` per float. -/
@[inline] def ofFn (m : M) (f : Nat → F) : TensorField m F :=
  { data := fillLoop f (card m) 0 0 (Flat.zeros (FlatFiber.width F * card m)),
    size_data := by rw [size_fillLoop, Flat.size_zeros] }

/-- Julia `TensorField(dom, x::Number)` (C12): the constant field. -/
@[inline] def const (m : M) (x : F) : TensorField m F := ofFn m fun _ => x

/-- The zero field (every fiber decoded from zeros). -/
instance : Inhabited (TensorField m F) := ⟨ofFn m fun _ => FlatFiber.read FloatArray.empty 0⟩

/-- A field from its flat fiber data (C1), when it has the right length. -/
def ofFlat? (m : M) (data : FloatArray) : Option (TensorField m F) :=
  if h : data.size = FlatFiber.width F * card m then some ⟨data, h, none⟩ else none

/-- Julia `TensorField(dom, cod::Array)` (C1), when `cod` has one value per point. -/
def ofArray? (m : M) (xs : Array F) : Option (TensorField m F) :=
  if xs.size = card m then
    some (ofFn m fun i => match xs[i]? with | some x => x | none => FlatFiber.read FloatArray.empty 0)
  else none

/-! ## Access -/

/-- Julia `base(t)`. -/
@[inline] def base (_ : TensorField m F) : M := m

/-- Julia `length(t)`: the number of base points. -/
@[inline] def length (_ : TensorField m F) : Nat := card m

/-- Julia `fiber(t)[i+1]`: the fiber at the 0-based linear index `i` (unchecked: past the end it
decodes zeros). -/
@[inline] def get (t : TensorField m F) (i : Nat) : F := FlatFiber.read t.data (i * FlatFiber.width F)

/-- Julia `collect(fiber(t))`, boxed (for tests and display). -/
def fiberArray (t : TensorField m F) : Array F := (Array.range (card m)).map t.get

/-- The underlying flat fiber data (Julia `fiber(t)` as a flat array). -/
@[inline] def fiberFlat (t : TensorField m F) : FloatArray := t.data

/-- Write `src[j]` at `base + j` for `j ∈ [j₀, j₀+k)` (in place once unshared). -/
def writeLoop (src : FloatArray) (base : Nat) : (k j : Nat) → FloatArray → FloatArray
  | 0, _, out => out
  | k + 1, j, out => writeLoop src base k (j + 1) (out.set! (base + j) (src.get! j))

theorem size_writeLoop (src : FloatArray) (base : Nat) : ∀ (k j : Nat) (out : FloatArray),
    (writeLoop src base k j out).size = out.size
  | 0, _, _ => rfl
  | k + 1, j, out => by rw [writeLoop, size_writeLoop src base k (j + 1), FloatArray.size_set!']

/-- Julia `t[i+1] = x` (`setindex!`, `Cartan.jl:231-248`): the field with the fiber at `i` replaced
(in place when the fibers are not shared; out-of-range indices leave the field unchanged). -/
def set (t : TensorField m F) (i : Nat) (x : F) : TensorField m F :=
  let w := FlatFiber.width F
  ⟨writeLoop (FlatFiber.push FloatArray.empty x) (i * w) w 0 t.data,
    by rw [size_writeLoop]; exact t.size_data, none⟩

/-- The same fibers with the range tag dropped. -/
@[inline] def eager (t : TensorField m F) : TensorField m F := { t with range? := none }

/-! ## Maps (Julia broadcasting, port notes §4.2) -/

/-- Julia `broadcast(f, t) = TensorField(base(t), f.(fiber(t)))` (`Cartan.jl:167`): apply `f` to
every fiber value. -/
@[inline] def map (f : F → F') (t : TensorField m F) : TensorField m F' :=
  ofFn m fun i => f (t.get i)

/-- Combine two fields over the same base pointwise (Julia `op.(fiber(a), fiber(b))`). -/
@[inline] def zipWith (f : F → F' → F'') (a : TensorField m F) (b : TensorField m F') :
    TensorField m F'' :=
  ofFn m fun i => f (a.get i) (b.get i)

/-- Julia's `iszero.(t)`-style predicates: a `Bool`-valued map gives the `0.0`/`1.0` field
(C7, `Cartan.jl:150`). -/
@[inline] def mapPred (p : F → Bool) (t : TensorField m F) : TensorField m Float :=
  ofFn m fun i => if p (t.get i) then 1.0 else 0.0

/-- Re-base the fibers on another base with the same number of points (Julia
`TensorField(dom, fiber(t))`, C8); `none` if the point counts differ. -/
def rebase? {M' : Type} [FrameBundle M'] (m' : M') (t : TensorField m F) : Option (TensorField m' F) :=
  if h : card m' = card m then some ⟨t.data, h ▸ t.size_data, t.range?⟩ else none

/-- Re-base along an equality of bases (free at runtime). -/
@[inline] def cast {m' : M} (h : m = m') (t : TensorField m F) : TensorField m' F := h ▸ t

/-- Julia `checkdomain(a, b)` then the pair: `b` over `a`'s base when the bases are equal (Julia
`==`, `Cartan.jl:494`), else `none`. -/
def cast? [BEq M] {m' : M} (t : TensorField m' F) (m : M) : Option (TensorField m F) :=
  if m' == m then t.rebase? m else none

/-! ## Coordinates -/

section Coordinates

variable {P G : Type} [Coordinates M P G]

/-- Julia `TensorField(dom::FrameBundle, fun)` = `fun.(dom)` (C11): `f` receives the
`Coordinate`s (point and metric) of the base. -/
@[inline] def tabulate (m : M) (f : Coordinate P G → F) : TensorField m F :=
  ofFn m fun i => f (FrameBundle.coordinate m i)

/-- `tabulate` with a function of the point only (Julia `fun(point(x))`). -/
@[inline] def tabulatePoint (m : M) (f : P → F) : TensorField m F :=
  ofFn m fun i => f (Coordinates.point m i)

/-- Julia `TensorField(dom)` for a frame bundle (C13 → C5): the identity field, whose fibers are
the base points. -/
@[inline] def identity (m : M) [FlatFiber P] : TensorField m P := tabulatePoint m id

/-- Julia `TensorField(dom, points(cod))` (C5): the points of another bundle with the same number
of points as fibers. -/
def ofPoints? {M' : Type} [FrameBundle M'] [FlatFiber P] (m : M) (cod : M') [Coordinates M' P G] :
    Option (TensorField m P) :=
  if card cod = card m then some (ofFn m (Coordinates.point cod)) else none

/-- Julia `t[i+1]` (`Cartan.jl:227`): the local tensor `base[i] ↦ fiber[i]`. -/
@[inline] def localAt (t : TensorField m F) (i : Nat) : LocalTensor (Coordinate P G) F :=
  ⟨FrameBundle.coordinate m i, t.get i⟩

/-- Julia `f.(t)` (dot broadcasting over a field, `Cartan.jl:259-268`): `f` receives the local
tensors `coordinate ↦ fiber`, and its results become the new fibers over the same base. -/
@[inline] def mapLocal (f : LocalTensor (Coordinate P G) F → F') (t : TensorField m F) :
    TensorField m F' :=
  ofFn m fun i => f (t.localAt i)

/-- Julia `f.(a, b)` over two fields: `f` receives both local tensors (the base of the first). -/
@[inline] def zipLocal (f : LocalTensor (Coordinate P G) F → LocalTensor (Coordinate P G) F' → F'')
    (a : TensorField m F) (b : TensorField m F') : TensorField m F'' :=
  ofFn m fun i => f (a.localAt i) (b.localAt i)

/-- Julia `collect(t)` as local tensors (boxed). -/
def localArray (t : TensorField m F) : Array (LocalTensor (Coordinate P G) F) :=
  (Array.range (card m)).map t.localAt

/-- Julia `points(t)` (`Cartan.jl:201-206`), boxed. -/
def points (_ : TensorField m F) : Array P := FrameBundle.pointArray m

/-- Julia `graph(s)` of a local tensor (`topology.jl:372-378`): the point coordinates followed by
the fiber coordinates, as one vector of the Euclidean algebra (default basis `v₁ …`). -/
def graphAt [FlatFiber P] (t : TensorField m F) (i : Nat) :
    Chain (TensorBundle.euclidean (FlatFiber.width P + FlatFiber.width F)) 1 Float :=
  let buf := FlatFiber.push (FlatFiber.push FloatArray.empty (Coordinates.point m i)) (t.get i)
  ⟨Values.ofFn fun j => buf[j.1]!⟩

/-- Julia `graph(t) = graph.(t)` (`fiber.jl:45`): the field of graph points
`(point, fiber)` over the same base. -/
def graph [FlatFiber P] (t : TensorField m F) :
    TensorField m (Chain (TensorBundle.euclidean (FlatFiber.width P + FlatFiber.width F)) 1 Float) :=
  ofFn m t.graphAt

end Coordinates

/-! ## Components (Julia `getindex.(t, j)`, `split`, `Chain.(t₁, …)`) -/

section Components

variable {V : TensorBundle} {G : Nat}

/-- Julia `getindex.(t, j+1)`: component `j` of a `Chain` field as a scalar field. -/
@[inline] def component (t : TensorField m (Chain V G Float)) (j : Nat) : TensorField m Float :=
  let w := FlatFiber.width (Chain V G Float)
  ofFn m fun i => t.data[i * w + j]!

/-- Julia `split(t)` (`Cartan.jl:458-472`): the component scalar fields of a `Chain` field. -/
def split (t : TensorField m (Chain V G Float)) : Array (TensorField m Float) :=
  (Array.range (Leibniz.binomial V.n G)).map t.component

/-- Julia `Chain{V,G}.(t₁, …)` / `TensorField(::Chain of fields)` (`Cartan.jl:340`, C16): the
`Chain` field whose component `j` is the scalar field `fs j`. -/
def chainOf (V : TensorBundle) (G : Nat) (fs : Fin (Leibniz.binomial V.n G) → TensorField m Float) :
    TensorField m (Chain V G Float) :=
  ofFn m fun i => Chain.ofFn fun j => (fs j).get i

end Components

end TensorField

/-! ## Grid fields -/

namespace TensorField

variable {F : Type} [FlatFiber F]

/-- Julia `TensorField(r)` for a 1-D coordinate vector (C13): the identity field of an open
interval with real points. Its fibers *are* the range (lazy in Julia), recorded in `range?`. -/
def ofAxis (a : Axis) : TensorField (GridBundle.ofAxis a) Float :=
  { ofFn (GridBundle.ofAxis a) a.get with range? := if a.isRange then some a else none }

/-- Julia `TensorField(r, fun)` for a 1-D vector (C10): `fun` sees the real points. -/
@[inline] def ofAxisFn (a : Axis) (f : Float → F) : TensorField (GridBundle.ofAxis a) F :=
  ofFn (GridBundle.ofAxis a) fun i => f (a.get i)

/-- Julia `TensorField(ProductSpace(…))` (C13): the identity field of an open product grid; the
fibers are the (affine) points. -/
def ofSpace {N : Nat} (ps : ProductSpace N) : TensorField (GridBundle.ofSpace ps) (AffinePoint N) :=
  identity (GridBundle.ofSpace ps)

/-- Julia `TensorField(ProductSpace(…), fun)` (C10): `fun` sees the affine points. -/
@[inline] def ofSpaceFn {N : Nat} (ps : ProductSpace N) (f : AffinePoint N → F) :
    TensorField (GridBundle.ofSpace ps) F :=
  tabulatePoint (GridBundle.ofSpace ps) f

/-- `tabulatePoint` on a 1-D grid with `f` of the coordinate (no point is built). -/
@[inline] def tabulate1 {P G : Type} (b : GridBundle 1 P G) (f : Float → F) : TensorField b F :=
  let c0 := b.space.coords[0]
  ofFn b fun k => f (c0.get! k)

/-- `tabulatePoint` on a 2-D grid with `f` of the two coordinates (Julia
`(x -> f(x[1], x[2])).(g)` without building the points). -/
@[inline] def tabulate2 {P G : Type} (b : GridBundle 2 P G) (f : Float → Float → F) : TensorField b F :=
  let c0 := b.space.coords[0]
  let c1 := b.space.coords[1]
  let n0 := c0.size
  ofFn b fun k => f (c0.get! (k % n0)) (c1.get! (k / n0))

/-- `tabulatePoint` on a 3-D grid with `f` of the three coordinates. -/
@[inline] def tabulate3 {P G : Type} (b : GridBundle 3 P G) (f : Float → Float → Float → F) :
    TensorField b F :=
  let c0 := b.space.coords[0]
  let c1 := b.space.coords[1]
  let c2 := b.space.coords[2]
  let n0 := c0.size
  let n01 := n0 * c1.size
  ofFn b fun k => f (c0.get! (k % n0)) (c1.get! (k / n0 % c1.size)) (c2.get! (k / n01))

/-- Julia `TensorField(f, r)` (C14, `Cartan.jl:160`): the curve `f` sampled on `r` (Julia's
default `r = -2π:0.0001:2π`). Julia applies `vector` to each value; here `f` returns the fiber. -/
@[inline] def curve (f : Float → F) (r : Axis := Axis.colon (-twoPiF) (f64! 0.0001) twoPiF) :
    TensorField (GridBundle.ofAxis r) F := ofAxisFn r f

/-- The identity field of a 1-D real grid (C13), recording the range for Julia's lazy range
arithmetic when the points are a range. -/
def identity1 {G : Type} (b : GridBundle 1 Float G) : TensorField b Float :=
  let a := b.space.axes[0]
  { ofFn b a.get with range? := if a.isRange then some a else none }

/-- Julia `TensorField(a::TensorField, b::TensorField)` (C6, `Cartan.jl:115`): a new 1-D grid whose
points are the values of the real field `a`, carrying the fibers of `b` (the reparametrization
used by `arcparametrize`). A range-valued `a` keeps its range as the new axis. Julia also accepts
multi-dimensional `a`, giving a grid of non-product points; that is not modelled. -/
def reparametrize {M : Type} [FrameBundle M] {m : M} (a : TensorField m Float) (b : TensorField m F) :
    TensorField (GridBundle.ofAxis (a.range?.getD (.explicit a.data))) F :=
  ofFn _ fun i => b.get i

end TensorField

end Cartan
